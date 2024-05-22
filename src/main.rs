#![allow(unreachable_code, clippy::match_single_binding)]
use std::path::Path;
use std::sync::atomic::{AtomicU32, Ordering};

use ruff_python_ast as py;
use ruff_text_size::{Ranged, TextRange, TextSize};
use swc_common::source_map::Pos;
use swc_common::sync::Lrc;
use swc_common::Spanned;
use swc_common::{
    errors::{ColorConfig, Handler},
    SourceMap,
};
use swc_ecma_ast::{self as js, EsVersion};
use swc_ecma_parser::{lexer::Lexer, Parser, StringInput, Syntax};

trait Convert: Sized {
    type Py;
    fn convert(self, state: &State) -> Self::Py {
        self.convert2(state, py::ExprContext::Load)
    }
    fn convert2(self, state: &State, _ctx: py::ExprContext) -> Self::Py {
        self.convert(state)
    }
}

impl Convert for swc_common::Span {
    type Py = TextRange;
    fn convert(self, _state: &State) -> Self::Py {
        TextRange::new(
            TextSize::new(self.lo().to_usize() as u32),
            TextSize::new(self.hi().to_usize() as u32),
        )
    }
}
impl Convert for js::Ident {
    type Py = py::Identifier;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span,
            sym,
            optional: _,
        } = self;
        py::Identifier {
            range: span.convert(state),
            id: sym.as_str().to_owned(),
        }
    }
}
impl<T: Convert> Convert for Vec<T> {
    type Py = Vec<T::Py>;
    fn convert(self, state: &State) -> Self::Py {
        self.into_iter().map(|x| x.convert(state)).collect()
    }
}
impl<T: Convert> Convert for Option<T> {
    type Py = Option<T::Py>;
    fn convert(self, state: &State) -> Self::Py {
        self.map(|x| x.convert(state))
    }
}
impl<T: Convert> Convert for Box<T> {
    type Py = Box<T::Py>;
    fn convert(self, state: &State) -> Self::Py {
        Box::new((*self).convert(state))
    }
}

impl Convert for js::Module {
    type Py = py::ModModule;
    fn convert(self, state: &State) -> Self::Py {
        py::ModModule {
            range: self.span.convert(state),
            body: self.body.convert(state).into_iter().flatten().collect(),
        }
    }
}

impl Convert for js::ModuleItem {
    type Py = Vec<py::Stmt>;
    fn convert(self, state: &State) -> Self::Py {
        match self {
            Self::Stmt(s) => s.convert(state),
            Self::ModuleDecl(m) => match m {
                js::ModuleDecl::Import(js::ImportDecl {
                    span,
                    phase: _,
                    specifiers,
                    src,
                    type_only: _,
                    with: _,
                }) => {
                    let src = src.value.as_str();
                    let src = src
                        .trim_end_matches(".js")
                        .trim_end_matches(".ts")
                        .replace('/', ".");
                    specifiers
                        .into_iter()
                        .map(|spec| match spec {
                            js::ImportSpecifier::Named(js::ImportNamedSpecifier {
                                imported,
                                local,
                                span: _,
                                is_type_only: _,
                            }) => py::Stmt::ImportFrom(py::StmtImportFrom {
                                range: span.convert(state),
                                module: Some(py::Identifier::new(
                                    src.clone(),
                                    TextRange::default(),
                                )),
                                names: vec![py::Alias {
                                    range: TextRange::default(),
                                    asname: imported
                                        .is_some()
                                        .then(|| local.clone().convert(state)),
                                    name: imported
                                        .map(|x| match x {
                                            js::ModuleExportName::Str(js::Str {
                                                span,
                                                value,
                                                raw: _,
                                            }) => js::Ident {
                                                sym: value,
                                                span,
                                                optional: false,
                                            },
                                            js::ModuleExportName::Ident(x) => x,
                                        })
                                        .unwrap_or(local)
                                        .convert(state),
                                }],
                                level: 0,
                            }),
                            js::ImportSpecifier::Default(x) => {
                                py::Stmt::ImportFrom(py::StmtImportFrom {
                                    range: span.convert(state),
                                    module: Some(py::Identifier::new(
                                        src.clone(),
                                        TextRange::default(),
                                    )),
                                    names: vec![py::Alias {
                                        range: TextRange::default(),
                                        asname: Some(x.local.convert(state)),
                                        name: py::Identifier::new("default", TextRange::default()),
                                    }],
                                    level: 0,
                                })
                            }
                            js::ImportSpecifier::Namespace(_) => {
                                todo!("ImportSpecifier::Namespace")
                            }
                        })
                        .collect()
                }
                _ => todo!("{m:?}"),
            },
        }
    }
}

struct HopefullyExpr {
    expr: py::Expr,
    stmts: Vec<py::Stmt>,
}
impl HopefullyExpr {
    fn map(self, func: impl FnOnce(py::Expr, &mut Vec<py::Stmt>) -> py::Expr) -> Self {
        let Self { expr, mut stmts } = self;
        Self {
            expr: func(expr, &mut stmts),
            stmts,
        }
    }
    fn unwrap_into(self, stmts: &mut Vec<py::Stmt>) -> py::Expr {
        stmts.extend(self.stmts);
        self.expr
    }
}
impl From<py::Expr> for HopefullyExpr {
    fn from(value: py::Expr) -> Self {
        Self {
            expr: value,
            stmts: Vec::new(),
        }
    }
}
struct State(AtomicU32);
impl State {
    fn gen_name(&self) -> String {
        format!("ts2py_{}", self.0.fetch_add(1, Ordering::Relaxed))
    }
    fn gen_ident(&self) -> py::Identifier {
        py::Identifier::new(self.gen_name(), TextRange::default())
    }
}
impl From<py::Stmt> for HopefullyExpr {
    fn from(stmt: py::Stmt) -> Self {
        let name = match &stmt {
            py::Stmt::FunctionDef(x) => x.name.clone(),
            x => todo!("{x:?}"),
        };
        Self {
            expr: py::Expr::Name(py::ExprName {
                range: TextRange::default(),
                id: name.to_string(),
                ctx: py::ExprContext::Load,
            }),
            stmts: vec![stmt],
        }
    }
}

impl Convert for js::Pat {
    type Py = (py::Identifier, Vec<py::Stmt>);
    fn convert(self, _state: &State) -> Self::Py {
        match self {
            Self::Ident(x) => (
                py::Identifier::new(x.sym.as_str(), TextRange::default()),
                vec![],
            ),
            x => todo!("{x:?}"),
        }
    }
}

impl Convert for js::Callee {
    type Py = HopefullyExpr;
    fn convert(self, state: &State) -> Self::Py {
        match self {
            js::Callee::Expr(x) => (*x).convert(state),
            x => todo!("{x:?}"),
        }
    }
}
impl Convert for js::Expr {
    type Py = HopefullyExpr;
    fn convert2(self, state: &State, ctx: py::ExprContext) -> Self::Py {
        match self {
            js::Expr::Call(js::CallExpr {
                span,
                callee,
                args,
                type_args: _,
            }) => callee.convert(state).map(|expr, stmts| {
                py::Expr::Call(py::ExprCall {
                    range: span.convert(state),
                    func: Box::new(expr),
                    arguments: py::Arguments {
                        range: TextRange::default(),
                        args: args
                            .convert(state)
                            .into_iter()
                            .map(|x| x.unwrap_into(stmts))
                            .collect(),
                        keywords: Box::new([]),
                    },
                })
            }),
            js::Expr::Ident(js::Ident {
                sym,
                span,
                optional: _,
            }) => py::Expr::Name(py::ExprName {
                ctx,
                id: sym.as_str().into(),
                range: span.convert(state),
            })
            .into(),
            js::Expr::Lit(js::Lit::Str(js::Str {
                span,
                value,
                raw: _,
            })) => py::Expr::StringLiteral(py::ExprStringLiteral {
                range: span.convert(state),
                value: py::StringLiteralValue::single(py::StringLiteral {
                    range: span.convert(state),
                    value: value.as_str().into(),
                    flags: py::StringLiteralFlags::default(),
                }),
            })
            .into(),
            js::Expr::Lit(js::Lit::Num(num)) => py::Expr::NumberLiteral(py::ExprNumberLiteral {
                range: num.span.convert(state),
                value: num.convert(state),
            })
            .into(),
            js::Expr::Array(js::ArrayLit { span, elems }) => {
                let mut stmts = Vec::new();
                let expr = py::Expr::List(py::ExprList {
                    range: span.convert(state),
                    elts: elems
                        .convert(state)
                        .into_iter()
                        .flatten()
                        .map(|x| x.unwrap_into(&mut stmts))
                        .collect(),
                    ctx,
                });
                HopefullyExpr { expr, stmts }
            }
            js::Expr::Fn(js::FnExpr { ident, function }) => {
                let js::Function {
                    params,
                    decorators,
                    span,
                    body,
                    is_generator,
                    is_async,
                    return_type,
                    type_params,
                } = *function;
                assert!(!is_generator);
                py::Stmt::FunctionDef(py::StmtFunctionDef {
                    is_async,
                    range: span.convert(state),
                    name: ident
                        .map(|x| x.convert(state))
                        .unwrap_or_else(|| state.gen_ident()),
                    parameters: Box::new(py::Parameters {
                        range: TextRange::default(),
                        args: params.convert(state),
                        posonlyargs: vec![],
                        kwonlyargs: vec![],
                        vararg: None,
                        kwarg: None,
                    }),
                    body: body.convert(state).unwrap_or_default(),
                    decorator_list: decorators
                        .convert(state)
                        .into_iter()
                        .map(|x| py::Decorator {
                            range: x.range(),
                            expression: x,
                        })
                        .collect(),
                    returns: return_type.convert(state),
                    type_params: type_params.map(|x| {
                        Box::new(py::TypeParams {
                            range: TextRange::default(),
                            type_params: (*x).convert(state),
                        })
                    }),
                })
                .into()
            }
            js::Expr::New(js::NewExpr {
                span,
                callee,
                args,
                type_args: _,
            }) => (*callee).convert(state).map(|expr, stmts| {
                py::Expr::Call(py::ExprCall {
                    range: span.convert(state),
                    func: Box::new(expr),
                    arguments: py::Arguments {
                        range: TextRange::default(),
                        args: args
                            .unwrap_or_default()
                            .convert(state)
                            .into_iter()
                            .map(|x| x.unwrap_into(stmts))
                            .collect(),
                        keywords: Box::new([]),
                    },
                })
            }),
            js::Expr::Arrow(js::ArrowExpr {
                span,
                params,
                body,
                type_params,
                is_async,
                is_generator,
                return_type: _,
            }) => {
                assert!(!is_generator);
                let mut stmts = vec![];
                let args = params
                    .convert(state)
                    .into_iter()
                    .map(|(id, stmts2)| {
                        stmts.extend(stmts2);
                        py::ParameterWithDefault {
                            range: TextRange::default(),
                            default: None,
                            parameter: py::Parameter {
                                range: TextRange::default(),
                                annotation: None,
                                name: id,
                            },
                        }
                    })
                    .collect();
                let parameters = py::Parameters {
                    range: TextRange::default(),
                    args,
                    posonlyargs: vec![],
                    kwonlyargs: vec![],
                    vararg: None,
                    kwarg: None,
                };
                let expr = match *body {
                    js::BlockStmtOrExpr::Expr(x) => {
                        Some((*x).convert(state).unwrap_into(&mut stmts))
                    }
                    js::BlockStmtOrExpr::BlockStmt(x) => {
                        stmts.extend(x.convert(state));
                        None
                    }
                };
                if stmts.is_empty() && expr.is_some() && !is_async && !is_generator {
                    let expr = expr.unwrap();
                    py::Expr::Lambda(py::ExprLambda {
                        range: span.convert(state),
                        body: Box::new(expr),
                        parameters: Some(Box::new(parameters)),
                    })
                    .into()
                } else {
                    if let Some(expr) = expr {
                        stmts.push(py::Stmt::Return(py::StmtReturn {
                            range: expr.range(),
                            value: Some(Box::new(expr)),
                        }));
                    }
                    py::Stmt::FunctionDef(py::StmtFunctionDef {
                        is_async,
                        range: span.convert(state),
                        name: state.gen_ident(),
                        parameters: Box::new(parameters),
                        body: stmts,
                        decorator_list: vec![],
                        returns: None,
                        type_params: type_params.map(|x| {
                            Box::new(py::TypeParams {
                                range: TextRange::default(),
                                type_params: (*x).convert(state),
                            })
                        }),
                    })
                    .into()
                }
            }
            js::Expr::Await(js::AwaitExpr { span, arg }) => {
                arg.convert(state).map(|expr, _stmts| {
                    py::Expr::Await(py::ExprAwait {
                        range: span.convert(state),
                        value: Box::new(expr),
                    })
                })
            }
            js::Expr::Member(js::MemberExpr { span, obj, prop }) => {
                (*obj).convert(state).map(|obj, stmts| match prop {
                    js::MemberProp::Ident(prop) => py::Expr::Attribute(py::ExprAttribute {
                        range: span.convert(state),
                        attr: prop.convert(state),
                        ctx,
                        value: Box::new(obj),
                    }),
                    js::MemberProp::Computed(js::ComputedPropName { span, expr }) => {
                        py::Expr::Subscript(py::ExprSubscript {
                            range: span.convert(state),
                            slice: Box::new(expr.convert(state).unwrap_into(stmts)),
                            ctx,
                            value: Box::new(obj),
                        })
                    }
                    x => todo!("{x:?}"),
                })
            }
            js::Expr::Bin(js::BinExpr {
                span,
                op,
                left,
                right,
            }) => (*left).convert(state).map(|left, stmts| {
                let right = right.convert(state).unwrap_into(stmts);
                py::Expr::BinOp(py::ExprBinOp {
                    range: span.convert(state),
                    op: match op {
                        js::BinaryOp::Div => py::Operator::Div,
                        js::BinaryOp::Add => py::Operator::Add,
                        js::BinaryOp::NullishCoalescing | js::BinaryOp::LogicalOr => {
                            return py::Expr::BoolOp(py::ExprBoolOp {
                                range: span.convert(state),
                                op: py::BoolOp::Or,
                                values: vec![left, right],
                            })
                        }
                        x => todo!("{x:?}"),
                    },
                    left: Box::new(left),
                    right: Box::new(right),
                })
            }),
            js::Expr::Paren(js::ParenExpr { span: _, expr }) => (*expr).convert(state),
            x => todo!("{x:?}"),
        }
    }
}

impl Convert for js::Number {
    type Py = py::Number;
    fn convert(self, _state: &State) -> Self::Py {
        let s = self.value.to_string();
        let s = if s.contains('.') {
            s.trim_end_matches('0').trim_end_matches('.')
        } else {
            &s
        };
        if !s.bytes().all(|x| x.is_ascii_digit()) {
            py::Number::Float(self.value)
        } else {
            py::Number::Int(s.parse().unwrap())
        }
    }
}

impl Convert for js::TsTypeAnn {
    type Py = py::Expr;
    fn convert(self, _state: &State) -> Self::Py {
        todo!()
    }
}

impl Convert for js::Decorator {
    type Py = py::Expr;
    fn convert(self, _state: &State) -> Self::Py {
        todo!()
    }
}

impl Convert for js::BlockStmt {
    type Py = Vec<py::Stmt>;
    fn convert(self, state: &State) -> Self::Py {
        self.stmts.convert(state).into_iter().flatten().collect()
    }
}

impl Convert for js::Stmt {
    type Py = Vec<py::Stmt>;
    fn convert(self, state: &State) -> Self::Py {
        match self {
            js::Stmt::Expr(js::ExprStmt { span, expr }) => {
                let HopefullyExpr { expr, mut stmts } = (*expr).convert(state);
                stmts.push(py::Stmt::Expr(py::StmtExpr {
                    range: span.convert(state),
                    value: Box::new(expr),
                }));
                stmts
            }
            js::Stmt::Decl(decl) => match decl {
                js::Decl::Var(d) => d
                    .decls
                    .into_iter()
                    .flat_map(|d| {
                        let (id, stmts2) = d.name.convert(state);
                        let HopefullyExpr { expr, mut stmts } = (*d.init.unwrap()).convert(state);
                        stmts.push(py::Stmt::Assign(py::StmtAssign {
                            range: d.span.convert(state),
                            targets: vec![py::Expr::Name(py::ExprName {
                                range: d.span.convert(state),
                                id: id.as_str().to_owned(),
                                ctx: py::ExprContext::Store,
                            })],
                            value: Box::new(expr),
                        }));
                        stmts.extend(stmts2);
                        stmts
                    })
                    .collect(),
                d => todo!("{d:?}"),
            },
            s => todo!("{s:?}"),
        }
    }
}

impl Convert for js::Param {
    type Py = py::ParameterWithDefault;
    fn convert(self, _state: &State) -> Self::Py {
        todo!()
    }
}

impl Convert for js::TsTypeParamDecl {
    type Py = Vec<py::TypeParam>;
    fn convert(self, _state: &State) -> Self::Py {
        todo!()
    }
}

impl Convert for js::ExprOrSpread {
    type Py = HopefullyExpr;
    fn convert(self, state: &State) -> Self::Py {
        if let Some(_spread) = self.spread {
            let span = self.span();
            (*self.expr).convert(state).map(|expr, _stmts| {
                py::Expr::Starred(py::ExprStarred {
                    range: span.convert(state),
                    value: Box::new(expr),
                    ctx: py::ExprContext::Load,
                })
            })
        } else {
            (*self.expr).convert(state)
        }
    }
}

fn main() {
    let cm: Lrc<SourceMap> = Default::default();
    let handler = Handler::with_tty_emitter(ColorConfig::Auto, true, false, Some(cm.clone()));

    let fm = cm
        .load_file(Path::new("test.ts"))
        .expect("failed to load test.ts");
    /*let fm = cm.new_source_file(
        FileName::Custom("test.ts".into()),
        "function foo() {}".into(),
    );*/
    let lexer = Lexer::new(
        // We want to parse ecmascript
        Syntax::Typescript(Default::default()),
        // EsVersion defaults to es5
        EsVersion::EsNext,
        StringInput::from(&*fm),
        None,
    );

    let mut parser = Parser::new_from(lexer);

    for e in parser.take_errors() {
        e.into_diagnostic(&handler).emit();
    }

    let module = parser
        .parse_module()
        .map_err(|e| {
            // Unrecoverable fatal error occurred
            e.into_diagnostic(&handler).emit()
        })
        .expect("failed to parser module");
    let module = module.convert(&State(0.into()));
    let locator = ruff_source_file::Locator::new("");
    let stylist = ruff_python_codegen::Stylist::from_tokens(&[], &locator);
    for stmt in module.body {
        let gen = ruff_python_codegen::Generator::new(
            stylist.indentation(),
            stylist.quote(),
            stylist.line_ending(),
        );
        println!("{}", gen.stmt(&stmt));
    }
}
