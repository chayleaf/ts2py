#![allow(clippy::match_single_binding)]
use std::collections::HashSet;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU32, Ordering};

use dashmap::DashSet;
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
            id: safe_name(sym.as_str()),
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

fn safe_name(s: &str) -> String {
    let mut s = (if matches!(s.chars().next(), Some(c) if unicode_ident::is_xid_start(c) || !unicode_ident::is_xid_continue(c)) {
        None
    } else {
        Some('_')
    })
    .into_iter()
    .chain(s.chars())
    .enumerate()
    .map(|(i, x)| {
        if if i == 0 { unicode_ident::is_xid_start(x) } else { unicode_ident::is_xid_continue(x) } {
            x
        } else {
            '_'
        }
    })
    .collect::<String>();
    match s.as_str() {
        "" | "False" | "await" | "else" | "import" | "pass" | "None" | "break" | "except"
        | "in" | "raise" | "True" | "class" | "finally" | "is" | "return" | "and" | "continue"
        | "for" | "lambda" | "try" | "as" | "def" | "from" | "nonlocal" | "while" | "assert"
        | "del" | "global" | "not" | "with" | "async" | "elif" | "if" | "or" | "yield" => {
            s.push('_')
        }
        _ => {}
    }
    s
}

fn safe_block(mut stmts: Vec<py::Stmt>) -> Vec<py::Stmt> {
    if stmts.is_empty() {
        stmts.push(py::Stmt::Pass(py::StmtPass {
            range: TextRange::default(),
        }));
    }
    stmts
}

fn safe_params(params: py::Parameters) -> py::Parameters {
    let py::Parameters {
        range,
        posonlyargs,
        args,
        vararg,
        kwarg,
        kwonlyargs,
    } = params;
    let mut must_have_default = false;
    py::Parameters {
        range,
        posonlyargs,
        args: args
            .into_iter()
            .map(|mut x| {
                if x.default.is_some() {
                    must_have_default = true;
                } else if must_have_default {
                    x.default = match &**x.parameter.annotation.as_ref().unwrap() {
                        py::Expr::Name(x) => match x.id.as_str() {
                            "str" => {
                                Some(Box::new(py::Expr::StringLiteral(py::ExprStringLiteral {
                                    range: TextRange::default(),
                                    value: py::StringLiteralValue::single(py::StringLiteral {
                                        range: TextRange::default(),
                                        value: "".into(),
                                        flags: py::StringLiteralFlags::default(),
                                    }),
                                })))
                            }
                            x => todo!("{x:?}"),
                        },
                        _ => Some(Box::new(py::Expr::NoneLiteral(py::ExprNoneLiteral {
                            range: TextRange::default(),
                        }))), // todo!("{x:?}"),
                    };
                }
                x
            })
            .collect(),
        vararg,
        kwarg,
        kwonlyargs,
    }
}

impl Convert for js::Module {
    type Py = py::ModModule;
    fn convert(self, state: &State) -> Self::Py {
        let mut ret = py::ModModule {
            range: self.span.convert(state),
            body: self.body.convert(state).into_iter().flatten().collect(),
        };
        if !state.py_imports.is_empty() {
            ret.body.insert(
                0,
                py::Stmt::Import(py::StmtImport {
                    range: TextRange::default(),
                    names: state
                        .py_imports
                        .iter()
                        .map(|x| py::Alias {
                            range: TextRange::default(),
                            name: py::Identifier::new(safe_name(x.as_str()), TextRange::default()),
                            asname: None,
                        })
                        .collect(),
                }),
            );
        }
        ret
    }
}

fn convert_import_path(script_path: &Path, src: &str, flatten_dirs: &HashSet<PathBuf>) -> String {
    let mut path = script_path.to_owned();
    path.pop();
    let src = src
        .strip_suffix(".ts")
        .or_else(|| src.strip_suffix(".js"))
        .unwrap_or(src);
    for comp in src.split('/') {
        if comp == ".." {
            path.pop();
        } else if comp != "." && !comp.is_empty() {
            path.push(comp);
        }
    }
    let mut ret = ".".to_owned();
    let mut path2 = PathBuf::new();
    if path.ends_with("index") {
        path.pop();
    }
    for comp in path.iter() {
        path2.push(comp);
        let comp2 = safe_name(comp.to_str().unwrap());
        ret.push_str(&comp2);
        if flatten_dirs.contains(&path2) {
            ret.push('_');
        } else {
            ret.push('.');
        }
    }
    ret.pop();
    ret
}

fn cleanup_import(state: &State, src: &str) -> String {
    if src.starts_with("./") || src.starts_with("../") {
        let conv1 = convert_import_path(&state.script_path, src, &state.flatten_dirs);
        let conv2 = convert_import_path(
            &state.script_path,
            if state.script_path.ends_with("index.js") || state.script_path.ends_with("index.ts") {
                "."
            } else {
                state
                    .script_path
                    .file_name()
                    .unwrap_or_default()
                    .to_str()
                    .unwrap()
            },
            &state.flatten_dirs,
        );
        let conv2 = conv2
            .split('.')
            .rev()
            .skip(1)
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
            .collect::<Vec<_>>()
            .join(".");
        let mut ret = conv1.strip_prefix(&conv2).unwrap().to_owned();
        if ret.is_empty() {
            ret.push('.');
        }
        ret
    } else {
        src.trim_end_matches(".js")
            .trim_end_matches(".ts")
            .trim_end_matches('/')
            .split('/')
            .map(safe_name)
            .fold(String::new(), |mut a, b| {
                if !a.is_empty() {
                    a.push('.');
                }
                a.push_str(&b);
                a
            })
    }
}

impl Convert for js::ImportDecl {
    type Py = Vec<py::Stmt>;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span,
            phase: _,
            specifiers,
            src,
            type_only: _,
            with: _,
        } = self;
        state.add_import(src.value.as_str());
        let src = cleanup_import(state, src.value.as_str());
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
                    module: Some(py::Identifier::new(&src, TextRange::default())),
                    names: vec![py::Alias {
                        range: TextRange::default(),
                        asname: imported.is_some().then(|| local.clone().convert(state)),
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
                js::ImportSpecifier::Default(x) => py::Stmt::ImportFrom(py::StmtImportFrom {
                    range: span.convert(state),
                    module: Some(py::Identifier::new(&src, TextRange::default())),
                    names: vec![py::Alias {
                        range: TextRange::default(),
                        asname: Some(x.local.convert(state)),
                        name: py::Identifier::new(safe_name("default"), TextRange::default()),
                    }],
                    level: 0,
                }),
                js::ImportSpecifier::Namespace(_) => {
                    todo!("ImportSpecifier::Namespace")
                }
            })
            .collect()
    }
}

impl Convert for js::ExportAll {
    type Py = py::StmtImportFrom;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span,
            src,
            type_only: _,
            with: _,
        } = self;
        state.add_import(src.value.as_str());
        let src = cleanup_import(state, src.value.as_str());
        py::StmtImportFrom {
            range: span.convert(state),
            module: Some(py::Identifier::new(src, TextRange::default())),
            names: vec![py::Alias {
                range: TextRange::default(),
                asname: None,
                name: py::Identifier::new("*", TextRange::default()),
            }],
            level: 0,
        }
    }
}

impl Convert for js::ExportDecl {
    type Py = Vec<py::Stmt>;
    fn convert(self, state: &State) -> Self::Py {
        let Self { span: _, decl } = self;
        decl.convert(state)
    }
}

fn expr_stmt(e: py::Expr) -> py::Stmt {
    match e {
        py::Expr::Named(py::ExprNamed {
            range,
            target,
            value,
        }) => py::Stmt::Assign(py::StmtAssign {
            range,
            targets: vec![*target],
            value,
        }),
        x => py::Stmt::Expr(py::StmtExpr {
            range: TextRange::default(),
            value: Box::new(x),
        }),
    }
}

impl Convert for js::ModuleItem {
    type Py = Vec<py::Stmt>;
    fn convert(self, state: &State) -> Self::Py {
        match self {
            Self::Stmt(s) => s.convert(state),
            Self::ModuleDecl(m) => match m {
                js::ModuleDecl::Import(decl) => decl.convert(state),
                js::ModuleDecl::ExportDecl(decl) => decl.convert(state),
                js::ModuleDecl::ExportAll(decl) => vec![py::Stmt::ImportFrom(decl.convert(state))],
                _ => todo!("{m:?}"),
            },
        }
    }
}

#[derive(Debug)]
struct WithStmts<T> {
    expr: T,
    stmts: Vec<py::Stmt>,
}
type HopefullyExpr = WithStmts<py::Expr>;
impl<T> WithStmts<T> {
    fn map<Y>(self, func: impl FnOnce(T, &mut Vec<py::Stmt>) -> Y) -> WithStmts<Y> {
        let Self { expr, mut stmts } = self;
        WithStmts {
            expr: func(expr, &mut stmts),
            stmts,
        }
    }
    fn map1<Y>(self, func: impl FnOnce(T) -> Y) -> WithStmts<Y> {
        let Self { expr, stmts } = self;
        WithStmts {
            expr: func(expr),
            stmts,
        }
    }
    fn unwrap_into(self, stmts: &mut Vec<py::Stmt>) -> T {
        stmts.extend(self.stmts);
        self.expr
    }
}
impl<T> From<T> for WithStmts<T> {
    fn from(value: T) -> Self {
        Self {
            expr: value,
            stmts: Vec::new(),
        }
    }
}
#[derive(Default)]
struct State {
    id: AtomicU32,
    py_imports: DashSet<String>,
    js_imports: DashSet<String>,
    script_path: PathBuf,
    flatten_dirs: HashSet<PathBuf>,
}
impl State {
    fn new(script_path: &Path, flatten_dirs: &HashSet<PathBuf>) -> Self {
        Self {
            script_path: script_path.to_owned(),
            flatten_dirs: flatten_dirs.clone(),
            ..Default::default()
        }
    }
    fn gen_name(&self) -> String {
        format!("ts2py_{}", self.id.fetch_add(1, Ordering::Relaxed))
    }
    fn gen_ident(&self) -> py::Identifier {
        py::Identifier::new(self.gen_name(), TextRange::default())
    }
    #[must_use]
    fn import(&self, name: &str) -> py::Expr {
        self.py_imports.insert(name.to_owned());
        py::Expr::Name(py::ExprName {
            range: TextRange::default(),
            id: name.to_owned(),
            ctx: py::ExprContext::Load,
        })
    }
    fn add_import(&self, name: &str) {
        self.js_imports.insert(name.to_owned());
    }
}
impl From<py::Stmt> for HopefullyExpr {
    fn from(stmt: py::Stmt) -> Self {
        Self::from(vec![stmt])
    }
}
impl From<Vec<py::Stmt>> for HopefullyExpr {
    fn from(stmts: Vec<py::Stmt>) -> Self {
        let name = match stmts.last().unwrap() {
            py::Stmt::FunctionDef(x) => x.name.clone(),
            py::Stmt::ClassDef(x) => x.name.clone(),
            py::Stmt::Assign(x) => {
                assert!(x.targets.len() == 1);
                match &x.targets[0] {
                    py::Expr::Name(x) => py::Identifier::new(x.id.clone(), x.range),
                    x => todo!("{x:?}"),
                }
            }
            x => todo!("{x:?}"),
        };
        Self {
            expr: py::Expr::Name(py::ExprName {
                range: TextRange::default(),
                id: name.to_string(),
                ctx: py::ExprContext::Load,
            }),
            stmts,
        }
    }
}

impl Convert for js::ObjectPat {
    type Py = WithStmts<PatPy>;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span: _,
            props,
            optional: _,
            type_ann,
        } = self;
        let id = state.gen_ident();
        let mut stmts = vec![];
        let mut body_stmts = vec![];
        for prop in props {
            match prop {
                js::ObjectPatProp::Assign(js::AssignPatProp {
                    span,
                    key,
                    value: _,
                }) => {
                    body_stmts.push(py::Stmt::Assign(py::StmtAssign {
                        range: span.convert(state),
                        targets: vec![py::Expr::Name(py::ExprName {
                            range: TextRange::default(),
                            id: key.id.clone().convert(state).id,
                            ctx: py::ExprContext::Load,
                        })],
                        value: Box::new(py::Expr::Attribute(py::ExprAttribute {
                            range: TextRange::default(),
                            attr: key.id.convert(state),
                            value: Box::new(py::Expr::Name(py::ExprName {
                                range: TextRange::default(),
                                id: safe_name(&id.id),
                                ctx: py::ExprContext::Load,
                            })),
                            ctx: py::ExprContext::Load,
                        })),
                    }));
                }
                js::ObjectPatProp::KeyValue(js::KeyValuePatProp { key, value }) => {
                    // assign key to value
                    let PatPy {
                        id: val,
                        type_ann,
                        body_stmts: stmts2,
                        def_val: _,
                    } = (*value).convert(state).unwrap_into(&mut stmts);
                    body_stmts.extend(stmts2);
                    let target = py::Expr::Name(py::ExprName {
                        range: TextRange::default(),
                        id: safe_name(&val.id),
                        ctx: py::ExprContext::Load,
                    });
                    let value = Box::new(py::Expr::Attribute(py::ExprAttribute {
                        range: TextRange::default(),
                        attr: match key.convert(state) {
                            WithStmts {
                                expr: py::Expr::StringLiteral(x),
                                stmts,
                            } if stmts.is_empty() => {
                                py::Identifier::new(safe_name(x.value.to_str()), x.range)
                            }
                            x => todo!("{x:?}"),
                        },
                        value: Box::new(py::Expr::Name(py::ExprName {
                            range: TextRange::default(),
                            id: safe_name(&id.id),
                            ctx: py::ExprContext::Load,
                        })),
                        ctx: py::ExprContext::Load,
                    }));
                    body_stmts.push(if let Some(ann) = type_ann {
                        py::Stmt::AnnAssign(py::StmtAnnAssign {
                            range: TextRange::default(),
                            target: Box::new(target),
                            value: Some(value),
                            annotation: Box::new(ann),
                            simple: true,
                        })
                    } else {
                        py::Stmt::Assign(py::StmtAssign {
                            range: TextRange::default(),
                            targets: vec![target],
                            value,
                        })
                    });
                }
                js::ObjectPatProp::Rest(x) => todo!("{x:?}"),
            }
        }
        WithStmts {
            expr: PatPy {
                id,
                type_ann: type_ann.map(|x| (*x).convert(state).unwrap_into(&mut stmts)),
                body_stmts,
                ..Default::default()
            },
            stmts,
        }
    }
}

struct PatPy<T = py::Identifier> {
    id: T,
    type_ann: Option<py::Expr>,
    body_stmts: Vec<py::Stmt>,
    def_val: Option<py::Expr>,
}

impl<T> PatPy<T> {
    fn map<Y>(self, x: impl FnOnce(T) -> Y) -> PatPy<Y> {
        PatPy {
            id: x(self.id),
            type_ann: self.type_ann,
            body_stmts: self.body_stmts,
            def_val: self.def_val,
        }
    }
}

impl Default for PatPy<py::Identifier> {
    fn default() -> Self {
        Self {
            id: py::Identifier {
                id: String::new(),
                range: TextRange::default(),
            },
            type_ann: None,
            body_stmts: vec![],
            def_val: None,
        }
    }
}

impl Default for PatPy<py::Expr> {
    fn default() -> Self {
        Self {
            id: py::Expr::Name(py::ExprName {
                range: TextRange::default(),
                id: String::new(),
                ctx: py::ExprContext::Load,
            }),
            type_ann: None,
            body_stmts: vec![],
            def_val: None,
        }
    }
}

impl Convert for js::Pat {
    type Py = WithStmts<PatPy>;
    fn convert(self, state: &State) -> Self::Py {
        match self {
            Self::Ident(js::BindingIdent { id, type_ann }) => {
                let mut stmts = Vec::new();
                WithStmts {
                    expr: PatPy {
                        id: id.convert(state),
                        type_ann: type_ann.map(|x| (*x).convert(state).unwrap_into(&mut stmts)),
                        ..Default::default()
                    },
                    stmts,
                }
            }
            Self::Object(x) => x.convert(state),
            Self::Array(x) => x.convert(state),
            Self::Rest(x) => x.convert(state),
            Self::Assign(x) => x.convert(state),
            x => todo!("{x:?}"),
        }
    }
}

impl Convert for js::AssignPat {
    type Py = WithStmts<PatPy>;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span: _,
            left,
            right,
        } = self;
        left.convert(state).map(|mut x, stmts| {
            x.def_val = Some((*right).convert(state).unwrap_into(stmts));
            x
        })
    }
}

impl Convert for js::RestPat {
    type Py = WithStmts<PatPy>;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span: _,
            dot3_token: _,
            arg,
            type_ann: _,
        } = self;
        (*arg).convert(state)
    }
}

impl Convert for js::ArrayPat {
    type Py = WithStmts<PatPy>;
    fn convert(self, state: &State) -> Self::Py {
        let id = state.gen_ident();
        let Self {
            span,
            elems,
            optional: _,
            type_ann,
        } = self;
        let mut body_stmts = vec![];
        let mut stmts = vec![];
        let ann = type_ann.map(|x| (*x).convert(state).unwrap_into(&mut stmts));
        let value = Box::new(py::Expr::Name(py::ExprName {
            range: id.range,
            id: safe_name(&id.id),
            ctx: py::ExprContext::Load,
        }));
        let target = py::Expr::Tuple(py::ExprTuple {
            range: span.convert(state),
            ctx: py::ExprContext::Store,
            parenthesized: false,
            elts: elems
                .into_iter()
                .map(|x| {
                    x.map_or_else(
                        || {
                            py::Expr::Name(py::ExprName {
                                range: TextRange::default(),
                                id: "_".to_owned(),
                                ctx: py::ExprContext::Store,
                            })
                        },
                        |x| {
                            // don't unwrap into stmts because it only contains type-related stmts, and type ann is
                            // ignored here
                            let PatPy {
                                id: x,
                                type_ann: _,
                                body_stmts: stmts2,
                                def_val: _,
                            } = x.convert(state).expr;
                            body_stmts.extend(stmts2);
                            py::Expr::Name(py::ExprName {
                                range: x.range,
                                id: safe_name(&x.id),
                                ctx: py::ExprContext::Store,
                            })
                        },
                    )
                })
                .collect(),
        });
        let ret = py::Stmt::Assign(py::StmtAssign {
            range: span.convert(state),
            value,
            targets: vec![target],
        });
        body_stmts.push(ret);
        WithStmts {
            expr: PatPy {
                id,
                type_ann: ann,
                body_stmts,
                ..Default::default()
            },
            stmts,
        }
    }
}

impl Convert for js::Callee {
    type Py = HopefullyExpr;
    fn convert(self, state: &State) -> Self::Py {
        match self {
            Self::Expr(x) => (*x).convert(state),
            Self::Super(x) => x.convert(state).into(),
            Self::Import(x) => todo!("{x:?}"),
        }
    }
}
impl Convert for js::Super {
    type Py = py::Expr;
    fn convert(self, state: &State) -> Self::Py {
        let Self { span } = self;
        py::Expr::Attribute(py::ExprAttribute {
            range: span.convert(state),
            ctx: py::ExprContext::Load,
            value: Box::new(py::Expr::Call(py::ExprCall {
                range: TextRange::default(),
                func: Box::new(py::Expr::Name(py::ExprName {
                    range: TextRange::default(),
                    id: "super".to_owned(),
                    ctx: py::ExprContext::Load,
                })),
                arguments: py::Arguments {
                    range: TextRange::default(),
                    args: Box::new([]),
                    keywords: Box::new([]),
                },
            })),
            attr: py::Identifier::new("__init__", TextRange::default()),
        })
    }
}
impl Convert for js::CallExpr {
    type Py = WithStmts<py::ExprCall>;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span,
            callee,
            args,
            type_args: _,
        } = self;
        callee.convert(state).map(|expr, stmts| py::ExprCall {
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
    }
}
impl Convert for js::NewExpr {
    type Py = WithStmts<py::ExprCall>;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span,
            callee,
            args,
            type_args: _,
        } = self;
        callee.convert(state).map(|expr, stmts| py::ExprCall {
            range: span.convert(state),
            func: Box::new(expr),
            arguments: py::Arguments {
                range: TextRange::default(),
                args: args
                    .convert(state)
                    .unwrap_or_default()
                    .into_iter()
                    .map(|x| x.unwrap_into(stmts))
                    .collect(),
                keywords: Box::new([]),
            },
        })
    }
}
impl Convert for js::Lit {
    type Py = py::Expr;
    fn convert2(self, state: &State, _ctx: py::ExprContext) -> Self::Py {
        match self {
            Self::Str(js::Str {
                span,
                value,
                raw: _,
            }) => py::Expr::StringLiteral(py::ExprStringLiteral {
                range: span.convert(state),
                value: py::StringLiteralValue::single(py::StringLiteral {
                    range: span.convert(state),
                    value: value.as_str().into(),
                    flags: py::StringLiteralFlags::default(),
                }),
            }),
            Self::Num(num) => py::Expr::NumberLiteral(py::ExprNumberLiteral {
                range: num.span.convert(state),
                value: num.convert(state),
            }),
            Self::Null(js::Null { span }) => py::Expr::NoneLiteral(py::ExprNoneLiteral {
                range: span.convert(state),
            }),
            Self::Bool(js::Bool { span, value }) => {
                py::Expr::BooleanLiteral(py::ExprBooleanLiteral {
                    range: span.convert(state),
                    value,
                })
            }
            x => todo!("{x:?}"),
        }
    }
}
impl Convert for js::ArrayLit {
    type Py = WithStmts<py::ExprList>;
    fn convert2(self, state: &State, ctx: py::ExprContext) -> Self::Py {
        let Self { span, elems } = self;
        let mut stmts = Vec::new();
        let expr = py::ExprList {
            range: span.convert(state),
            elts: elems
                .convert(state)
                .into_iter()
                .flatten()
                .map(|x| x.unwrap_into(&mut stmts))
                .collect(),
            ctx,
        };
        WithStmts { expr, stmts }
    }
}
fn convert_func(
    state: &State,
    ident: Option<js::Ident>,
    function: js::Function,
) -> WithStmts<py::StmtFunctionDef> {
    let js::Function {
        params,
        decorators,
        span,
        body,
        is_generator,
        is_async,
        return_type,
        type_params,
    } = function;
    assert!(!is_generator);
    let mut body_stmts = vec![];
    let returns = return_type.map(|x| Box::new((*x).convert(state).unwrap_into(&mut body_stmts)));
    let type_params =
        type_params.map(|x| Box::new((*x).convert(state).unwrap_into(&mut body_stmts)));
    let mut ret_stmts = vec![];
    WithStmts {
        expr: py::StmtFunctionDef {
            is_async,
            range: span.convert(state),
            name: ident.map_or_else(|| state.gen_ident(), |x| x.convert(state)),
            parameters: Box::new(safe_params(py::Parameters {
                range: TextRange::default(),
                args: params
                    .convert(state)
                    .into_iter()
                    .map(|x| {
                        let (a, b) = x.unwrap_into(&mut ret_stmts);
                        body_stmts.extend(b);
                        a
                    })
                    .collect(),
                posonlyargs: vec![],
                kwonlyargs: vec![],
                vararg: None,
                kwarg: None,
            })),
            body: {
                body_stmts.extend(body.convert(state).unwrap_or_default());
                safe_block(body_stmts)
            },
            decorator_list: decorators
                .convert(state)
                .into_iter()
                .map(|x| py::Decorator {
                    range: x.range(),
                    expression: x,
                })
                .collect(),
            returns,
            type_params,
        },
        stmts: ret_stmts,
    }
}
impl Convert for js::FnExpr {
    type Py = WithStmts<py::StmtFunctionDef>;
    fn convert(self, state: &State) -> Self::Py {
        let Self { ident, function } = self;
        convert_func(state, ident, *function)
    }
}
impl Convert for js::ArrowExpr {
    type Py = HopefullyExpr;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span,
            params,
            body,
            type_params,
            is_async,
            is_generator,
            return_type: _,
        } = self;
        assert!(!is_generator);
        let mut body_stmts = vec![];
        let mut stmts = vec![];
        let args = params
            .convert(state)
            .into_iter()
            .map(|x| {
                let PatPy {
                    id,
                    type_ann,
                    body_stmts: stmts2,
                    def_val,
                } = x.unwrap_into(&mut stmts);
                body_stmts.extend(stmts2);
                py::ParameterWithDefault {
                    range: TextRange::default(),
                    default: def_val.map(Box::new),
                    parameter: py::Parameter {
                        range: TextRange::default(),
                        annotation: type_ann.map(Box::new),
                        name: id,
                    },
                }
            })
            .collect();
        let mut parameters = py::Parameters {
            range: TextRange::default(),
            args,
            posonlyargs: vec![],
            kwonlyargs: vec![],
            vararg: None,
            kwarg: None,
        };
        let expr = match *body {
            js::BlockStmtOrExpr::Expr(x) => Some((*x).convert(state).unwrap_into(&mut body_stmts)),
            js::BlockStmtOrExpr::BlockStmt(x) => {
                body_stmts.extend(x.convert(state));
                None
            }
        };
        if body_stmts.is_empty() && expr.is_some() && !is_async && !is_generator {
            let expr = expr.unwrap();
            // lambdas cant have type params
            for arg in &mut parameters.args {
                arg.parameter.annotation = None;
            }
            WithStmts {
                expr: py::Expr::Lambda(py::ExprLambda {
                    range: span.convert(state),
                    body: Box::new(expr),
                    parameters: Some(Box::new(safe_params(parameters))),
                }),
                stmts,
            }
        } else {
            if let Some(expr) = expr {
                body_stmts.push(py::Stmt::Return(py::StmtReturn {
                    range: expr.range(),
                    value: Some(Box::new(expr)),
                }));
            }
            let ret = py::Stmt::FunctionDef(py::StmtFunctionDef {
                is_async,
                range: span.convert(state),
                name: state.gen_ident(),
                parameters: Box::new(safe_params(parameters)),
                body: safe_block(body_stmts),
                decorator_list: vec![],
                returns: None,
                type_params: type_params
                    .map(|x| Box::new((*x).convert(state).unwrap_into(&mut stmts))),
            });
            stmts.push(ret);
            stmts.into()
        }
    }
}
impl Convert for js::AwaitExpr {
    type Py = WithStmts<py::ExprAwait>;
    fn convert(self, state: &State) -> Self::Py {
        let Self { span, arg } = self;
        arg.convert(state).map1(|expr| py::ExprAwait {
            range: span.convert(state),
            value: Box::new(expr),
        })
    }
}
impl Convert for js::MemberExpr {
    type Py = HopefullyExpr;
    fn convert2(self, state: &State, ctx: py::ExprContext) -> Self::Py {
        let Self { span, obj, prop } = self;
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
            js::MemberProp::PrivateName(x) => todo!("{x:?}"),
        })
    }
}
impl Convert for js::UnaryExpr {
    type Py = HopefullyExpr;
    fn convert(self, state: &State) -> Self::Py {
        let Self { span, op, arg } = self;
        arg.convert(state).map1(|expr| {
            py::Expr::UnaryOp(py::ExprUnaryOp {
                range: span.convert(state),
                op: match op {
                    js::UnaryOp::Plus => py::UnaryOp::UAdd,
                    js::UnaryOp::Bang => py::UnaryOp::Not,
                    js::UnaryOp::Minus => py::UnaryOp::USub,
                    js::UnaryOp::Tilde => py::UnaryOp::Invert,
                    x => todo!("{x:?}"),
                },
                operand: Box::new(expr),
            })
        })
    }
}
impl Convert for js::BinExpr {
    type Py = HopefullyExpr;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span,
            op,
            left,
            right,
        } = self;
        (*left).convert(state).map(|left, stmts| {
            let right = right.convert(state).unwrap_into(stmts);
            py::Expr::BinOp(py::ExprBinOp {
                range: span.convert(state),
                op: match op {
                    js::BinaryOp::NullishCoalescing | js::BinaryOp::LogicalOr => {
                        return py::Expr::BoolOp(py::ExprBoolOp {
                            range: span.convert(state),
                            op: py::BoolOp::Or,
                            values: vec![left, right],
                        })
                    }
                    js::BinaryOp::LogicalAnd => {
                        return py::Expr::BoolOp(py::ExprBoolOp {
                            range: span.convert(state),
                            op: py::BoolOp::And,
                            values: vec![left, right],
                        })
                    }
                    js::BinaryOp::EqEq => {
                        return py::Expr::Compare(py::ExprCompare {
                            range: span.convert(state),
                            ops: Box::new([py::CmpOp::Eq]),
                            left: Box::new(left),
                            comparators: Box::new([right]),
                        })
                    }
                    js::BinaryOp::NotEq => {
                        return py::Expr::Compare(py::ExprCompare {
                            range: span.convert(state),
                            ops: Box::new([py::CmpOp::NotEq]),
                            left: Box::new(left),
                            comparators: Box::new([right]),
                        })
                    }
                    js::BinaryOp::EqEqEq => {
                        return py::Expr::Compare(py::ExprCompare {
                            range: span.convert(state),
                            ops: Box::new([py::CmpOp::Is]),
                            left: Box::new(left),
                            comparators: Box::new([right]),
                        })
                    }
                    js::BinaryOp::NotEqEq => {
                        return py::Expr::Compare(py::ExprCompare {
                            range: span.convert(state),
                            ops: Box::new([py::CmpOp::IsNot]),
                            left: Box::new(left),
                            comparators: Box::new([right]),
                        })
                    }
                    js::BinaryOp::GtEq => {
                        return py::Expr::Compare(py::ExprCompare {
                            range: span.convert(state),
                            ops: Box::new([py::CmpOp::GtE]),
                            left: Box::new(left),
                            comparators: Box::new([right]),
                        })
                    }
                    js::BinaryOp::LtEq => {
                        return py::Expr::Compare(py::ExprCompare {
                            range: span.convert(state),
                            ops: Box::new([py::CmpOp::LtE]),
                            left: Box::new(left),
                            comparators: Box::new([right]),
                        })
                    }
                    js::BinaryOp::Gt => {
                        return py::Expr::Compare(py::ExprCompare {
                            range: span.convert(state),
                            ops: Box::new([py::CmpOp::Gt]),
                            left: Box::new(left),
                            comparators: Box::new([right]),
                        })
                    }
                    js::BinaryOp::Lt => {
                        return py::Expr::Compare(py::ExprCompare {
                            range: span.convert(state),
                            ops: Box::new([py::CmpOp::Lt]),
                            left: Box::new(left),
                            comparators: Box::new([right]),
                        })
                    }
                    js::BinaryOp::InstanceOf => {
                        return py::Expr::Call(py::ExprCall {
                            range: span.convert(state),
                            func: Box::new(py::Expr::Name(py::ExprName {
                                range: TextRange::default(),
                                id: "isinstance".to_owned(),
                                ctx: py::ExprContext::Load,
                            })),
                            arguments: py::Arguments {
                                range: span.convert(state),
                                args: Box::new([left, right]),
                                keywords: Box::new([]),
                            },
                        })
                    }
                    js::BinaryOp::In => {
                        return py::Expr::Compare(py::ExprCompare {
                            range: span.convert(state),
                            ops: Box::new([py::CmpOp::In]),
                            left: Box::new(left),
                            comparators: Box::new([right]),
                        })
                    }
                    js::BinaryOp::Div => py::Operator::Div,
                    js::BinaryOp::Add => py::Operator::Add,
                    js::BinaryOp::Sub => py::Operator::Sub,
                    js::BinaryOp::Mul => py::Operator::Mult,
                    js::BinaryOp::BitOr => py::Operator::BitOr,
                    x => todo!("{x:?}"),
                },
                left: Box::new(left),
                right: Box::new(right),
            })
        })
    }
}
impl Convert for js::Expr {
    type Py = HopefullyExpr;
    fn convert2(self, state: &State, ctx: py::ExprContext) -> Self::Py {
        match self {
            Self::Call(expr) => expr.convert2(state, ctx).map1(py::Expr::Call),
            Self::Ident(js::Ident {
                sym,
                span,
                optional: _,
            }) => match sym.as_str() {
                "undefined" => py::Expr::NoneLiteral(py::ExprNoneLiteral {
                    range: span.convert(state),
                }),
                "Promise" => py::Expr::Attribute(py::ExprAttribute {
                    range: span.convert(state),
                    value: Box::new(py::Expr::Attribute(py::ExprAttribute {
                        range: span.convert(state),
                        value: Box::new(state.import("collections")),
                        attr: py::Identifier::new("abc", TextRange::default()),
                        ctx: py::ExprContext::Load,
                    })),
                    attr: py::Identifier::new("Coroutine", TextRange::default()),
                    ctx,
                }),
                "Iterator" => py::Expr::Attribute(py::ExprAttribute {
                    range: span.convert(state),
                    value: Box::new(py::Expr::Attribute(py::ExprAttribute {
                        range: span.convert(state),
                        value: Box::new(state.import("collections")),
                        attr: py::Identifier::new("abc", TextRange::default()),
                        ctx: py::ExprContext::Load,
                    })),
                    attr: py::Identifier::new("Iterator", TextRange::default()),
                    ctx,
                }),
                "AsyncIterator" => py::Expr::Attribute(py::ExprAttribute {
                    range: span.convert(state),
                    value: Box::new(py::Expr::Attribute(py::ExprAttribute {
                        range: span.convert(state),
                        value: Box::new(state.import("collections")),
                        attr: py::Identifier::new("abc", TextRange::default()),
                        ctx: py::ExprContext::Load,
                    })),
                    attr: py::Identifier::new("AsyncIterator", TextRange::default()),
                    ctx,
                }),
                "Generator" => py::Expr::Attribute(py::ExprAttribute {
                    range: span.convert(state),
                    value: Box::new(py::Expr::Attribute(py::ExprAttribute {
                        range: span.convert(state),
                        value: Box::new(state.import("collections")),
                        attr: py::Identifier::new("abc", TextRange::default()),
                        ctx: py::ExprContext::Load,
                    })),
                    attr: py::Identifier::new("Generator", TextRange::default()),
                    ctx,
                }),
                "AsyncGenerator" => py::Expr::Attribute(py::ExprAttribute {
                    range: span.convert(state),
                    value: Box::new(py::Expr::Attribute(py::ExprAttribute {
                        range: span.convert(state),
                        value: Box::new(state.import("collections")),
                        attr: py::Identifier::new("abc", TextRange::default()),
                        ctx: py::ExprContext::Load,
                    })),
                    attr: py::Identifier::new("AsyncGenerator", TextRange::default()),
                    ctx,
                }),
                "atob" => py::Expr::Attribute(py::ExprAttribute {
                    range: span.convert(state),
                    value: Box::new(state.import("base64")),
                    attr: py::Identifier::new("b64decode", TextRange::default()),
                    ctx,
                }),
                "btoa" => py::Expr::Attribute(py::ExprAttribute {
                    range: span.convert(state),
                    value: Box::new(state.import("base64")),
                    attr: py::Identifier::new("b64encode", TextRange::default()),
                    ctx,
                }),
                "Infinity" => py::Expr::Attribute(py::ExprAttribute {
                    range: span.convert(state),
                    value: Box::new(state.import("math")),
                    attr: py::Identifier::new("inf", TextRange::default()),
                    ctx,
                }),
                "NaN" => py::Expr::Attribute(py::ExprAttribute {
                    range: span.convert(state),
                    value: Box::new(state.import("math")),
                    attr: py::Identifier::new("nan", TextRange::default()),
                    ctx,
                }),
                "Object" => py::Expr::Attribute(py::ExprAttribute {
                    range: span.convert(state),
                    value: Box::new(state.import("typing")),
                    attr: py::Identifier::new("Any", TextRange::default()),
                    ctx,
                }),
                "Date" => py::Expr::Attribute(py::ExprAttribute {
                    range: span.convert(state),
                    value: Box::new(state.import("datetime")),
                    attr: py::Identifier::new("datetime", TextRange::default()),
                    ctx,
                }),
                "Math" => state.import("math"),
                "Function" => py::Expr::Attribute(py::ExprAttribute {
                    range: span.convert(state),
                    value: Box::new(py::Expr::Attribute(py::ExprAttribute {
                        range: span.convert(state),
                        value: Box::new(state.import("collections")),
                        attr: py::Identifier::new("abc", TextRange::default()),
                        ctx: py::ExprContext::Load,
                    })),
                    attr: py::Identifier::new("Callable", TextRange::default()),
                    ctx,
                }),
                s => py::Expr::Name(py::ExprName {
                    ctx,
                    id: match s {
                        "Error" => "Exception".to_owned(),
                        "RangeError" => "ValueError".to_owned(),
                        "Boolean" => "bool".to_owned(),
                        "parseInt" | "BigInt" => "int".to_owned(),
                        "parseFloat" | "Number" => "float".to_owned(),
                        "String" => "str".to_owned(),
                        "Array" => "list".to_owned(),
                        "Map" => "dict".to_owned(),
                        "Set" => "set".to_owned(),
                        s => safe_name(s),
                    },
                    range: span.convert(state),
                }),
            }
            .into(),
            Self::Lit(lit) => lit.convert2(state, ctx).into(),
            Self::Array(lit) => lit.convert2(state, ctx).map1(py::Expr::List),
            Self::Fn(expr) => {
                let WithStmts { expr, mut stmts } = expr.convert2(state, ctx);
                stmts.push(py::Stmt::FunctionDef(expr));
                stmts.into()
            }
            Self::New(expr) => expr.convert2(state, ctx).map1(py::Expr::Call),
            Self::Arrow(expr) => expr.convert2(state, ctx),
            Self::Await(expr) => expr.convert2(state, ctx).map1(py::Expr::Await),
            Self::Member(expr) => expr.convert2(state, ctx),
            Self::Bin(expr) => expr.convert2(state, ctx),
            Self::Unary(expr) => expr.convert2(state, ctx),
            Self::Paren(js::ParenExpr { span: _, expr }) => (*expr).convert2(state, ctx),
            Self::Object(lit) => lit.convert2(state, ctx).map1(py::Expr::Dict),
            Self::Tpl(tpl) => tpl.convert2(state, ctx).map1(py::Expr::FString),
            Self::Assign(expr) => expr.convert2(state, ctx),
            Self::Cond(expr) => expr.convert2(state, ctx),
            Self::TsAs(expr) => expr.convert2(state, ctx),
            Self::This(expr) => expr.convert2(state, ctx).into(),
            Self::TsNonNull(expr) => expr.convert2(state, ctx),
            Self::OptChain(expr) => expr.convert2(state, ctx),
            Self::Update(expr) => expr.convert2(state, ctx),
            Self::SuperProp(expr) => expr.convert2(state, ctx),
            Self::TaggedTpl(expr) => expr.convert2(state, ctx),
            x => todo!("{x:?}"),
        }
    }
}

impl Convert for js::SuperPropExpr {
    type Py = HopefullyExpr;
    fn convert(self, state: &State) -> Self::Py {
        let Self { span, obj, prop } = self;
        let js::Super { span: obj_span } = obj;
        let sup = Box::new(py::Expr::Call(py::ExprCall {
            range: obj_span.convert(state),
            func: Box::new(py::Expr::Name(py::ExprName {
                range: obj_span.convert(state),
                id: "super".to_owned(),
                ctx: py::ExprContext::Load,
            })),
            arguments: py::Arguments {
                range: TextRange::default(),
                args: Box::new([]),
                keywords: Box::new([]),
            },
        }));
        match prop {
            js::SuperProp::Ident(id) => py::Expr::Attribute(py::ExprAttribute {
                range: span.convert(state),
                ctx: py::ExprContext::Load,
                value: sup,
                attr: id.convert(state),
            })
            .into(),
            js::SuperProp::Computed(x) => todo!("{x:?}"),
        }
    }
}

impl Convert for js::UpdateExpr {
    type Py = HopefullyExpr;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span,
            op,
            prefix,
            arg,
        } = self;
        let mut stmts = vec![];
        // prefix = ++i, !prefix = i++
        let arg = (*arg).convert(state).unwrap_into(&mut stmts);
        if arg.is_name_expr() {
            let expr = py::Expr::Named(py::ExprNamed {
                range: span.convert(state),
                target: Box::new(arg.clone()),
                value: Box::new(py::Expr::BinOp(py::ExprBinOp {
                    range: TextRange::default(),
                    left: Box::new(arg.clone()),
                    op: match op {
                        js::UpdateOp::PlusPlus => py::Operator::Add,
                        js::UpdateOp::MinusMinus => py::Operator::Sub,
                    },
                    right: Box::new(py::Expr::NumberLiteral(py::ExprNumberLiteral {
                        range: TextRange::default(),
                        value: py::Number::Int(py::Int::ONE),
                    })),
                })),
            });
            if prefix {
                WithStmts {
                    expr,
                    stmts: vec![],
                }
            } else {
                let var = state.gen_name();
                WithStmts {
                    expr: py::Expr::Subscript(py::ExprSubscript {
                        range: span.convert(state),
                        ctx: py::ExprContext::Load,
                        value: Box::new(py::Expr::Tuple(py::ExprTuple {
                            range: TextRange::default(),
                            elts: vec![
                                py::Expr::Named(py::ExprNamed {
                                    range: TextRange::default(),
                                    target: Box::new(py::Expr::Name(py::ExprName {
                                        range: TextRange::default(),
                                        id: var,
                                        ctx: py::ExprContext::Store,
                                    })),
                                    value: Box::new(arg),
                                }),
                                expr,
                            ],
                            ctx: py::ExprContext::Load,
                            parenthesized: true,
                        })),
                        slice: Box::new(py::Expr::NumberLiteral(py::ExprNumberLiteral {
                            range: TextRange::default(),
                            value: py::Number::Int(py::Int::ZERO),
                        })),
                    }),
                    stmts: vec![],
                }
            }
        } else {
            let stmt = py::Stmt::AugAssign(py::StmtAugAssign {
                range: span.convert(state),
                target: Box::new(arg.clone()),
                op: match op {
                    js::UpdateOp::PlusPlus => py::Operator::Add,
                    js::UpdateOp::MinusMinus => py::Operator::Sub,
                },
                value: Box::new(py::Expr::NumberLiteral(py::ExprNumberLiteral {
                    range: TextRange::default(),
                    value: py::Number::Int(py::Int::ONE),
                })),
            });
            if prefix {
                stmts.push(stmt);
                WithStmts { expr: arg, stmts }
            } else {
                let tmp = state.gen_name();
                stmts.push(py::Stmt::Assign(py::StmtAssign {
                    range: span.convert(state),
                    targets: vec![py::Expr::Name(py::ExprName {
                        range: TextRange::default(),
                        id: tmp.clone(),
                        ctx: py::ExprContext::Store,
                    })],
                    value: Box::new(arg),
                }));
                stmts.push(stmt);
                WithStmts {
                    expr: py::Expr::Name(py::ExprName {
                        range: TextRange::default(),
                        id: tmp,
                        ctx: py::ExprContext::Load,
                    }),
                    stmts,
                }
            }
        }
    }
}

impl Convert for js::OptChainExpr {
    type Py = HopefullyExpr;
    fn convert2(self, state: &State, ctx: py::ExprContext) -> Self::Py {
        let Self {
            span: _,
            optional: _,
            base,
        } = self;
        (*base).convert2(state, ctx)
    }
}

impl Convert for js::OptChainBase {
    type Py = HopefullyExpr;
    fn convert2(self, state: &State, ctx: py::ExprContext) -> Self::Py {
        match self {
            Self::Call(js::OptCall {
                span,
                callee,
                args,
                type_args,
            }) => {
                assert!(type_args.is_none());
                callee.convert(state).map(|expr, stmts| {
                    py::Expr::BoolOp(py::ExprBoolOp {
                        range: span.convert(state),
                        op: py::BoolOp::And,
                        values: vec![
                            expr.clone(),
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
                            }),
                        ],
                    })
                })
            }
            Self::Member(js::MemberExpr { span, obj, prop }) => {
                (*obj).convert(state).map(|obj, stmts| {
                    py::Expr::BoolOp(py::ExprBoolOp {
                        range: span.convert(state),
                        op: py::BoolOp::And,
                        values: vec![
                            obj.clone(),
                            match prop {
                                js::MemberProp::Ident(prop) => {
                                    py::Expr::Attribute(py::ExprAttribute {
                                        range: span.convert(state),
                                        attr: prop.convert(state),
                                        ctx,
                                        value: Box::new(obj),
                                    })
                                }
                                js::MemberProp::Computed(js::ComputedPropName { span, expr }) => {
                                    py::Expr::Subscript(py::ExprSubscript {
                                        range: span.convert(state),
                                        slice: Box::new(expr.convert(state).unwrap_into(stmts)),
                                        ctx,
                                        value: Box::new(obj),
                                    })
                                }
                                js::MemberProp::PrivateName(x) => todo!("{x:?}"),
                            },
                        ],
                    })
                })
            }
        }
    }
}

impl Convert for js::TsNonNullExpr {
    type Py = HopefullyExpr;
    fn convert2(self, state: &State, ctx: py::ExprContext) -> Self::Py {
        let Self { span: _, expr } = self;
        (*expr).convert2(state, ctx)
    }
}

impl Convert for js::ThisExpr {
    type Py = py::Expr;
    fn convert2(self, state: &State, ctx: py::ExprContext) -> Self::Py {
        let Self { span } = self;
        py::Expr::Name(py::ExprName {
            range: span.convert(state),
            id: "self".to_owned(),
            ctx,
        })
    }
}

impl Convert for js::TsAsExpr {
    type Py = HopefullyExpr;
    fn convert2(self, state: &State, ctx: py::ExprContext) -> Self::Py {
        let Self {
            span: _,
            expr,
            type_ann: _,
        } = self;
        (*expr).convert2(state, ctx)
    }
}

impl Convert for js::CondExpr {
    type Py = HopefullyExpr;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span,
            test,
            cons,
            alt,
        } = self;
        let mut stmts = Vec::new();
        let test = (*test).convert(state).unwrap_into(&mut stmts);
        let WithStmts {
            expr: cons,
            stmts: mut stmts2,
        } = (*cons).convert(state);
        let WithStmts {
            expr: alt,
            stmts: mut stmts3,
        } = (*alt).convert(state);
        if stmts2.is_empty() && stmts3.is_empty() {
            return WithStmts {
                expr: py::Expr::BoolOp(py::ExprBoolOp {
                    range: span.convert(state),
                    op: py::BoolOp::And,
                    values: vec![
                        py::Expr::BoolOp(py::ExprBoolOp {
                            range: span.convert(state),
                            op: py::BoolOp::And,
                            values: vec![test, cons],
                        }),
                        alt,
                    ],
                }),
                stmts,
            };
        }
        let tmp = state.gen_name();
        stmts2.push(py::Stmt::Assign(py::StmtAssign {
            range: TextRange::default(),
            targets: vec![py::Expr::Name(py::ExprName {
                ctx: py::ExprContext::Store,
                range: TextRange::default(),
                id: tmp.clone(),
            })],
            value: Box::new(cons),
        }));
        stmts3.push(py::Stmt::Assign(py::StmtAssign {
            range: TextRange::default(),
            targets: vec![py::Expr::Name(py::ExprName {
                ctx: py::ExprContext::Store,
                range: TextRange::default(),
                id: tmp.clone(),
            })],
            value: Box::new(alt),
        }));
        stmts.push(py::Stmt::If(py::StmtIf {
            range: TextRange::default(),
            test: Box::new(test),
            body: safe_block(stmts2),
            elif_else_clauses: vec![py::ElifElseClause {
                range: TextRange::default(),
                test: None,
                body: safe_block(stmts3),
            }],
        }));
        WithStmts {
            stmts,
            expr: py::Expr::Name(py::ExprName {
                ctx: py::ExprContext::Load,
                range: TextRange::default(),
                id: tmp,
            }),
        }
    }
}

impl Convert for js::AssignExpr {
    type Py = HopefullyExpr;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span,
            op,
            left,
            right,
        } = self;
        let WithStmts {
            expr:
                PatPy {
                    id: target,
                    type_ann,
                    body_stmts,
                    def_val: _,
                },
            stmts: stmts2,
        } = left.convert2(state, py::ExprContext::Store);
        let WithStmts { expr, mut stmts } = (*right).convert(state);
        match op {
            js::AssignOp::Assign => {
                if stmts2.len() == 1
                    && expr.is_name_expr()
                    && matches!(stmts2[0], py::Stmt::ClassDef(_) | py::Stmt::FunctionDef(_))
                {
                    let py::ExprName { range, id, ctx: _ } = target.clone().name_expr().unwrap();
                    match &mut stmts[0] {
                        py::Stmt::ClassDef(x) => x.name = py::Identifier { id, range },
                        py::Stmt::FunctionDef(x) => x.name = py::Identifier { id, range },
                        x => todo!("{x:?}"),
                    }
                    stmts.extend(stmts2);
                } else {
                    stmts.extend(stmts2);
                    stmts.push(if let Some(type_ann) = type_ann {
                        py::Stmt::AnnAssign(py::StmtAnnAssign {
                            range: span.convert(state),
                            target: Box::new(target.clone()),
                            annotation: Box::new(type_ann),
                            simple: target.is_name_expr(),
                            value: Some(Box::new(expr)),
                        })
                    } else if body_stmts.is_empty() && target.is_name_expr() {
                        return WithStmts {
                            expr: py::Expr::Named(py::ExprNamed {
                                range: span.convert(state),
                                target: Box::new(target),
                                value: Box::new(expr),
                            }),
                            stmts,
                        };
                    } else {
                        py::Stmt::Assign(py::StmtAssign {
                            range: span.convert(state),
                            targets: vec![target.clone()],
                            value: Box::new(expr),
                        })
                    });
                }
                stmts.extend(body_stmts);
                WithStmts {
                    expr: target,
                    stmts,
                }
            }
            x => {
                stmts.extend(stmts2);
                stmts.push(py::Stmt::AugAssign(py::StmtAugAssign {
                    range: span.convert(state),
                    target: Box::new(target.clone()),
                    value: Box::new(expr),
                    op: match x {
                        js::AssignOp::AddAssign => py::Operator::Add,
                        x => todo!("{x:?}"),
                    },
                }));
                stmts.extend(body_stmts);
                WithStmts {
                    expr: target,
                    stmts,
                }
            }
        }
    }
}

impl Convert for js::AssignTarget {
    type Py = WithStmts<PatPy<py::Expr>>;
    fn convert(self, state: &State) -> Self::Py {
        match self {
            Self::Simple(x) => match x {
                js::SimpleAssignTarget::Member(x) => {
                    x.convert2(state, py::ExprContext::Store).map1(|x| PatPy {
                        id: x,
                        ..Default::default()
                    })
                }
                js::SimpleAssignTarget::Ident(js::BindingIdent { id, type_ann }) => {
                    let py::Identifier { range, id } = id.convert2(state, py::ExprContext::Store);
                    let mut stmts = Vec::new();
                    let type_ann = type_ann.map(|x| (*x).convert(state).unwrap_into(&mut stmts));
                    WithStmts {
                        expr: PatPy {
                            id: py::Expr::Name(py::ExprName {
                                range,
                                id,
                                ctx: py::ExprContext::Store,
                            }),
                            type_ann,
                            ..Default::default()
                        },
                        stmts,
                    }
                }
                x => todo!("{x:?}"),
            },
            Self::Pat(x) => match x {
                js::AssignTargetPat::Array(x) => x.convert(state).map1(|x| {
                    x.map(|x| {
                        py::Expr::Name(py::ExprName {
                            range: x.range,
                            id: x.id,
                            ctx: py::ExprContext::Store,
                        })
                    })
                }),
                x => todo!("{x:?}"),
            },
        }
    }
}

impl Convert for js::TaggedTpl {
    type Py = WithStmts<py::Expr>;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span,
            tag,
            type_params: _,
            tpl,
        } = self;
        (*tag).convert(state).map(|tag, stmts| {
            py::Expr::Call(py::ExprCall {
                range: span.convert(state),
                func: Box::new(tag),
                arguments: py::Arguments {
                    range: TextRange::default(),
                    args: Box::new([py::Expr::FString((*tpl).convert(state).unwrap_into(stmts))]),
                    keywords: Box::new([]),
                },
            })
        })
    }
}

impl Convert for js::Tpl {
    type Py = WithStmts<py::ExprFString>;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span,
            exprs,
            quasis,
        } = self;
        let mut stmts = vec![];
        WithStmts {
            expr: py::ExprFString {
                range: span.convert(state),
                value: py::FStringValue::single(py::FString {
                    range: span.convert(state),
                    elements: py::FStringElements::from(
                        quasis
                            .into_iter()
                            .zip(exprs.into_iter().map(Some).chain([None]))
                            .flat_map(|(q, e)| {
                                std::iter::once(py::FStringElement::Literal(q.convert(state)))
                                    .chain(e.map(|e| {
                                        py::FStringElement::Expression(
                                            py::FStringExpressionElement {
                                                range: e.span().convert(state),
                                                expression: Box::new(
                                                    (*e).convert(state).unwrap_into(&mut stmts),
                                                ),
                                                debug_text: None,
                                                conversion: py::ConversionFlag::None,
                                                format_spec: None,
                                            },
                                        )
                                    }))
                            })
                            .collect::<Vec<_>>(),
                    ),
                    flags: py::FStringFlags::default(),
                }),
            },
            stmts,
        }
    }
}

impl Convert for js::TplElement {
    type Py = py::FStringLiteralElement;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span,
            tail: _,
            cooked,
            raw: _,
        } = self;
        py::FStringLiteralElement {
            range: span.convert(state),
            value: cooked.unwrap().as_str().into(),
        }
    }
}

impl Convert for js::ObjectLit {
    type Py = WithStmts<py::ExprDict>;
    fn convert(self, state: &State) -> Self::Py {
        let Self { span, props } = self;
        let mut stmts = Vec::new();
        WithStmts {
            expr: py::ExprDict {
                range: span.convert(state),
                items: props
                    .into_iter()
                    .map(|x| x.convert(state).unwrap_into(&mut stmts))
                    .collect(),
            },
            stmts,
        }
    }
}
impl Convert for js::PropName {
    type Py = HopefullyExpr;
    fn convert(self, state: &State) -> Self::Py {
        match self {
            Self::Ident(js::Ident {
                span,
                sym,
                optional: _,
            }) => py::Expr::StringLiteral(py::ExprStringLiteral {
                range: span.convert(state),
                value: py::StringLiteralValue::single(py::StringLiteral {
                    range: span.convert(state),
                    value: sym.as_str().into(),
                    flags: py::StringLiteralFlags::default(),
                }),
            })
            .into(),
            Self::Computed(js::ComputedPropName { span: _, expr }) => (*expr).convert(state),
            Self::Str(js::Str {
                span,
                value,
                raw: _,
            }) => py::Expr::StringLiteral(py::ExprStringLiteral {
                range: span.convert(state),
                value: py::StringLiteralValue::single(py::StringLiteral {
                    range: span.convert(state),
                    value: value.as_str().into(),
                    flags: py::StringLiteralFlags::default(),
                }),
            })
            .into(),
            x => todo!("{x:?}"),
        }
    }
}

impl Convert for js::PropOrSpread {
    type Py = WithStmts<py::DictItem>;
    fn convert(self, state: &State) -> Self::Py {
        let mut stmts = vec![];
        WithStmts {
            expr: match self {
                Self::Prop(prop) => match *prop {
                    js::Prop::KeyValue(js::KeyValueProp { key, value }) => py::DictItem {
                        key: Some(key.convert(state).unwrap_into(&mut stmts)),
                        value: (*value).convert(state).unwrap_into(&mut stmts),
                    },
                    js::Prop::Shorthand(id) => py::DictItem {
                        key: Some(
                            js::PropName::Ident(id.clone())
                                .convert(state)
                                .unwrap_into(&mut stmts),
                        ),
                        value: py::Expr::Name(py::ExprName {
                            range: id.span.convert(state),
                            id: safe_name(id.sym.as_str()),
                            ctx: py::ExprContext::Load,
                        }),
                    },
                    x => todo!("{x:?}"),
                },
                Self::Spread(prop) => {
                    let js::SpreadElement {
                        dot3_token: _,
                        expr,
                    } = prop;
                    py::DictItem {
                        key: None,
                        value: expr.convert(state).unwrap_into(&mut stmts),
                    }
                }
            },
            stmts,
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
        if s.bytes().all(|x| x.is_ascii_digit()) {
            py::Number::Int(s.parse().unwrap())
        } else {
            py::Number::Float(self.value)
        }
    }
}

impl Convert for js::TsTypeAnn {
    type Py = HopefullyExpr;
    fn convert(self, state: &State) -> Self::Py {
        let Self { span: _, type_ann } = self;
        (*type_ann).convert(state)
    }
}

impl Convert for js::TsType {
    type Py = WithStmts<py::Expr>;
    fn convert(self, state: &State) -> Self::Py {
        match self {
            Self::TsTypeRef(x) => x.convert(state),
            Self::TsUnionOrIntersectionType(x) => x.convert(state),
            Self::TsTypeLit(x) => x.convert(state).into(),
            Self::TsKeywordType(x) => x.convert(state).into(),
            Self::TsArrayType(x) => x.convert(state),
            Self::TsParenthesizedType(x) => x.convert(state),
            Self::TsMappedType(x) => x.convert(state),
            Self::TsTypeOperator(x) => x.convert(state).into(),
            Self::TsFnOrConstructorType(x) => x.convert(state),
            Self::TsTupleType(x) => x.convert(state),
            Self::TsThisType(x) => x.convert(state).into(),
            Self::TsLitType(x) => x.convert(state),
            Self::TsTypePredicate(x) => x.convert(state).into(),
            x => todo!("{x:?}"),
        }
    }
}

impl Convert for js::TsLitType {
    type Py = WithStmts<py::Expr>;
    fn convert(self, state: &State) -> Self::Py {
        let Self { span: _, lit } = self;
        lit.convert(state)
    }
}

impl Convert for js::TsLit {
    type Py = WithStmts<py::Expr>;
    fn convert(self, state: &State) -> Self::Py {
        match self {
            Self::Number(x) => py::Expr::NumberLiteral(py::ExprNumberLiteral {
                range: x.span.convert(state),
                value: x.convert(state),
            })
            .into(),
            Self::Bool(js::Bool { span, value }) => {
                py::Expr::BooleanLiteral(py::ExprBooleanLiteral {
                    range: span.convert(state),
                    value,
                })
                .into()
            }
            Self::Str(js::Str {
                span,
                value,
                raw: _,
            }) => py::Expr::StringLiteral(py::ExprStringLiteral {
                range: span.convert(state),
                value: py::StringLiteralValue::single(py::StringLiteral {
                    range: span.convert(state),
                    value: value.as_str().into(),
                    flags: py::StringLiteralFlags::default(),
                }),
            })
            .into(),
            x => todo!("{x:?}"),
        }
    }
}

impl Convert for js::TsThisType {
    type Py = py::Expr;
    fn convert(self, state: &State) -> Self::Py {
        let Self { span } = self;
        py::Expr::Attribute(py::ExprAttribute {
            range: span.convert(state),
            value: Box::new(state.import("typing")),
            attr: py::Identifier {
                range: TextRange::default(),
                id: "Self".to_owned(),
            },
            ctx: py::ExprContext::Load,
        })
    }
}

impl Convert for js::TsFnOrConstructorType {
    type Py = WithStmts<py::Expr>;
    fn convert(self, state: &State) -> Self::Py {
        match self {
            Self::TsFnType(x) => x.convert(state),
            Self::TsConstructorType(x) => todo!("{x:?}"),
        }
    }
}

impl Convert for js::TsFnType {
    type Py = WithStmts<py::Expr>;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span,
            params,
            type_params: _,
            type_ann,
        } = self;
        let mut stmts = vec![];
        WithStmts {
            expr: py::Expr::Subscript(py::ExprSubscript {
                range: span.convert(state),
                value: Box::new(py::Expr::Attribute(py::ExprAttribute {
                    range: span.convert(state),
                    value: Box::new(py::Expr::Attribute(py::ExprAttribute {
                        range: span.convert(state),
                        value: Box::new(state.import("collections")),
                        attr: py::Identifier {
                            range: TextRange::default(),
                            id: "abc".to_owned(),
                        },
                        ctx: py::ExprContext::Load,
                    })),
                    attr: py::Identifier {
                        range: TextRange::default(),
                        id: "Callable".to_owned(),
                    },
                    ctx: py::ExprContext::Load,
                })),
                slice: Box::new(py::Expr::Tuple(py::ExprTuple {
                    range: TextRange::default(),
                    parenthesized: false,
                    ctx: py::ExprContext::Load,
                    elts: vec![
                        py::Expr::List(py::ExprList {
                            range: TextRange::default(),
                            ctx: py::ExprContext::Load,
                            elts: params
                                .into_iter()
                                .map(|x| match x.convert(state).unwrap_into(&mut stmts) {
                                    PyParameter::Single(x) => x.parameter.annotation.map_or_else(
                                        || {
                                            py::Expr::Attribute(py::ExprAttribute {
                                                range: span.convert(state),
                                                value: Box::new(state.import("typing")),
                                                attr: py::Identifier {
                                                    range: TextRange::default(),
                                                    id: "Any".to_owned(),
                                                },
                                                ctx: py::ExprContext::Load,
                                            })
                                        },
                                        |x| *x,
                                    ),
                                    PyParameter::Rest(_) => {
                                        py::Expr::EllipsisLiteral(py::ExprEllipsisLiteral {
                                            range: TextRange::default(),
                                        })
                                    }
                                })
                                .collect(),
                        }),
                        (*type_ann).convert(state).unwrap_into(&mut stmts),
                    ],
                })),
                ctx: py::ExprContext::Load,
            }),
            stmts,
        }
    }
}

impl Convert for js::TsTypeOperator {
    type Py = py::Expr;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span,
            op,
            type_ann: _,
        } = self;
        match op {
            js::TsTypeOperatorOp::Unique
            | js::TsTypeOperatorOp::KeyOf
            | js::TsTypeOperatorOp::ReadOnly => py::Expr::Attribute(py::ExprAttribute {
                range: span.convert(state),
                value: Box::new(state.import("typing")),
                attr: py::Identifier {
                    range: TextRange::default(),
                    id: "Any".to_owned(),
                },
                ctx: py::ExprContext::Load,
            }),
        }
    }
}

impl Convert for js::TsTypePredicate {
    type Py = py::Expr;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span,
            asserts: _,
            param_name: _,
            type_ann: _,
        } = self;
        py::Expr::Attribute(py::ExprAttribute {
            range: span.convert(state),
            value: Box::new(state.import("typing")),
            attr: py::Identifier {
                range: TextRange::default(),
                id: "Any".to_owned(),
            },
            ctx: py::ExprContext::Load,
        })
    }
}

impl Convert for js::TsMappedType {
    type Py = WithStmts<py::Expr>;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span,
            readonly: _,
            type_param,
            name_type,
            optional: _,
            type_ann,
        } = self;
        // i think this maps type_param to type_ann?
        assert!(name_type.is_none());
        let mut stmts = Vec::new();
        WithStmts {
            expr: py::Expr::Subscript(py::ExprSubscript {
                range: span.convert(state),
                value: Box::new(py::Expr::Name(py::ExprName {
                    range: TextRange::default(),
                    id: "dict".to_owned(),
                    ctx: py::ExprContext::Load,
                })),
                slice: Box::new(py::Expr::Tuple(py::ExprTuple {
                    range: TextRange::default(),
                    parenthesized: false,
                    ctx: py::ExprContext::Load,
                    elts: vec![
                        match type_param.convert(state).unwrap_into(&mut stmts) {
                            py::TypeParam::TypeVar(py::TypeParamTypeVar {
                                range: _,
                                bound: _,
                                default: _,
                                name: py::Identifier { range, id },
                            }) => py::Expr::Name(py::ExprName {
                                range,
                                id,
                                ctx: py::ExprContext::Load,
                            }),
                            x => todo!("{x:?}"),
                        },
                        type_ann.unwrap().convert(state).unwrap_into(&mut stmts),
                    ],
                })),
                ctx: py::ExprContext::Load,
            }),
            stmts,
        }
    }
}

impl Convert for js::TsParenthesizedType {
    type Py = WithStmts<py::Expr>;
    fn convert(self, state: &State) -> Self::Py {
        let Self { span: _, type_ann } = self;
        (*type_ann).convert(state)
    }
}

impl Convert for js::TsTupleType {
    type Py = HopefullyExpr;
    fn convert(self, state: &State) -> Self::Py {
        let Self { span, elem_types } = self;
        let mut stmts = vec![];
        HopefullyExpr {
            expr: py::Expr::Subscript(py::ExprSubscript {
                range: span.convert(state),
                ctx: py::ExprContext::Load,
                value: Box::new(py::Expr::Attribute(py::ExprAttribute {
                    range: span.convert(state),
                    value: Box::new(state.import("typing")),
                    attr: py::Identifier {
                        range: TextRange::default(),
                        id: "Tuple".to_owned(),
                    },
                    ctx: py::ExprContext::Load,
                })),
                slice: Box::new(py::Expr::Tuple(py::ExprTuple {
                    ctx: py::ExprContext::Load,
                    range: TextRange::default(),
                    parenthesized: false,
                    elts: elem_types
                        .into_iter()
                        .map(|x| x.convert(state).unwrap_into(&mut stmts))
                        .collect(),
                })),
            }),
            stmts,
        }
    }
}

impl Convert for js::TsTupleElement {
    type Py = WithStmts<py::Expr>;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span: _,
            label: _,
            ty,
        } = self;
        (*ty).convert(state)
    }
}

impl Convert for js::TsArrayType {
    type Py = HopefullyExpr;
    fn convert(self, state: &State) -> Self::Py {
        let Self { span, elem_type } = self;
        let mut stmts = vec![];
        HopefullyExpr {
            expr: py::Expr::Subscript(py::ExprSubscript {
                range: span.convert(state),
                ctx: py::ExprContext::Load,
                value: Box::new(py::Expr::Attribute(py::ExprAttribute {
                    range: span.convert(state),
                    value: Box::new(state.import("typing")),
                    attr: py::Identifier {
                        range: TextRange::default(),
                        id: "List".to_owned(),
                    },
                    ctx: py::ExprContext::Load,
                })),
                slice: Box::new((*elem_type).convert(state).unwrap_into(&mut stmts)),
            }),
            stmts,
        }
    }
}

impl Convert for js::TsKeywordType {
    type Py = py::Expr;
    fn convert(self, state: &State) -> Self::Py {
        let Self { span, kind } = self;
        let range = span.convert(state);
        match kind {
            js::TsKeywordTypeKind::TsNullKeyword
            | js::TsKeywordTypeKind::TsUndefinedKeyword
            | js::TsKeywordTypeKind::TsVoidKeyword => {
                py::Expr::NoneLiteral(py::ExprNoneLiteral { range })
            }
            js::TsKeywordTypeKind::TsUnknownKeyword | js::TsKeywordTypeKind::TsAnyKeyword => {
                py::Expr::Attribute(py::ExprAttribute {
                    range: span.convert(state),
                    value: Box::new(state.import("typing")),
                    attr: py::Identifier {
                        range: TextRange::default(),
                        id: "Any".to_owned(),
                    },
                    ctx: py::ExprContext::Load,
                })
            }
            js::TsKeywordTypeKind::TsStringKeyword | js::TsKeywordTypeKind::TsSymbolKeyword => {
                py::Expr::Name(py::ExprName {
                    range,
                    id: "str".to_owned(),
                    ctx: py::ExprContext::Load,
                })
            }
            js::TsKeywordTypeKind::TsNumberKeyword => py::Expr::Name(py::ExprName {
                range,
                id: "int".to_owned(),
                ctx: py::ExprContext::Load,
            }),
            js::TsKeywordTypeKind::TsBooleanKeyword => py::Expr::Name(py::ExprName {
                range,
                id: "bool".to_owned(),
                ctx: py::ExprContext::Load,
            }),
            x => todo!("{x:?}"),
        }
    }
}

impl Convert for js::TsUnionOrIntersectionType {
    type Py = HopefullyExpr;
    fn convert(self, state: &State) -> Self::Py {
        match self {
            Self::TsIntersectionType(x) => x.convert(state),
            Self::TsUnionType(x) => x.convert(state),
        }
    }
}

impl Convert for js::TsIntersectionType {
    type Py = HopefullyExpr;
    fn convert(self, state: &State) -> Self::Py {
        let Self { span, types } = self;
        let mut stmts = vec![];
        let name = state.gen_ident();
        let ret = py::Stmt::ClassDef(py::StmtClassDef {
            range: span.convert(state),
            decorator_list: vec![],
            name: name.clone(),
            type_params: None,
            arguments: Some(Box::new(py::Arguments {
                range: TextRange::default(),
                keywords: Box::new([]),
                args: types
                    .into_iter()
                    .map(|x| (*x).convert(state).unwrap_into(&mut stmts))
                    .collect(),
            })),
            body: safe_block(vec![]),
        });
        stmts.push(ret);
        HopefullyExpr {
            expr: py::Expr::Name(py::ExprName {
                range: name.range,
                id: name.id,
                ctx: py::ExprContext::Load,
            }),
            stmts,
        }
    }
}

impl Convert for js::TsUnionType {
    type Py = HopefullyExpr;
    fn convert(self, state: &State) -> Self::Py {
        let Self { span, types } = self;
        let mut stmts = vec![];
        HopefullyExpr {
            expr: py::Expr::Subscript(py::ExprSubscript {
                range: span.convert(state),
                ctx: py::ExprContext::Load,
                value: Box::new(py::Expr::Attribute(py::ExprAttribute {
                    range: span.convert(state),
                    value: Box::new(state.import("typing")),
                    attr: py::Identifier {
                        range: TextRange::default(),
                        id: "Union".to_owned(),
                    },
                    ctx: py::ExprContext::Load,
                })),
                slice: Box::new(if types.len() == 1 {
                    (*types.into_iter().next().unwrap())
                        .convert(state)
                        .unwrap_into(&mut stmts)
                } else {
                    py::Expr::Tuple(py::ExprTuple {
                        range: span.convert(state),
                        ctx: py::ExprContext::Load,
                        parenthesized: false,
                        elts: types
                            .into_iter()
                            .map(|x| (*x).convert(state).unwrap_into(&mut stmts))
                            .collect(),
                    })
                }),
            }),
            stmts,
        }
    }
}

impl Convert for js::TsTypeRef {
    type Py = HopefullyExpr;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span,
            type_name,
            type_params,
        } = self;
        let ret = type_name.convert(state);
        if let Some(params) = type_params {
            let mut stmts = Vec::new();

            HopefullyExpr {
                expr: py::Expr::Subscript(py::ExprSubscript {
                    range: span.convert(state),
                    ctx: py::ExprContext::Load,
                    value: Box::new(ret),
                    slice: Box::new(if params.params.len() == 1 {
                        (*params.params.into_iter().next().unwrap())
                            .convert(state)
                            .unwrap_into(&mut stmts)
                    } else {
                        py::Expr::Tuple(py::ExprTuple {
                            range: span.convert(state),
                            ctx: py::ExprContext::Load,
                            parenthesized: false,
                            elts: params
                                .params
                                .into_iter()
                                .map(|x| (*x).convert(state).unwrap_into(&mut stmts))
                                .collect(),
                        })
                    }),
                }),
                stmts,
            }
        } else {
            ret.into()
        }
    }
}

impl Convert for js::TsEntityName {
    type Py = py::Expr;
    fn convert(self, state: &State) -> Self::Py {
        match self {
            Self::Ident(js::Ident {
                span,
                sym,
                optional: _,
            }) => py::Expr::Name(py::ExprName {
                range: span.convert(state),
                id: safe_name(sym.as_str()),
                ctx: py::ExprContext::Load,
            }),
            Self::TsQualifiedName(x) => (*x).convert(state),
        }
    }
}

impl Convert for js::TsQualifiedName {
    type Py = py::Expr;
    fn convert(self, state: &State) -> Self::Py {
        let Self { left, right } = self;
        py::Expr::Attribute(py::ExprAttribute {
            range: TextRange::default(),
            value: Box::new(left.convert(state)),
            attr: right.convert(state),
            ctx: py::ExprContext::Load,
        })
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

impl Convert for js::ExprStmt {
    type Py = Vec<py::Stmt>;
    fn convert(self, state: &State) -> Self::Py {
        let Self { span: _, expr } = self;
        let WithStmts { expr, mut stmts } = (*expr).convert(state);
        if !expr.is_name_expr() {
            stmts.push(expr_stmt(expr));
        }
        stmts
    }
}

impl Convert for js::Decl {
    type Py = Vec<py::Stmt>;
    fn convert(self, state: &State) -> Self::Py {
        match self {
            Self::Var(d) => (*d).convert(state),
            Self::TsTypeAlias(d) => (*d).convert(state),
            Self::Class(d) => d.convert(state),
            Self::Fn(d) => d.convert(state),
            Self::TsInterface(d) => (*d).convert(state),
            Self::TsEnum(d) => (*d).convert(state),
            d => todo!("{d:?}"),
        }
    }
}

impl Convert for js::TsEnumDecl {
    type Py = Vec<py::Stmt>;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span,
            declare: _,
            is_const: _,
            id,
            members,
        } = self;
        let mut last_val = None;
        let mut stmts = vec![];
        let ret = py::Stmt::ClassDef(py::StmtClassDef {
            range: span.convert(state),
            decorator_list: vec![],
            name: id.convert(state),
            type_params: None,
            arguments: Some(Box::new(py::Arguments {
                range: TextRange::default(),
                keywords: Box::new([]),
                args: Box::new([py::Expr::Attribute(py::ExprAttribute {
                    range: span.convert(state),
                    value: Box::new(state.import("enum")),
                    attr: py::Identifier {
                        range: TextRange::default(),
                        id: "Enum".to_owned(),
                    },
                    ctx: py::ExprContext::Load,
                })]),
            })),
            body: safe_block(
                members
                    .into_iter()
                    .map(|x| {
                        let js::TsEnumMember { span, id, init } = x;
                        let init = init.map_or_else(
                            || match &last_val {
                                Some(py::Expr::NumberLiteral(py::ExprNumberLiteral {
                                    value: py::Number::Int(x),
                                    range,
                                })) => py::Expr::NumberLiteral(py::ExprNumberLiteral {
                                    value: py::Number::Int(
                                        (x.to_string().parse::<u64>().unwrap() + 1)
                                            .to_string()
                                            .parse()
                                            .unwrap(),
                                    ),
                                    range: *range,
                                }),
                                None => py::Expr::NumberLiteral(py::ExprNumberLiteral {
                                    value: py::Number::Int(py::Int::ZERO),
                                    range: TextRange::default(),
                                }),
                                x => todo!("{x:?}"),
                            },
                            |x| (*x).convert(state).unwrap_into(&mut stmts),
                        );
                        last_val = Some(init.clone());
                        let id = id.convert(state);
                        py::Stmt::Assign(py::StmtAssign {
                            range: span.convert(state),
                            targets: vec![py::Expr::Name(py::ExprName {
                                range: id.range,
                                id: safe_name(&id.id),
                                ctx: py::ExprContext::Store,
                            })],
                            value: Box::new(init),
                        })
                    })
                    .collect(),
            ),
        });
        stmts.push(ret);
        stmts
    }
}

impl Convert for js::TsEnumMemberId {
    type Py = py::Identifier;
    fn convert(self, state: &State) -> Self::Py {
        match self {
            Self::Ident(x) => x.convert(state),
            Self::Str(x) => todo!("{x:?}"),
        }
    }
}

impl Convert for js::TsInterfaceDecl {
    type Py = Vec<py::Stmt>;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span,
            id,
            declare: _,
            type_params,
            extends,
            body,
        } = self;
        let mut stmts = vec![];
        let (body, index) = body.convert(state).unwrap_into(&mut stmts);
        if let Some((k, v)) = index {
            assert!(body.is_empty());
            stmts.push(index_assign(
                id.convert(state).id,
                k,
                v,
                span.convert(state),
            ));
            return stmts;
        }
        let ret = py::StmtClassDef {
            range: span.convert(state),
            decorator_list: vec![],
            arguments: Some(Box::new(py::Arguments {
                range: TextRange::default(),
                keywords: Box::new([]),
                args: extends
                    .into_iter()
                    .map(|x| x.convert(state).unwrap_into(&mut stmts))
                    .collect(),
            })),
            type_params: type_params.map(|x| Box::new((*x).convert(state).unwrap_into(&mut stmts))),
            name: id.convert(state),
            body: safe_block(body),
        };
        stmts.push(py::Stmt::ClassDef(ret));
        stmts
    }
}

#[allow(clippy::type_complexity)]
fn convert_class_body(
    state: &State,
    body: Vec<js::TsTypeElement>,
) -> WithStmts<(Vec<py::Stmt>, Option<(py::Expr, py::Expr)>)> {
    let mut stmts = Vec::new();
    let mut index = None;
    WithStmts {
        expr: (
            body.convert(state)
                .into_iter()
                .flat_map(|x| match x.unwrap_into(&mut stmts) {
                    ClassMember::Member(x) => Some(x),
                    ClassMember::Index(a, b) => {
                        index = Some((a, b));
                        None
                    }
                })
                .collect(),
            index,
        ),
        stmts,
    }
}

impl Convert for js::TsInterfaceBody {
    type Py = WithStmts<(Vec<py::Stmt>, Option<(py::Expr, py::Expr)>)>;
    fn convert(self, state: &State) -> Self::Py {
        let Self { span: _, body } = self;
        convert_class_body(state, body)
    }
}

impl Convert for js::TsExprWithTypeArgs {
    type Py = WithStmts<py::Expr>;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span: _,
            expr,
            type_args: _,
        } = self;
        (*expr).convert(state)
    }
}

impl Convert for js::FnDecl {
    type Py = Vec<py::Stmt>;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            ident,
            declare: _,
            function,
        } = self;
        let WithStmts { expr, mut stmts } = convert_func(state, Some(ident), *function);
        stmts.push(py::Stmt::FunctionDef(expr));
        stmts
    }
}

impl Convert for js::ClassDecl {
    type Py = Vec<py::Stmt>;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            ident,
            declare: _,
            class,
        } = self;
        let js::Class {
            span,
            decorators,
            body,
            super_class,
            is_abstract: _,
            type_params,
            super_type_params: _,
            implements,
        } = *class;
        let mut stmts = vec![];
        let ret = py::StmtClassDef {
            range: span.convert(state),
            decorator_list: decorators
                .convert(state)
                .into_iter()
                .map(|x| py::Decorator {
                    range: x.range(),
                    expression: x,
                })
                .collect(),
            arguments: Some(Box::new(py::Arguments {
                range: TextRange::default(),
                keywords: Box::new([]),
                args: {
                    let mut args = super_class
                        .map(|x| vec![(*x).convert(state).unwrap_into(&mut stmts)])
                        .unwrap_or_default();
                    args.extend(
                        implements
                            .into_iter()
                            .map(|x| x.convert(state).unwrap_into(&mut stmts)),
                    );
                    args.into()
                },
            })),
            type_params: type_params.map(|x| Box::new((*x).convert(state).unwrap_into(&mut stmts))),
            name: ident.convert(state),
            body: safe_block(
                body.into_iter()
                    .map(|x| x.convert(state).unwrap_into(&mut stmts))
                    .collect(),
            ),
        };
        stmts.push(py::Stmt::ClassDef(ret));
        stmts
    }
}

impl Convert for js::ClassMember {
    type Py = WithStmts<py::Stmt>;
    fn convert(self, state: &State) -> Self::Py {
        match self {
            Self::Method(x) => x.convert(state).map1(py::Stmt::FunctionDef),
            Self::ClassProp(x) => x.convert(state),
            Self::Constructor(x) => x.convert(state).map1(py::Stmt::FunctionDef),
            x => todo!("{x:?}"),
        }
    }
}
impl Convert for js::Constructor {
    type Py = WithStmts<py::StmtFunctionDef>;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span,
            key,
            params,
            body,
            accessibility: _,
            is_optional: _,
        } = self;
        let mut stmts = vec![];
        let mut body_stmts = vec![];
        WithStmts {
            expr: py::StmtFunctionDef {
                range: span.convert(state),
                is_async: false,
                decorator_list: vec![],
                name: py::Identifier::new("__init__", key.span().convert(state)),
                parameters: Box::new(safe_params(py::Parameters {
                    range: TextRange::default(),
                    args: std::iter::once(py::ParameterWithDefault {
                        range: TextRange::default(),
                        default: None,
                        parameter: py::Parameter {
                            range: TextRange::default(),
                            name: py::Identifier::new("self", TextRange::default()),
                            annotation: None,
                        },
                    })
                    .chain(params.convert(state).into_iter().map(|x| {
                        let (x, stmts) = x.unwrap_into(&mut stmts);
                        body_stmts.extend(stmts);
                        x
                    }))
                    .collect(),
                    posonlyargs: vec![],
                    kwonlyargs: vec![],
                    vararg: None,
                    kwarg: None,
                })),
                body: {
                    body_stmts.extend(body.unwrap().convert(state));
                    safe_block(body_stmts)
                },
                returns: None,
                type_params: None,
            },
            stmts,
        }
    }
}
impl Convert for js::ClassProp {
    type Py = WithStmts<py::Stmt>;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span,
            key,
            value,
            type_ann,
            is_static: _,
            decorators: _,
            accessibility: _,
            is_abstract: _,
            is_optional,
            is_override: _,
            readonly: _,
            declare: _,
            definite: _,
        } = self;
        let mut stmts = vec![];
        let target = match key {
            js::PropName::Ident(x) => {
                let id = x.convert(state);
                py::Expr::Name(py::ExprName {
                    range: id.range,
                    id: safe_name(&id.id),
                    ctx: py::ExprContext::Store,
                })
            }
            key => key.convert(state).unwrap_into(&mut stmts),
        };
        let val = value.map(|x| (*x).convert(state).unwrap_into(&mut stmts));
        let type_ann = type_ann.map(|type_ann| {
            let mut ann = (*type_ann).convert(state).unwrap_into(&mut stmts);
            if is_optional {
                ann = py::Expr::Subscript(py::ExprSubscript {
                    range: TextRange::default(),
                    ctx: py::ExprContext::Load,
                    value: Box::new(py::Expr::Attribute(py::ExprAttribute {
                        range: span.convert(state),
                        value: Box::new(state.import("typing")),
                        attr: py::Identifier {
                            range: TextRange::default(),
                            id: "Optional".to_owned(),
                        },
                        ctx: py::ExprContext::Load,
                    })),
                    slice: Box::new(ann),
                });
            }
            ann
        });
        WithStmts {
            expr: if let Some(type_ann) = type_ann {
                py::Stmt::AnnAssign(py::StmtAnnAssign {
                    range: span.convert(state),
                    simple: target.is_name_expr(),
                    target: Box::new(target),
                    annotation: Box::new(type_ann),
                    value: val.map(Box::new),
                })
            } else {
                py::Stmt::Assign(py::StmtAssign {
                    range: span.convert(state),
                    targets: vec![target],
                    value: Box::new(val.unwrap()),
                })
            },
            stmts,
        }
    }
}

impl Convert for js::ClassMethod {
    type Py = WithStmts<py::StmtFunctionDef>;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span: _,
            key,
            function,
            kind,
            is_static,
            accessibility: _,
            is_abstract: _,
            is_optional: _,
            is_override: _,
        } = self;
        let mut func = convert_func(state, key.ident(), *function);
        match (is_static, kind) {
            (false, js::MethodKind::Method) => func.expr.parameters.args.insert(
                0,
                py::ParameterWithDefault {
                    range: TextRange::default(),
                    parameter: py::Parameter {
                        annotation: None,
                        range: TextRange::default(),
                        name: py::Identifier::new("self", TextRange::default()),
                    },
                    default: None,
                },
            ),
            (true, js::MethodKind::Method) => {
                func.expr.decorator_list.push(py::Decorator {
                    range: TextRange::default(),
                    expression: py::Expr::Name(py::ExprName {
                        range: TextRange::default(),
                        id: "staticmethod".to_owned(),
                        ctx: py::ExprContext::Load,
                    }),
                });
            }
            (false, js::MethodKind::Getter) => {
                func.expr.parameters.args.insert(
                    0,
                    py::ParameterWithDefault {
                        range: TextRange::default(),
                        parameter: py::Parameter {
                            annotation: None,
                            range: TextRange::default(),
                            name: py::Identifier::new("self", TextRange::default()),
                        },
                        default: None,
                    },
                );
                func.expr.decorator_list.push(py::Decorator {
                    range: TextRange::default(),
                    expression: py::Expr::Name(py::ExprName {
                        range: TextRange::default(),
                        id: "property".to_owned(),
                        ctx: py::ExprContext::Load,
                    }),
                });
            }
            x => todo!("{x:?}"),
        }
        func
    }
}

fn index_assign(name: String, k: py::Expr, v: py::Expr, span: TextRange) -> py::Stmt {
    py::Stmt::Assign(py::StmtAssign {
        range: span,
        targets: vec![py::Expr::Name(py::ExprName {
            range: TextRange::default(),
            id: name,
            ctx: py::ExprContext::Store,
        })],
        value: Box::new(py::Expr::Subscript(py::ExprSubscript {
            range: TextRange::default(),
            value: Box::new(py::Expr::Name(py::ExprName {
                range: TextRange::default(),
                id: "dict".to_owned(),
                ctx: py::ExprContext::Load,
            })),
            slice: Box::new(py::Expr::Tuple(py::ExprTuple {
                range: TextRange::default(),
                parenthesized: false,
                ctx: py::ExprContext::Load,
                elts: vec![k, v],
            })),
            ctx: py::ExprContext::Load,
        })),
    })
}

fn convert_type_lit(
    state: &State,
    lit: js::TsTypeLit,
    id: Option<js::Ident>,
    type_params: Option<js::TsTypeParamDecl>,
) -> Vec<py::Stmt> {
    let js::TsTypeLit { span, members } = lit;
    let mut stmts = vec![];
    let (body, index) = convert_class_body(state, members).unwrap_into(&mut stmts);
    if let Some((k, v)) = index {
        assert!(body.is_empty());
        stmts.push(index_assign(
            id.map(|x| x.convert(state).id)
                .unwrap_or_else(|| state.gen_name()),
            k,
            v,
            span.convert(state),
        ));
        return stmts;
    }
    let ret = py::Stmt::ClassDef(py::StmtClassDef {
        range: span.convert(state),
        decorator_list: vec![],
        arguments: Some(Box::new(py::Arguments {
            range: TextRange::default(),
            keywords: Box::new([]),
            args: Box::new([py::Expr::Attribute(py::ExprAttribute {
                range: span.convert(state),
                value: Box::new(state.import("typing")),
                attr: py::Identifier {
                    range: TextRange::default(),
                    id: "TypedDict".to_owned(),
                },
                ctx: py::ExprContext::Load,
            })]),
        })),
        type_params: type_params.map(|x| Box::new(x.convert(state).unwrap_into(&mut stmts))),
        name: id.convert(state).unwrap_or_else(|| state.gen_ident()),
        body: safe_block(body),
    });
    stmts.push(ret);
    stmts
}

impl Convert for js::TsTypeLit {
    type Py = Vec<py::Stmt>;
    fn convert(self, state: &State) -> Self::Py {
        convert_type_lit(state, self, None, None)
    }
}

impl Convert for js::TsTypeAliasDecl {
    type Py = Vec<py::Stmt>;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span: _,
            declare: _,
            id,
            type_params,
            type_ann,
        } = self;
        match *type_ann {
            js::TsType::TsTypeLit(lit) => {
                convert_type_lit(state, lit, Some(id), type_params.map(|x| *x))
            }
            x => {
                let WithStmts { expr, mut stmts } = x.convert(state);
                stmts.push(py::Stmt::Assign(py::StmtAssign {
                    range: expr.range(),
                    targets: vec![py::Expr::Name(py::ExprName {
                        range: id.span.convert(state),
                        id: safe_name(id.sym.as_str()),
                        ctx: py::ExprContext::Store,
                    })],
                    value: Box::new(expr),
                }));
                stmts
            }
        }
    }
}

impl Convert for js::TsTypeElement {
    type Py = WithStmts<ClassMember>;
    fn convert(self, state: &State) -> Self::Py {
        match self {
            Self::TsPropertySignature(ty) => ty
                .convert(state)
                .map1(py::Stmt::AnnAssign)
                .map1(ClassMember::Member),
            Self::TsMethodSignature(ty) => ty
                .convert(state)
                .map1(py::Stmt::FunctionDef)
                .map1(ClassMember::Member),
            Self::TsIndexSignature(ty) => ty.convert(state),
            x => todo!("{x:?}"),
        }
    }
}

enum ClassMember {
    Index(py::Expr, py::Expr),
    Member(py::Stmt),
}

impl Convert for js::TsIndexSignature {
    type Py = WithStmts<ClassMember>;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            params,
            type_ann,
            readonly: _,
            is_static,
            span,
        } = self;
        assert!(!is_static);
        assert_eq!(params.len(), 1);
        let mut stmts = Vec::new();
        WithStmts {
            expr: ClassMember::Index(
                match params
                    .into_iter()
                    .next()
                    .unwrap()
                    .convert(state)
                    .unwrap_into(&mut stmts)
                {
                    PyParameter::Single(x) => x.parameter.annotation.map_or_else(
                        || {
                            py::Expr::Attribute(py::ExprAttribute {
                                range: span.convert(state),
                                value: Box::new(state.import("typing")),
                                attr: py::Identifier {
                                    range: TextRange::default(),
                                    id: "Any".to_owned(),
                                },
                                ctx: py::ExprContext::Load,
                            })
                        },
                        |x| *x,
                    ),
                    PyParameter::Rest(_) => py::Expr::EllipsisLiteral(py::ExprEllipsisLiteral {
                        range: TextRange::default(),
                    }),
                },
                type_ann.unwrap().convert(state).unwrap_into(&mut stmts),
            ),
            stmts,
        }
    }
}

impl Convert for js::TsMethodSignature {
    type Py = WithStmts<py::StmtFunctionDef>;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span,
            readonly: _,
            key,
            computed: _,
            optional: _,
            params,
            type_ann,
            type_params,
        } = self;
        let mut stmts = vec![];
        let returns = type_ann.map(|x| Box::new((*x).convert(state).unwrap_into(&mut stmts)));
        let type_params =
            type_params.map(|x| Box::new((*x).convert(state).unwrap_into(&mut stmts)));
        WithStmts {
            expr: py::StmtFunctionDef {
                is_async: false,
                range: span.convert(state),
                name: key.as_ident().unwrap().clone().convert(state),
                parameters: Box::new(create_params(
                    params
                        .convert(state)
                        .into_iter()
                        .map(|x| x.unwrap_into(&mut stmts)),
                )),
                body: vec![py::Stmt::Raise(py::StmtRaise {
                    range: TextRange::default(),
                    exc: Some(Box::new(py::Expr::Name(py::ExprName {
                        ctx: py::ExprContext::Load,
                        range: TextRange::default(),
                        id: "NotImplementedError".to_owned(),
                    }))),
                    cause: None,
                })],
                decorator_list: vec![],
                returns,
                type_params,
            },
            stmts,
        }
    }
}

fn create_params(params: impl Iterator<Item = PyParameter>) -> py::Parameters {
    let mut args = vec![];
    let mut vararg = None;
    for param in params {
        match param {
            PyParameter::Single(x) => args.push(x),
            PyParameter::Rest(x) => vararg = Some(Box::new(x)),
        }
    }
    py::Parameters {
        range: TextRange::default(),
        posonlyargs: vec![],
        args,
        vararg,
        kwonlyargs: vec![],
        kwarg: None,
    }
}

enum PyParameter {
    Single(py::ParameterWithDefault),
    Rest(py::Parameter),
}

impl Convert for js::TsFnParam {
    type Py = WithStmts<PyParameter>;
    fn convert(self, state: &State) -> Self::Py {
        let mut stmts = Vec::new();
        WithStmts {
            expr: match self {
                Self::Ident(js::BindingIdent { id, type_ann }) => {
                    PyParameter::Single(py::ParameterWithDefault {
                        range: TextRange::default(),
                        default: None,
                        parameter: py::Parameter {
                            range: TextRange::default(),
                            annotation: type_ann
                                .map(|x| Box::new((*x).convert(state).unwrap_into(&mut stmts))),
                            name: id.convert(state),
                        },
                    })
                }
                Self::Rest(js::RestPat {
                    span: _,
                    dot3_token: _,
                    arg,
                    type_ann,
                }) => {
                    let arg = arg.convert(state);
                    PyParameter::Rest(py::Parameter {
                        range: TextRange::default(),
                        annotation: type_ann
                            .map(|x| Box::new((*x).convert(state).unwrap_into(&mut stmts))),
                        name: arg.expr.id,
                    })
                }
                x => todo!("{x:?}"),
            },
            stmts,
        }
    }
}

impl Convert for js::TsPropertySignature {
    type Py = WithStmts<py::StmtAnnAssign>;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span,
            readonly: _,
            key,
            computed: _,
            optional,
            init,
            params,
            type_ann,
            type_params,
        } = self;
        assert!(params.is_empty());
        assert!(type_params.is_none());
        let mut stmts = vec![];
        let mut ann = type_ann.map_or_else(
            || {
                py::Expr::Attribute(py::ExprAttribute {
                    range: span.convert(state),
                    value: Box::new(state.import("typing")),
                    attr: py::Identifier {
                        range: TextRange::default(),
                        id: "Any".to_owned(),
                    },
                    ctx: py::ExprContext::Load,
                })
            },
            |x| (*x).convert(state).unwrap_into(&mut stmts),
        );
        if optional {
            ann = py::Expr::Subscript(py::ExprSubscript {
                range: TextRange::default(),
                ctx: py::ExprContext::Load,
                value: Box::new(py::Expr::Attribute(py::ExprAttribute {
                    range: span.convert(state),
                    value: Box::new(state.import("typing")),
                    attr: py::Identifier {
                        range: TextRange::default(),
                        id: "Optional".to_owned(),
                    },
                    ctx: py::ExprContext::Load,
                })),
                slice: Box::new(ann),
            });
        }
        WithStmts {
            expr: py::StmtAnnAssign {
                range: span.convert(state),
                simple: true,
                value: init.map(|x| {
                    Box::new(
                        (*x).convert2(state, py::ExprContext::Load)
                            .unwrap_into(&mut stmts),
                    )
                }),
                target: Box::new(
                    (*key)
                        .convert2(state, py::ExprContext::Store)
                        .unwrap_into(&mut stmts),
                ),
                annotation: Box::new(ann),
            },
            stmts,
        }
    }
}

impl Convert for js::VarDecl {
    type Py = Vec<py::Stmt>;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span: _,
            kind: _,
            declare: _,
            decls,
        } = self;
        decls
            .into_iter()
            .flat_map(|d| {
                let js::VarDeclarator {
                    span,
                    name,
                    init,
                    definite: _,
                } = d;
                let mut stmts = Vec::new();
                let PatPy {
                    id,
                    type_ann,
                    body_stmts: stmts2,
                    def_val: _,
                } = name.convert(state).unwrap_into(&mut stmts);
                let init = init.map(|x| (*x).convert(state).unwrap_into(&mut stmts));
                if stmts.len() == 1
                    && matches!(stmts[0], py::Stmt::ClassDef(_) | py::Stmt::FunctionDef(_))
                {
                    match &mut stmts[0] {
                        py::Stmt::ClassDef(x) => x.name = id,
                        py::Stmt::FunctionDef(x) => x.name = id,
                        x => todo!("{x:?}"),
                    }
                    return stmts;
                } else if let Some(typ) = type_ann {
                    stmts.push(py::Stmt::AnnAssign(py::StmtAnnAssign {
                        range: span.convert(state),
                        target: Box::new(py::Expr::Name(py::ExprName {
                            range: span.convert(state),
                            id: safe_name(id.as_str()),
                            ctx: py::ExprContext::Store,
                        })),
                        simple: true,
                        annotation: Box::new(typ),
                        value: init.map(Box::new),
                    }));
                } else {
                    stmts.push(py::Stmt::Assign(py::StmtAssign {
                        range: span.convert(state),
                        targets: vec![py::Expr::Name(py::ExprName {
                            range: span.convert(state),
                            id: safe_name(id.as_str()),
                            ctx: py::ExprContext::Store,
                        })],
                        value: Box::new(init.unwrap_or_else(|| {
                            py::Expr::NoneLiteral(py::ExprNoneLiteral {
                                range: TextRange::default(),
                            })
                        })),
                    }));
                }
                stmts.extend(stmts2);
                stmts
            })
            .collect()
    }
}

impl Convert for js::Stmt {
    type Py = Vec<py::Stmt>;
    fn convert(self, state: &State) -> Self::Py {
        match self {
            Self::Expr(stmt) => stmt.convert(state),
            Self::Decl(decl) => decl.convert(state),
            Self::If(stmt) => stmt.convert(state),
            Self::Block(stmt) => stmt.convert(state),
            Self::Return(stmt) => stmt.convert(state),
            Self::Switch(stmt) => stmt.convert(state),
            Self::Throw(stmt) => stmt.convert(state),
            Self::ForOf(stmt) => stmt.convert(state),
            Self::Continue(stmt) => stmt.convert(state),
            Self::Try(stmt) => (*stmt).convert(state),
            Self::Break(stmt) => stmt.convert(state),
            Self::For(stmt) => stmt.convert(state),
            Self::While(stmt) => stmt.convert(state),
            Self::DoWhile(stmt) => stmt.convert(state),
            s => todo!("{s:?}"),
        }
    }
}

impl Convert for js::TryStmt {
    type Py = Vec<py::Stmt>;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span,
            block,
            handler,
            finalizer,
        } = self;
        let mut stmts = vec![];
        let ret = py::Stmt::Try(py::StmtTry {
            range: span.convert(state),
            body: safe_block(block.convert(state)),
            handlers: handler
                .into_iter()
                .map(|x| x.convert(state).unwrap_into(&mut stmts))
                .collect::<Vec<_>>(),
            finalbody: finalizer.convert(state).unwrap_or_default(),
            orelse: vec![],
            is_star: false,
        });
        stmts.push(ret);
        stmts
    }
}

impl Convert for js::CatchClause {
    type Py = WithStmts<py::ExceptHandler>;
    fn convert(self, state: &State) -> Self::Py {
        let Self { span, param, body } = self;
        let mut stmts = vec![];
        let body = body.convert(state);
        WithStmts {
            expr: if let Some(PatPy {
                id: name,
                type_ann: typ,
                mut body_stmts,
                def_val: _,
            }) = param.convert(state).map(|x| x.unwrap_into(&mut stmts))
            {
                body_stmts.extend(body);
                py::ExceptHandler::ExceptHandler(py::ExceptHandlerExceptHandler {
                    range: span.convert(state),
                    type_: Some(Box::new(typ.unwrap_or_else(|| {
                        py::Expr::Name(py::ExprName {
                            range: TextRange::default(),
                            id: "Exception".to_owned(),
                            ctx: py::ExprContext::Load,
                        })
                    }))),
                    name: Some(name),
                    body: safe_block(body_stmts),
                })
            } else {
                py::ExceptHandler::ExceptHandler(py::ExceptHandlerExceptHandler {
                    range: span.convert(state),
                    type_: None,
                    name: None,
                    body,
                })
            },
            stmts,
        }
    }
}

impl Convert for js::ContinueStmt {
    type Py = Vec<py::Stmt>;
    fn convert(self, state: &State) -> Self::Py {
        let Self { span, label } = self;
        assert!(label.is_none());
        vec![py::Stmt::Continue(py::StmtContinue {
            range: span.convert(state),
        })]
    }
}

impl Convert for js::BreakStmt {
    type Py = Vec<py::Stmt>;
    fn convert(self, state: &State) -> Self::Py {
        let Self { span, label } = self;
        assert!(label.is_none());
        vec![py::Stmt::Break(py::StmtBreak {
            range: span.convert(state),
        })]
    }
}

impl Convert for js::ForStmt {
    type Py = Vec<py::Stmt>;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span,
            init,
            test,
            update,
            body,
        } = self;
        let mut stmts = vec![];
        if let Some(init) = init {
            init.convert(state);
        }
        let mut body = (*body).convert(state);
        if let Some(upd) = update {
            let WithStmts { expr, stmts } = (*upd).convert(state);
            body.extend(stmts);
            if !expr.is_name_expr() {
                body.push(expr_stmt(expr));
            }
        }
        let test = test.map_or_else(
            || {
                py::Expr::BooleanLiteral(py::ExprBooleanLiteral {
                    range: TextRange::default(),
                    value: true,
                })
            },
            |test| {
                let WithStmts {
                    expr: test,
                    stmts: test_stmts,
                } = (*test).convert(state);
                stmts.extend(test_stmts.clone());
                body.extend(test_stmts);
                test
            },
        );
        stmts.push(py::Stmt::While(py::StmtWhile {
            range: span.convert(state),
            test: Box::new(test),
            body,
            orelse: vec![],
        }));
        stmts
    }
}

impl Convert for js::DoWhileStmt {
    type Py = Vec<py::Stmt>;
    fn convert(self, state: &State) -> Self::Py {
        let Self { span, test, body } = self;
        let mut stmts = vec![];
        let mut body = (*body).convert(state);
        let WithStmts {
            expr: test,
            stmts: test_stmts,
        } = (*test).convert(state);
        stmts.extend(test_stmts.clone());
        body.extend(test_stmts);
        body.push(py::Stmt::If(py::StmtIf {
            range: TextRange::default(),
            test: Box::new(test),
            body: vec![py::Stmt::Break(py::StmtBreak {
                range: span.convert(state),
            })],
            elif_else_clauses: vec![],
        }));
        stmts.push(py::Stmt::While(py::StmtWhile {
            range: span.convert(state),
            test: Box::new(py::Expr::BooleanLiteral(py::ExprBooleanLiteral {
                range: TextRange::default(),
                value: true,
            })),
            body,
            orelse: vec![],
        }));
        stmts
    }
}

impl Convert for js::WhileStmt {
    type Py = Vec<py::Stmt>;
    fn convert(self, state: &State) -> Self::Py {
        let Self { span, test, body } = self;
        let mut stmts = vec![];
        let mut body = (*body).convert(state);
        let WithStmts {
            expr: test,
            stmts: test_stmts,
        } = (*test).convert(state);
        stmts.extend(test_stmts.clone());
        body.extend(test_stmts);
        stmts.push(py::Stmt::While(py::StmtWhile {
            range: span.convert(state),
            test: Box::new(test),
            body,
            orelse: vec![],
        }));
        stmts
    }
}

impl Convert for js::VarDeclOrExpr {
    type Py = Vec<py::Stmt>;
    fn convert(self, state: &State) -> Self::Py {
        match self {
            Self::VarDecl(x) => (*x).convert(state),
            Self::Expr(x) => {
                let WithStmts { expr, mut stmts } = (*x).convert(state);
                if !expr.is_name_expr() {
                    stmts.push(expr_stmt(expr));
                }
                stmts
            }
        }
    }
}

impl Convert for js::ForOfStmt {
    type Py = Vec<py::Stmt>;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span,
            is_await,
            left,
            right,
            body: body1,
        } = self;
        let mut stmts = vec![];
        let (target, mut body) = left.convert(state);
        body.extend((*body1).convert(state));
        let ret = py::Stmt::For(py::StmtFor {
            range: span.convert(state),
            is_async: is_await,
            target: Box::new(target),
            body,
            iter: Box::new((*right).convert(state).unwrap_into(&mut stmts)),
            orelse: vec![],
        });
        stmts.push(ret);
        stmts
    }
}

impl Convert for js::ForHead {
    type Py = (py::Expr, Vec<py::Stmt>);
    fn convert(self, state: &State) -> Self::Py {
        match self {
            Self::VarDecl(x) => {
                let js::VarDecl {
                    span: _,
                    kind: _,
                    declare: _,
                    decls,
                } = *x;
                assert_eq!(decls.len(), 1);
                let decl = decls.into_iter().next().unwrap();
                let js::VarDeclarator {
                    span,
                    name,
                    init,
                    definite: _,
                } = decl;
                // use .expr and don't unwrap_into because we ignore the type ann
                let PatPy {
                    id: name,
                    type_ann: _,
                    body_stmts,
                    def_val: _,
                } = name.convert(state).expr;
                assert!(init.is_none());
                (
                    py::Expr::Name(py::ExprName {
                        range: span.convert(state),
                        id: safe_name(&name.id),
                        ctx: py::ExprContext::Store,
                    }),
                    body_stmts,
                )
            }
            x => todo!("{x:?}"),
        }
    }
}

impl Convert for js::ThrowStmt {
    type Py = Vec<py::Stmt>;
    fn convert(self, state: &State) -> Self::Py {
        let Self { span, arg } = self;
        let mut stmts = vec![];
        let ret = py::Stmt::Raise(py::StmtRaise {
            range: span.convert(state),
            exc: Some(Box::new((*arg).convert(state).unwrap_into(&mut stmts))),
            cause: None,
        });
        stmts.push(ret);
        stmts
    }
}

impl Convert for js::SwitchStmt {
    type Py = Vec<py::Stmt>;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span,
            discriminant,
            mut cases,
        } = self;
        cases.sort_by_key(|x| x.test.is_none());
        let mut cases = cases.into_iter();
        let tmp = state.gen_name();
        let var = py::Expr::Name(py::ExprName {
            ctx: py::ExprContext::Load,
            range: TextRange::default(),
            id: tmp,
        });
        let WithStmts {
            expr: discriminant,
            mut stmts,
        } = (*discriminant).convert(state);
        stmts.push(py::Stmt::Assign(py::StmtAssign {
            range: TextRange::default(),
            targets: vec![var.clone()],
            value: Box::new(discriminant),
        }));
        let Some(case) = cases.next() else {
            return stmts;
        };
        let js::SwitchCase {
            span: span2,
            test,
            cons,
        } = case;
        let cons = cons.into_iter().flat_map(|stmt| {
            if stmt.is_break_stmt() {
                vec![]
            } else {
                stmt.convert(state)
            }
        });
        let Some(test) = test else {
            stmts.extend(cons);
            return stmts;
        };
        let test = test.convert(state).unwrap_into(&mut stmts);
        let ret = py::Stmt::If(py::StmtIf {
            range: span.convert(state),
            test: Box::new(py::Expr::Compare(py::ExprCompare {
                range: span2.convert(state),
                ops: Box::new([py::CmpOp::Eq]),
                left: Box::new(var.clone()),
                comparators: Box::new([test]),
            })),
            body: safe_block(cons.collect()),
            elif_else_clauses: cases
                .map(|case| {
                    let js::SwitchCase { span, test, cons } = case;
                    let test = test.convert(state).map(|x| x.unwrap_into(&mut stmts));
                    let cons = cons.into_iter().flat_map(|stmt| {
                        if stmt.is_break_stmt() {
                            vec![]
                        } else {
                            stmt.convert(state)
                        }
                    });
                    py::ElifElseClause {
                        range: span.convert(state),
                        test: test.map(|test| {
                            py::Expr::Compare(py::ExprCompare {
                                range: span2.convert(state),
                                ops: Box::new([py::CmpOp::Eq]),
                                left: Box::new(var.clone()),
                                comparators: Box::new([test]),
                            })
                        }),
                        body: safe_block(cons.collect()),
                    }
                })
                .collect(),
        });
        stmts.push(ret);
        stmts
    }
}

impl Convert for js::ReturnStmt {
    type Py = Vec<py::Stmt>;
    fn convert(self, state: &State) -> Self::Py {
        let Self { span, arg } = self;
        arg.map_or_else(
            || {
                vec![py::Stmt::Return(py::StmtReturn {
                    range: span.convert(state),
                    value: None,
                })]
            },
            |arg| {
                let WithStmts { expr, mut stmts } = (*arg).convert(state);
                stmts.push(py::Stmt::Return(py::StmtReturn {
                    range: span.convert(state),
                    value: Some(Box::new(expr)),
                }));
                stmts
            },
        )
    }
}

impl Convert for js::IfStmt {
    type Py = Vec<py::Stmt>;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span,
            test,
            cons,
            alt,
        } = self;
        let WithStmts { expr, mut stmts } = (*test).convert(state);
        let mut elif_clauses = vec![];
        if let Some(alt) = alt {
            elif_clauses.push(py::ElifElseClause {
                range: alt.span().convert(state),
                test: None,
                body: safe_block((*alt).convert(state)),
            });
        }
        loop {
            let clause = match elif_clauses.pop() {
                Some(x) if x.body.len() == 1 && x.body[0].is_if_stmt() && x.test.is_none() => x,
                Some(x) => {
                    elif_clauses.push(x);
                    break;
                }
                None => break,
            };
            let Some(py::Stmt::If(py::StmtIf {
                range,
                test,
                body,
                elif_else_clauses,
            })) = clause.body.into_iter().next()
            else {
                todo!()
            };
            elif_clauses.push(py::ElifElseClause {
                range,
                test: Some(*test),
                body,
            });
            elif_clauses.extend(elif_else_clauses);
        }
        stmts.push(py::Stmt::If(py::StmtIf {
            range: span.convert(state),
            test: Box::new(expr),
            body: safe_block((*cons).convert(state)),
            elif_else_clauses: elif_clauses,
        }));
        stmts
    }
}

impl Convert for js::Param {
    type Py = WithStmts<(py::ParameterWithDefault, Vec<py::Stmt>)>;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span,
            decorators: _,
            pat,
        } = self;
        let mut stmts = vec![];
        let PatPy {
            id,
            type_ann: ann,
            body_stmts,
            def_val,
        } = pat.convert(state).unwrap_into(&mut stmts);
        WithStmts {
            expr: (
                py::ParameterWithDefault {
                    range: span.convert(state),
                    default: def_val.map(Box::new),
                    parameter: py::Parameter {
                        range: span.convert(state),
                        name: id,
                        annotation: ann.map(Box::new),
                    },
                },
                body_stmts,
            ),
            stmts,
        }
    }
}

impl Convert for js::ParamOrTsParamProp {
    type Py = WithStmts<(py::ParameterWithDefault, Vec<py::Stmt>)>;
    fn convert(self, state: &State) -> Self::Py {
        match self {
            Self::Param(x) => x.convert(state),
            Self::TsParamProp(x) => x.convert(state),
        }
    }
}

impl Convert for js::TsParamProp {
    type Py = WithStmts<(py::ParameterWithDefault, Vec<py::Stmt>)>;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span: _,
            decorators: _,
            accessibility: _,
            is_override: _,
            readonly: _,
            param,
        } = self;
        param.convert(state)
    }
}
impl Convert for js::TsParamPropParam {
    type Py = WithStmts<(py::ParameterWithDefault, Vec<py::Stmt>)>;
    fn convert(self, state: &State) -> Self::Py {
        let span = self.span();
        match self {
            Self::Ident(x) => {
                let js::BindingIdent { id, type_ann } = x;
                let mut stmts = vec![];
                let id = id.convert(state);
                let ann = type_ann.convert(state).map(|x| x.unwrap_into(&mut stmts));
                WithStmts {
                    expr: (
                        py::ParameterWithDefault {
                            range: span.convert(state),
                            default: None,
                            parameter: py::Parameter {
                                range: id.range,
                                name: id,
                                annotation: ann.map(Box::new),
                            },
                        },
                        vec![],
                    ),
                    stmts,
                }
            }
            Self::Assign(x) => x.convert(state).map1(|x| {
                let PatPy {
                    id,
                    type_ann,
                    body_stmts,
                    def_val,
                } = x;
                (
                    py::ParameterWithDefault {
                        range: span.convert(state),
                        default: def_val.map(Box::new),
                        parameter: py::Parameter {
                            range: id.range,
                            name: id,
                            annotation: type_ann.map(Box::new),
                        },
                    },
                    body_stmts,
                )
            }),
        }
    }
}

impl Convert for js::TsTypeParamDecl {
    type Py = WithStmts<py::TypeParams>;
    fn convert(self, state: &State) -> Self::Py {
        let Self { span, params } = self;
        let mut stmts = Vec::new();
        WithStmts {
            expr: py::TypeParams {
                range: span.convert(state),
                type_params: params
                    .into_iter()
                    .map(|x| x.convert(state).unwrap_into(&mut stmts))
                    .collect(),
            },
            stmts,
        }
    }
}

impl Convert for js::TsTypeParam {
    type Py = WithStmts<py::TypeParam>;
    fn convert(self, state: &State) -> Self::Py {
        let Self {
            span,
            name,
            is_in: _,
            is_out: _,
            is_const: _,
            constraint,
            default,
        } = self;
        let mut stmts = vec![];
        WithStmts {
            expr: py::TypeParam::TypeVar(py::TypeParamTypeVar {
                range: span.convert(state),
                name: name.convert(state),
                bound: constraint.map(|x| Box::new((*x).convert(state).unwrap_into(&mut stmts))),
                default: default.map(|x| Box::new((*x).convert(state).unwrap_into(&mut stmts))),
            }),
            stmts,
        }
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
    let cm: Lrc<SourceMap> = Lrc::default();
    let handler = Handler::with_tty_emitter(ColorConfig::Auto, true, false, Some(cm.clone()));

    let mut paths = Vec::new();

    for entry in walkdir::WalkDir::new("a") {
        let Ok(entry) = entry else { continue };
        let Ok(meta) = entry.metadata() else { continue };
        if !meta.is_file() {
            continue;
        }
        let path = entry.path();
        let Some(stem) = path.file_stem() else {
            continue;
        };
        let Some(ext) = path.extension() else {
            continue;
        };
        let Some(stem) = stem.to_str() else { continue };
        if !ext.eq_ignore_ascii_case("ts") && !ext.eq_ignore_ascii_case("js") {
            continue;
        }
        if stem.ends_with(".d") {
            continue;
        }
        paths.push(path.to_owned());
    }

    let mut flatten_dirs = HashSet::new();
    for path in &paths {
        let path2 = path.strip_prefix("a").unwrap();
        let ext = path.extension().unwrap();
        let fm = cm.load_file(path).expect("failed to load file");
        let lexer = Lexer::new(
            if ext.eq_ignore_ascii_case("ts") {
                Syntax::Typescript(Default::default())
            } else {
                Syntax::Es(Default::default())
            },
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
                e.into_diagnostic(&handler).emit();
            })
            .expect("failed to parse module");
        let state = State::default();
        let _module = module.convert(&state);
        for import in state.js_imports.iter() {
            let mut import = import.as_str();
            let mut path2 = path2.to_owned();
            while let Some(x) = import.strip_prefix("../") {
                path2.pop();
                flatten_dirs.insert(path2.clone());
                import = x;
            }
        }
    }

    for path in paths {
        let script_path = path.strip_prefix("a").unwrap();
        let stem = path.file_stem().unwrap().to_str().unwrap();
        let stem = if stem == "index" { "" } else { stem };
        let ext = path.extension().unwrap();
        let out_path = PathBuf::new().join("b").join(PathBuf::from(
            convert_import_path(script_path, stem, &flatten_dirs)
                .trim_start_matches('.')
                .replace('.', "/")
                + ".py",
        ));
        if out_path.exists() {
            continue;
        }
        if let Some(parent) = out_path.parent() {
            let _ = fs::create_dir_all(parent);
        }
        eprintln!("{path:?} -> {out_path:?}");
        let fm = cm.load_file(&path).expect("failed to load file");
        let lexer = Lexer::new(
            if ext.eq_ignore_ascii_case("ts") {
                Syntax::Typescript(Default::default())
            } else {
                Syntax::Es(Default::default())
            },
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
                e.into_diagnostic(&handler).emit();
            })
            .expect("failed to parse module");
        let module = module.convert(&State::new(script_path, &flatten_dirs));
        let locator = ruff_source_file::Locator::new("");
        let stylist = ruff_python_codegen::Stylist::from_tokens(&[], &locator);
        let mut code = String::new();
        for stmt in module.body {
            let gen = ruff_python_codegen::Generator::new(
                stylist.indentation(),
                stylist.quote(),
                stylist.line_ending(),
            );
            code.push_str(&gen.stmt(&stmt));
            code.push('\n');
        }
        let formatted = ruff_python_formatter::format_module_source(
            &code,
            ruff_python_formatter::PyFormatOptions::default(),
        )
        .unwrap_or_else(|err| {
            eprintln!("{code}");
            panic!("{err}");
        });
        let mut out = fs::File::create(&out_path).unwrap();
        if out.write_all(formatted.as_code().as_bytes()).is_err() {
            drop(out);
            let _ = fs::remove_file(out_path);
            panic!("write failed");
        }
    }
}
