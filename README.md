# ts2py

A basic JavaScript/TypeScript to Python converter. This won't produce
working code because I obviously don't plan to port all of node.js to
Python, but it will translate the JS/TS AST to Python AST and serialize
it using [Ruff](https://github.com/astral-sh/ruff).

## Usage

The program will look at the directory `./a`, convert all .js/.ts
files into .py files and put them to the `./b` directory. Some stuff
will inevitably break as there are `todo!()`s littered all over the
code, but you're smart, you'll figure this out, right?
