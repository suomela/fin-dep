# Blueprint

This folder contains the Lean blueprint setup for this project, based on
[PatrickMassot/leanblueprint](https://github.com/PatrickMassot/leanblueprint).

## Layout

- `src/`: blueprint source (`web.tex`, `print.tex`, `content.tex`, macros, plasTeX config)
- `print/`: generated PDF output (ignored in git)
- `web/`: generated web output (ignored in git)

## Local usage

From the repository root:

```sh
# Printable PDF output
cd blueprint/src && latexmk -output-directory=../print

# Copy bibliography to web input (recommended before web build)
cp blueprint/print/print.bbl blueprint/src/web.bbl

# Web output (requires plasTeX + leanblueprint plugin)
cd blueprint/src && plastex -c plastex.cfg web.tex

# Check declarations in \lean{...} (run after web build)
lake exe checkdecls blueprint/lean_decls
```

If you prefer the CLI wrapper and have it installed, equivalent commands are:

```sh
leanblueprint pdf
leanblueprint web
leanblueprint checkdecls
```

There is also a convenience wrapper from the repository root:

```sh
make -C blueprint all
```

For installation prerequisites of the web stack (notably Graphviz headers needed by
`pygraphviz`), follow the notes in the leanblueprint README.
