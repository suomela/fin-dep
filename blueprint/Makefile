pdf:
	cd src && latexmk -output-directory=../print
	if [ -f print/print.bbl ]; then cp print/print.bbl src/web.bbl; fi

web:
	cd src && plastex -c plastex.cfg web.tex

checkdecls:
	lake exe checkdecls blueprint/lean_decls

all: pdf web checkdecls
