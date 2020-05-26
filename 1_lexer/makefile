.PHONY: all
all: main

main: main.ml
	ocamlopt -o main main.ml

main.ml: main.mll
	ocamllex main.mll	  

.PHONY: clean
clean: 
	rm -f main.cmx main.o main.cmi main main.ml
