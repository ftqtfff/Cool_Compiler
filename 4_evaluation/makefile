.PHONY: all 
all: main

main: main.ml
	ocamlopt -o main str.cmxa main.ml  

.PHONY: clean
clean: 
	rm -f main.cmx main.o main.cmi main
