.PHONY: all
all: main

main: main.ml
	rm main.mli
	ocamlopt -o main main.ml 

main.ml: main.mly
	ocamlyacc main.mly

.PHONY: clean
clean: 
	rm -f main.mli main.ml main.cmx main.o main.cmi main
