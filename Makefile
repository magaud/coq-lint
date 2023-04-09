TARGET=clint
SRC=src
BIN=bin
OCAMLC=ocamlc
OPTIONS=unix.cma

all:	src/main.ml
	$(OCAMLC) $(OPTIONS) $< -o $(BIN)/$(TARGET)

clean:
	rm -f bin/clint $(SRC)/*.cmi $(SRC)/*.cmo
