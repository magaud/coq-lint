TARGET=clint
SRC=src
BIN=bin
OCAMLC=ocamlc
OPTIONS=unix.cma

all:	src/main.ml src/main.cmi
	$(OCAMLC) $(OPTIONS) -I $(SRC) $< -o $(BIN)/$(TARGET)

src/main.cmi: 	src/main.mli
	$(OCAMLC) -c $<

clean:
	rm -f bin/clint $(SRC)/*.cmi $(SRC)/*.cmo
