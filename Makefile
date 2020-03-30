native:
	ocamlbuild -r -no-hygiene main.native

byte:
	ocamlbuild -r -no-hygiene main.d.byte

test:
	./runtests.sh

clean:
	ocamlbuild -clean
