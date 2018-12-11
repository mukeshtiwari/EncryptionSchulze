%.vo : %.v
	coqc $*.v

ListLemma.vo : ListLemma.v

ValidityExist.vo : ListLemma.vo ValidityExist.v

EncryptionSchulze.vo : ValidityExist.vo EncryptionSchulze.v

Extraction.vo : EncryptionSchulze.vo Extraction.v

ExtractionNative.vo : EncryptionSchulze.vo ExtractionNative.v

lib.ml : Extraction.vo

lib.mli : lib.ml


benchByte : MainByte rand.pl
	 @for i in 100 1000 10000 100000; do \
	echo -n "Counting $$i ballots ..\n  "; \
	./rand.pl $$i | time -f %E ./main.byte > /dev/null; \
	done


clean:
	rm -rf _build *.vo *.glob *.class *.cmi *.cmx *.o a.out lib.ml lib.mli main.native main.byte 2>/dev/null || true


Main : parser.mli parser.ml big.ml lexer.ml lib.mli lib.ml cryptobinding.ml derivation.ml main.ml 
	ocamlfind ocamlopt  -O3 -o a.out  -linkpkg -package str,num,menhirLib -I ocaml-java/bin/camljava camljava.cmxa -ppx ocaml-java/bin/ocaml-java-ppx parser.mli parser.ml big.ml lexer.ml lib.mli lib.ml cryptobinding.ml derivation.ml main.ml

run : a.out
	LD_LIBRARY_PATH=/usr/lib/jvm/java-8-openjdk-amd64/jre/lib/amd64/server ./a.out

