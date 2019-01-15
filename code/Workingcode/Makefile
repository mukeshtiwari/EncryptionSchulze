# use make JAVA_HOME="$JAVA_HOME" run to run the executable
%.vo : %.v
	coqc $*.v

ListLemma.vo : ListLemma.v

ValidityExist.vo : ListLemma.vo ValidityExist.v

EncryptionSchulze.vo : ValidityExist.vo EncryptionSchulze.v

Extraction.vo : EncryptionSchulze.vo Extraction.v

ExtractionNative.vo : EncryptionSchulze.vo ExtractionNative.v

lib.ml : Extraction.vo

lib.mli : lib.ml

ballot_gen : parser.mli parser.ml big.ml lexer.ml lib.mli lib.ml cryptobinding.ml derivation.ml generate_ballot.ml 
	ocamlfind ocamlopt  -O3 -o ballot.out  -linkpkg -package str,num,menhirLib -I ocaml-java/bin/camljava camljava.cmxa -ppx ocaml-java/bin/ocaml-java-ppx parser.mli parser.ml big.ml lexer.ml lib.mli lib.ml cryptobinding.ml derivation.ml generate_ballot.ml


bench : ballot_gen Main
		@for i in 50 100 200 300 400 500 600 700 800 900 1000 2000 3000 4000 10000; do \
		   echo -n "Counting $$i ballots ..\n  "; \
		    /usr/bin/time -f "%E" bash -c "./ballot.out $$i | LD_LIBRARY_PATH=/usr/lib/jvm/java-8-openjdk-amd64/jre/lib/amd64/server ./a.out > /dev/null" ; \
		  done

clean:
	rm -rf _build *.vo *.glob *.class *.cmi *.cmx *.o *.out lib.ml lib.mli main.native main.byte 2>/dev/null || true


Main : parser.mli parser.ml big.ml lexer.ml lib.mli lib.ml cryptobinding.ml derivation.ml main.ml 
	ocamlfind ocamlopt  -O3 -o a.out  -linkpkg -package str,num,menhirLib -I ocaml-java/bin/camljava camljava.cmxa -ppx ocaml-java/bin/ocaml-java-ppx parser.mli parser.ml big.ml lexer.ml lib.mli lib.ml cryptobinding.ml derivation.ml main.ml

runlinux : Main
	 LD_LIBRARY_PATH=/usr/lib/jvm/java-8-openjdk-amd64/jre/lib/amd64/server ./a.out 

run : a.out
	LD_LIBRARY_PATH=$(JAVA_HOME)/jre/lib/server ./a.out

