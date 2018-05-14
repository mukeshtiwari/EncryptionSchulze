%.vo : %.v
	coqc $*.v

ListLemma.vo : ListLemma.v

Existfun.vo : ListLemma.vo

EncryptionSchulze.vo : Existfun.vo EncryptionSchulze.v

Extraction.vo : EncryptionSchulze.vo Extraction.v

ExtractionNative.vo : EncryptionSchulze.vo ExtractionNative.v

lib.ml : Extraction.vo

lib.mli : lib.ml

benchNative: MainNative rand.pl
	@for i in 100 1000 10000 100000 250000 500000 1000000 2000000 4000000 8000000; do \
    echo -n "Counting $$i ballots ..\n  "; \
    ./rand.pl $$i | time -f %E ./main.native > /dev/null; \
  done

benchByte : MainByte rand.pl
	 @for i in 100 1000 10000 100000; do \
	echo -n "Counting $$i ballots ..\n  "; \
	./rand.pl $$i | time -f %E ./main.byte > /dev/null; \
	done


clean:
	rm -rf _build *.vo *.glob *.class *.cmi *.cmx *.o a.out lib.ml lib.mli main.native main.byte schulze/*.class schulze.jar schulze/*.jar 2>/dev/null || true

MainNative : big.ml lib.ml lib.mli derivation.ml main.ml
	ocamlbuild  -use-ocamlfind -r -use-menhir -package num main.native	

MainByte: big.ml lib.ml lib.mli derivation.ml main.ml
	ocamlbuild  -use-ocamlfind -r -use-menhir  -package num main.byte


HelloWorld.class : schulze/HelloWorld.java 
	javac -cp ".:javacryptocode/jarfiles/unicrypt-2.3.jar:javacryptocode/jarfiles/jnagmp-2.0.0.jar:javacryptocode/jarfiles/jna-4.5.0.jar" schulze/HelloWorld.java 

HelloWorld : schulze/HelloWorld.class
	java -cp ".:javacryptocode/jarfiles/unicrypt-2.3.jar:javacryptocode/jarfiles/jnagmp-2.0.0.jar:javacryptocode/jarfiles/jna-4.5.0.jar" schulze.HelloWorld

jarfile : schulze/HelloWorld.class
	jar cvf schulze.jar schulze/HelloWorld.class 

ocajavaexe : javaocamlbinding.ml 
	ocamlfind ocamlopt -g  -I ../ocaml-java/bin/camljava camljava.cmxa -ppx ../ocaml-java/bin/ocaml-java-ppx javaocamlbinding.ml 

runocaexe : a.out
	LD_LIBRARY_PATH=/usr/lib/jvm/java-8-openjdk-amd64/jre/lib/amd64/server ./a.out

