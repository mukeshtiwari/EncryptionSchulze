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
	rm -rf _build *.vo *.glob lib.ml lib.mli main.native main.byte 2>/dev/null || true

MainNative : big.ml lib.ml lib.mli derivation.ml main.ml
	ocamlbuild  -use-ocamlfind -r -use-menhir -package num main.native	

MainByte: big.ml lib.ml lib.mli derivation.ml main.ml
	ocamlbuild  -use-ocamlfind -r -use-menhir  -package num main.byte

