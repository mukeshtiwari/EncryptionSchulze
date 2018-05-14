Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import EncryptionSchulze.
Require Import Coq.Strings.String.
Require Import ZArith.
Require Import EqNat.
Require Import Coq.extraction.ExtrOcamlZBigInt.
Require Import Coq.extraction.ExtrOcamlString.
(*
Extraction Language Haskell.
Extraction "lib.hs" schulze_winners_pf. *)

Extraction Language Ocaml.
Extraction "lib.ml" schulze_winners_pf.
