Require Import Reals Gappa.Gappa_library.
Require Import sqrt1_gappa.
Import Raux FLT Generic_fmt Gappa_definitions.

Notation round' x :=
   (Generic_fmt.round Gappa_definitions.radix2 (FLT.FLT_exp (-149) 24) rndNE x).

Check l1.
Print s1.
Print s2.
Print i2.
Print f3.

Lemma titi (y : R) : 
  (Rabs (round' (round' (y + round' ((y ^ 2) / y)) / Float1 2) -
          (y + (y ^ 2) / y)) <= 3 * bpow radix2 (-23))%R.
Proof.
apply Rabs_le.
generalize l1; unfold s1, s2, i1, f1, BND; simpl.
unfold float2R, Defs.F2R.
Gappa_definitions 
