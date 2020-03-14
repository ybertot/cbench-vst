Require Import Reals Gappa.Gappa_library Psatz.
Require Import sqrt1_gappa.
Import Raux FLT Generic_fmt Gappa_definitions.

Notation round' x :=
   (Generic_fmt.round Gappa_definitions.radix2 (FLT.FLT_exp (-149) 24) rndNE x).

Lemma titi (x y : R) :
  (1 <= x <= 4)%R ->
  (Rabs (y - sqrt x) <=  3 * bpow radix2 (-23))%R ->
  (Rabs (round' (round' (y + round' (x / y)) / 2) -
          ((y + x / y) / 2)) <= 3 * bpow radix2 (-23))%R.
Proof.
intros intx ybnd; apply Rabs_le.
generalize l1; unfold s1, s2, i1, i2, BND; cbv[ lower upper]; lazy zeta.
replace (float2R f1) with 1%R by (compute; ring).
replace (float2R f2) with 2%R by (compute; ring).
replace (float2R f3) with ((-3) * bpow radix2 (-23))%R by reflexivity.
rewrite Ropp_mult_distr_l.
replace (IZR (-3)) with (Ropp (IZR(3))) by ring.
replace (float2R f4) with (3 * bpow radix2 (-23))%R by reflexivity.
replace (IPR 2) with (2%R) by reflexivity. 
replace (Float1 2) with (2%R) by reflexivity.
intros l1'.
replace (y ^ 2)%R with (y * y)%R by ring.
assert (tmp:= l1' y); lra.
Qed.
