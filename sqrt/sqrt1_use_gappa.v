Require Import Reals Gappa.Gappa_library Psatz.
Require Import sqrt1_gappa.
Import Raux FLT Generic_fmt Gappa_definitions.

Notation round' x :=
   (Generic_fmt.round Gappa_definitions.radix2 (FLT.FLT_exp (-149) 24) rndNE x).

Lemma close_computation (x y : R) :
  (1 <= x <= 4)%R ->
  (Rabs (y - sqrt x) <=  1 * bpow radix2 (-19))%R ->
  (Rabs (round' (round' (y + round' (x / y)) / 2) -
          ((y + x / y) / 2)) <= 3 * bpow radix2 (-24))%R.
Proof.
intros intx ybnd; apply Rabs_le.
generalize l1; unfold s1, s2, s3, i1, i2, i3, BND.
cbv[ lower upper]; lazy zeta.
replace (float2R f1) with 1%R by (compute; ring).
replace (float2R f2) with 2%R by (compute; ring).
replace (float2R f3) with (-(1) * bpow radix2 (-19))%R by reflexivity.
rewrite Ropp_mult_distr_l.
replace (IZR (-5)) with (Ropp (IZR(5))) by ring.
replace (float2R f4) with (1 * bpow radix2 (-19))%R by reflexivity.
replace (float2R f5) with (-(3) * bpow radix2 (-24))%R by reflexivity.
replace (float2R f6) with (3 * bpow radix2 (-24))%R by reflexivity.
intros l1'.
assert (tmp := l1' (sqrt x) (y - sqrt x)%R); revert tmp.
rewrite sqrt_sqrt by lra; replace (sqrt x + (y - sqrt x))%R with y by ring.
replace (Float1 2) with 2%R by reflexivity.
intros tmp.
apply Rabs_def2b in ybnd.
assert (1 <= sqrt x <= 2)%R.
  rewrite <- sqrt_1, <- (sqrt_pow2 2); replace (2 ^ 2)%R with 4%R by ring.
    split; apply sqrt_le_1_alt; lra.
  lra.
lra.
Qed.
