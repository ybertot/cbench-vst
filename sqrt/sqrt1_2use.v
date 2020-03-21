Require Import Reals Gappa.Gappa_library Psatz.
Require Import sqrt1_2gappa.
Import Raux FLT Generic_fmt Gappa_definitions.

Notation round' x :=
   (round Gappa_definitions.radix2 (FLT.FLT_exp (-149) 24) rndNE x).

Lemma rounded_to_formula (x y : R) :
  (1 <= x <= 4)%R ->
  (- / 2 ^ 12 <= y - sqrt x <=  sqrt x)%R ->
  (Rabs (round' (round' (y + round' (x / y)) / 2) -
          ((y + x / y) / 2)) <= 5 * / 2 ^ 23)%R.
Proof.
generalize sqrt1_2gappa.l1.
unfold s1, s2, s3, i1, i2, i3, BND.
cbv [lower upper]; lazy zeta.
replace (float2R f1) with 1%R by (compute; ring).
replace (float2R f2) with 2%R by (compute; ring).
replace (float2R f3) with (-1 / bpow radix2 12)%R by (compute; lra).
replace (float2R f4) with (-5 / bpow radix2 23)%R by (compute; lra).
replace (float2R f5) with (5 / bpow radix2 23)%R by (compute; lra).
replace (bpow Gappa_definitions.radix2 23) with (2 ^ 23)%R by (compute; lra).
replace (bpow Gappa_definitions.radix2 12) with (2 ^ 12)%R by (compute; lra).
replace (Float1 2) with 2%R by reflexivity.
intros l1' intx ybnd; apply Rabs_le.
rewrite Ropp_mult_distr_l.
assert (tmp := l1' (sqrt x) (((y - sqrt x) / sqrt x))%R).
assert (1 <= sqrt x <= 2)%R.
  rewrite <- sqrt_1, <- (sqrt_pow2 2); replace (2 ^ 2)%R with 4%R by ring.
    split; apply sqrt_le_1_alt; lra.
  lra.
assert (- / 2 ^ 12 <= (y - sqrt x) / sqrt x <= 1)%R.
  split; (apply Rmult_le_reg_r with (sqrt x);[lra | ]);
    unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra;[ | lra].
  apply Rle_trans with (2 := proj1 ybnd).
  rewrite <- Ropp_mult_distr_l.
  apply Ropp_le_contravar; rewrite <- (Rmult_1_r (/ (2 ^ 12))) at 1.
  apply Rmult_le_compat_l;[apply Rlt_le, Rinv_0_lt_compat; lra | lra].
revert tmp; clear l1'.
replace ((y - sqrt x) / sqrt x * sqrt x)%R with (y - sqrt x)%R by (field; lra).
replace (sqrt x + (y - sqrt x))%R with y by ring.
rewrite sqrt_sqrt by lra.
intros tmp.
lra.
Qed.
