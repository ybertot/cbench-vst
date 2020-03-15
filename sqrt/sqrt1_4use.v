Require Import Reals Gappa.Gappa_library Psatz.
Require Import sqrt1_4gappa.
Import Raux FLT Generic_fmt Gappa_definitions.

Notation round' x :=
   (Generic_fmt.round Gappa_definitions.radix2 (FLT.FLT_exp (-149) 24) rndNE x).

Lemma reduce_error (x y : R) :
  (1 <= x <= 4)%R ->
  (/4 * sqrt x <= y - sqrt x <=  sqrt x)%R ->
  (Rabs ((round' (round' (y + round' (x / y)) / 2) -
         sqrt x) / (y - sqrt x)) <=
   127 * bpow radix2 (-7))%R.
Proof.
intros intx ybnd; apply Rabs_le.
generalize l1; unfold s1, s2, s3, i1, i2, i3, BND.
cbv[ lower upper]; lazy zeta.
replace (float2R f1) with 1%R by (compute; ring).
replace (float2R f2) with 2%R by (compute; ring).
replace (float2R f3) with (1 * bpow radix2 (-2))%R by reflexivity.
replace (float2R f4) with (-(127) * bpow radix2 (-7))%R by reflexivity.
rewrite Ropp_mult_distr_l.
replace (float2R f5) with (127 * bpow radix2 (-7))%R by reflexivity.

intros l1'.
assert (1 <= sqrt x)%R  by (rewrite <- sqrt_1; apply sqrt_le_1_alt; lra).
assert (tmp := l1' (sqrt x) ((y - sqrt x) / sqrt x)%R); revert tmp.
rewrite sqrt_sqrt by lra.
replace (sqrt x + (y - sqrt x) / sqrt x * sqrt x)%R with y by (field; lra).
replace (sqrt x + (y - sqrt x))%R with y by ring.
replace ((y - sqrt x) / sqrt x * sqrt x)%R with (y - sqrt x)%R by (field; lra).
replace (Float1 2) with 2%R by reflexivity.
intros tmp.
assert (1 <= sqrt x <= 2)%R.
  rewrite <- sqrt_1, <- (sqrt_pow2 2); replace (2 ^ 2)%R with 4%R by ring.
    split; apply sqrt_le_1_alt; lra.
  lra.
move ybnd after tmp.
assert ( bpow radix2 (-2) <= (y - sqrt x) / sqrt x <= 1)%R.
  split.
    simpl bpow.
    apply Rmult_le_reg_r with (sqrt x);[lra | ].
    field_simplify; lra.
  apply Rmult_le_reg_r with (sqrt x);[lra | ].
  field_simplify; lra.
lra.
Qed.
