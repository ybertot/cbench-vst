Require Import VST.floyd.functional_base.
From compcert Require Import Fcore Floats Fcore_defs Fappli_IEEE.
From compcert Require Import Fappli_IEEE_extra.
Require Import Reals Psatz.

Print compcert.flocq.Appli.Fappli_IEEE_bits.binary32.
Print Fappli_IEEE.binary_float.

Definition float_to_nat (z: float32) : nat :=
  match z with 
   | B754_zero _ => O
   | B754_infinity _ => O
   | B754_nan _ _ => O
   | B754_finite _ m e _ => Pos.to_nat m * 2 ^ Z.to_nat(e + 149)
   end.

Definition float_to_exp (z : float32) : Z :=
  match z with
  | B754_finite _ m e _ => e
  | _ => 0
  end.

Lemma Rabs_INR (n : nat) : Rabs(INR n) = INR n.
Proof.
apply Rabs_pos_eq, pos_INR.
Qed.

Lemma Zpow_natpow (x y : nat) : Z.of_nat (x ^ y) =
  Z.of_nat x ^ Z.of_nat y.
Proof.
induction y as [ | y IH].
  reflexivity.
rewrite <- Zpower_nat_Z.
simpl.
now rewrite Nat2Z.inj_mul, IH, <- Zpower_nat_Z.
Qed.

Lemma IZR_INR_Z2N n : 
  0 <= n -> IZR n = INR (Z.to_nat n).
Proof.
destruct n as [ | p | p]; auto; try lia.
now unfold Z.to_nat, IZR; rewrite INR_IPR.
Qed.

Lemma float_to_nat_prop (z : float32) :
  is_finite 24 128 z = true -> (-149 <= float_to_exp z) ->
  INR (float_to_nat z) = Rabs (B2R 24 128 z  * bpow radix2 149).
Proof.
intros fin1 fin2.
destruct z as [dummy | dummy | dum1 dum2 | sign m e validity];
  try discriminate fin1.
- now rewrite Rmult_0_l, Rabs_R0.
- unfold float_to_nat, B2R.
  rewrite F2R_cond_Zopp; unfold F2R; simpl Z2R; simpl Fexp.
  rewrite !Rabs_mult, abs_cond_Ropp, Rabs_mult, mult_INR.
  rewrite P2R_INR, Rabs_INR.
  rewrite !Rabs_pos_eq; try apply bpow_ge_0.
  rewrite Rmult_assoc, <- bpow_plus.
  rewrite (INR_IZR_INZ (2 ^ _)).
  rewrite Zpow_natpow, <- pow_IZR.
  replace (IZR (Z.of_nat 2)) with 2%R by reflexivity.
  rewrite <- Rpower_pow;[ | lra].
  rewrite bpow_powerRZ, powerRZ_Rpower; simpl;[ | lra].
  rewrite !IZR_INR_Z2N; [easy | | lia].
  simpl in fin2; lia.
Qed.

Definition body_exp x y :=
  Float32.div (Float32.add y (Float32.div x y))
     (Float32.of_int (Int.repr 2)).

Transparent Float32.div.
Transparent Float32.add.
Transparent Float32.of_int.
Transparent Int.repr.

Definition f32_exp := FLT_exp (3 - 128 -24) 24.

Notation round' := (round radix2 f32_exp (round_mode mode_NE)).

Record pos_float :=
 { pos_float_val : float32;
   pos_float_fin : is_finite 24 128 pos_float_val = true;
   pos_float_cond : (0 < B2R 24 128 pos_float_val)%R}.

Definition body_exp_pos_R x y := 
  round' (round' (B2R 24 128 (pos_float_val y) +
      round' (B2R 24 128 (pos_float_val x) / B2R 24 128 (pos_float_val y))) / 2).

Lemma round1 m: round radix2 f32_exp (round_mode m) 1 = 1%R.
Proof.
assert (for1 : generic_format radix2 f32_exp 1).
  replace 1%R with (F2R (Float radix2 (cond_Zopp false (2 ^ 23)) (-23))).
    now apply generic_format_canonic, canonic_canonic_mantissa.
  compute; lra.
now apply round_generic; auto; apply valid_rnd_round_mode.
Qed.

Lemma round'1 : round' 1 = 1%R.
Proof. now apply round1. Qed.

Lemma round'2 : round' 2 = 2%R.
Proof.
assert (for2 : generic_format radix2 (FLT_exp (3 - 128 - 24) 24) 2).
  replace 2%R with (F2R (Float radix2 (cond_Zopp false (2 ^ 23)) (-22))).
    now apply generic_format_canonic, canonic_canonic_mantissa.
  compute; lra.
now apply round_generic; auto; apply valid_rnd_round_mode.
Qed.

Lemma round'4 : round' 4 = 4%R.
Proof.
assert (for2 : generic_format radix2 (FLT_exp (3 - 128 - 24) 24) 4).
  replace 4%R with (F2R (Float radix2 (cond_Zopp false (2 ^ 23)) (-21))).
    now apply generic_format_canonic, canonic_canonic_mantissa.
  compute; lra.
now apply round_generic; auto; apply valid_rnd_round_mode.
Qed.

Lemma round_le' (x y : R) : (x <= y)%R -> (round' x <= round' y)%R.
Proof.
intros xley.
apply round_le; auto.
  now apply fexp_correct.
now apply valid_rnd_round_mode.
Qed.

Definition fmax :=  Float radix2 (2 ^ 24 - 1) 104.

Definition f32max : float32 :=
    B754_finite 24 128 false (2 ^ 24 - 1) 104 eq_refl.

Lemma float32pow2_aux (exp : Z) : 
  -149 <= exp <= 104 ->
  bounded 24 128 (2 ^ 23) exp = true.
Proof.
intros cnd1; unfold bounded.
rewrite andb_true_intro; auto.
split.
  apply Zeq_bool_true; unfold FLT_exp; simpl (Z.pos _).
  rewrite Z.max_l;[ring | lia].
apply Zle_imp_le_bool; lia.
Qed.

Definition float32pow2 (exp : Z) :=
  match Z_le_gt_dec exp 104 with
  | left h1 =>
    match Z_le_gt_dec (-149) exp with
    | left h2 => B754_finite 24 128 false (2 ^ 23) exp
                    (float32pow2_aux exp (conj h2 h1))
    | right _ => B754_zero 24 128 false
    end
  | right _ => B754_zero 24 128 false
  end.

Definition predf32max : float32 :=
    B754_finite 24 128 false (2 ^ 24 - 2) 104 eq_refl.

Lemma boundf32max : (B2R 24 128 f32max < bpow radix2 128)%R.
Proof.
now apply (bounded_lt_emax 24 128).
Qed.

Lemma boundpredf32max : (B2R 24 128 predf32max < B2R 24 128 f32max)%R.
Proof.
compute; lra.
Qed.

Lemma round_B2R' x : round' (B2R 24 128 x) = B2R 24 128 x.
Proof.
assert (tmp := generic_format_FLT radix2 _ 24 _ (FLT_format_B2R 24 128 eq_refl x)).
now apply round_generic;[ apply valid_rnd_round_mode | exact tmp ].
Qed.

Lemma body_exp_div_x_y_bounds1 x y :
  (1 < B2R 24 128 (pos_float_val x))%R ->
  (1 < B2R 24 128 (pos_float_val y) <= B2R 24 128 (pos_float_val x))%R ->
  (1 <= B2R 24 128 (pos_float_val x) / B2R 24 128 (pos_float_val y)
     <= B2R 24 128 (pos_float_val x))%R.
Proof.
destruct x as [x finx x0]; destruct y as [y finy y0]; simpl pos_float_val.
set (x' := B2R 24 128 x); set (y':= B2R 24 128 y).
intros intx inty.
assert (ygt0 : y' <> 0%R) by lra.
split.
  apply Rmult_le_reg_r with y';[lra | ].
  now unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_l, Rmult_1_r; lra.
apply Rmult_le_reg_r with y';[lra | ].
now unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r; [nra | lra].
Qed.

Lemma body_exp_div_x_y_bounds x y :
  (1 < B2R 24 128 (pos_float_val x))%R ->
  (1 < B2R 24 128 (pos_float_val y) <= B2R 24 128 (pos_float_val x))%R ->
  (1 <= round' (B2R 24 128 (pos_float_val x) / B2R 24 128 (pos_float_val y))
     <= B2R 24 128 (pos_float_val x))%R.
Proof.
destruct x as [x finx x0]; destruct y as [y finy y0]; simpl pos_float_val.
set (x' := B2R 24 128 x); set (y':= B2R 24 128 y).
intros intx inty.
assert (ygt0 : y' <> 0%R) by lra.
assert (divint : (1 <= x' / y' <= x')%R).
  exact (body_exp_div_x_y_bounds1 (Build_pos_float x finx x0)
            (Build_pos_float y finy y0) intx inty).
split.
  rewrite <- round'1; apply round_le'; tauto.
unfold x' at 2; rewrite <- round_B2R'; fold x'.
apply round_le'; tauto.
Qed.

Lemma body_exp_sum_bounds x y :
  (1 < B2R 24 128 (pos_float_val x) <  B2R 24 128 predf32max)%R ->
  (1 < B2R 24 128 (pos_float_val y) <= B2R 24 128 (pos_float_val x))%R ->
  (2 <= round' (B2R 24 128 (pos_float_val y) + 
          round' (B2R 24 128 (pos_float_val x) / B2R 24 128 (pos_float_val y)))
     <= B2R 24 128 f32max)%R.
Proof.
destruct x as [x finx x0]; destruct y as [y finy y0]; simpl pos_float_val.
set (x' := B2R 24 128 x); set (y':= B2R 24 128 y).
intros intx inty.
assert ((1 <= round' (x' / y') <= x')%R).
  exact (body_exp_div_x_y_bounds
           (Build_pos_float x finx x0) (Build_pos_float y finy y0)
           (proj1 intx) inty).
destruct (Rlt_le_dec x' (bpow radix2 64)) as [xlow | xhigh].
  split.
    rewrite <- round'2.
    apply round_le'; lra.
  assert (two65 : (2 * bpow radix2 64 =
                  (B2R 24 128 (B754_finite 24 128 false (2 ^ 23) 42 eq_refl)))%R).
    compute; lra.
  apply Rle_trans with (2 * bpow radix2 64)%R.
    rewrite two65.
    rewrite <- (round_B2R' (B754_finite _ _ _ (2 ^ 23) _ _)).
    apply round_le'; rewrite <- two65; lra.
  compute; lra.
rewrite <- round'2, <- round_B2R'.
assert (sqrtemax : sqrt (bpow radix2 128) = bpow radix2 64).
  apply sqrt_lem_1; try apply bpow_ge_0.
  now rewrite <- bpow_plus.
destruct (Rlt_le_dec y' (sqrt x')) as [ylow | yhigh].
  assert (y' < bpow radix2 64)%R.
    apply Rlt_trans with (1 := ylow).
    rewrite <-sqrtemax.
    apply sqrt_lt_1_alt.
    split; [ lra | ].
    apply Rlt_trans with (1 := proj2 intx).
    compute; lra.    
  split; apply round_le'; try lra.
  apply Rle_trans with (bpow radix2 64 + B2R 24 128 predf32max)%R.
    now apply Rplus_le_compat; lra.
  compute; lra.
split; apply round_le'; try lra.
assert (0 < sqrt x')%R.
  apply sqrt_lt_R0; lra.
assert (divsqrt : (x' / y' <= sqrt x')%R).
  apply Rmult_le_reg_r with y';[lra | ].
    unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r;[ | lra].
    rewrite <- (sqrt_sqrt x') at 1;[ | lra].
    now apply Rmult_le_compat_l;[lra | ].
apply Rle_trans with (B2R 24 128 predf32max + bpow radix2 64)%R.
  apply Rplus_le_compat;[lra | ].
  assert (two64 : (bpow radix2 64 =
                  (B2R 24 128 (B754_finite 24 128 false (2 ^ 23) 41 eq_refl)))%R).
    compute; lra.
  rewrite two64, <- round_B2R'; apply round_le'; rewrite <- two64.
apply Rle_trans with (1 := divsqrt).
  rewrite <- sqrtemax; apply Rlt_le, sqrt_lt_1_alt; split;[lra | ].
  apply Rlt_trans with (2 := boundf32max).
  apply Rlt_trans with (2 := boundpredf32max); tauto.
compute; lra.
Qed.

Lemma body_exp_bounds x y :
  (1 < B2R 24 128 (pos_float_val x) < B2R 24 128 predf32max)%R ->
  (1 < B2R 24 128 (pos_float_val y) <= B2R 24 128 (pos_float_val x))%R ->
  (1 <= body_exp_pos_R x y <= B2R 24 128 f32max)%R.
Proof.
destruct x as [x finx x0]; destruct y as [y finy y0]; simpl pos_float_val.
set (x' := B2R 24 128 x); set (y':= B2R 24 128 y).
intros intx inty.
assert ((2 <= round' (y' + round' (x' / y')) <= B2R 24 128 f32max)%R).
  exact (body_exp_sum_bounds
           (Build_pos_float x finx x0) (Build_pos_float y finy y0)
           intx inty).
unfold body_exp_pos_R; simpl pos_float_val; fold x' y'.
rewrite <- round'1, <- round_B2R'.
split.
  apply round_le'; lra.
apply round_le'; lra.
Qed.

Lemma float32_bound_ulp x :
  (1 <= x)%R ->
  (0 < ulp radix2 f32_exp x < x / bpow radix2 21)%R.
Proof.
intros intx; assert (xn0 : x <> 0%R) by lra.
split.
  apply Rlt_le_trans with (ulp radix2 f32_exp (bpow radix2 0)).
    rewrite ulp_bpow; compute; lra.
  apply ulp_le_pos.
        now apply fexp_correct.
      now apply FLT_exp_monotone.
    now apply bpow_ge_0.
  now simpl bpow; lra.
apply Rle_lt_trans with (ulp radix2 f32_exp (bpow radix2 (ln_beta radix2 x))).
  apply ulp_le_pos.
        now apply fexp_correct.
      now apply FLT_exp_monotone.
  lra.
  destruct (ln_beta radix2 x) as [v vbeta].
  simpl; replace x with (Rabs x) by now rewrite Rabs_pos_eq; lra.
  now assert (vbeta' :=  vbeta xn0); lra.
rewrite ulp_bpow.
destruct (ln_beta radix2 x) as [v vbeta].
assert (vbeta' := vbeta xn0).
simpl (f32_exp _).
assert (absx : Rabs x = x) by now rewrite Rabs_pos_eq; lra.
assert (0 < v).
  apply (lt_bpow radix2).
  apply Rle_lt_trans with (2 := proj2 vbeta').
  now rewrite absx; simpl bpow; lra.
assert (fexpv : f32_exp (v + 1) = v - 23).
  now unfold f32_exp, FLT_exp; rewrite Z.max_l; lia.
apply Rlt_le_trans with (bpow radix2 (v - 1) / bpow radix2 21)%R.
  unfold Rdiv; rewrite <- bpow_opp, <- bpow_plus, fexpv; apply bpow_lt; lia.
apply Rmult_le_compat_r.
  now apply Rlt_le, Rinv_0_lt_compat, bpow_gt_0.
now rewrite <- absx; lra.
Qed.

Definition ulp1 := bpow radix2 (-23).

Lemma canonic_exp_bpow : forall x e, x <> 0%R -> 
  -149 < canonic_exp radix2 f32_exp x ->
  -149 < e + canonic_exp radix2 f32_exp x ->
  canonic_exp radix2 f32_exp (x * bpow radix2 e)%R = canonic_exp radix2 f32_exp x + e.
Proof.
intros x e xn0 xbnds ebnds.
revert xbnds ebnds.
unfold canonic_exp, f32_exp, FLT_exp.
rewrite ln_beta_mult_bpow; auto.
destruct (Z_le_gt_dec (3 - 128 - 24) (ln_beta radix2 x - 24)).
  rewrite Z.max_l; lia.
rewrite Z.max_r; lia.
Qed.

Lemma canonic_exp_32 e r :
  -126 < e ->
  (bpow radix2 (e - 1) <= r < bpow radix2 e)%R ->
  canonic_exp radix2 f32_exp r = e - 24.
Proof.
intros ce inte.
unfold canonic_exp, f32_exp, FLT_exp.
assert (r0 : (0 <= r)%R).
  assert (tmp := bpow_ge_0 radix2 (e - 1)); lra.
assert (vln : ln_beta_val radix2 _ (ln_beta radix2 r) = e).
  now  apply ln_beta_unique; rewrite Rabs_pos_eq.
rewrite vln.
apply Z.max_l; lia.
Qed.

Lemma mantissa_bpow x e : 
  x <> 0%R ->
  -149 < canonic_exp radix2 f32_exp x ->
  -149 < e + canonic_exp radix2 f32_exp x ->
  (scaled_mantissa radix2 f32_exp (x * bpow radix2 e) = 
  scaled_mantissa radix2 f32_exp x)%R.
Proof.
unfold scaled_mantissa.
intros xn0 cndx cnde; rewrite canonic_exp_bpow; auto.
rewrite !Rmult_assoc, <- !bpow_plus.
apply f_equal with (f := fun u => (x * bpow radix2 u)%R); ring.
Qed.



Lemma round_mult_bpow x e :
  (x <> 0)%R ->
  -149 < canonic_exp radix2 f32_exp x ->
  -149 < e + canonic_exp radix2 f32_exp x ->
  (round' (x * bpow radix2 e) = round' x * bpow radix2 e)%R.
Proof.
intros xn0 canx inte.
unfold round, F2R; simpl.
rewrite mantissa_bpow by tauto.
rewrite canonic_exp_bpow by tauto.
now rewrite bpow_plus, Rmult_assoc.
Qed.

Lemma ulp_1_2 x : (1 <= x < 2)%R ->
   ulp radix2 f32_exp x = ulp1.
Proof.
intros intx.
rewrite ulp_neq_0; try lra.
rewrite (canonic_exp_32 1); try (simpl bpow; lra); try lia.
reflexivity.
Qed.

Lemma canonic_exp_m23 x :
  x <> 0%R ->
  canonic_exp radix2 f32_exp x = -23 <->
  ln_beta_val _ x (ln_beta radix2 x) = 1.
Proof.
intros xn0.
split; unfold canonic_exp, f32_exp; destruct (ln_beta radix2 x) as [v vprop];
  simpl ln_beta_val; unfold FLT_exp.
  destruct (Z_le_gt_dec (-149) (v - 24)) as [it | abs].
    rewrite Z.max_l; lia.
  rewrite Z.max_r; lia.
intros v1; rewrite v1, Z.max_l; lia.
Qed.

Lemma canonic_exp_m22 x :
  x <> 0%R ->
  canonic_exp radix2 f32_exp x = -22 <->
  ln_beta_val _ x (ln_beta radix2 x) = 2.
Proof.
intros xn0.
split; unfold canonic_exp, f32_exp; destruct (ln_beta radix2 x) as [v vprop];
  simpl ln_beta_val; unfold FLT_exp.
  destruct (Z_le_gt_dec (-149) (v - 24)) as [it | abs].
    rewrite Z.max_l; lia.
  rewrite Z.max_r; lia.
intros v1; rewrite v1, Z.max_l; lia.
Qed.

Lemma canonic_exp_m21 x :
  x <> 0%R ->
  canonic_exp radix2 f32_exp x = -21 <->
  ln_beta_val _ x (ln_beta radix2 x) = 3.
Proof.
intros xn0.
split; unfold canonic_exp, f32_exp; destruct (ln_beta radix2 x) as [v vprop];
  simpl ln_beta_val; unfold FLT_exp.
  destruct (Z_le_gt_dec (-149) (v - 24)) as [it | abs].
    rewrite Z.max_l; lia.
  rewrite Z.max_r; lia.
intros v1; rewrite v1, Z.max_l; lia.
Qed.

Lemma body_exp_value x y :
  let x' := B2R 24 128 (pos_float_val x) in
  let y' := B2R 24 128 (pos_float_val y) in
  (1 < x' < B2R 24 128 predf32max)%R ->
  (1 < y' <= x')%R ->
  B2R 24 128 (body_exp (pos_float_val x) (pos_float_val y)) = 
        round' (round' (y' + round' (x' / y')) / 2).
Proof.
lazy zeta.
destruct x as [x finx x0]; destruct y as [y finy y0]; simpl pos_float_val.
set (x' := B2R 24 128 x); set (y':= B2R 24 128 y).
intros intx' inty'.
assert (yn0 : y' <> 0%R) by lra.
unfold body_exp, Float32.div.
assert (tmp := body_exp_bounds (Build_pos_float x finx x0)
                                 (Build_pos_float y finy y0) intx' inty').
assert (tm2 := body_exp_sum_bounds (Build_pos_float x finx x0)
                                     (Build_pos_float y finy y0)
                    intx' inty').
assert (tm3 := body_exp_div_x_y_bounds (Build_pos_float x finx x0)
                                     (Build_pos_float y finy y0)
                    (proj1 intx') inty').
unfold body_exp_pos_R in tmp, tm2, tm3; simpl pos_float_val in tmp, tm2, tm3.
assert (tm4 := Bdiv_correct 24 128 eq_refl eq_refl Float32.binop_pl mode_NE x y yn0).
fold x' in tmp, tm2, tm3, tm4; fold y' in tmp, tm2, tm3, tm4.
assert (divlt : Rlt_bool (Rabs (round' (x' / y'))) (bpow radix2 128) = true).
  apply Rlt_bool_true.
  rewrite Rabs_pos_eq;[ | lra].
  now assert (tmp5:= conj boundpredf32max boundf32max); lra.
fold f32_exp in tm4.
rewrite divlt in tm4; destruct tm4 as [vdivxy [findivxy signdivxy]].
clear divlt.
unfold Float32.add.
set (divxy := Bdiv 24 128 eq_refl eq_refl Float32.binop_pl mode_NE x y).
fold divxy in signdivxy, findivxy, vdivxy.
set (divxy' := B2R _ _ divxy).
assert (findivxy' : is_finite 24 128 divxy = true).
  now rewrite findivxy, finx.
assert (tm6 := Bplus_correct 24 128 eq_refl eq_refl Float32.binop_pl mode_NE y
                     divxy finy findivxy').
assert (pluslt :
      Rlt_bool (Rabs (round' (y' + divxy'))) (bpow radix2 128) = true).
  apply Rlt_bool_true; unfold divxy'; rewrite vdivxy, Rabs_pos_eq.
    now assert (tmp5:= conj boundpredf32max boundf32max); lra.
  lra.      
fold y' divxy' f32_exp in tm6; rewrite pluslt in tm6; clear pluslt.
destruct tm6 as [vsum [finsum signsum]].
assert (fin2 : is_finite 24 128 (Float32.of_int (Int.repr 2)) = true).
  reflexivity.
 assert (b2n0 : B2R 24 128 (Float32.of_int (Int.repr 2)) <> 0%R).
  now compute; lra.
assert (tm4 := Bdiv_correct 24 128 eq_refl eq_refl Float32.binop_pl mode_NE
                   (Bplus 24 128 eq_refl eq_refl Float32.binop_pl mode_NE y
          (Bdiv 24 128 eq_refl eq_refl Float32.binop_pl mode_NE x y))
                   _ b2n0).
  set (bexp :=   Bdiv 24 128 eq_refl eq_refl Float32.binop_pl mode_NE
              (Bplus 24 128 eq_refl eq_refl Float32.binop_pl mode_NE y
                 (Bdiv 24 128 eq_refl eq_refl Float32.binop_pl mode_NE x y))
              (Float32.of_int (Int.repr 2))).
fold bexp in tm4.
set (sum := (Bplus 24 128 eq_refl eq_refl Float32.binop_pl mode_NE y
                       divxy)).
fold divxy sum in vsum, finsum, signsum, tm4.
assert (explt : Rlt_bool (Rabs (round' (B2R 24 128 sum /
               B2R 24 128 (Float32.of_int (Int.repr 2)))))
              (bpow radix2 128) = true).
apply Rlt_bool_true.
replace (B2R 24 128 (Float32.of_int (Int.repr 2))) with 2%R
       by (now compute; lra).
rewrite vsum; unfold divxy'; rewrite vdivxy.
rewrite Rabs_pos_eq;[ | lra].
  now assert (tmp5:= conj boundpredf32max boundf32max); lra.
fold f32_exp in tm4.
rewrite explt in tm4; destruct tm4 as [vexp [finexp signexp]].
replace (B2R 24 128 (Float32.of_int (Int.repr 2))) with 2%R in vexp
       by now compute; lra.
unfold bexp in vexp; rewrite vsum in vexp; unfold divxy' in vexp.
rewrite vdivxy in vexp; exact vexp.
Qed.

Notation cexp' := (canonic_exp radix2 f32_exp).

Lemma body_exp_value_scale x y e:
  let x' := B2R 24 128 x in
  let y' := B2R 24 128 y in
  (1 < x' <= 4)%R ->
  (sqrt x' <= y' <= 2 * sqrt x')%R ->
  -125 < e ->
  -149 < (2 * e) + canonic_exp radix2 f32_exp x' ->
  (round' (round' (y' + round' (x' / y')) / 2) * bpow radix2 e =
  round' (round' (y' * bpow radix2 e +
              round' ((x' * bpow radix2 (2 * e)) /
                      (y' * bpow radix2 e))) / 2))%R.
Proof.
intros x' y' intx inty elb inte.
assert (1 < sqrt x')%R.
  rewrite <- sqrt_1.
  apply sqrt_lt_1_alt; lra.
assert (yn0 : y' <> 0%R) by lra.
assert (bpgt0 : (0 < bpow radix2 e)%R) by apply bpow_gt_0.
assert (sqrtlt : (sqrt x' < x')%R).
  enough (1 * sqrt x' < x')%R by lra.
  rewrite <- (sqrt_sqrt x') at 2 by lra.
  apply Rmult_lt_compat_r; lra.
assert (sle2 : (sqrt x' <= 2)%R).
  rewrite <- (sqrt_pow2 2) by lra.
  apply sqrt_le_1_alt; lra.
assert (qgth : (/2 < x' / y')%R).
  apply Rmult_lt_reg_r with y';[lra | ].
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
  lra.
assert (qgt0 : (0 < x' / y')%R) by lra.
replace (2 * e) with (e + e) by ring.
rewrite bpow_plus.
replace (x' * (bpow radix2 e * bpow radix2 e) / (y' * bpow radix2 e))%R with
    ((x' / y') * bpow radix2 e)%R by now field; lra.
assert (rh : (round' (/2) = /2)%R).
  apply round_generic; try typeclasses eauto.
  replace (/2)%R with (bpow radix2 (-1)) by (compute; lra).
  apply generic_format_bpow'.
    apply FLT_exp_valid; reflexivity.
  apply Z.lt_le_incl; reflexivity.
assert (rqgth : (/2 <= round' (x' / y'))%R).
  rewrite <- rh; apply round_le'; lra.
assert (sumgt1 : (3/2 < y' + round' (x' / y'))%R) by lra.
assert (rsumgt1 : (1 <= round' (y' + round' (x' / y')))%R).
  rewrite <- round'1; apply round_le'; lra.
assert (expgeh : (/2 <= round' (y' + round' (x' / y')) / 2)%R) by lra.
assert (rexpgeh : (/2 <= round' (round' (y' + round' (x' / y')) / 2))%R).
  now rewrite <- rh; apply round_le'.
assert (qle2 : (x' / y' <= 2)%R).
  apply Rmult_le_reg_r with y';[lra | ].
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
  rewrite <- (sqrt_sqrt x') by lra.
  apply Rmult_le_compat; try lra.
  rewrite <- (sqrt_pow2 2) by lra.
assert (rqle2 : (round' (x' / y') <= 2)%R).
  now rewrite <- round'2; apply round_le'.
assert (r6 : round' 6 = 6%R).
  assert (ccexp : 6 <> 0 -> -21 <= 0) by lia.
  generalize (generic_format_F2R radix2 f32_exp 6 0 ).
  replace (canonic_exp radix2 f32_exp (F2R {|Fnum := 6; Fexp := 0|})) with
     (-21); cycle 1.
    unfold canonic_exp; simpl.
    replace (ln_beta_val radix2 _
                    (ln_beta radix2 (F2R {|Fnum :=6; Fexp :=0|}))) with
    3.
      reflexivity.
    symmetry; apply ln_beta_unique.
    replace (F2R {| Fnum := 6; Fexp := 0|}) with 6%R by (compute; lra).
    rewrite Rabs_pos_eq by lra.
    compute; lra.
  replace (F2R {| Fnum := 6; Fexp := 0|}) with 6%R by (compute; lra).
  intros tmp; assert (gf6 := tmp ccexp); clear tmp.
  apply round_generic; try typeclasses eauto.
  exact gf6.
assert (sumle6: (y' + round' (x' / y') <= 6)%R) by lra.
assert (rsumle6 : (round' (y' + round' (x' / y')) <= 6)%R).
  now rewrite <- r6; apply round_le'.
assert (exple4: (round' (y' + round' (x' / y')) / 2 <= 4)%R) by lra.
assert (-24 <= cexp' (x' / y') <= -22).
  destruct (Rle_lt_dec 1 (x' / y')).
    destruct (Rle_lt_dec 2 (x' / y')).
      rewrite (canonic_exp_32 2);[lia | lia| simpl bpow; split; lra].
    rewrite (canonic_exp_32 1);[lia | lia| simpl bpow; split; lra].
  rewrite (canonic_exp_32 0);[lia | lia| simpl bpow; split; lra].
rewrite round_mult_bpow; try lra; try lia.
rewrite <- Rmult_plus_distr_r.
assert (-23 <= (cexp' (y' + round' (x' / y'))) <= -21).
  destruct (Rle_lt_dec 2 (y' + round' (x' / y'))).
    destruct (Rle_lt_dec 4 (y' + round' (x' / y'))).
      rewrite (canonic_exp_32 3);[lia | lia| simpl bpow; split; lra].
    rewrite (canonic_exp_32 2);[lia | lia| simpl bpow; split; lra].
  rewrite (canonic_exp_32 1);[lia | lia| simpl bpow; split; lra].
rewrite sqrt_pow2 by lra.
rewrite round_mult_bpow; try lra; try lia.
assert (tech : forall a b, ((a * b) / 2 = (a / 2) * b)%R)
   by (intros; field; lra).
rewrite tech; clear tech.
assert (-24 <= (cexp' (round' (y' + round' (x' / y')) / 2)) <= -22).
  destruct (Rle_lt_dec 1 (round' (y' + round' (x' / y')) / 2)).
    destruct (Rle_lt_dec 2 (round' (y' + round' (x' / y')) / 2)).
      rewrite (canonic_exp_32 2);[lia | lia| simpl bpow; split; lra].
    rewrite (canonic_exp_32 1);[lia | lia| simpl bpow; split; lra].
  rewrite (canonic_exp_32 0);[lia | lia| simpl bpow; split; lra].
rewrite round_mult_bpow; try lra; try lia.
Qed.

Lemma body_exp_decrease1 x y :
  let x' := B2R 24 128 (pos_float_val x) in
  let y' := B2R 24 128 (pos_float_val y) in
  (1 < x' < B2R 24 128 predf32max)%R ->
  (2 * sqrt x' < y' <= x')%R ->
  (round' (sqrt x') <=
      B2R 24 128 (body_exp (pos_float_val x) (pos_float_val y)) < 2 / 3 * y')%R.
Proof.
lazy zeta.
destruct x as [x finx x0]; destruct y as [y finy y0]; simpl pos_float_val.
set (x' := B2R 24 128 x); set (y':= B2R 24 128 y).
intros intx' inty'.
assert (sgt0 : (1 < sqrt x')%R).
  now rewrite <- sqrt_1; apply sqrt_lt_1_alt; lra.
assert (sx0 : (sqrt x' <> 0)%R) by lra.
set (e := (y' - sqrt x')%R).
assert (divlow : (x' / y' <= sqrt x' / 2)%R).
  rewrite <- (sqrt_sqrt x') at 1 by lra.
  unfold Rdiv; rewrite Rmult_assoc; apply Rmult_le_compat_l;[lra | ].
  apply Rmult_le_reg_r with y'; [lra | ].
  rewrite Rmult_assoc, Rinv_l, Rmult_1_r;lra.
replace (sqrt x' * sqrt x' / y')%R with
  (sqrt x' - e + e ^ 2 / (sqrt x' * (1 + e / sqrt x')))%R; cycle 1.
  unfold e; field; lra.
assert (ygt1 : (1 < y')%R) by lra.
assert (yn0 : y' <> 0%R) by lra.
assert (tmp := body_exp_value (Build_pos_float x finx x0)(Build_pos_float y finy y0)
                 intx' (conj ygt1 (proj2 inty'))).
  simpl pos_float_val in tmp; fold x' y' in tmp; rewrite tmp; clear tmp.
assert (boundxy1 : (x' / y' < sqrt x' / 2)%R).
  unfold Rdiv; apply Rmult_lt_reg_r with y';[lra | ]. 
  rewrite Rmult_assoc, Rinv_l, Rmult_1_r;[ | lra].
  rewrite <- (sqrt_sqrt x') at 1;[ | lra].
  rewrite Rmult_assoc; apply Rmult_lt_compat_l; lra.
assert (tm1 := body_exp_div_x_y_bounds1
       (Build_pos_float x finx x0)
       (Build_pos_float y finy y0) (proj1 intx') (conj ygt1 (proj2 inty'))).
 simpl pos_float_val in tm1; fold x' y' in tm1.
assert (tmp := @error_le_ulp radix2 f32_exp
        (@FLT_exp_valid (3 - 128 - 24) 24 eq_refl)
        (round_mode mode_NE) (valid_rnd_round_mode _) (x' / y')).
apply Rabs_le_inv in tmp.
assert (tm2 := float32_bound_ulp _ (proj1 tm1)).
assert (roundy : round' y' = y') by apply round_B2R'.
split.
  assert (1 <= round' (x' / y'))%R.
    rewrite <- round'1; apply round_le'; lra.
  assert (y' <= round' (y' + round' (x' / y')))%R.
    rewrite <- roundy at 1; apply round_le'; lra.
  apply round_le'; lra.
change (round radix2 f32_exp (round_mode mode_NE) (x' / y')) with
           (round' (x' / y')) in tmp.
assert (boundxy : (round' (x' / y') < 9 / 32 * y')%R).
  apply Rle_lt_trans with (x' / y' + ulp radix2 f32_exp (x' / y'))%R.
    lra.  
  apply Rlt_le_trans with ((x' / y') + /32 * (x' / y'))%R.
    apply Rplus_lt_compat_l, Rlt_trans with (1 := proj2 tm2). 
    unfold Rdiv; rewrite Rmult_comm; apply Rmult_lt_compat_r;[lra | ].
    compute; lra.
  lra.
    assert (1 <= round' (x' / y'))%R.
      now rewrite <- round'1; apply round_le'; lra.
assert (tm3 : (2 <= y' + round' (x' / y'))%R) by lra.
assert (tm3' : (1 <= y' + round' (x' / y'))%R) by lra.
assert (tm4 := float32_bound_ulp _ tm3').
assert (tm5 :=  @error_le_ulp radix2 f32_exp
        (@FLT_exp_valid (3 - 128 - 24) 24 eq_refl)
        (round_mode mode_NE) (valid_rnd_round_mode _)
        (y' + round' (x' / y'))).
apply Rabs_le_inv in tm5.
assert (boundsum : (round' (y' + round' (x' / y')) < 42 / 32 * y')%R).
  apply Rle_lt_trans with (y' + round' (x' / y') +
   ulp radix2 f32_exp (y' +  (round' (x' / y'))))%R.
    assert (tech : forall a b c : R, (a - b <= c)%R -> (a <= b + c)%R).
      now intros; lra.
    apply tech, Rle_trans with (1 := proj2 tm5); lra.
  assert (ulp radix2 f32_exp (y' + round' (x' / y')) < y' / 32)%R.
    assert (lt41 : (y' + round' (x' / y') < y' * (41/32))%R) by lra.
    apply Rlt_trans with (1 := proj2 tm4).
    apply Rmult_lt_reg_r with (bpow radix2 21);[apply bpow_gt_0 | ].
    unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r
       by (apply Rgt_not_eq, bpow_gt_0).
    apply Rlt_trans with (1 := lt41).
    rewrite Rmult_assoc; apply Rmult_lt_compat_l;[lra |].
    compute; lra.
  lra.
assert (tm6 : (2 <= round' (y' + round' (x' / y')))%R).
  rewrite <- round'2; apply round_le'; lra.
assert (tm6' : (1 <= round' (y' + round' (x' / y')) / 2)%R) by lra.
assert (tm7 := float32_bound_ulp _ tm6').
assert (tm8 :=  @error_le_ulp radix2 f32_exp
        (@FLT_exp_valid (3 - 128 - 24) 24 eq_refl)
        (round_mode mode_NE) (valid_rnd_round_mode _)
        (round' (y' + round' (x' / y')) / 2)).
apply Rabs_le_inv in tm8.
assert (ulp radix2 f32_exp (round' (y' + round' (x' / y')) / 2) < y' / 128)%R.
  apply Rlt_le_trans with (1 := proj2 tm7).
  assert (128 < bpow radix2 21)%R by now (compute; lra).
  unfold Rdiv; apply Rmult_le_reg_r with (bpow radix2 21).
    now apply bpow_gt_0.
  rewrite Rmult_assoc, Rinv_l, Rmult_1_r;[ |apply Rgt_not_eq, bpow_gt_0 ].
  apply Rmult_le_reg_r with 2%R;[lra | ].
  rewrite Rmult_assoc, Rinv_l, Rmult_1_r;[ | lra].
  apply Rlt_le, Rlt_le_trans with (1 := boundsum).
  rewrite Rmult_comm, !Rmult_assoc; apply Rmult_le_compat_l;[lra | ].
  lra.
change (round radix2 f32_exp (round_mode mode_NE) 
              ((round' (y' + round' (x' / y')) / 2))) with
           (round' ((round' (y' + round' (x' / y')) / 2))) in tm8.
lra.
Qed.

Definition body_exp_R x y :=
   round' (round' (y + round' (x / y)) / 2).

Lemma inv_add_error x : (1 + x <> 0)%R -> (/ (1 + x) = 1 - x + x ^ 2 /(1 + x))%R.
Proof. now intros; field.  Qed.

Lemma target_below_s x y :
  let x' := B2R 24 128 x in
  let y' := B2R 24 128 y in
  (sqrt x' - 8 * ulp1 <= y' <= sqrt x')%R ->
  (1 <= x' < 4)%R ->
  (y' <= body_exp_R x' y')%R ->
  (Rabs (body_exp_R x' y' - sqrt x') <= 6 * ulp1)%R.
Proof.
intros x' y' inty' intx' stop.
assert (st3 : (Rabs (body_exp_R x' y' - ((y' + (x' / y')) / 2)) <= 8 * ulp1)%R).
  admit.
Qed.

Lemma target_above_s x y :
  let x' := B2R 24 128 x in
  let y' := B2R 24 128 y in
  (y' <= x')%R ->
  (y' <= 2 * sqrt x')%R ->
  (1 <= x' < 4)%R ->
  (sqrt x' <= y')%R ->
  (y' <= body_exp_R x' y')%R ->
  (Rabs (body_exp_R x' y' - sqrt x') <= 6 * ulp1)%R.
Proof.
intros x' y' yx inty intx lowerbound stop.
assert (sge1 : (1 <= sqrt x')%R).
  rewrite <- sqrt_1; apply sqrt_le_1_alt; lra.
assert (yge1 : (1 <= y')%R).
  lra.
assert (sle2 : (sqrt x' < 2)%R).
  rewrite <- (sqrt_pow2 2); try lra.
  apply sqrt_lt_1_alt; lra.
assert (ulpbnd : ulp radix2 f32_exp (sqrt x') = ulp1).
  apply ulp_1_2; lra.
set (ulps := ulp radix2 f32_exp (sqrt x')).
assert (ulps1 : ulps = ulp1) by (apply ulp_1_2; lra).
assert (u4 : (ulps < /4)%R) by (rewrite ulps1; unfold ulp1; simpl bpow; lra).
assert (ulpgt0 : (0 < ulp1)%R).
  unfold ulp1; apply bpow_gt_0.
assert (yu : (sqrt x' - ulps <= y')%R).
  assert (tm1 :=  @error_le_ulp radix2 f32_exp
        (@FLT_exp_valid (3 - 128 - 24) 24 eq_refl)
        (round_mode mode_DN) (valid_rnd_round_mode _) (sqrt x')).
  apply Rabs_le_inv in tm1; lra.
assert (rh : (round' (/2) = /2)%R). (* TODO remove duplication *)
  apply round_generic; try typeclasses eauto.
  replace (/2)%R with (bpow radix2 (-1)) by (compute; lra).
  apply generic_format_bpow'. (* TODO make type classes work for Valid *)
    apply FLT_exp_valid; reflexivity.
  apply Z.lt_le_incl; reflexivity.
assert (tm1 :=  @error_le_ulp radix2 f32_exp
        (@FLT_exp_valid (3 - 128 - 24) 24 eq_refl)
        (round_mode mode_NE) (valid_rnd_round_mode _)
        (x' / y')).
apply Rabs_le_inv in tm1.
assert (tm2 :=  @error_le_ulp radix2 f32_exp
        (@FLT_exp_valid (3 - 128 - 24) 24 eq_refl)
        (round_mode mode_NE) (valid_rnd_round_mode _)
        (y' + round' (x' / y'))).
apply Rabs_le_inv in tm2.
assert (tm3 :=  @error_le_ulp radix2 f32_exp
        (@FLT_exp_valid (3 - 128 - 24) 24 eq_refl)
        (round_mode mode_NE) (valid_rnd_round_mode _)
        (round' (y' + round' (x' / y')) / 2)).
apply Rabs_le_inv in tm3.
assert (rdivge1 : (1 <= round' (x' / y'))%R).
  rewrite <- round'1; apply round_le', Rmult_le_reg_r with y';[lra |].
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r; lra.
assert (x' / y' <= 4)%R.
  apply Rmult_le_reg_r with y';[lra | ].
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r; lra.
assert (x' / y' <= sqrt x')%R.
  apply Rmult_le_reg_r with y';[lra | ].
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
  rewrite <- (sqrt_sqrt x') at 1 by lra.
  apply Rmult_le_compat_l; lra.
assert (round' (x' / y') <= 2)%R.
  rewrite <- round'2; apply round_le'.
  apply Rle_trans with (sqrt x');[lra | apply Rlt_le; assumption].
assert (qge1 : (1 <= (x' / y'))%R).
   apply Rmult_le_reg_r with y';[lra |].
    unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r; lra.
assert (ulpdiv : (0 <= ulp radix2 f32_exp (x' / y') <= ulps)%R).
  split.
    now apply ulp_ge_0.
  apply ulp_le.
      now apply FLT_exp_valid.
    now apply FLT_exp_monotone.
  rewrite !Rabs_pos_eq; lra.
assert (ulpsum : (ulp radix2 f32_exp (y' + round' (x' / y')) <= 4 * ulps)%R).
  rewrite ulp_neq_0; try lra.
  destruct (Rle_lt_dec 4 (y' + round' (x' / y'))).
    rewrite (canonic_exp_32 3); try (simpl bpow; lra); try lia.
    rewrite ulps1; unfold ulp1; simpl bpow; lra.
  rewrite (canonic_exp_32 2); try (simpl bpow; lra); try lia.
  rewrite ulps1; unfold ulp1; simpl bpow; lra.

destruct (Rle_lt_dec (sqrt x' + 16 * ulps) y').
  enough (body_exp_R x' y' < y')%R by lra.
  assert (round' (x' / y') <= sqrt x' + ulps)%R.
    apply Rle_trans with (x' / y' + ulp radix2 f32_exp (x' / y'))%R.
      lra.    
    apply Rplus_le_compat;[lra | ].
    apply ulp_le_pos;[now apply FLT_exp_valid | typeclasses eauto | lra| lra].
  assert (sums : (y' + round' (x' / y') <= y' + sqrt x' + ulps)%R) by lra.
  assert (round' (y' + round' (x' / y')) <= y' + sqrt x' + 5 * ulps)%R.
    assert (1 <= round' (x' / y'))%R.
      rewrite <- round'1; apply round_le', Rmult_le_reg_r with y';[lra |].
    unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r; lra.
    clear - ulpsum tm2 sums; lra.
  assert (rsumub : (round' (y' + round' (x' / y')) / 2 <
                 (y' + sqrt x') / 2 + 3 * ulps)%R) by lra.
  assert(final: (round' (round' (y' + round' (x' / y')) / 2) < 
                      (y' + sqrt x') / 2 + 7 * ulps)%R).
  assert (ulp radix2 f32_exp (round' (y' + round' (x' / y')) / 2) <=
            4 * ulps)%R;[ | lra].
    rewrite ulp_neq_0; cycle 1. (* TODO : here lra loops. *)
      clear - ulpsum tm2 rdivge1 yge1 u4; lra.
    destruct (Rle_lt_dec 2 (round' (y' + round' (x' / y')) / 2)).
      rewrite (canonic_exp_32 2); try lia.
        rewrite ulps1; unfold ulp1; simpl bpow; clear; lra.
      simpl bpow; split;[| clear -rsumub yx intx u4 ulps1 sle2]; lra.
    destruct (Rle_lt_dec 1 (round' (y' + round' (x' / y')) / 2)).
      rewrite (canonic_exp_32 1); try lia. (* TODO here lra loops. *)
        rewrite ulps1; unfold ulp1; simpl bpow; lra.
      split;simpl bpow; assumption.
    rewrite (canonic_exp_32 0); try lia.
      clear -ulps1 ; rewrite ulps1; unfold ulp1; simpl bpow; lra.
    split; simpl bpow;[clear -tm2 yge1 rdivge1 ulpsum u4; lra| assumption].
  unfold body_exp_R; clear u4.
  assert (usmall : (ulps < /256)%R).
    rewrite ulps1; unfold ulp1; simpl bpow; lra.
  apply Rlt_le_trans with (1 := final); lra.
set (e := (y' - sqrt x')%R).
set (e' := (e / sqrt x')%R).
assert (sumlb : (2 <= round' (y' + round' (x' / y')))%R).
  rewrite <- round'2.
  apply round_le'; lra.
assert (lastround: 
   (ulp radix2 f32_exp (round' (y' + round' (x' / y')) / 2) <= 2 * ulps)%R).
  rewrite ulp_neq_0; try lra.
  destruct (Rle_lt_dec 2 (round' (y' + round' (x' / y')) / 2)).
    rewrite (canonic_exp_32 2); try lia.
      rewrite ulps1; unfold ulp1; simpl bpow; clear; lra.
    simpl bpow; lra.
  rewrite (canonic_exp_32 1); try lia.
    rewrite ulps1; unfold ulp1; simpl bpow; lra.
  simpl bpow; split; [ clear - sumlb; lra |lra].
move tm1 after lastround.
move tm2 after lastround.
move tm3 after lastround.
assert (eb : (e < 16 * ulps)%R) by (unfold e; lra).
(* step : body_exp x' y' - round' (y' + round' (x' / y')) / 2 *)
assert (st1 : (-2 * ulps <=
        body_exp_R x' y' - round' (y' + round' (x' / y')) / 2 <= 2 * ulps)%R).
  unfold body_exp_R; lra.
clear tm3 lastround.
(* step : body_exp x' y' - (y' + round' (x' / y')) / 2 *)
assert (st2 : (-4 * ulps <=
          body_exp_R x' y' - (y' + round' (x' / y')) / 2 <= 4 * ulps)%R).
  clear - st1 ulpsum tm2; lra.
  clear ulpsum tm2.
(* step : body_exp x' y' - (y' + (x' / y') / 2 *)
assert (st3 : (-5 * ulps <=
                body_exp_R x' y' - (y' + x' / y') / 2 <=
                5 * ulps)%R).
   clear - st2 ulpdiv tm1; lra.
assert (expand : (x' / y' = sqrt x' - e + e ^ 2 / y')%R).
  unfold e', e; rewrite <- (sqrt_sqrt x') at 1 by lra.
  field; lra.
assert (expand2 :
         ((y' + x' / y') / 2 - sqrt x' = e ^ 2 / (2 * y'))%R).
  rewrite expand; unfold e; field; lra.
assert (math : (0 <= (y' + x' / y') / 2 - sqrt x' < ulps)%R).
  rewrite expand2; split.
    apply Rmult_le_pos;[apply pow2_ge_0 | ].
    apply Rlt_le, Rinv_0_lt_compat; lra.
  apply Rle_lt_trans with (e ^ 2)%R.
    apply Rmult_le_reg_r with (2 * y')%R;[lra | ].
    unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
    rewrite <- (Rmult_1_r (e ^ 2)) at 1.
    apply Rmult_le_compat_l;[apply pow2_ge_0 | lra].
  assert (ep : (0 <= e)%R) by (unfold e; lra).
  apply Rlt_trans with ((16 * ulps) ^ 2)%R.
     simpl; apply Rmult_lt_compat; lra.
  rewrite ulps1; unfold ulp1; simpl bpow; lra.
apply Rabs_le.
lra.
Qed.

Lemma body_exp_decrease2 x y :
  let x' := B2R 24 128 (pos_float_val x) in
  let y' := B2R 24 128 (pos_float_val y) in
  (1 < x' < B2R 24 128 predf32max)%R ->
  (y' <= 2 * sqrt x')%R ->
  (round' (sqrt x') <=
      B2R 24 128 (body_exp (pos_float_val x) (pos_float_val y)) < 2 / 3 * y')%R.


Lemma fsqrt_loop_terminates : forall x y,
  Float32.cmp Clt (body_exp (pos_float_val x) (pos_float_val y)) 
    (pos_float_val y)= true ->
  (float_to_nat (body_exp (pos_float_val x) (pos_float_val y)) <
    float_to_nat (pos_float_val y))%nat.
Proof.
intros [x finx x0] [y finy y0]; simpl.

Lemma fsqrt_terminates: forall x y,
 Float32.cmp Clt (body_exp x y) y = true ->
 (fsqrt_terminate (body_exp x y) < fsqrt_terminate y)%nat.
Proof.

Admitted.

Function fsqrt_loop (xy : float32*float32) {measure fsqrt_terminate xy} :
       float32 :=
 let '(x,y) := xy in
 let z' := y in
 let y' :=  Float32.div (Float32.add z' (Float32.div x z'))
                         (Float32.of_int (Int.repr 2)) in
 if Float32.cmp Clt y' z'
 then fsqrt_loop (x,y')
 else y'.
Proof.
intros.
subst.
apply fsqrt_terminates; auto.
Defined.

Definition fsqrt (x: float32) : float32 :=
  if Float32.cmp Cle x (Float32.of_int (Int.repr 0)) 
  then (Float32.of_int (Int.repr 0)) 
  else
  let y := if Float32.cmp Cge x (Float32.of_int (Int.repr 1))
               then x else Float32.of_int (Int.repr 1)  in
  fsqrt_loop (x,y).

Lemma fsqrt_result_aux: 
  forall x y: float32,
Float32.cmp Cgt x Float32.zero = true ->
Float32.cmp Cge y (Float32.of_int (Int.repr 1)) = true ->
Float32.cmp Cge y x = true ->
Float32.cmp Ceq (Float32.mul (fsqrt_loop (x, y)) (fsqrt_loop (x, y))) x =
true.
Admitted.

Lemma fsqrt_result:
  forall x, 
  Float32.cmp Cge x (Float32.of_int (Int.repr 0)) = true ->
  Float32.cmp Ceq (Float32.mul (fsqrt x) (fsqrt x)) x = true.
Proof.
intros.
unfold fsqrt.
rewrite Float32.cmp_ge_gt_eq, orb_true_iff in H. 
destruct H.
2:{ 
rewrite Float32.cmp_le_lt_eq.
rewrite H.
rewrite orb_true_r.
change (Float32.mul (Float32.of_int (Int.repr 0)) (Float32.of_int (Int.repr 0)))
  with (Float32.of_int (Int.repr 0)).
rewrite <- Float32.cmp_swap. auto.
}
rewrite Float32.cmp_le_lt_eq.
destruct (Float32.cmp Clt x (Float32.of_int (Int.repr 0))) eqn:?H.
contradiction (Float32.cmp_lt_gt_false _ _ H0 H).
simpl.
destruct (Float32.cmp Ceq x (Float32.of_int (Int.repr 0))) eqn:?H.
contradiction (Float32.cmp_gt_eq_false _ _ H H1).
clear H0 H1.
set (y := if Float32.cmp Cge x (Float32.of_int (Int.repr 1))
        then x
        else Float32.of_int (Int.repr 1)).
assert (Float32.cmp Cge y (Float32.of_int (Int.repr 1)) = true).
subst y.
destruct (Float32.cmp Cge x (Float32.of_int (Int.repr 1))) eqn:?H.
auto.
reflexivity.
assert (Float32.cmp Cge y x = true). {
 subst y.
destruct (Float32.cmp Cge x (Float32.of_int (Int.repr 1))) eqn:?H.
-
rewrite Float32.cmp_ge_gt_eq.
rewrite orb_true_iff. right.
clear - H.
Transparent Float32.cmp.
unfold Float32.cmp in *.
Opaque Float32.cmp.
simpl in *.
unfold Float32.compare in *.
change (Float32.of_int (Int.repr 0)) with (Fappli_IEEE.B754_zero 24 128 false) in H.
destruct x; simpl in H; try destruct s; inv  H; simpl.
reflexivity.
rewrite Z.compare_refl.
rewrite Pcompare_refl.
auto.
-
rewrite Float32.cmp_ge_gt_eq.
rewrite Float32.cmp_ge_gt_eq in H1. rewrite orb_false_iff in H1.
destruct H1.
rewrite <- Float32.cmp_swap in H2. simpl in H2.
rewrite H2.
rewrite orb_false_r.
clear - H1 H2 H.
change (Float32.of_int (Int.repr 0)) with (Fappli_IEEE.B754_zero 24 128 false) in H.
destruct x; try destruct s; inv H; auto.
change (Float32.of_int (Int.repr 1)) 
  with (Fappli_IEEE.B754_finite 24 128 false 8388608 (-23)
         (proj1
            (Fappli_IEEE.binary_round_correct 24 128 eq_refl eq_refl
               Fappli_IEEE.mode_NE false 1 0))) in *.
set (p := proj1
             (Fappli_IEEE.binary_round_correct 24 128 eq_refl eq_refl
                Fappli_IEEE.mode_NE false 1 0)) in *. clearbody p.
Transparent Float32.cmp.
unfold Float32.cmp in *.
Opaque Float32.cmp.
unfold Float32.compare in *.
simpl.
destruct e; auto.
unfold cmp_of_comparison in *.
unfold Fappli_IEEE.Bcompare in *.
rewrite <- Pos.compare_antisym.
forget 8388608%positive as K.
change (Z.neg p0) with (- (Z.pos p0)) in *.
change (-23)%Z with (Z.opp 23) in H1,H2.
forget 23%positive as J.
rewrite Z.compare_opp in H2,H1.
simpl Z.compare in H1,H2.
rewrite Pos.compare_antisym in H1.
destruct (p0 ?= J)%positive eqn:?H.
simpl in H1,H2|-*.
rewrite <- (Pos.compare_cont_antisym _ _ Eq) in H1.
destruct (Pos.compare_cont Eq K m); auto.
simpl in H1.
inv H1.
auto.
}
clearbody y.
apply fsqrt_result_aux; auto.
Qed.

