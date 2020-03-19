From compcert Require Import Core Floats Defs Bits Binary.
Require Import Reals Psatz.
Require Import FunInd Recdef.

Open Scope Z_scope.

Definition float_to_nat (z: float32) : nat :=
  match z with
   | B754_zero _ => 2 ^ Z.to_nat 280
   | B754_infinity sign => if sign then 0 else 2 ^ Z.to_nat 600
   | B754_nan _ _ _ => O
   | B754_finite sign m e _ =>
     if sign then
        2 ^ Z.to_nat 280
        - Pos.to_nat m * 2 ^ Z.to_nat(e + 149)
     else
        2 ^ Z.to_nat 280
        + Pos.to_nat m * 2 ^ Z.to_nat(e + 149)
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

Lemma natpow_Zpow (x y : nat) : Z.of_nat (x ^ y) =
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

Lemma bounded_bound_exp m e : 
  Binary.bounded 24 128 m e = true -> -149 <= e <= 104.
Proof.
intros vc; unfold Binary.bounded in vc.
destruct (andb_prop _ _ vc) as [vc1 vc2].
apply (canonical_canonical_mantissa _ _ false) in vc1.
apply Zle_bool_imp_le in vc2.
split;[simpl in vc1 |- *; clear vc vc2 | exact vc2].
revert vc1.
unfold canonical, F2R, cexp; simpl; unfold FLT_exp.
destruct (mag radix2 (IZR (Z.pos m) * bpow radix2 e) - 24);
  intros v; rewrite v; apply Z.le_max_r.  
Qed.

Lemma bound_exp_float32 (z : float32) :
  -149 <= float_to_exp z <= 104.
Proof.
destruct z as [dummy | dummy | dum1 dum2 dum3 | sign m e vc];
  try (split; intros; discriminate).
now simpl; apply (bounded_bound_exp m).
Qed.

Lemma pow2_pos x : (0 < 2 ^ x)%nat.
Proof.  induction x as [ | x IH]; try (simpl; lia).  Qed.

Lemma Zto_nat_pow x y : 0 <= x -> 0 <= y -> (Z.to_nat (x ^ y)) = 
         (Z.to_nat x ^ Z.to_nat y)%nat.
Proof.
intros x0 y0.
pattern y; apply Zlt_0_ind;[clear y y0| exact y0].
intros y IH y0.
apply Zle_lt_or_eq in y0; destruct y0 as [ygt0 | yeq0].
  assert (0 <= (y - 1)) by lia.
  assert (y1 : y = y - 1 + 1) by ring.
  rewrite y1, Z.pow_add_r, Z.pow_1_r, Z2Nat.inj_mul; try lia.
    rewrite Z2Nat.inj_add; try lia.  
    rewrite Nat.pow_add_r.
    rewrite IH; try lia.
  replace (Z.to_nat 1) with 1%nat by reflexivity.
  rewrite Nat.pow_1_r; reflexivity.
now apply Z.pow_nonneg.
rewrite <- yeq0; reflexivity.
Qed.

Lemma bound_mantissa_digits m k :
  Z.pos (Digits.digits2_pos m) <= k ->
  (Pos.to_nat m < 2 ^ Z.to_nat k)%nat.
Proof.
intros nd.
assert (0 <= k).
  apply Z.le_trans with (2 := nd); lia.
rewrite Digits.Zpos_digits2_pos in nd.
replace (Pos.to_nat m) with (Z.to_nat (Z.pos m)) by reflexivity; try lia.
replace (2 ^ Z.to_nat k)%nat with (Z.to_nat (2 ^ k)) by ( apply Zto_nat_pow; lia).
  rewrite <- Z2Nat.inj_lt; try lia.
  apply (Digits.Zpower_gt_Zdigits radix2 k (Z.pos m)).
  lia.
now apply Z.pow_nonneg.
Qed.

Lemma lower_bound_mantissa_digits m :
  (2 ^ (Pos.to_nat (Digits.digits2_pos m) - 1) <= Pos.to_nat m)%nat.
Proof.
replace (Pos.to_nat m) with (Z.to_nat (Z.pos m)) by reflexivity.
replace (Pos.to_nat (Digits.digits2_pos m)) with
  (Z.to_nat (Z.pos (Digits.digits2_pos m))) by reflexivity.
replace 1%nat with (Z.to_nat 1) at 2 by reflexivity.
rewrite <- Z2Nat.inj_sub;[ | lia].
replace (2 ^ Z.to_nat (Z.pos (Digits.digits2_pos m) - 1))%nat with
  (Z.to_nat (2 ^ (Z.pos (Digits.digits2_pos m) - 1)))
   by ( apply Zto_nat_pow; lia).
rewrite <- Z2Nat.inj_le;[ | apply Z.lt_le_incl, Z.pow_pos_nonneg; lia | lia].
rewrite Digits.Zpos_digits2_pos.
rewrite <- (Z.abs_eq (Z.pos m)) at 2;[ | lia].
apply (Digits.Zpower_le_Zdigits radix2); lia.
Qed.

Lemma bound_mantissa_nat m e :
  Binary.bounded 24 128 m e = true ->
  (Pos.to_nat m < 2 ^ 24)%nat.
Proof.
intros v.
apply (bound_mantissa_digits m 24); try lia.
unfold Binary.bounded in v.
unfold canonical_mantissa in v.
apply andb_prop in v; destruct v as [v _].
apply Zeq_bool_eq in v; unfold FLT_exp in v.
destruct (Z_le_gt_dec (3 - 128 - 24) (Z.pos (Digits.digits2_pos m) + e - 24))
      as [l | r].
  rewrite Z.max_l in v; [lia | assumption].
lia.
Qed.

Lemma lower_bound_mantissa_nat e m :
  -149 < e ->
  Binary.bounded 24 128 m e = true ->
  (2 ^ 23 <= Pos.to_nat m)%nat.
Proof.
intros elb v.
apply le_trans with (2 := lower_bound_mantissa_digits m).
unfold Binary.bounded in v.
unfold canonical_mantissa in v.
apply andb_prop in v; destruct v as [v _].
apply Zeq_bool_eq in v; unfold FLT_exp in v.
destruct (Z_le_gt_dec (3 - 128 - 24) (Z.pos (Digits.digits2_pos m) + e - 24))
      as [l | r].
  rewrite Z.max_l in v; [ | assumption].
  assert (vd : Z.pos (Digits.digits2_pos m) = 24) by lia.
  injection vd; intros vd'; rewrite vd'.
  now apply Nat.pow_le_mono_r.
lia.
Qed.

Lemma bound_float : forall x e, Binary.bounded 24 128 x e = true ->
              (Pos.to_nat x * 2 ^ Z.to_nat (e + 149) < 2 ^ Z.to_nat 280)%nat.
Proof.
intros x e v.
apply lt_trans with (2 ^ 24 * 2 ^ Z.to_nat (e + 149))%nat.
apply Nat.mul_lt_mono_pos_r.
    now apply pow2_pos.
  now apply (bound_mantissa_nat x e).
rewrite <- Nat.pow_add_r.
apply Nat.pow_lt_mono_r; try lia.
assert (tmp := bounded_bound_exp _ _ v); lia.
Qed.

Transparent Float32.cmp.

Lemma float_to_nat_Clt a b :
  Float32.cmp Integers.Clt a b = true ->
    (float_to_nat a < float_to_nat b)%nat.
Proof.
destruct a as [da | da | da1 da2 da3 | signa ma ea vca];
  destruct b as [db | db | db1 db2 db3 | signb mb eb vcb]; try
  discriminate.
- unfold Float32.cmp, Float32.compare, Bcompare, cmp_of_comparison, float_to_nat.
  case db;[discriminate | intros _; apply Nat.pow_lt_mono_r; lia].
- unfold Float32.cmp, Float32.compare, Bcompare, cmp_of_comparison, float_to_nat.
  case signb;[ discriminate | intros].
  apply Nat.le_lt_trans with (2 ^ Z.to_nat 280 + 0)%nat.
    now rewrite Nat.add_0_r; apply le_n.
  apply Nat.add_lt_mono_l, Nat.mul_pos_pos.
    now apply Pos2Nat.is_pos.  
  now apply pow2_pos.
- unfold Float32.cmp, Float32.compare, Bcompare, cmp_of_comparison, float_to_nat.
  case da; [now intros; apply pow2_pos | discriminate ].
- unfold Float32.cmp, Float32.compare, Bcompare, cmp_of_comparison, float_to_nat.
  now case da; case db; try discriminate; intros; apply pow2_pos.
- unfold Float32.cmp, Float32.compare, Bcompare, cmp_of_comparison, float_to_nat.
  case da;[intros | discriminate].
  case signb.
    apply lt_minus_O_lt.
    now apply bound_float.
  apply Nat.add_pos_r.
  apply Nat.mul_pos; split;[lia | apply pow2_pos].
- unfold Float32.cmp, Float32.compare, Bcompare, cmp_of_comparison, float_to_nat.
  case signa;[ intros | discriminate].
  assert (tech : forall a b, (0 < a -> 0 < b -> a - b < a)%nat).
    intros a b a0 b0; destruct a as [ | a]; destruct b as [ | b]; lia.
  apply tech;[| apply Nat.mul_pos; split;[lia |]]; apply pow2_pos.
- unfold Float32.cmp, Float32.compare, Bcompare, cmp_of_comparison, float_to_nat.
  case db;[discriminate | intros _].
  case signa.
    apply lt_trans with (2 ^ Z.to_nat 280)%nat.
  assert (tech : forall a b, (0 < a -> 0 < b -> a - b < a)%nat).
    intros a b a0 b0; destruct a as [ | a]; destruct b as [ | b]; lia.
  apply tech;[| apply Nat.mul_pos; split;[lia |]]; apply pow2_pos.
  apply Nat.pow_lt_mono_r; lia.  
  apply lt_trans with (2 ^ Z.to_nat 280 + 2 ^ Z.to_nat 280)%nat.
    apply Nat.add_lt_mono_l.
    now apply bound_float.
  assert (tech : forall x, (x + x = 2 ^ 1 * x)%nat) by (intros; simpl; ring).
  rewrite tech, <- Nat.pow_add_r; apply Nat.pow_lt_mono_r; lia.
- unfold Float32.cmp, Float32.compare, Bcompare, cmp_of_comparison, float_to_nat.
  case signa; case signb; try discriminate.
  * assert (tech : (forall a b c, b <= a -> c <= a -> c < b -> a - b < a - c)%nat).
      intros a b c ba ca cb; lia.
    destruct (ea ?= eb) eqn:eaeb; try discriminate.
     destruct (CompOpp (Pos.compare_cont Eq ma mb)) eqn:mamb; try discriminate.
     destruct (Pos.compare_cont Eq ma mb) eqn: mamb'; try discriminate.
     apply nat_of_P_gt_Gt_compare_morphism in mamb'.
     intros _; apply tech.
         now apply Nat.lt_le_incl, bound_float.
       now apply Nat.lt_le_incl, bound_float.
     rewrite (Z.compare_eq _ _ eaeb).
     rewrite <- Nat.mul_lt_mono_pos_r;[lia | apply pow2_pos].
    intros _; apply tech.
        now apply Nat.lt_le_incl, bound_float.
      now apply Nat.lt_le_incl, bound_float.
    rewrite Z.compare_gt_iff in eaeb.
    replace ea with (ea - eb + eb) by ring.
    assert (ebb := bounded_bound_exp _ _ vcb).
    rewrite <- Z.add_assoc, (Z2Nat.inj_add (ea - eb)), Nat.pow_add_r; try lia.
    rewrite Nat.mul_assoc; apply Nat.mul_lt_mono_pos_r; try apply pow2_pos.
    apply Nat.lt_le_trans with (1 := bound_mantissa_nat _ _ vcb).
    apply Nat.le_trans with ((2 ^ 23) * 2 ^ Z.to_nat (ea - eb))%nat; cycle 1.
      apply Nat.mul_le_mono_pos_r;[now apply pow2_pos | ].
      apply (lower_bound_mantissa_nat ea);[lia | assumption].
    replace (ea - eb) with (1 + (ea - eb -1)) by ring.
    rewrite Nat.pow_succ_r', Nat.mul_comm.
    apply Nat.mul_le_mono_l; rewrite Z2Nat.inj_add;[ | lia | lia].
    rewrite Nat.pow_add_r.
    replace 2%nat with (2 * 1)%nat at 1 by ring.
    now apply Nat.mul_le_mono_l, pow2_pos.
  * intros _.
    apply bound_float in vca; apply bound_float in vcb.
    enough (0 < Pos.to_nat mb * 2 ^ Z.to_nat (eb + 149) /\
            0 < Pos.to_nat ma * 2 ^ Z.to_nat (ea + 149))%nat by lia.
    split; apply Nat.mul_pos_pos; try apply pow2_pos; lia.
  * destruct (ea ?= eb) eqn:eaeb; try discriminate.
     destruct (Pos.compare_cont Eq ma mb) eqn:mamb; try discriminate.
     apply nat_of_P_lt_Lt_compare_morphism in mamb.
     intros _; apply Nat.add_lt_mono_l.
     rewrite (Z.compare_eq _ _ eaeb).
     rewrite <- Nat.mul_lt_mono_pos_r;[lia | apply pow2_pos].
    intros _; apply Nat.add_lt_mono_l.
    rewrite Z.compare_lt_iff in eaeb.
    replace eb with (eb - ea + ea) by ring.
    assert (eba := bounded_bound_exp _ _ vca).
    rewrite <- Z.add_assoc, (Z2Nat.inj_add (eb - ea)), Nat.pow_add_r; try lia.
    rewrite Nat.mul_assoc; apply Nat.mul_lt_mono_pos_r; try apply pow2_pos.
    apply Nat.lt_le_trans with (1 := bound_mantissa_nat _ _ vca).
    apply Nat.le_trans with ((2 ^ 23) * 2 ^ Z.to_nat (eb - ea))%nat; cycle 1.
      apply Nat.mul_le_mono_pos_r;[now apply pow2_pos | ].
      apply (lower_bound_mantissa_nat eb);[lia | assumption].
    replace (eb - ea) with (1 + (eb - ea -1)) by ring.
    rewrite Nat.pow_succ_r', Nat.mul_comm.
    apply Nat.mul_le_mono_l; rewrite Z2Nat.inj_add;[ | lia | lia].
    rewrite Nat.pow_add_r.
    replace 2%nat with (2 * 1)%nat at 1 by ring.
    now apply Nat.mul_le_mono_l, pow2_pos.
Qed.

Lemma Float32cmp_correct x y :
  is_finite 24 128 x = true ->
  is_finite 24 128 y = true ->
  Float32.cmp Integers.Clt x y = true ->
  (B2R 24 128 x < B2R 24 128 y)%R.
Proof.
intros finx finy; unfold Float32.cmp, Float32.compare.
rewrite Bcompare_correct; auto.
destruct (Rcompare (B2R 24 128 x) (B2R 24 128 y)) eqn:test; simpl; try discriminate.
now apply Rcompare_Lt_inv in test.
Qed.

Opaque Float32.cmp.

Definition main_loop_measure (p : float32 * float32) : nat :=
  float_to_nat (snd p).

Definition body_exp x y :=
  Float32.div (Float32.add y (Float32.div x y))
     (Float32.of_int (Integers.Int.repr 2)).


(* The beauty of it is that we don't need to know what computation is performed,
  only the test matters. *)
Function main_loop (p : float32 * float32) {measure main_loop_measure} :
   float32 :=
  match p with
  | (x, y) =>
    if Float32.cmp Integers.Clt (body_exp x y) y then
       main_loop (x, body_exp x y)
    else
      body_exp x y
  end.
Proof.
now intros p x y eqxy; apply float_to_nat_Clt.
Qed.

Section main_loop_reasoning.

(* This section is useless, as main_loop_prop has the same statement
  as main_loop_ind.  It is here to make the next reasoning steps more
  easily visible. *)
Variable invariant : float32 * float32 -> Prop.

Hypothesis invariant_spec :
  forall x y,  Float32.cmp Integers.Clt (body_exp x y) y = true ->
              invariant (x, y) ->
             invariant (x, body_exp x y).

Variable final : float32 -> Prop.

Hypothesis invariant_final :
  forall x y, invariant (x, y) ->
     Float32.cmp Integers.Clt (body_exp x y) y = false ->
     final (body_exp x y).

Lemma main_loop_prop x y :
  invariant (x, y) -> final (main_loop (x, y)).
Proof.
apply main_loop_ind; clear x y.
  now intros p x y pxy test IH v; apply IH, invariant_spec.
now intros p x y pxy test v; apply invariant_final.
Qed.

End main_loop_reasoning.

(* The invariant we wish to establish is that:

 1/  x and y finite floats
 2/  round (sqrt x) (1 -  2 ^ -19) <= y <= x
*)

(* the final property is that | y - sqrt x | < 3 * 2 ^-24 * sqrt x *)

(* when 1 < x, we assume (body_exp x y) <= y
       (as tested by Float32.cmp, with roundings included.)

   if 2 * sqrt x < y < x, then y <= (body_exp x y) is not contradicted

   if 2 * sqrt x < y < x, then we can scale the problem by dividing
   2 ^ (2 * p) and y by 2 ^ p,
     where p is such that (2 ^ (2 * (p - 1)) <= x < 2 ^ (2 * p)

   Then we can suppose that 1 <= y <= 2 and 1 <= x <= 4

   In this range, we show that if 2 ^ -19 < | y - sqrt x |, then
    y <= body_exp x y is contradicted

   Finally, if |y - sqrt x | <= 2 ^ -19 is satisfied, then
     |body_exp x y|  < 3 * 2 ^ -24 (this case is proved automatically by
   gappa. *)

Transparent Float32.div.
Transparent Float32.add.
Transparent Float32.mul.
Transparent Float32.of_int.
Transparent Integers.Int.repr.

Definition f32_exp := FLT_exp (3 - 128 -24) 24.

Notation round' := (round radix2 f32_exp (round_mode mode_NE)).

Lemma round1 m: round radix2 f32_exp (round_mode m) 1 = 1%R.
Proof.
assert (for1 : generic_format radix2 f32_exp 1).
  replace 1%R with (F2R (Float radix2 (cond_Zopp false (2 ^ 23)) (-23))).
    now apply generic_format_canonical, canonical_canonical_mantissa.
  compute; lra.
now apply round_generic; auto; apply valid_rnd_round_mode.
Qed.

Lemma round'1 : round' 1 = 1%R.
Proof. now apply round1. Qed.

Lemma round'2 : round' 2 = 2%R.
Proof.
assert (for2 : generic_format radix2 (FLT_exp (3 - 128 - 24) 24) 2).
  replace 2%R with (F2R (Float radix2 (cond_Zopp false (2 ^ 23)) (-22))).
    now apply generic_format_canonical, canonical_canonical_mantissa.
  compute; lra.
now apply round_generic; auto; apply valid_rnd_round_mode.
Qed.

Lemma round'4 : round' 4 = 4%R.
Proof.
assert (for2 : generic_format radix2 (FLT_exp (3 - 128 - 24) 24) 4).
  replace 4%R with (F2R (Float radix2 (cond_Zopp false (2 ^ 23)) (-21))).
    now apply generic_format_canonical, canonical_canonical_mantissa.
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
  Binary.bounded 24 128 (2 ^ 23) exp = true.
Proof.
intros cnd1; unfold Binary.bounded.
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
  (1 <= B2R 24 128 x)%R ->
  (1 <= B2R 24 128 y <= B2R 24 128 x)%R ->
  (1 <= B2R 24 128 x / B2R 24 128 y
     <= B2R 24 128 x)%R.
Proof.
set (x' := B2R 24 128 x); set (y':= B2R 24 128 y).
intros intx inty.
assert (ygt0 : y' <> 0%R) by lra.
split.
  apply Rmult_le_reg_r with y';[lra | ].
  now unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_l, Rmult_1_r; lra.
apply Rmult_le_reg_r with y';[lra | ].
unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r; [ nra | lra].
Qed.

Lemma body_exp_div_x_y_bounds x y :
  (1 <= B2R 24 128 x)%R ->
  (1 <= B2R 24 128 y <= B2R 24 128 x)%R ->
  (1 <= round' (B2R 24 128 x / B2R 24 128 y)
     <= B2R 24 128 x)%R.
Proof.
set (x' := B2R 24 128 x); set (y':= B2R 24 128 y).
intros intx inty.
assert (ygt0 : y' <> 0%R) by lra.
assert (divint : (1 <= x' / y' <= x')%R).
  now apply body_exp_div_x_y_bounds1.
split.
  rewrite <- round'1; apply round_le'; tauto.
unfold x' at 2; rewrite <- round_B2R'; fold x'.
apply round_le'; tauto.
Qed.

Lemma body_exp_sum_bounds x y :
  (1 <= B2R 24 128 x <  B2R 24 128 predf32max)%R ->
  (1 <= B2R 24 128 y <= B2R 24 128 x)%R ->
  (2 <= round' (B2R 24 128 y +
          round' (B2R 24 128 x / B2R 24 128 y))
     <= B2R 24 128 f32max)%R.
Proof.
set (x' := B2R 24 128 x); set (y':= B2R 24 128 y).
intros intx inty.
assert ((1 <= round' (x' / y') <= x')%R).
  now apply body_exp_div_x_y_bounds.
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

Definition body_exp_R x y :=
   round' (round' (y + round' (x / y)) / 2).

Lemma body_exp_bounds x y :
  (1 <= B2R 24 128 x < B2R 24 128 predf32max)%R ->
  (1 <= B2R 24 128 y <= B2R 24 128 x)%R ->
  (1 <= body_exp_R (B2R 24 128 x) (B2R 24 128 y) <= B2R 24 128 f32max)%R.
Proof.
set (x' := B2R 24 128 x); set (y':= B2R 24 128 y).
intros intx inty.
assert ((2 <= round' (y' + round' (x' / y')) <= B2R 24 128 f32max)%R).
  now apply body_exp_sum_bounds.
unfold body_exp_R.
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
apply Rle_lt_trans with (ulp radix2 f32_exp (bpow radix2 (mag radix2 x))).
  apply ulp_le_pos.
        now apply fexp_correct.
      now apply FLT_exp_monotone.
  lra.
  destruct (mag radix2 x) as [v vbeta].
  simpl; replace x with (Rabs x) by now rewrite Rabs_pos_eq; lra.
  now assert (vbeta' :=  vbeta xn0); lra.
rewrite ulp_bpow.
destruct (mag radix2 x) as [v vbeta].
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

Lemma cexp_bpow : forall x e, x <> 0%R ->
  -149 < cexp radix2 f32_exp x ->
  -149 < e + cexp radix2 f32_exp x ->
  cexp radix2 f32_exp (x * bpow radix2 e)%R = cexp radix2 f32_exp x + e.
Proof.
intros x e xn0 xbnds ebnds.
revert xbnds ebnds.
unfold cexp, f32_exp, FLT_exp.
rewrite mag_mult_bpow; auto.
destruct (Z_le_gt_dec (3 - 128 - 24) (mag radix2 x - 24)).
  rewrite Z.max_l; lia.
rewrite Z.max_r; lia.
Qed.

Lemma Zdigits_cond_Zopp r b z :
  Digits.Zdigits r (cond_Zopp b z) = Digits.Zdigits r z.
Proof.
now case b; simpl; unfold Digits.Zdigits; destruct z.
Qed.

Lemma bound_mag_float32 x :
  is_finite_strict 24 128 x = true ->
  (- 149 <= mag radix2 (B2R 24 128 x) <= 128).
Proof.
destruct x as [ | | | s m e p]; try discriminate; intros _.
revert p; unfold Binary.bounded; simpl; rewrite Bool.andb_true_iff.
unfold canonical_mantissa, FLT_exp; intros [p1 p2].
apply Zle_bool_imp_le in p2.
apply Zeq_bool_eq in p1.
rewrite mag_F2R_Zdigits;[ | case s; simpl; lia].
rewrite Digits.Zpos_digits2_pos in p1.
rewrite Zdigits_cond_Zopp.
destruct (Z_le_dec (Digits.Zdigits radix2 (Z.pos m) + e - 24) (3 - 128 - 24))
  as [l | r].
  rewrite Z.max_r in p1 by assumption.
  compute in p1.
  assert (d0 := Digits.Zdigits_ge_0 radix2 (Z.pos m)); lia.
rewrite Z.max_l in p1; lia.
Qed.

Lemma cexp_32 e r :
  -126 < e ->
  (bpow radix2 (e - 1) <= r < bpow radix2 e)%R ->
  cexp radix2 f32_exp r = e - 24.
Proof.
intros ce inte.
unfold cexp, f32_exp, FLT_exp.
assert (r0 : (0 <= r)%R).
  assert (tmp := bpow_ge_0 radix2 (e - 1)); lra.
assert (vln : mag_val radix2 _ (mag radix2 r) = e).
  now  apply mag_unique; rewrite Rabs_pos_eq.
rewrite vln.
apply Z.max_l; lia.
Qed.

Lemma mantissa_bpow x e :
  x <> 0%R ->
  -149 < cexp radix2 f32_exp x ->
  -149 < e + cexp radix2 f32_exp x ->
  (scaled_mantissa radix2 f32_exp (x * bpow radix2 e) =
  scaled_mantissa radix2 f32_exp x)%R.
Proof.
unfold scaled_mantissa.
intros xn0 cndx cnde; rewrite cexp_bpow; auto.
rewrite !Rmult_assoc, <- !bpow_plus.
apply f_equal with (f := fun u => (x * bpow radix2 u)%R); ring.
Qed.

Lemma round_mult_bpow x e :
  (x <> 0)%R ->
  -149 < cexp radix2 f32_exp x ->
  -149 < e + cexp radix2 f32_exp x ->
  (round' (x * bpow radix2 e) = round' x * bpow radix2 e)%R.
Proof.
intros xn0 canx inte.
unfold round, F2R; simpl.
rewrite mantissa_bpow by tauto.
rewrite cexp_bpow by tauto.
now rewrite bpow_plus, Rmult_assoc.
Qed.

Lemma ulp_1_2 x : (1 <= x < 2)%R ->
   ulp radix2 f32_exp x = ulp1.
Proof.
intros intx.
rewrite ulp_neq_0; try lra.
rewrite (cexp_32 1); try (simpl bpow; lra); try lia.
reflexivity.
Qed.

Lemma cexp_m23 x :
  x <> 0%R ->
  cexp radix2 f32_exp x = -23 <->
  mag_val _ x (mag radix2 x) = 1.
Proof.
intros xn0.
split; unfold cexp, f32_exp; destruct (mag radix2 x) as [v vprop];
  simpl mag_val; unfold FLT_exp.
  destruct (Z_le_gt_dec (-149) (v - 24)) as [it | abs].
    rewrite Z.max_l; lia.
  rewrite Z.max_r; lia.
intros v1; rewrite v1, Z.max_l; lia.
Qed.

Lemma cexp_m22 x :
  x <> 0%R ->
  cexp radix2 f32_exp x = -22 <->
  mag_val _ x (mag radix2 x) = 2.
Proof.
intros xn0.
split; unfold cexp, f32_exp; destruct (mag radix2 x) as [v vprop];
  simpl mag_val; unfold FLT_exp.
  destruct (Z_le_gt_dec (-149) (v - 24)) as [it | abs].
    rewrite Z.max_l; lia.
  rewrite Z.max_r; lia.
intros v1; rewrite v1, Z.max_l; lia.
Qed.

Lemma cexp_m21 x :
  x <> 0%R ->
  cexp radix2 f32_exp x = -21 <->
  mag_val _ x (mag radix2 x) = 3.
Proof.
intros xn0.
split; unfold cexp, f32_exp; destruct (mag radix2 x) as [v vprop];
  simpl mag_val; unfold FLT_exp.
  destruct (Z_le_gt_dec (-149) (v - 24)) as [it | abs].
    rewrite Z.max_l; lia.
  rewrite Z.max_r; lia.
intros v1; rewrite v1, Z.max_l; lia.
Qed.

Lemma body_exp_finite_value x y :
  is_finite 24 128 x = true ->
  is_finite 24 128 y = true ->
  let x' := B2R 24 128 x in
  let y' := B2R 24 128 y in
  (1 <= x' < B2R 24 128 predf32max)%R ->
  (1 <= y' <= x')%R ->
  B2R 24 128 (body_exp x y) =
  body_exp_R x' y' /\ is_finite 24 128 (body_exp x y) = true.
Proof.
intros finx finy x' y'; unfold body_exp_R.
intros intx' inty'.
assert (yn0 : y' <> 0%R) by lra.
unfold body_exp, Float32.div.
assert (tmp := body_exp_bounds x
                                 y intx' inty').
assert (tm2 := body_exp_sum_bounds x
                                     y
                    intx' inty').
assert (tm3 := body_exp_div_x_y_bounds x
                                     y
                    (proj1 intx') inty').
unfold body_exp_R in tmp, tm2, tm3.
assert (tm4 := Bdiv_correct 24 128 eq_refl eq_refl Float32.binop_nan mode_NE x y yn0).
fold x' in tmp, tm2, tm3, tm4; fold y' in tmp, tm2, tm3, tm4.
assert (divlt : Rlt_bool (Rabs (round' (x' / y'))) (bpow radix2 128) = true).
  apply Rlt_bool_true.
  rewrite Rabs_pos_eq;[ | lra].
  now assert (tmp5:= conj boundpredf32max boundf32max); lra.
fold f32_exp in tm4.
rewrite divlt in tm4; destruct tm4 as [vdivxy [findivxy signdivxy]].
clear divlt.
unfold Float32.add.
set (divxy := Bdiv 24 128 eq_refl eq_refl Float32.binop_nan mode_NE x y).
fold divxy in signdivxy, findivxy, vdivxy.
set (divxy' := B2R _ _ divxy).
assert (findivxy' : is_finite 24 128 divxy = true).
  now rewrite findivxy, finx.
assert (tm6 := Bplus_correct 24 128 eq_refl eq_refl Float32.binop_nan mode_NE y
                     divxy finy findivxy').
assert (pluslt :
      Rlt_bool (Rabs (round' (y' + divxy'))) (bpow radix2 128) = true).
  apply Rlt_bool_true; unfold divxy'; rewrite vdivxy, Rabs_pos_eq.
    now assert (tmp5:= conj boundpredf32max boundf32max); lra.
  lra.
fold y' divxy' f32_exp in tm6; rewrite pluslt in tm6; clear pluslt.
destruct tm6 as [vsum [finsum signsum]].
assert (fin2 : is_finite 24 128 (Float32.of_int (Integers.Int.repr 2)) = true).
  reflexivity.
 assert (b2n0 : B2R 24 128 (Float32.of_int (Integers.Int.repr 2)) <> 0%R).
  now compute; lra.
assert (tm4 := Bdiv_correct 24 128 eq_refl eq_refl Float32.binop_nan mode_NE
                   (Bplus 24 128 eq_refl eq_refl Float32.binop_nan mode_NE y
          (Bdiv 24 128 eq_refl eq_refl Float32.binop_nan mode_NE x y))
                   _ b2n0).
  set (bexp :=   Bdiv 24 128 eq_refl eq_refl Float32.binop_nan mode_NE
              (Bplus 24 128 eq_refl eq_refl Float32.binop_nan mode_NE y
                 (Bdiv 24 128 eq_refl eq_refl Float32.binop_nan mode_NE x y))
              (Float32.of_int (Integers.Int.repr 2))).
fold bexp in tm4.
set (sum := (Bplus 24 128 eq_refl eq_refl Float32.binop_nan mode_NE y
                       divxy)).
fold divxy sum in vsum, finsum, signsum, tm4.
assert (explt : Rlt_bool (Rabs (round' (B2R 24 128 sum /
               B2R 24 128 (Float32.of_int (Integers.Int.repr 2)))))
              (bpow radix2 128) = true).
  apply Rlt_bool_true.
  replace (B2R 24 128 (Float32.of_int (Integers.Int.repr 2))) with 2%R
       by (now compute; lra).
   rewrite vsum; unfold divxy'; rewrite vdivxy.
  rewrite Rabs_pos_eq;[ | lra].
  now assert (tmp5:= conj boundpredf32max boundf32max); lra.
fold f32_exp in tm4.
rewrite explt in tm4; destruct tm4 as [vexp [finexp signexp]].
replace (B2R 24 128 (Float32.of_int (Integers.Int.repr 2))) with 2%R in vexp
       by now compute; lra.
unfold bexp in vexp; rewrite vsum in vexp; unfold divxy' in vexp.
rewrite vdivxy in vexp.
split;[ exact vexp | rewrite finsum in finexp;exact finexp].
Qed.

Lemma body_exp_value x y :
  is_finite 24 128 x = true ->
  is_finite 24 128 y = true ->
  let x' := B2R 24 128 x in
  let y' := B2R 24 128 y in
  (1 <= x' < B2R 24 128 predf32max)%R ->
  (1 <= y' <= x')%R ->
  B2R 24 128 (body_exp x y) =
  body_exp_R x' y'.
Proof.
now intros finx finy x' y' intx inty; apply body_exp_finite_value.
Qed.

Lemma body_exp_finite x y :
  is_finite 24 128 x = true ->
  is_finite 24 128 y = true ->
  let x' := B2R 24 128 x in
  let y' := B2R 24 128 y in
  (1 <= x' < B2R 24 128 predf32max)%R ->
  (1 <= y' <= x')%R ->
  is_finite 24 128 (body_exp x y) = true.
Proof.
now intros finx finy x' y' intx inty; apply body_exp_finite_value.
Qed.

Notation cexp' := (cexp radix2 f32_exp).

Lemma body_exp_value_scale x y e:
  let x' := B2R 24 128 x in
  let y' := B2R 24 128 y in
  (1 <= x' <= 4)%R ->
  (sqrt x' <= y' <= 2 * sqrt x')%R ->
  -125 < e ->
  -149 < (2 * e) + cexp radix2 f32_exp x' ->
  (round' (round' (y' + round' (x' / y')) / 2) * bpow radix2 e =
  round' (round' (y' * bpow radix2 e +
              round' ((x' * bpow radix2 (2 * e)) /
                      (y' * bpow radix2 e))) / 2))%R.
Proof.
intros x' y' intx inty elb inte.
assert (1 <= sqrt x')%R.
  rewrite <- sqrt_1.
  apply sqrt_le_1_alt; lra.
assert (yn0 : y' <> 0%R) by lra.
assert (bpgt0 : (0 < bpow radix2 e)%R) by apply bpow_gt_0.
assert (sqrtle : (sqrt x' <= x')%R).
  enough (1 * sqrt x' <= x')%R by lra.
  rewrite <- (sqrt_sqrt x') at 2 by lra.
  apply Rmult_le_compat_r; lra.
assert (sle2 : (sqrt x' <= 2)%R).
  rewrite <- (sqrt_pow2 2) by lra.
  apply sqrt_le_1_alt; lra.
assert (qgth : (/2 <= x' / y')%R).
  apply Rmult_le_reg_r with y';[lra | ].
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
assert (sumgt1 : (3/2 <= y' + round' (x' / y'))%R) by lra.
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
  replace (cexp radix2 f32_exp (F2R {|Fnum := 6; Fexp := 0|})) with
     (-21); cycle 1.
    unfold cexp; simpl.
    replace (mag_val radix2 _
                    (mag radix2 (F2R {|Fnum :=6; Fexp :=0|}))) with
    3.
      reflexivity.
    symmetry; apply mag_unique.
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
      rewrite (cexp_32 2);[lia | lia| simpl bpow; split; lra].
    rewrite (cexp_32 1);[lia | lia| simpl bpow; split; lra].
  rewrite (cexp_32 0);[lia | lia| simpl bpow; split; lra].
rewrite round_mult_bpow; try lra; try lia.
rewrite <- Rmult_plus_distr_r.
assert (-23 <= (cexp' (y' + round' (x' / y'))) <= -21).
  destruct (Rle_lt_dec 2 (y' + round' (x' / y'))).
    destruct (Rle_lt_dec 4 (y' + round' (x' / y'))).
      rewrite (cexp_32 3);[lia | lia| simpl bpow; split; lra].
    rewrite (cexp_32 2);[lia | lia| simpl bpow; split; lra].
  rewrite (cexp_32 1);[lia | lia| simpl bpow; split; lra].
rewrite sqrt_pow2 by lra.
rewrite round_mult_bpow; try lra; try lia.
assert (tech : forall a b, ((a * b) / 2 = (a / 2) * b)%R)
   by (intros; field; lra).
rewrite tech; clear tech.
assert (-24 <= (cexp' (round' (y' + round' (x' / y')) / 2)) <= -22).
  destruct (Rle_lt_dec 1 (round' (y' + round' (x' / y')) / 2)).
    destruct (Rle_lt_dec 2 (round' (y' + round' (x' / y')) / 2)).
      rewrite (cexp_32 2);[lia | lia| simpl bpow; split; lra].
    rewrite (cexp_32 1);[lia | lia| simpl bpow; split; lra].
  rewrite (cexp_32 0);[lia | lia| simpl bpow; split; lra].
rewrite round_mult_bpow; try lra; try lia.
Qed.

Axiom reduce_error_from_gappa : forall (x y : R),
  (1 <= x <= 4)%R ->
  (/4 * sqrt x <= y - sqrt x <=  sqrt x)%R ->
  (Rabs ((round' (round' (y + round' (x / y)) / 2) -
         sqrt x) / (y - sqrt x)) <=
   127 * bpow radix2 (-7))%R.

Lemma body_exp_decrease2 x y :
  is_finite 24 128 x = true ->
  is_finite 24 128 y = true ->
  let x' := B2R 24 128 x in
  let y' := B2R 24 128 y in
  (1 <= x' < B2R 24 128 predf32max)%R ->
  (2 * sqrt x' < y' <= x')%R ->
  (round' (sqrt x') <=
      B2R 24 128 (body_exp x y) < 2 / 3 * y')%R.
Proof.
intros finx finy x' y' intx' inty'.
assert (sge0 : (1 <= sqrt x')%R).
  now rewrite <- sqrt_1; apply sqrt_le_1_alt; lra.
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
assert (yge1 : (1 <= y')%R) by lra.
assert (yn0 : y' <> 0%R) by lra.
rewrite body_exp_value; try tauto.
assert (boundxy1 : (x' / y' < sqrt x' / 2)%R).
  unfold Rdiv; apply Rmult_lt_reg_r with y';[lra | ].
  rewrite Rmult_assoc, Rinv_l, Rmult_1_r;[ | lra].
  rewrite <- (sqrt_sqrt x') at 1;[ | lra].
  rewrite Rmult_assoc; apply Rmult_lt_compat_l; lra.
assert (tm1 := body_exp_div_x_y_bounds1
       x
       y (proj1 intx') (conj yge1 (proj2 inty'))).
fold x' y' in tm1 |- *.
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
unfold body_exp_R; lra.
Qed.

Lemma inv_add_error x : (1 + x <> 0)%R -> (/ (1 + x) = 1 - x + x ^ 2 /(1 + x))%R.
Proof. now intros; field.  Qed.

Lemma target_above_s' x y :
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
    rewrite (cexp_32 3); try (simpl bpow; lra); try lia.
    rewrite ulps1; unfold ulp1; simpl bpow; lra.
  rewrite (cexp_32 2); try (simpl bpow; lra); try lia.
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
      rewrite (cexp_32 2); try lia.
        rewrite ulps1; unfold ulp1; simpl bpow; clear; lra.
      simpl bpow; split;[| clear -rsumub yx intx u4 ulps1 sle2]; lra.
    destruct (Rle_lt_dec 1 (round' (y' + round' (x' / y')) / 2)).
      rewrite (cexp_32 1); try lia. (* TODO here lra loops. *)
        rewrite ulps1; unfold ulp1; simpl bpow; lra.
      split;simpl bpow; assumption.
    rewrite (cexp_32 0); try lia.
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
    rewrite (cexp_32 2); try lia.
      rewrite ulps1; unfold ulp1; simpl bpow; clear; lra.
    simpl bpow; lra.
  rewrite (cexp_32 1); try lia.
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

Definition unscale_mantissa (m : Z) :=
  m * 2 ^ (23 - Digits.Zdigits radix2 m).

Lemma digits2_pos_pow2 (k : positive):
  Digits.digits2_pos (2 ^ k) = Pos.succ k.
Proof.
assert (tech : forall x y, Zpos x = Zpos y -> x = y)
  by (now clear; intros x y h; injection h; auto).
apply tech.
rewrite Digits.Zpos_digits2_pos, Pos2Z.inj_pow_pos, Z.pow_pos_fold.
now rewrite Digits.Zdigits_Zpower, Pos2Z.inj_succ, Z.add_1_r.
Qed.
    
Lemma float_pow_proof (x : Z) :
  Binary.bounded 24 128 (2 ^ 23) (Z.max (Z.min x 104) (-149)) = true.
Proof.
destruct (Z_lt_le_dec x (-149)) as [xle149 | xgt149];
    (rewrite Z.max_l;[ | lia]) || (rewrite Z.max_r;[ | lia]).
  reflexivity.
destruct (Z_le_dec 104 x) as [xge104 | xlt104];
    (rewrite Z.min_l;[ | lia]) || (rewrite Z.min_r;[ | lia]).
  reflexivity.
unfold Binary.bounded, canonical_mantissa, FLT_exp.
replace (Z.pos (Digits.digits2_pos (2 ^ 23))) with 24 by reflexivity.
rewrite Z.max_l by lia.
rewrite Bool.andb_true_iff; split.
  apply Zeq_bool_true; ring.
apply Zle_bool_true; lia.
Qed.

(* This should be used to replace float_four and float_two *)
Definition float_pow (x : Z) : float32 :=
  B754_finite 24 128 false
    (2 ^ 23) (Z.max (Z.min (x - 23) 104) (-149)) (float_pow_proof (x - 23)).

Lemma float_pow_val (x : Z) :
  -127 < x < 128 ->
   B2R 24 128 (float_pow x) = bpow radix2 x.
Proof.
intros intx; unfold float_pow; simpl.
rewrite Z.min_l by lia.
rewrite Z.max_l by lia.
unfold F2R; simpl. rewrite Pos2Z.inj_pow, (IZR_Zpower radix2) by lia.
rewrite <- bpow_plus; apply f_equal; ring.
Qed.

Definition float_one : float32 := Bone 24 128 eq_refl eq_refl.

Lemma float_mag_proof (m : positive) (e : Z)
  (p : Binary.bounded 24 128 m e = true) :
  Binary.bounded 24 128
    (if (m =? 1)%positive then
       m
    else
       (2 ^ Pos.pred (Digits.digits2_pos m))) e = true.
Proof.
unfold Binary.bounded in p |- *.
apply andb_prop in p; destruct p as [cm eb].
rewrite eb, Bool.andb_true_r.
destruct (m =? 1)%positive eqn:vm.
  exact cm.
unfold canonical_mantissa; rewrite digits2_pos_pow2.
  rewrite Pos.succ_pred.
  exact cm.
destruct m as [p | p | ]; simpl; try discriminate;
apply Pos.succ_not_1.
Qed.

Definition float_mag (x : float32) : float32 :=
  match x with
   | B754_zero s => B754_zero 24 128 s
   | B754_infinity sign => B754_infinity 24 128 sign
   | B754_nan a b c => B754_nan 24 128 a b c
   | B754_finite sign m e p =>
     B754_finite 24 128 false
      (if (m =? 1)%positive then
         m
      else
         (2 ^ Pos.pred (Digits.digits2_pos m))) e
        (float_mag_proof m e p)
   end.

Lemma even_mag x p :
  (1 <= x)%R ->
  (bpow radix2 (p - 1) <= x < bpow radix2 p)%R ->
  (bpow radix2 (2 * (p / 2 + p mod 2) - 2) <= x <
   bpow radix2 (2 * (p / 2 + p mod 2)))%R.
Proof.
intros xge1 plog.
replace (2 * (p / 2 + p mod 2) - 2) with
  ((2 * (p / 2) + p mod 2) + p mod 2 - 2) by ring.
replace (2 * (p / 2 + p mod 2)) with
  ((2 * (p / 2) + p mod 2) + p mod 2) by ring.
rewrite <- Z_div_mod_eq by lia.
split.
  apply Rle_trans with (bpow radix2 (p - 1));[ | tauto].
  apply bpow_le; replace (p + p mod 2 - 2) with (p + (p mod 2 - 2)) by ring.
  apply Z.add_le_mono_l; assert (mb := Z.mod_pos_bound p 2 eq_refl); lia.
apply Rlt_le_trans with (1 := proj2 plog).
apply bpow_le; assert (mb := Z.mod_pos_bound p 2 eq_refl); lia.
Qed.

Lemma non_zero_finite_strict (x : float32) :
  B2R 24 128 x <> 0%R -> is_finite 24 128 x = true ->
  is_finite_strict 24 128 x = true.
Proof.
destruct x; auto; intros abs; case abs; reflexivity.
Qed.

Definition Float32_two : float32 :=
  binary_normalize 24 128 eq_refl eq_refl mode_NE 2 0 false.

Lemma Float32_two_val : B2R 24 128 Float32_two = 2%R.
Proof. compute; lra. Qed.

Definition Float32_four : float32 :=
  binary_normalize 24 128 eq_refl eq_refl mode_NE 4 0 false.

Lemma Float32_four_val : B2R 24 128 Float32_four = 4%R.
Proof. compute; lra. Qed.

Lemma Float32_two_finite : is_finite 24 128 Float32_two = true.
Proof.
assert (tmp := binary_normalize_correct 24 128 eq_refl eq_refl mode_NE 2 0 false).
match goal with tmp : context[Rlt_bool ?v _] |- _ => assert (v2 : v = 2%R) end.
  set (vf := F2R _).
  replace vf with 2%R by (compute; ring).
  assert (vfq : vf = 2%R) by (compute; ring).
  assert (Rabs 2 = 2%R) by (rewrite Rabs_pos_eq; lra).
  assert (Valid_rnd (round_mode mode_NE)) by apply valid_rnd_round_mode.
  rewrite round_generic; auto.
  replace 2%R with (bpow radix2 1) by (compute; lra).
  now apply generic_format_bpow; compute; discriminate.
rewrite v2 in tmp.
assert (2 < bpow radix2 128)%R by (compute; lra).
rewrite Rlt_bool_true in tmp; auto.
Qed.

Lemma Float32_four_finite : is_finite 24 128 Float32_four = true.
Proof.
assert (tmp := binary_normalize_correct 24 128 eq_refl eq_refl mode_NE 4 0 false).
match goal with tmp : context[Rlt_bool ?v _] |- _ => assert (v4 : v = 4%R) end.
  set (vf := F2R _).
  replace vf with 4%R by (compute; ring).
  assert (vfq : vf = 4%R) by (compute; ring).
  assert (Rabs 4 = 4%R) by (rewrite Rabs_pos_eq; lra).
  assert (Valid_rnd (round_mode mode_NE)) by apply valid_rnd_round_mode.
  rewrite round_generic; auto.
  replace 4%R with (bpow radix2 2) by (compute; lra).
  now apply generic_format_bpow; compute; discriminate.
rewrite v4 in tmp.
assert (4 < bpow radix2 128)%R by (compute; lra).
rewrite Rlt_bool_true in tmp; auto.
Qed.

Lemma small_inject x :
  is_finite 24 128 x = true ->
  (/2 <= B2R 24 128 x < 1)%R ->
  match x with
  | B754_zero _ => False
  | B754_finite s m e p =>
    (s = false /\ Digits.digits2_pos m = 24%positive /\
    e = -24)
  | _ => False
  end.
destruct x as [s | | | s m e p]; try discriminate.
  simpl B2R; intros; lra.
intros _; simpl B2R.
destruct s eqn:sval; unfold F2R; simpl.
  intros [abs _].
  assert (abs': (0 < IZR (Z.neg m))%R).
    now apply Rmult_lt_reg_r with (bpow radix2 e);[apply bpow_gt_0 | lra].
  apply lt_IZR in abs'; lia.
intros intme.
split;[auto | ].
unfold Binary.bounded in p.
apply andb_prop in p; destruct p as [cm be].
unfold canonical_mantissa in cm.
unfold FLT_exp in cm.
destruct (Z_le_gt_dec (Z.pos (Digits.digits2_pos m) + e - 24) (3 - 128 - 24))
  as [abs | ok].
  rewrite Z.max_r in cm by lia.
  rewrite <- Zeq_is_eq_bool in cm.
  rewrite <- Zle_is_le_bool in be.
  rewrite <- cm in abs, intme.
  assert (bm : Z.pos (Digits.digits2_pos m) <= 24) by lia.
  rewrite Digits.Zpos_digits2_pos in bm.
  apply Digits.Zpower_gt_Zdigits in bm.
  rewrite Z.abs_eq in bm by lia.
  apply IZR_lt in bm; rewrite IZR_Zpower in bm by lia.
  assert (bm' : (IZR (Z.pos m) * bpow radix2 (3 -128 - 24) <
                bpow radix2 24 * bpow radix2 (3 -128 - 24))%R).
    apply Rmult_lt_compat_r;[apply bpow_gt_0 | assumption].
  rewrite <- bpow_plus in bm'.
  destruct intme as [abs2 _]; apply Rle_not_lt in abs2; case abs2.
  apply Rlt_trans with (1 := bm'); compute; lra.
rewrite Digits.Zpos_digits2_pos in ok, cm.
rewrite Z.max_l in cm by lia.
rewrite <- Zeq_is_eq_bool in cm.
assert (dq : Digits.Zdigits radix2 (Z.pos m) = 24) by lia.
assert (backinj : forall x y, Z.pos x = Z.pos y -> x = y).
  now intros x y a; injection a.
split;[apply backinj; rewrite  Digits.Zpos_digits2_pos; assumption | ].
assert (tmp := Digits.Zdigits_correct radix2 (Z.pos m)).
rewrite Z.abs_eq in tmp by lia; destruct tmp as [tmp1 tmp2].
apply IZR_le in tmp1; rewrite IZR_Zpower in tmp1 by lia.
apply IZR_lt in tmp2; rewrite IZR_Zpower in tmp2 by lia.
assert (mgt0 : (0 < IZR (Z.pos m))%R) by (apply IZR_lt; lia).
assert (e < -23).
  apply (lt_bpow radix2).
  apply Rnot_le_lt; intros abs.
  apply (Rmult_le_compat_l
              (IZR (Z.pos m)) _ _ (Rlt_le _ _ mgt0)) in abs.
  rewrite dq in tmp1.
  apply (Rmult_le_compat_r
              (bpow radix2 (-23)) _ _ (bpow_ge_0 _ _)) in tmp1.
  assert (abs2 := Rle_trans _ _ _ tmp1 abs).
  assert (sim1 : (bpow radix2 (24 - 1) * bpow radix2 (-23) = 1)%R).
    rewrite <- bpow_plus; ring_simplify (24 - 1 + (-23)); simpl bpow; ring.
  lra.
assert (-25 < e).
  apply (lt_bpow radix2).
  apply Rnot_le_lt; intros abs.
  apply (Rmult_le_compat_l
              (IZR (Z.pos m)) _ _ (Rlt_le _ _ mgt0)) in abs.
  apply (Rmult_lt_compat_r
              (bpow radix2 (-25)) _ _ (bpow_gt_0 _ _)) in tmp2.
  rewrite dq, <- bpow_plus in tmp2.
  assert (simh : (bpow radix2 (24 + -25) = /2)%R).
    ring_simplify (24 + -25); compute; lra.
  rewrite simh in tmp2; lra.
lia.
Qed.

Lemma mul_small_inbounds_2 x :
  is_finite 24 128 x = true ->
  (/2 <= B2R 24 128 x < 1)%R ->
  Rlt_bool (Rabs (round' (2 * B2R 24 128 x))) (bpow radix2 128) = true.
Proof.
intros finx intx.
assert (vbnd : (1 <= 2 * B2R 24 128 x < 2)%R) by lra.
assert (tm1 :=  @error_le_ulp radix2 f32_exp
      (@FLT_exp_valid (3 - 128 - 24) 24 eq_refl)
      (round_mode mode_NE) (valid_rnd_round_mode _) (2 * B2R 24 128 x)).
assert (prodn0 : (2 * B2R 24 128 x <> 0)%R) by lra.
assert (0 < ulp radix2 f32_exp (2 * B2R 24 128 x) < / 4)%R.
  rewrite ulp_neq_0 by auto.
  unfold cexp.
  assert (vm : mag_val radix2 _ (mag radix2 (2 * B2R 24 128 x)) = 1).
    apply mag_unique.
    rewrite Rabs_pos_eq by lra.
    replace (bpow radix2 (1 - 1)) with 1%R by (compute; lra).
    now replace (bpow radix2 1) with 2%R by (compute; lra).
  rewrite vm; compute; lra.
assert (nooverflow : (Rabs (round' (2 * B2R 24 128 x)) < bpow radix2 128)%R).
  apply Rabs_le_inv in tm1.
  rewrite Rabs_pos_eq by lra.
  apply Rlt_trans with 5%R;[ | compute]; lra.
now apply Rlt_bool_true.
Qed.

Lemma mul_small_inbounds_4 x :
  is_finite 24 128 x = true ->
  (/2 <= B2R 24 128 x < 1)%R ->
  Rlt_bool (Rabs (round' (4 * B2R 24 128 x))) (bpow radix2 128) = true.
Proof.
(* TODO: correct this proof so that it uses mag_unique, like the previous
  one.  Even better: make a generic proof. *)
intros finx intx.
assert (vbnd : (2 <= 4 * B2R 24 128 x < 4)%R) by lra.
assert (tm1 :=  @error_le_ulp radix2 f32_exp
      (@FLT_exp_valid (3 - 128 - 24) 24 eq_refl)
      (round_mode mode_NE) (valid_rnd_round_mode _) (4 * B2R 24 128 x)).
assert (prodn0 : (4 * B2R 24 128 x <> 0)%R) by lra.
assert (0 < ulp radix2 f32_exp (4 * B2R 24 128 x) < / 2)%R.
  rewrite ulp_neq_0 by auto.
  unfold cexp.
  destruct (mag radix2 (4 * B2R 24 128 x)) as [vm aux].
  assert (pv := aux prodn0); simpl; clear aux.
  assert (0 < vm).
    apply (lt_bpow radix2); apply Rlt_trans with (2 := proj2 pv).
    rewrite Rabs_pos_eq by lra.
    apply Rlt_le_trans with (2 := proj1 vbnd); compute; lra.
  assert (vm - 1 < 2).
    apply (lt_bpow radix2), Rle_lt_trans with (1:= proj1 pv).
    rewrite Rabs_pos_eq by lra.
    apply Rlt_le_trans with (1 := proj2 vbnd); compute; lra.
  split;[apply bpow_gt_0 | ].
  apply Rlt_trans with (bpow radix2 (-2));[ | compute; lra].
  apply bpow_lt; unfold f32_exp, FLT_exp.
  rewrite Z.max_l; lia.
assert (nooverflow : (Rabs (round' (4 * B2R 24 128 x)) < bpow radix2 128)%R).
  apply Rabs_le_inv in tm1.
  rewrite Rabs_pos_eq by lra.
  apply Rlt_trans with 5%R;[ | compute]; lra.
now apply Rlt_bool_true.
Qed.

Lemma mul_small_finite x :
  is_finite 24 128 x = true ->
  (/2 <= B2R 24 128 x < 1)%R ->
  is_finite 24 128 (Float32.mul Float32_four x) = true.
Proof.
(* TODO: this should be superseded by bounded_finite. *)
intros finx intx.
assert (tmp := Bmult_correct 24 128 eq_refl eq_refl Float32.binop_nan mode_NE
               Float32_four x).
fold f32_exp in tmp; rewrite Float32_four_val in tmp.
rewrite mul_small_inbounds_4 in tmp; auto; destruct tmp as [val [finval _]].
(* TODO: is this too hard. *)
match goal with finval : ?v = (_ && _)%bool |- _ => transitivity v end.
  reflexivity.
now rewrite finval, finx, Float32_four_finite.
Qed.

Lemma mul_small_val2 x :
  is_finite 24 128 x = true ->
  (/2 <= B2R 24 128 x < 1)%R ->
  B2R 24 128 (Float32.mul Float32_two x) = (2 * B2R 24 128 x)%R.
Proof.
intros finx intx.
assert (tmp := Bmult_correct 24 128 eq_refl eq_refl Float32.binop_nan mode_NE
               Float32_two x).
fold f32_exp in tmp; rewrite Float32_two_val in tmp.
rewrite mul_small_inbounds_2 in tmp; auto; destruct tmp as [val [finval _]].
(* TODO: is this too hard. *)
match goal with val : ?v = round' _ |- _ => transitivity v end.
  reflexivity.
assert (vexp  : -149 < cexp' (B2R 24 128 x)).
  unfold cexp.
  assert (vmeq : @mag_val radix2 _ (mag radix2 (B2R 24 128 x)) = 0).
    assert (xn0 : (B2R 24 128 x <> 0)%R) by lra.
    apply mag_unique.
    replace (bpow radix2 (0 - 1)) with (/ 2)%R by (compute; lra).
    replace (bpow radix2 0) with 1%R by (compute; lra).
    now rewrite Rabs_pos_eq by lra.
  now rewrite vmeq; compute.
rewrite val.
replace 2%R with (bpow radix2 1) by (compute; lra).
rewrite Rmult_comm.
rewrite round_mult_bpow, round_B2R';[easy | lra | lia| lia].
Qed.

Lemma mul_small_val4 x :
  is_finite 24 128 x = true ->
  (/2 <= B2R 24 128 x < 1)%R ->
  B2R 24 128 (Float32.mul Float32_four x) = (4 * B2R 24 128 x)%R.
Proof.
intros finx intx.
assert (tmp := Bmult_correct 24 128 eq_refl eq_refl Float32.binop_nan mode_NE
               Float32_four x).
fold f32_exp in tmp; rewrite Float32_four_val in tmp.
rewrite mul_small_inbounds_4 in tmp; auto; destruct tmp as [val [finval _]].
(* TODO: is this too hard. *)
match goal with val : ?v = round' _ |- _ => transitivity v end.
  reflexivity.
assert (vexp  : -149 < cexp' (B2R 24 128 x)).
  unfold cexp.
  assert (vmeq : @mag_val radix2 _ (mag radix2 (B2R 24 128 x)) = 0).
    assert (xn0 : (B2R 24 128 x <> 0)%R) by lra.
    apply mag_unique.
    replace (bpow radix2 (0 - 1)) with (/ 2)%R by (compute; lra).
    replace (bpow radix2 0) with 1%R by (compute; lra).
    now rewrite Rabs_pos_eq by lra.
  now rewrite vmeq; compute.
rewrite val.
replace 4%R with (bpow radix2 2) by (compute; lra).
rewrite Rmult_comm.
rewrite round_mult_bpow, round_B2R';[easy | lra | lia| lia].
Qed.

Lemma bounded_finite x :
   (bpow radix2 (-149) <= B2R 24 128 x)%R ->
   is_finite 24 128 x = true.
Proof.
assert (t1 := bpow_gt_0 radix2 (-149)).
destruct x as [ s | s | | s m e p]; simpl B2R; auto; try lra.
Qed.

Lemma above1 x y :
  is_finite 24 128 x = true ->
  is_finite 24 128 y = true ->
  let x' := B2R 24 128 x in
  let y' := B2R 24 128 y in
  (1 <= x' < B2R 24 128 predf32max)%R ->
  (sqrt x' - 16 * ulp radix2 f32_exp (sqrt x') <= y' <= x')%R ->
  (y' <= body_exp_R x' y')%R ->
  (Rabs (body_exp_R x' y' - sqrt x') <=
     6 * ulp radix2 f32_exp (sqrt x'))%R.
Proof.
intros finx finy x' y' intx inty stop.
assert (sge1 : (1 <= sqrt x')%R).
  rewrite <- sqrt_1; apply sqrt_le_1_alt; lra.
destruct (Rlt_le_dec (2 * sqrt x') y') as [ygt2s | yle2s].
  assert (tmp := body_exp_decrease2 x y finx finy intx (conj ygt2s (proj2 inty))).
  case (Rle_not_lt _ _ stop).
  assert (yge1 : (1 <= y')%R) by lra.
  assert (tm2 := body_exp_value _ _ finx finy intx (conj yge1 (proj2 inty))).
  fold x' y'  in tm2, tmp; rewrite <- tm2; apply Rlt_trans with (1 := proj2 tmp).
  lra.
assert (finx' : is_finite_strict 24 128 x = true).
  apply non_zero_finite_strict; auto; fold x'; lra.
destruct (Bfrexp_correct 24 128 eq_refl (Z.lt_le_incl 3 128 eq_refl)
             x finx') as [cnd1 [cnd2 cnd3]].
set (xm := fst (Bfrexp 24 128 eq_refl (Z.lt_le_incl 3 128 eq_refl) x)).
set (xm':= B2R 24 128 xm).
fold xm xm' in cnd1, cnd2, cnd3.
set (xe := snd (Bfrexp 24 128 eq_refl (Z.lt_le_incl 3 128 eq_refl) x)).
fold xe in cnd2, cnd3.
fold x' in cnd2, cnd3.
set (xe2 := (xe / 2)).
assert (0 < xm')%R.
  apply Rmult_lt_reg_r with (bpow radix2 xe);[apply bpow_gt_0 | lra].
assert (scales : exists e' x4, (x' = B2R 24 128 x4 * bpow radix2 (2 * e') /\
   1 <= B2R 24 128 x4 < 4)%R /\ -80 < e' <= 64).
  assert (cases : xe mod 2 = 0 \/ xe mod 2 = 1).
    assert (tmp := Z.mod_pos_bound xe 2 eq_refl); lia.
  destruct cases as [even_e | odd_e].
    exists (xe2 - 1), (Float32.mul Float32_four xm).
    rewrite Rabs_pos_eq in cnd1 by lra.
    rewrite mul_small_val4; cycle 1.
        apply bounded_finite; fold xm'.
        apply Rle_trans with (2 := proj1 cnd1); compute; lra.
      assumption.
    split.
      split.
        replace 4%R with (bpow radix2 2) by (compute; lra).
        rewrite (Rmult_comm (bpow _ 2)), Rmult_assoc, <- bpow_plus.
        replace (2 + 2 * (xe2 - 1)) with xe;[assumption | ].
        fold xm'.
        rewrite (Z.div_mod _ 2), even_e by lia.
        fold xe2; ring.
      fold xm'; lra.
    assert (tmp := bound_mag_float32 x finx').
    fold x' in tmp; rewrite <- cnd3 in tmp.
    assert (xe = 2 * xe2) by (rewrite (Z.div_mod _ 2); lia).
    lia.
  exists xe2, (Float32.mul Float32_two xm).
  rewrite Rabs_pos_eq in cnd1 by lra.
  rewrite mul_small_val2; cycle 1.
      apply bounded_finite; fold xm'.
      apply Rle_trans with (2 := proj1 cnd1); compute; lra.
    assumption.
  split.
    split.
      replace 2%R with (bpow radix2 1) by (compute; lra).
      rewrite (Rmult_comm (bpow _ 1)), Rmult_assoc, <- bpow_plus.
      replace (1 + 2 * xe2) with xe;[assumption | ].
      rewrite (Z.div_mod _ 2), odd_e by lia.
      fold xe2; ring.
    fold xm'; lra.
  assert (tmp := bound_mag_float32 x finx').
  fold x' in tmp; rewrite <- cnd3 in tmp.
  assert (xe = 2 * xe2 + 1) by (rewrite (Z.div_mod _ 2); lia).
  lia.
destruct scales as [e2 [x2 [[x'val intx2] eb]]].
set (y2 := Float32.mul y (float_pow (-e2))).
assert (tmp := Bmult_correct 24 128 eq_refl eq_refl Float32.binop_nan
               mode_NE x (float_pow (2 * (-e2)))).
fold f32_exp in tmp |- *.
rewrite Rlt_bool_true in tmp; cycle 1.
  clear tmp.    
  rewrite float_pow_val by lia.
  rewrite round_mult_bpow, round_B2R'.
Qed.
SearchPattern full_float.

Check F754_finite false 1 2.
   Compute FF2R radix2 (F754_finite false 1 2).

destruct (mag radix2 x') as [p tmp].
assert (xn0 : (x' <> 0)%R) by lra; assert (Pp := tmp xn0); clear tmp.
set (p' := p / 2 + p mod 2).

set (x1 := Bdiv x 

Axiom close_computation_from_gappa : forall (x y : R),
  (1 <= x <= 4)%R ->
  (Rabs (y - sqrt x) <=  1 * bpow radix2 (-19))%R ->
  (Rabs (round' (round' (y + round' (x / y)) / 2) -
          ((y + x / y) / 2)) <= 3 * bpow radix2 (-24))%R.


Lemma target_above_s x y :
  is_finite 24 128 x = true ->
  is_finite 24 128 y = true ->
  let x' := B2R 24 128 x in
  let y' := B2R 24 128 y in
  (y' <= x')%R ->
  (y' <= 3 / 2 * sqrt x')%R ->
  (1 <= x' < 4)%R ->
  (sqrt x' - bpow radix2 (-19) <= y')%R ->
  (y' <= body_exp_R x' y')%R ->
  (Rabs (body_exp_R x' y' - sqrt x') <= 6 * ulp1)%R.
Proof.
intros finx finy x' y' yx y2s intx sy yb.
assert (maxgt4: (4 < B2R 24 128 predf32max)%R).
  unfold B2R, predf32max; rewrite F2R_cond_Zopp; unfold cond_Ropp.
  unfold F2R; replace 4%R with (4 * 1)%R by ring.
  apply Rmult_lt_compat; try lra.
    apply IZR_lt; reflexivity.
  replace 1%R with (bpow radix2 0) by reflexivity.
  now apply bpow_lt; reflexivity.
assert (xltmax : (1 <= x' < B2R 24 128 predf32max)%R) by lra.
assert (y' <= sqrt x' + bpow radix2 (-19))%R.
  apply Rnot_lt_le; intros abs; apply (Rle_not_lt _ _ yb).
Admitted.

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
Admitted.

Lemma body_exp_decrease1 x y :
  is_finite 24 128 x = true ->
  is_finite 24 128 y = true ->
  let x' := B2R 24 128 x in
  let y' := B2R 24 128 y in
  (1 <= x' < B2R 24 128 predf32max)%R ->
  (3 / 2 * sqrt x' < y' <= x')%R ->
  (sqrt (x' - 5 * ulp radix2 f32_exp (sqrt x')) <=
      B2R 24 128 (body_exp x y) < 63/64 * y')%R.
Proof.
intros finx finy x' y' intx' inty'.
assert (sgt0 : (1 <= sqrt x')%R).
  now rewrite <- sqrt_1; apply sqrt_le_1_alt; lra.
assert (sx0 : (sqrt x' <> 0)%R) by lra.
set (e := (y' - sqrt x')%R).
assert (divlow : (x' / y' <= sqrt x' * (2 / 3))%R).
  rewrite <- (sqrt_sqrt x') at 1 by lra.
  unfold Rdiv; rewrite Rmult_assoc; apply Rmult_le_compat_l;[lra | ].
  apply Rmult_le_reg_r with y'; [lra | ].
  rewrite Rmult_assoc, Rinv_l, Rmult_1_r;lra.
replace (sqrt x' * sqrt x' / y')%R with
  (sqrt x' - e + e ^ 2 / (sqrt x' * (1 + e / sqrt x')))%R; cycle 1.
  unfold e; field; lra.
assert (yge1 : (1 <= y')%R) by lra.
assert (yn0 : y' <> 0%R) by lra.
rewrite (body_exp_value x y finx finy
                 intx' (conj yge1 (proj2 inty'))).
assert (boundxy1 : (x' / y' < sqrt x' * (2 / 3))%R).
  unfold Rdiv; apply Rmult_lt_reg_r with y';[lra | ].
  rewrite Rmult_assoc, Rinv_l, Rmult_1_r;[ | lra].
  rewrite <- (sqrt_sqrt x') at 1;[ | lra].
  rewrite Rmult_assoc; apply Rmult_lt_compat_l; lra.
assert (tm1 := body_exp_div_x_y_bounds1
       x
       y (proj1 intx') (conj yge1 (proj2 inty'))).
assert (tmp := @error_le_ulp radix2 f32_exp
        (@FLT_exp_valid (3 - 128 - 24) 24 eq_refl)
        (round_mode mode_NE) (valid_rnd_round_mode _) (x' / y')).
apply Rabs_le_inv in tmp.
assert (tm2 := float32_bound_ulp _ (proj1 tm1)).
fold x' y' in tm1, tm2 |- *.
assert (roundy : round' y' = y') by apply round_B2R'.
split.
  destruct (Rle_dec (2 * sqrt x') y') as [yabove | ybelow]. 

(* unsure here *)
  assert (1 <= round' (x' / y'))%R.
    rewrite <- round'1; apply round_le'; lra.
  assert (ulp radix2 f32_exp (x' / y') < sqrt x' / bpow radix2 21)%R.
    apply Rlt_trans with (1 := proj2 tm2).
    apply Rmult_lt_compat_r; [ rewrite <-bpow_opp; apply bpow_gt_0|lra].
  assert (formula : (x' / y' = 2 * sqrt x' - y' + (y' - sqrt x') ^ 2 / y')%R).
    rewrite <- (sqrt_sqrt x') at 1 by lra.
    field; lra.
  assert (lb1 : (2 * sqrt x' - y' +  /4 * x' / y'  <= x' / y')%R).
    rewrite formula; apply Rplus_le_compat_l.
    apply Rmult_le_compat_r;[apply Rlt_le, Rinv_0_lt_compat; lra |].
    replace (/4 * x')%R with ((sqrt x' / 2) ^ 2)%R.
      apply pow_incr; lra.
    replace ((sqrt x' / 2) ^ 2)%R with (sqrt x' * sqrt x' / 4)%R by field.
    rewrite sqrt_sqrt; lra.
  assert (step1:((2 * sqrt x' - (x' / y') /bpow radix2 21)
     < y' + round' (x' / y'))%R).
     lra.
  assert (step2 : (sqrt x'* (2 - (2 / 3) * /bpow radix2 21)
               < y' + round' (x' / y'))%R).
    apply Rlt_trans with (2 := step1).
    rewrite Rmult_minus_distr_l, Rmult_comm; apply Rplus_lt_compat_l.
    rewrite <- !Rmult_assoc; unfold Rdiv.
    apply Ropp_lt_contravar, Rmult_lt_compat_r.
      now rewrite <- bpow_opp; apply bpow_gt_0.
    assumption.
  assert (step3 : (y' + round' (x' / y') < 3 * sqrt x')%R).
    apply Rle_lt_trans with (2 * sqrt x' + (y' - sqrt x') ^ 2 / y'
                 + sqrt x' / bpow radix2 21)%R.
      lra.

admit. admit.
      
change (round radix2 f32_exp (round_mode mode_NE) (x' / y')) with
           (round' (x' / y')) in tmp.
assert (boundxy : (round' (x' / y') < 15 / 32 * y')%R).
  apply Rle_lt_trans with (x' / y' + ulp radix2 f32_exp (x' / y'))%R.
    lra.
  apply Rlt_le_trans with ((x' / y') + /1024 * (x' / y'))%R.
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
assert (boundsum : (round' (y' + round' (x' / y')) < 48 / 32 * y')%R).
  apply Rle_lt_trans with (y' + round' (x' / y') +
   ulp radix2 f32_exp (y' +  (round' (x' / y'))))%R.
    assert (tech : forall a b c : R, (a - b <= c)%R -> (a <= b + c)%R).
      now intros; lra.
    apply tech, Rle_trans with (1 := proj2 tm5); lra.
  assert (ulp radix2 f32_exp (y' + round' (x' / y')) < y' / 32)%R.
    assert (lt41 : (y' + round' (x' / y') < y' * (47/32))%R) by lra.
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
assert (ulp radix2 f32_exp (round' (y' + round' (x' / y')) / 2) < y' / 2048)%R.
  apply Rlt_le_trans with (1 := proj2 tm7).
  assert (2048 < bpow radix2 21)%R by now (compute; lra).
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
Admitted.

Lemma fsqrt_loop_terminates : forall x y,
  Float32.cmp Clt (body_exp x y)
    y= true ->
  (float_to_nat (body_exp x y) <
    float_to_nat y)%nat.
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

