Require Import VST.floyd.proofauto.
Require Import fac4.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Require Import fac_facts.

Definition fac_spec :=
 DECLARE _fac
  WITH n: Z
  PRE  [ _n OF tint ] 
     PROP(0 <= n <= 12)
     LOCAL(temp _n (Vint (Int.repr n)))
     SEP ()
  POST [ tint ]  
     PROP() 
     LOCAL (temp ret_temp (Vint (Int.repr (fac n))))
     SEP().

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog nil gv
  POST [ tint ]  
     PROP() 
     LOCAL (temp ret_temp (Vint (Int.repr (fac 5))))
     SEP(TT).

Definition Gprog : funspecs :=
        ltac:(with_library prog [fac_spec; main_spec]).

Lemma body_fac:  semax_body Vprog Gprog f_fac fac_spec.
Proof.
start_function.
forward_if (temp _t'1 (Vint (Int.repr (fac n)))).
forward.
entailer!.
forward_call.
omega.
forward.
entailer!.
rewrite Int.signed_repr.
replace (n * (fac(n-1)))%Z with (fac n).
apply fac_in_range; auto.
rewrite (fac_equation n). rewrite if_true by omega. auto.
pose proof (fac_mono 0 (n-1)).
spec H1; [omega|].
change (fac 0) with 1 in H1.
split.
rep_omega.
apply Z.le_trans with (fac n).
apply fac_mono; omega.
apply fac_in_range; auto.
entailer!.
rewrite (fac_equation n). rewrite if_true by omega.
auto.
forward.
Qed.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
forward_call.
omega.
forward.
Qed.

Existing Instance NullExtension.Espec.

Lemma prog_correct: semax_prog prog Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons body_fac.
semax_func_cons body_main.
Qed.
