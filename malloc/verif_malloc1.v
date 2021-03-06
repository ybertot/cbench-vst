Require Import VST.floyd.proofauto.
Require Import malloc1.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition malloc_token (sh: share) (t: type) (p: val) :=
  emp.

Definition HEAPSIZE := proj1_sig (opaque_constant 1000).
Definition HEAPSIZE_eq : HEAPSIZE = 1000 := proj2_sig (opaque_constant _).
Hint Rewrite HEAPSIZE_eq : rep_omega.

Definition mem_mgr (gv: globals) :=
 EX r:Z,
   !! (0 <= r <= HEAPSIZE /\ (natural_alignment | r)) &&
   data_at Ews (tptr tuchar) 
      (offset_val r (gv _heap)) (gv _limit) *
   data_at_ Ews (tarray tuchar (HEAPSIZE-r)) 
       (offset_val r (gv _heap)).

Definition BOGUS (t: type) :=
  (* Because malloc1.c has a bug, described in
     https://github.com/cverified/cbench/issues/2
     we need to add this bogus requirement in the
     precondition of malloc *)
 (natural_alignment | sizeof t).

Definition malloc_spec :=
   DECLARE _malloc
   WITH t:type, gv: globals
   PRE [ _n OF tint ]
       PROP (0 <= sizeof t <= Int.max_signed;
                complete_legal_cosu_type t = true;
                natural_aligned natural_alignment t = true;
                BOGUS t)
       LOCAL (temp _n (Vint (Int.repr (sizeof t))); gvars gv)
       SEP (mem_mgr gv)
    POST [ tptr tuchar ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (mem_mgr gv;
             if eq_dec p nullval then emp
            else (malloc_token Ews t p * data_at_ Ews t p)).

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog nil gv
  POST [ tint ]  
     PROP() 
     LOCAL (temp ret_temp (Vint (Int.repr 0)))
     SEP(TT).

Definition Gprog : funspecs :=
         [malloc_spec; main_spec].

Lemma init_mem_mgr:
 forall (gv: globals),
 data_at Ews
          (Tpointer
             (Tint I8 Unsigned
                {|
                attr_volatile := false;
                attr_alignas := None |}) noattr)
          (offset_val 0 (gv _heap)) 
          (gv _limit) *
 data_at_ Ews (tarray tuchar 1000) (gv _heap) |--
 mem_mgr gv.
Proof.
intros.
unfold mem_mgr.
Exists 0.
rewrite <- HEAPSIZE_eq.
entailer!.
apply Z.divide_0_r.
cancel.
Qed.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
fold noattr.
fold tuchar.
fold (tptr tuchar).
sep_apply init_mem_mgr.
forward.
Qed.

Lemma body_malloc: semax_body Vprog Gprog f_malloc malloc_spec.
Proof.
start_function.
rename H2 into H_BOGUS.
unfold mem_mgr in *.
Intros r.
rename H3 into Halign_r.
forward_if (temp _t'1 (Vint (Int.repr 
                    (if zle (sizeof t) 0 
                    then 1
                    else if zle (sizeof t) (HEAPSIZE-r)
                           then 0 else 1)))).
-
forward.
entailer!.
f_equal.
f_equal.
change (@sizeof _ t) with (@sizeof cenv_cs t) in *.
rewrite Int.signed_repr in H3 by rep_omega.
f_equal.
destruct (zle (sizeof t) 0); try omega.
-
forward.
forward.
entailer!.
unfold denote_tc_samebase.
entailer!.
destruct (gv _heap); try contradiction; simpl.
destruct (peq b b); auto. clear - n; congruence.
change (@sizeof _ t) with (@sizeof cenv_cs t) in *.
rewrite Int.signed_repr in H3 by rep_omega.
rewrite <- HEAPSIZE_eq.
entailer!.
destruct (zle (sizeof t) 0); try omega.
destruct (zle (sizeof t) (HEAPSIZE-r)); try omega.
destruct (gv _heap); try contradiction; simpl.
unfold sem_sub_pp, both_int; simpl.
rewrite if_true by auto.
normalize.
rewrite !(Ptrofs.add_commut i).
rewrite (Ptrofs.sub_shifted).
unfold Ptrofs.divs.
normalize.
rewrite (Ptrofs.signed_repr 1) by rep_omega.
rewrite Z.quot_1_r.
unfold Int.lt.
rewrite if_false. reflexivity.
change (@sizeof _ t) with (@sizeof cenv_cs t) in *.
rewrite (Int.signed_repr (sizeof _)) by rep_omega.
rewrite Ptrofs.signed_repr by rep_omega.
rewrite Int.signed_repr by rep_omega.
omega.
destruct (gv _heap); try contradiction; simpl.
unfold sem_sub_pp, both_int; simpl.
rewrite if_true by auto.
rewrite !(Ptrofs.add_commut i).
rewrite (Ptrofs.sub_shifted).
unfold Ptrofs.divs.
rewrite (Ptrofs.signed_repr 1) by rep_omega.
rewrite Z.quot_1_r.
unfold Int.lt.
normalize.
rewrite Ptrofs.signed_repr by rep_omega.
rewrite if_true. reflexivity.
change (@sizeof _ t) with (@sizeof cenv_cs t) in *.
normalize.
omega.
-
forward_if.
forward.
Exists (Vint (Int.repr 0)) r.
entailer!.
rewrite if_true by auto.
cancel.
forward.
forward.
forward.
forward.
change (@sizeof _ t) with (@sizeof cenv_cs t) in *.
destruct (zle (sizeof t) 0); try discriminate H3.
destruct (zle (sizeof t) (HEAPSIZE-r)); try discriminate H3.
Exists (offset_val r (gv _heap)) (r+sizeof t).
entailer!.
apply Z.divide_add_r; auto.
rewrite if_false.
2:{ destruct (gv _heap); try contradiction; intro Hx; inv Hx. }
change (data_at_ Ews (tarray tuchar (HEAPSIZE - r)))
  with (data_at Ews (tarray tuchar (HEAPSIZE - r))
                      (list_repeat (Z.to_nat (HEAPSIZE-r)) Vundef)).
unfold tarray.
erewrite (split2_data_at_Tarray Ews tuchar
                (HEAPSIZE-r) (sizeof t) 
                 (list_repeat (Z.to_nat (HEAPSIZE-r)) Vundef)
                 (list_repeat (Z.to_nat (HEAPSIZE-r)) Vundef)).
5,6: reflexivity.
2: omega.
2: list_solve.
2: autorewrite with sublist; auto.
autorewrite with sublist.
rewrite sepcon_comm.
apply sepcon_derives.
+
replace (HEAPSIZE - r - sizeof t)
 with (HEAPSIZE - (r + sizeof t)) by omega.
unfold data_at_, data_at, field_at_.
simpl.
apply derives_refl'.
f_equal.
unfold field_address0.
simpl.
rewrite if_true.
normalize.
eapply field_compatible0_cons_Tarray; auto.
reflexivity.
change (@sizeof _ t) with (@sizeof cenv_cs t) in *.
rep_omega.
+
sep_apply (data_at_memory_block Ews (Tarray tuchar (sizeof t) noattr)
 (list_repeat (Z.to_nat (sizeof t)) Vundef) (offset_val r (gv _heap))).
rewrite <- memory_block_data_at_.
apply derives_refl'.
f_equal.
simpl.
change (@sizeof _ t) with (@sizeof cenv_cs t) in *.
 rewrite Z.max_r by rep_omega. normalize.
clear H8 H6 H5.
destruct (gv _heap); try contradiction.
apply malloc_compatible_field_compatible; auto.
split.
destruct HP_heap as [b' ?].
symmetry in H5; inv H5.
normalize.
rewrite Ptrofs.unsigned_repr by rep_omega.
auto.
destruct HP_heap as [b' ?].
symmetry in H5; inv H5.
normalize.
rewrite Ptrofs.unsigned_repr by rep_omega.
rep_omega.
Qed.
