Require Import SystemMP.Project.Infrastructure.
Require Import SystemMP.Project.Helpers.
Require Import Coq.Program.Equality.
Import ListNotations.

(* ------------------------------ Lemma 3.1, 3.3 ------------------------------ *)

Lemma narrowing_val_aux :
  (forall E_,
    wf_env E_ ->
    (forall E F z S S',
      E_ = E ++ (z, bind_val S) :: F ->
      sub F S' S ->
      wf_typ F S' ->
      wf_env (E ++ (z, bind_val S') :: F))) /\
  (forall E_ T,
    wf_typ E_ T ->
    (forall E F z S S',
      E_ = E ++ (z, bind_val S) :: F ->
      sub F S' S ->
      wf_env (E ++ (z, bind_val S') :: F) ->
      wf_typ (E ++ (z, bind_val S') :: F) T)) /\
  (forall E_ T U,
    sub E_ T U ->
    (forall E F z S S',
      E_ = E ++ (z, bind_val S) :: F ->
      sub F S' S ->
      wf_typ F S' ->
      sub (E ++ (z, bind_val S') :: F) T U)).
Proof with eauto 5 using wf_env_weaken_val, wf_typ_weaken_val, sub_weaken_val.
  apply wf_env_typ_sub_ind; intros; subst...

  (* ------------- wf_env ------------- *)

  (* Case w_nil *)
  exfalso.
  rewrite_env (E ++ [(z, bind_val S)] ++ F) in H...
  apply nil_neq_one_mid in H...

  (* Case w_val, w_typ *)
  1,2: destruct E0.
  1,3 : simpl_env in *; inversion H1; subst;
        eauto; apply w_val...
  1,2: destruct p; simpl_env in H1;
       destruct b; inversion H1;
       subst; econstructor...

  (* ------------- wf_typ ------------- *)

  (* Case w_var, w_tvar *)
  1,2: analyze_binds b...

  (* Case w_fst, w_tfst, w_snd, w_tsnd *)
  1-4: assert (wf_typ F S') by (
        apply wf_env_strengthen_head in H2; eauto;
        inversion H2; subst; eauto
       )...

  (* Case w_fun, w_pair, w_tpair *)
  pick fresh x and apply w_fun...
  3: pick fresh x and apply w_pair...
  4: pick fresh x and apply w_tpair...
  1,3,4: eapply (H0 x ltac:(fsetdec) ((x, bind_val S) :: E0)); eauto ; [reflexivity | ];
    rewrite_alist (nil ++ (x, bind_val S) :: (E0 ++ (z, bind_val S') :: F));
    apply wf_env_weaken_val...

  (* Case w_tfun *)
  pick fresh X and apply w_tfun...
  eapply (H0 X ltac:(fsetdec) ((X, bind_typ S) :: E0))...
  reflexivity.
  rewrite_alist (nil ++ (X, bind_typ S) :: (E0 ++ (z, bind_val S') :: F)).
  apply wf_env_weaken_typ...

  (* ------------- sub ------------- *)

  (* Case s_var *)
  analyze_binds b...
  inversion BindsTacVal; subst...
  apply sub_trans with (T := S')...
  rewrite_alist ((E0 ++ [(z, bind_val S')]) ++ F)...
  eapply sub_weaken_tail...
  simpl_env...
  eapply H...

  (* Case s_tvar *)
  analyze_binds b...

  (* Case s_fun, s_par, s_tpair *)
  pick fresh x and apply sub_fun...
  3: pick fresh x and apply sub_pair...
  4: pick fresh x and apply sub_tpair...
  1,3,4: eapply (H0 x ltac:(fsetdec) ((x, bind_val S2) :: E0)); eauto; reflexivity.

  (* Case s_tfun *)
  pick fresh X and apply sub_tfun...
  eapply (H0 X ltac:(fsetdec) ((X, bind_typ S2) :: E0)); eauto; reflexivity.
Qed.

Theorem wf_typ_narrow_val : forall E F z S S' T,
  wf_typ (E ++ (z, bind_val S) :: F) T ->
  sub F S' S ->
  wf_env (E ++ (z, bind_val S') :: F) ->
  wf_typ (E ++ (z, bind_val S') :: F) T.
Proof with eauto.
  intros.
  pose proof ((proj1 (proj2 narrowing_val_aux)) (E ++ (z, bind_val S) :: F) T).
  eapply H2...
Qed.

Theorem sub_narrow_val : forall E F z S S' T U,
  sub (E ++ (z, bind_val S) :: F) T U ->
  sub F S' S ->
  wf_env (E ++ (z, bind_val S') :: F) ->
  sub (E ++ (z, bind_val S') :: F) T U.
Proof with eauto.
  intros.
  pose proof ((proj2 (proj2 narrowing_val_aux)) (E ++ (z, bind_val S) :: F) T U).
  eapply H2...
  eapply wf_env_strengthen_head in H1...
  inversion H1; subst...
Qed.


(* ------------------------------ Lemma 3.2, 3.4 ------------------------------ *)

Lemma narrowing_typ_aux :
  (forall E_,
    wf_env E_ ->
    (forall E F z S S',
      E_ = E ++ (z, bind_typ S) :: F ->
      sub F S' S ->
      wf_typ F S' ->
      wf_env (E ++ (z, bind_typ S') :: F))) /\
  (forall E_ T,
    wf_typ E_ T ->
    (forall E F z S S',
      E_ = E ++ (z, bind_typ S) :: F ->
      sub F S' S ->
      wf_env (E ++ (z, bind_typ S') :: F) ->
      wf_typ (E ++ (z, bind_typ S') :: F) T)) /\
  (forall E_ T U,
    sub E_ T U ->
    (forall E F z S S',
      E_ = E ++ (z, bind_typ S) :: F ->
      sub F S' S ->
      wf_typ F S' ->
      sub (E ++ (z, bind_typ S') :: F) T U)).
Proof with eauto 5 using wf_env_weaken_typ, wf_typ_weaken_typ, sub_weaken_typ.
  apply wf_env_typ_sub_ind; intros; subst...

  (* ------------- wf_env ------------- *)

  (* Case w_nil *)
  exfalso.
  rewrite_env (E ++ [(z, bind_typ S)] ++ F) in H...
  apply nil_neq_one_mid in H...

  (* Case w_val, w_typ *)
  1,2: destruct E0.
  1,3 : simpl_env in *; inversion H1; subst;
        eauto; apply w_typ...
  1,2: destruct p; simpl_env in H1;
       destruct b; inversion H1;
       subst; econstructor...

  (* ------------- wf_typ ------------- *)

  (* Case w_var, w_tvar *)
  1,2: analyze_binds b...

  (* Case w_fst, w_tfst, w_snd, w_tsnd *)
  1-4: assert (wf_typ F S') by (
        apply wf_env_strengthen_head in H2; eauto;
        inversion H2; subst; eauto
       )...

  (* Case w_fun, w_pair, w_tpair *)
  pick fresh x and apply w_fun...
  3: pick fresh x and apply w_pair...
  4: pick fresh x and apply w_tpair...
  1,3,4: eapply (H0 x ltac:(fsetdec) ((x, bind_val S) :: E0)); eauto ; [reflexivity | ];
    rewrite_alist (nil ++ (x, bind_val S) :: (E0 ++ (z, bind_typ S') :: F));
    apply wf_env_weaken_val...

  (* Case w_tfun *)
  pick fresh X and apply w_tfun...
  eapply (H0 X ltac:(fsetdec) ((X, bind_typ S) :: E0))...
  reflexivity.
  rewrite_alist (nil ++ (X, bind_typ S) :: (E0 ++ (z, bind_typ S') :: F)).
  apply wf_env_weaken_typ...

  (* ------------- sub ------------- *)

  (* Case s_var *)
  analyze_binds b...

  (* Case s_tvar *)
  analyze_binds b...
  inversion BindsTacVal; subst...
  apply sub_trans with (T := S')...
  rewrite_alist ((E0 ++ [(z, bind_typ S')]) ++ F)...
  eapply sub_weaken_tail...
  simpl_env...
  eapply H...

  (* Case s_fun, s_par, s_tpair *)
  pick fresh x and apply sub_fun...
  3: pick fresh x and apply sub_pair...
  4: pick fresh x and apply sub_tpair...
  1,3,4: eapply (H0 x ltac:(fsetdec) ((x, bind_val S2) :: E0)); eauto; reflexivity.

  (* Case s_tfun *)
  pick fresh X and apply sub_tfun...
  eapply (H0 X ltac:(fsetdec) ((X, bind_typ S2) :: E0)); eauto; reflexivity.
Qed.

Theorem wf_typ_narrow_typ : forall E F z S S' T,
  wf_typ (E ++ (z, bind_typ S) :: F) T ->
  sub F S' S ->
  wf_env (E ++ (z, bind_typ S') :: F) ->
  wf_typ (E ++ (z, bind_typ S') :: F) T.
Proof with eauto.
  intros.
  pose proof ((proj1 (proj2 narrowing_typ_aux)) (E ++ (z, bind_typ S) :: F) T).
  eapply H2...
Qed.

Theorem sub_narrow_typ : forall E F z S S' T U,
  sub (E ++ (z, bind_typ S) :: F) T U ->
  sub F S' S ->
  wf_env (E ++ (z, bind_typ S') :: F) ->
  sub (E ++ (z, bind_typ S') :: F) T U.
Proof with eauto.
  intros.
  pose proof ((proj2 (proj2 narrowing_typ_aux)) (E ++ (z, bind_typ S) :: F) T U).
  eapply H2...
  eapply wf_env_strengthen_head in H1...
  inversion H1; subst...
Qed.

(* ------------------------------ Lemma 3.5 ------------------------------ *)

Theorem typing_narrowing_val : forall E F z S S' e T,
  typing (E ++ (z, bind_val S) :: F) e T ->
  sub F S' S ->
  wf_env (E ++ (z, bind_val S') :: F) ->
  typing (E ++ (z, bind_val S') :: F) e T.
Proof with eauto 5 using wf_env_weaken_val, wf_typ_weaken_val, sub_weaken_val, wf_typ_narrow_val, sub_narrow_val.
  intros.
  dependent induction H...
  - pick fresh x and apply t_abs...
    eapply (H1 x ltac:(fsetdec) ((x, bind_val S0) :: E)); eauto.
    reflexivity.
    rewrite_alist ((x, bind_val S0) :: (E ++ (z, bind_val S') :: F))...
  - pick fresh x and apply t_tabs...
    eapply (H1 x ltac:(fsetdec) ((x, bind_typ S0) :: E)); eauto.
    reflexivity.
    rewrite_alist ((x, bind_typ S0) :: (E ++ (z, bind_val S') :: F))...
  - pick fresh x' and apply t_pair...
    specialize (H0 x' ltac:(fsetdec)).
    rewrite_env (((x', bind_val S0) :: E) ++ (z, bind_val S') :: F).
    rewrite_env (((x', bind_val S0) :: E) ++ (z, bind_val S) :: F) in H0.
    apply wf_typ_narrow_val with (S := S)...
    simpl_env in *. apply w_val...
    apply wf_typ_narrow_val with (S := S)...
    apply wf_typ_env_wf in H0.
    inversion H0; subst...
  - pick fresh x' and apply t_tpair...
    specialize (H0 x' ltac:(fsetdec)).
    rewrite_env (((x', bind_val S0) :: E) ++ (z, bind_val S') :: F).
    rewrite_env (((x', bind_val S0) :: E) ++ (z, bind_val S) :: F) in H0.
    apply wf_typ_narrow_val with (S := S)...
    simpl_env in *. apply w_val...
    apply wf_typ_narrow_val with (S := S)...
    apply wf_typ_env_wf in H0.
    inversion H0; subst...
  - pick fresh x and apply t_let...
    eapply (H2 x ltac:(fsetdec) ((x, bind_val S0) :: E)); eauto.
    reflexivity.
    rewrite_alist ((x, bind_val S0) :: (E ++ (z, bind_val S') :: F))...
    apply w_val...
    specialize (H1 x ltac:(fsetdec)).
    apply typing_env_wf in H1.
    inversion H1; subst...
Qed.

(* ------------------------------ Lemma 3.6 ------------------------------ *)

Theorem typing_narrowing_typ : forall E F z S S' e T,
  typing (E ++ (z, bind_typ S) :: F) e T ->
  sub F S' S ->
  wf_env (E ++ (z, bind_typ S') :: F) ->
  typing (E ++ (z, bind_typ S') :: F) e T.
Proof with eauto 5 using wf_env_weaken_typ, wf_typ_weaken_typ, sub_weaken_typ, wf_typ_narrow_typ, sub_narrow_typ.
  intros.
  dependent induction H...
  - pick fresh x and apply t_abs...
    eapply (H1 x ltac:(fsetdec) ((x, bind_val S0) :: E)); eauto.
    reflexivity.
    rewrite_alist ((x, bind_val S0) :: (E ++ (z, bind_typ S') :: F))...
  - pick fresh x and apply t_tabs...
    eapply (H1 x ltac:(fsetdec) ((x, bind_typ S0) :: E)); eauto.
    reflexivity.
    rewrite_alist ((x, bind_typ S0) :: (E ++ (z, bind_typ S') :: F))...
  - pick fresh x' and apply t_pair...
    specialize (H0 x' ltac:(fsetdec)).
    rewrite_env (((x', bind_val S0) :: E) ++ (z, bind_typ S') :: F).
    rewrite_env (((x', bind_val S0) :: E) ++ (z, bind_typ S) :: F) in H0.
    apply wf_typ_narrow_typ with (S := S)...
    simpl_env in *. apply w_val...
    apply wf_typ_narrow_typ with (S := S)...
    apply wf_typ_env_wf in H0.
    inversion H0; subst...
  - pick fresh x' and apply t_tpair...
    specialize (H0 x' ltac:(fsetdec)).
    rewrite_env (((x', bind_val S0) :: E) ++ (z, bind_typ S') :: F).
    rewrite_env (((x', bind_val S0) :: E) ++ (z, bind_typ S) :: F) in H0.
    apply wf_typ_narrow_typ with (S := S)...
    simpl_env in *. apply w_val...
    apply wf_typ_narrow_typ with (S := S)...
    apply wf_typ_env_wf in H0.
    inversion H0; subst...
  - pick fresh x and apply t_let...
    eapply (H2 x ltac:(fsetdec) ((x, bind_val S0) :: E)); eauto.
    reflexivity.
    rewrite_alist ((x, bind_val S0) :: (E ++ (z, bind_typ S') :: F))...
    apply w_val...
    specialize (H1 x ltac:(fsetdec)).
    apply typing_env_wf in H1.
    inversion H1; subst...
Qed.
