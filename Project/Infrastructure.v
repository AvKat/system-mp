Require Import SystemMP.Project.Definitions.
Require Import Coq.Program.Equality.
Require Import CpdtTactics.
Require Import Coq.Program.Wf.
Require Import Coq.Lists.List.
Import ListNotations.

Lemma wf_env_uniq : forall E,
  wf_env E ->
  uniq E.
Proof with eauto.
  intros. dependent induction H...
Qed.

Hint Resolve wf_env_uniq : core.

(* Lemma 1.1 *)
Theorem env_binds_equal_var : forall E x U T,
  wf_env E ->
  binds x (bind_val U) E ->
  binds x (bind_val T) E ->
  U = T.
Proof with eauto using binds_nil_iff.
  intros. dependent induction H.
  inversion H0.
  2: rename X into x0.
  all: destruct (x0 == x); subst.
  2,4: analyze_binds H2; analyze_binds H3...
  all: eapply binds_unique with (b := bind_val U) in H3; auto;
    inversion H3; auto.
Qed.

Theorem env_binds_equal_typ : forall E X U T,
  wf_env E ->
  binds X (bind_typ U) E ->
  binds X (bind_typ T) E ->
  U = T.
Proof.
  intros. dependent induction H.
  inversion H0.
  rename x into X0.
  all: destruct (X0 == X); subst.
  1,3: eapply binds_unique with (b := bind_typ U) in H3; auto;
       inversion H3; auto.
  all: analyze_binds H2; analyze_binds H3.
Qed.

(* NOTE: Lemma 1.2 is a runtime lemma that is tentatively skipped  *)

(* Lemma 2.1, 2.4, 2.6 *)
Theorem wf_env_weaken_val : forall E F z S,
  wf_env (E ++ F) ->
  z `notin` dom E `union` dom F ->
  wf_typ F S ->
  wf_env (E ++ (z, bind_val S) :: F)
with wf_typ_weaken_val : forall E F z S T,
  wf_typ (E ++ F) T ->
  wf_typ F S ->
  z `notin` dom E `union` dom F ->
  wf_typ (E ++ (z, bind_val S) :: F) T
with sub_weaken_val : forall E F z S T U,
  sub (E ++ F) T U ->
  wf_typ F S ->
  z `notin` dom E `union` dom F ->
  sub (E ++ (z, bind_val S) :: F) T U.
Proof with eauto.
  {
    (* Lemma 2.1 *)
    clear - wf_typ_weaken_val.
    intros. dependent induction E.
    - simpl in *. auto.
    - inversion H; subst; constructor; auto.
  }
  {
    (* Lemma 2.3 *)
    clear - wf_env_weaken_val sub_weaken_val.
    intros. dependent induction H.
    (* Case: w_var, w_tvar *)
    econstructor; eauto; rewrite_alist (E ++ [(z, bind_val S)] ++ F); apply binds_weaken...
    eapply w_tvar; eauto. rewrite_alist (E ++ [(z, bind_val S)] ++ F); apply binds_weaken...
    (* Case: w_fst, w_tfst, w_snd, w_tsnd *)
    1-4: econstructor; eauto; rewrite_alist (E ++ [(z, bind_val S)] ++ F); apply binds_weaken...
    (* Case: w_top, w_bot *)
    1-2: constructor; apply wf_env_weaken_val; auto.
    (* Case: w_fun, w_tfun, w_vpair, w_tpair *)
    - pick fresh x and apply w_fun...
      apply (H1 x ltac:(fsetdec) ((x, bind_val S0) :: E))...
    - pick fresh X and apply w_tfun...
      eapply (H1 X ltac:(fsetdec) ((X, bind_typ S0) :: E))...
    - pick fresh x and apply w_pair...
      eapply (H1 x ltac:(fsetdec) ((x, bind_val S0) :: E))...
    - pick fresh x and apply w_tpair...
      eapply (H1 x ltac:(fsetdec) ((x, bind_val S0) :: E))...
  }
  {
    (* Lemma 2.6 *)
    clear - wf_env_weaken_val wf_typ_weaken_val.
    intros. dependent induction H.
    (* Case: sub_refl, sub_symm *)
    1,3: constructor...
    (* Case: sub_trans *)
    apply sub_trans with (T := T)...
    (* Case: sub_var *)
    constructor...
    rewrite_alist (E ++ [(z, bind_val S)] ++ F)...
    (* Case: sub_tvar *)
    apply sub_tvar...
    rewrite_alist (E ++ [(z, bind_val S)] ++ F)...
    (* Case: sub_fst, sub_tfst, sub_snd, sub_tsnd *)
    1-4: specialize (IHsub E F ltac:(auto) H0)...
    (* Case: sub_top, sub_bot *)
    1-2: constructor...
    (* Case: sub_fun *)
    - pick fresh x and apply sub_fun...
      apply (H1 x ltac:(fsetdec) ((x, bind_val S2) :: E))...
    - pick fresh X and apply sub_tfun...
      eapply (H1 X ltac:(fsetdec) ((X, bind_typ S2) :: E))...
    - pick fresh x and apply sub_pair...
      eapply (H1 x ltac:(fsetdec) ((x, bind_val S2) :: E))...
    - pick fresh x and apply sub_tpair...
      eapply (H1 x ltac:(fsetdec) ((x, bind_val S2) :: E))...
  }
  Admitted.

(* Lemma 2.2, 2.4, 2.7 *)
Lemma wf_env_weaken_typ : forall E F Z S,
  wf_env (E ++ F) ->
  Z `notin` dom E `union` dom F ->
  wf_typ F S ->
  wf_env (E ++ (Z, bind_typ S) :: F)
with wf_typ_weaken_typ : forall E F Z S T,
  wf_typ (E ++ F) T ->
  wf_typ F S ->
  Z `notin` dom E `union` dom F ->
  wf_typ (E ++ (Z, bind_typ S) :: F) T
with sub_weaken_typ : forall E F Z S T U,
  sub (E ++ F) T U ->
  wf_typ F S ->
  Z `notin` dom E `union` dom F ->
  sub (E ++ (Z, bind_typ S) :: F) T U.
Proof with eauto.
  {
    (* Lemma 2.2 *)
    clear - wf_typ_weaken_typ.
    intros. dependent induction E.
    - simpl in *; auto.
    - inversion H; subst; constructor; auto.
  }
  {
    (* Lemma 2.4 *)
    clear - wf_env_weaken_typ sub_weaken_typ.
    intros. dependent induction H.
    (* Case: w_var, w_tvar *)
     econstructor; eauto;
     rewrite_alist (E ++ [(Z, bind_typ S)] ++ F);
     apply binds_weaken...
     eapply w_tvar; eauto;
     rewrite_alist (E ++ [(Z, bind_typ S)] ++ F);
     apply binds_weaken...
    (* Case: w_fst, w_tfst, w_snd, w_tsnd *)
    1-4: apply sub_weaken_typ with (Z := Z) (S := S) in H...
    (* Case: w_top, w_bot *)
    1-2: constructor; apply wf_env_weaken_typ; auto.
    (* Case: w_fun, w_vpair, w_tpair *)
    - pick fresh x and apply w_fun...
      apply (H1 x ltac:(fsetdec) ((x, bind_val S0) :: E))...
    - pick fresh X and apply w_tfun...
      eapply (H1 X ltac:(fsetdec) ((X, bind_typ S0) :: E))...
    - pick fresh x and apply w_pair...
      eapply (H1 x ltac:(fsetdec) ((x, bind_val S0) :: E))...
    - pick fresh x and apply w_tpair...
      eapply (H1 x ltac:(fsetdec) ((x, bind_val S0) :: E))...
  }
  {
    (* Lemma 2.7 *)
    clear - wf_env_weaken_typ wf_typ_weaken_typ sub_weaken_typ.
    intros. dependent induction H.
    (* Case: sub_refl, sub_symm *)
    1,3: constructor...
    (* Case: sub_trans *)
    apply sub_trans with (T := T)...
    (* Case: sub_var *)
    constructor...
    rewrite_alist (E ++ [(Z, bind_typ S)] ++ F)...
    (* Case: sub_tvar *)
    apply sub_tvar...
    rewrite_alist (E ++ [(Z, bind_typ S)] ++ F)...
    (* Case: sub_fst, sub_tfst, sub_snd, sub_tsnd *)
    1-4: specialize (IHsub E F ltac:(auto) H0)...
    (* Case: sub_top, sub_bot *)
    1-2: constructor...
    (* Case: sub_fun *)
    - pick fresh x and apply sub_fun...
      apply (H1 x ltac:(fsetdec) ((x, bind_val S2) :: E))...
    - pick fresh X and apply sub_tfun...
      eapply (H1 X ltac:(fsetdec) ((X, bind_typ S2) :: E))...
    - pick fresh x and apply sub_pair...
      eapply (H1 x ltac:(fsetdec) ((x, bind_val S2) :: E))...
    - pick fresh x and apply sub_tpair...
      eapply (H1 x ltac:(fsetdec) ((x, bind_val S2) :: E))...
  }
  Admitted.

(* Hints to make applying the above lemmas easier *)

Hint Extern 1 (wf_env ((?x, ?b) :: ?E)) =>
  rewrite_alist (nil ++ (x, b) :: E); eauto
  : core.

Hint Extern 1 (wf_typ ((?x, ?b) :: ?E) ?T) =>
  rewrite_alist (nil ++ (x, b) :: E); eauto
  : core.

Hint Extern 1 (sub ((?x, ?b) :: ?E) ?T ?U) =>
  rewrite_alist (nil ++ (x, b) :: E); eauto
  : core.

Hint Extern 1 =>
  match goal with
  | H : binds _ _ nil |- _ => inversion H
  end : core.

(* Lemma 1.3 *)
Lemma wf_env_binds_val_wf : forall E x T,
  wf_env E ->
  binds x (bind_val T) E ->
  wf_typ E T.
Proof with eauto using wf_typ_weaken_val, wf_typ_weaken_typ.
  intros. dependent induction H...
  all: analyze_binds H2...
  inversion BindsTacVal; subst...
Qed.

(* Lemma 1.4 *)
Lemma wf_env_binds_typ_wf : forall E X T,
  wf_env E ->
  binds X (bind_typ T) E ->
  wf_typ E T.
Proof with eauto using wf_typ_weaken_val, wf_typ_weaken_typ.
  intros. dependent induction H...
  all: analyze_binds H2...
  inversion BindsTacVal; subst...
Qed.

(* Lemma 2.5 *)
Theorem wf_typ_weaken_tail : forall E F T,
  wf_typ F T ->
  wf_env (E ++ F) ->
  wf_typ (E ++ F) T.
Proof with eauto using wf_typ_weaken_val, wf_typ_weaken_typ.
  intros. induction E; simpl in *...
  inversion H0; subst...
Qed.

(* Lemma 2.8 *)
Theorem sub_weaken_tail : forall E F T U,
  sub F T U ->
  wf_env (E ++ F) ->
  sub (E ++ F) T U.
Proof with eauto using sub_weaken_val, sub_weaken_typ.
  intros. induction E; simpl in *...
  inversion H0; subst...
Qed.

(* Lemma 2.9 *)
Theorem typing_weaken_val : forall E F e T z S,
  typing (E ++ F) e T ->
  z `notin` dom E `union` dom F ->
  wf_typ F S ->
  typing (E ++ (z, bind_val S) :: F) e T.
Proof with eauto using wf_typ_weaken_val, wf_env_weaken_val, sub_weaken_val.
  intros. dependent induction H.
  (* generalize dependent E. *)
  - constructor...
  - apply t_sub with (S := S0)...
  - pick fresh x and apply t_abs...
    eapply H1 with (E := (x, bind_val S0) :: E)...
  - apply t_app with (S := S0)...
  - pick fresh X and apply t_tabs...
    eapply H1 with (E := (X, bind_typ S0) :: E)...
  - apply t_tapp with (S := S0)...
  - pick fresh x' and apply t_pair...
    apply wf_typ_weaken_val with (E := (x', bind_val S0) :: E)...
  - pick fresh x' and apply t_tpair...
    apply wf_typ_weaken_val with (E := (x', bind_val S0) :: E)...
  - pick fresh x and apply t_let...
    apply (H2 x ltac:(fsetdec) ((x, bind_val S0) :: E))...
Qed.

(* Lemma 2.10 *)
Theorem typing_weaken_typ : forall E F e T Z S,
  typing (E ++ F) e T ->
  Z `notin` dom E `union` dom F ->
  wf_typ F S ->
  typing (E ++ (Z, bind_typ S) :: F) e T.
Proof with eauto using wf_typ_weaken_typ, wf_env_weaken_typ, sub_weaken_typ.
  intros. dependent induction H.
  - constructor...
  - apply t_sub with (S := S0)...
  - pick fresh x and apply t_abs...
    eapply H1 with (E := (x, bind_val S0) :: E)...
  - apply t_app with (S := S0)...
  - pick fresh X and apply t_tabs...
    eapply H1 with (E := (X, bind_typ S0) :: E)...
  - apply t_tapp with (S := S0)...
  - pick fresh x' and apply t_pair...
    apply wf_typ_weaken_typ with (E := (x', bind_val S0) :: E)...
  - pick fresh x' and apply t_tpair...
    apply wf_typ_weaken_typ with (E := (x', bind_val S0) :: E)...
  - pick fresh x and apply t_let...
    apply (H2 x ltac:(fsetdec) ((x, bind_val S0) :: E))...
Qed.

Hint Extern 1 (typing ((?x, ?b) :: ?E) ?e ?T) =>
  rewrite_alist (nil ++ (x, b) :: E); eauto
  : core.

(* Lemma 2.11 *)
Theorem typing_weaken_tail : forall E F e T,
  typing F e T ->
  wf_env (E ++ F) ->
  typing (E ++ F) e T.
Proof with eauto using typing_weaken_typ, typing_weaken_val.
  intros. induction E; simpl in *...
  inversion H0; subst...
Qed.
