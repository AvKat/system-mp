Require Export SystemMP.Project.Infrastructure.
Require Import Coq.Program.Equality.

(* Basic Well-formdness Relations *)

Lemma sub_env_wf : forall E T U,
  sub E T U ->
  wf_env E.
Proof with eauto.
  intros. dependent induction H...
Qed.

Lemma wf_typ_env_wf : forall E T,
  wf_typ E T ->
  wf_env E.
Proof with eauto using sub_env_wf.
  intros. dependent induction H...
Qed.

Lemma typing_env_wf : forall E p T,
  typing E p T ->
  wf_env E.
Proof with eauto using wf_typ_env_wf, sub_env_wf.
  intros. dependent induction H...
Qed.

Lemma typed_path_wf : forall E (p: pth) T,
  typing E p T ->
  wf_typ E p.
Proof with eauto.
  intros. dependent induction H...
Qed.

Lemma wf_pth_path : forall E (p : pth),
  wf_typ E p ->
  path p
with sub_pth_path : forall E (p : pth) T,
  sub E p T ->
  path p.
Proof with eauto.
  - clear wf_pth_path.
    intros. dependent induction H...
  - clear sub_pth_path.
    intros. dependent induction H...
Qed.

Lemma wf_typ_type : forall E T,
  wf_typ E T ->
  type T.
Proof with eauto.
  intros. dependent induction H...
Qed.

Hint Resolve sub_env_wf wf_typ_env_wf typing_env_wf typed_path_wf wf_pth_path sub_pth_path wf_typ_type : core.

(* Free variables *)

Lemma fv_pp_sub_fv_pp_open_pv : forall p x z k,
  z `notin` fv_pp (open_pv p x k) ->
  z `notin` fv_pp p.
Proof with eauto.
  intros. dependent induction p; simpl in *; try fsetdec...
  destruct v...
Qed.

Lemma fv_tp_sub_fv_tp_open_tv : forall T x z k,
  z `notin` fv_tp (open_tv_rec T x k) ->
  z `notin` fv_tp T.
Proof with eauto using fv_pp_sub_fv_pp_open_pv.
  intros. dependent induction T; simpl in *; try fsetdec...
Qed.

Lemma fv_tp_sub_fv_tp_open_tt : forall T x z k,
  z `notin` fv_tp (open_tt_rec T x k) ->
  z `notin` fv_tp T.
Proof with eauto.
  intros. dependent induction T; simpl in *; try fsetdec...
Qed.

Lemma fv_tt_sub_fv_tt_open_tv : forall T x z k,
  z `notin` fv_tt (open_tv_rec T x k) ->
  z `notin` fv_tt T.
Proof with eauto.
  intros. dependent induction T; simpl in *; try fsetdec...
Qed.

Lemma fv_tt_sub_fv_tt_open_tt : forall T x z k,
  z `notin` fv_tt (open_tt_rec T x k) ->
  z `notin` fv_tt T.
Proof with eauto.
  intros. dependent induction T; simpl in *; try fsetdec...
  destruct v; simpl in *...
Qed.

Lemma fv_pp_open_pp_sub_fv_pp : forall p q k z,
  z `notin` fv_pp p `union` fv_pp q ->
  z `notin` fv_pp (open_pp_rec p q k).
Proof with eauto.
  intros. dependent induction p; simpl in *; try fsetdec...
  destruct v...
  destruct (n == k)...
Qed.

Lemma fv_tp_open_tp_sub_fv_tp_pp : forall T p k z,
  z `notin` fv_tp T `union` fv_pp p ->
  z `notin` fv_tp (open_tp_rec T p k).
Proof with eauto using fv_pp_open_pp_sub_fv_pp.
  intros.
  dependent induction T; simpl in *; try fsetdec...
Qed.

Lemma fv_tt_open_tp_sub_fv_tt_pp : forall T p k z,
  z `notin` fv_tt T `union` fv_pp p ->
  z `notin` fv_tt (open_tp_rec T p k).
Proof with eauto using fv_pp_open_pp_sub_fv_pp.
  intros.
  dependent induction T; simpl in *; try fsetdec...
Qed.

(* fvars_from env *)

Lemma fvar_from_env_aux :
  (forall E,
    wf_env E ->
    forall z x T,
      binds x (bind_val T) E \/ binds x (bind_typ T) E ->
      z `notin` dom E ->
      z `notin` fv_tp T /\ z `notin` fv_tt T) /\
  (forall E T,
    wf_typ E T ->
    forall z,
      z `notin` dom E ->
      z `notin` fv_tp T /\ z `notin` fv_tt T) /\
  (forall E T U,
    sub E T U ->
    forall z,
      z `notin` dom E ->
      z `notin` fv_tp T /\ z `notin` fv_tp U /\ z `notin` fv_tt T /\ z `notin` fv_tt U).
Proof with eauto 4 using fv_tp_sub_fv_tp_open_tv, fv_tp_sub_fv_tp_open_tt, fv_tt_sub_fv_tt_open_tv, fv_tt_sub_fv_tt_open_tt.
  apply wf_env_typ_sub_ind; intros; simpl in *...

  (* wf_env *)
  1,2: simpl in *; destruct H1; subst;
       analyze_binds H1; eauto;
       inversion BindsTacVal; subst...

  (* wf_typ *)
   enough (z <> x) by fsetdec;
   eapply binds_In in b; fsetdec.

   enough (z <> X) by fsetdec;
   eapply binds_In in b; fsetdec.

  1-4: pose proof (proj1 (H _ H0)); simpl in *; fsetdec.

  1-4: pick fresh x;
       specialize (H z H1);
       enough (z `notin` fv_tp T `union` fv_tt T) by (clear - H H2; fsetdec);
       assert (Temp: z `notin` dom ((x, bind_val S) :: E)) by (simpl; clear - H1 Fr; fsetdec);
       destruct (H0 x ltac:(fsetdec) z Temp) as [FvTp FvTt]...

  (* sub *)
  specialize (H0 z H1)...

  specialize (H z H1). specialize (H0 z H1).
  split; fsetdec.

  specialize (H z H0). simpl in H... pose proof (wf_env_binds_val_wf _ _ _ w b).

  repeat split; try (apply (H z x T); eauto); auto.
  apply binds_In in b; fsetdec.

  repeat split; try (apply (H z X T); eauto); auto.
  apply binds_In in b; fsetdec.

  1,2: destruct (H z H0); simpl in *; fsetdec.

  1,2: destruct (H z H0); repeat split; try fsetdec;
       [eapply fv_tp_open_tp_sub_fv_tp_pp | eapply fv_tt_open_tp_sub_fv_tt_pp];
       simpl; clear - H1 H2; fsetdec.

  1,2: specialize (H0 z H1); repeat split...

  (* sub_fun, sub_tfun, sub_pair, sub_tpair *)
  1,2:
  pick fresh x;
  assert (ZNotIn: z `notin` dom ((x, bind_val S2) :: E))
      by (destruct_notin; clear - H2 NotInTac; simpl; fsetdec); simpl in ZNotIn;
  destruct (H1 x ltac:(fsetdec) z ZNotIn) as
    [NotInT1OpenTp [NotInT2OpenTp [NotInT1OpenTt NotInT2OpenTt]]];
  destruct (H z H2) as [NotInS2Tp [NotInS1Tp [NotInS2Tt NotInS1Tt]]].

  3,4:
  pick fresh x;
  assert (z `notin` dom ((x, bind_val S2) :: E))
      by (destruct_notin; clear - H1 NotInTac; simpl; fsetdec);
   destruct (H0 x ltac:(fsetdec) z H2) as
    [NotInT1OpenTp [NotInT2OpenTp [NotInT1OpenTt NotInT2OpenTt]]];
   destruct (H z H1) as [NotinS2Tp [NotinS1Tp [NotinS2Tt NotinS1Tt]]].

  1,3,4:
  apply fv_tp_sub_fv_tp_open_tv in NotInT1OpenTp;
  apply fv_tp_sub_fv_tp_open_tv in NotInT2OpenTp;
  apply fv_tt_sub_fv_tt_open_tv in NotInT1OpenTt;
  apply fv_tt_sub_fv_tt_open_tv in NotInT2OpenTt...

  apply fv_tp_sub_fv_tp_open_tt in NotInT1OpenTp;
  apply fv_tp_sub_fv_tp_open_tt in NotInT2OpenTp;
  apply fv_tt_sub_fv_tt_open_tt in NotInT1OpenTt;
  apply fv_tt_sub_fv_tt_open_tt in NotInT2OpenTt...
Qed.

Lemma wf_typ_fv_tp_from_env : forall E T z,
  wf_typ E T ->
  z `notin` dom E ->
  z `notin` fv_tp T.
Proof with eauto.
  intros. apply (proj2 fvar_from_env_aux) with (E := E)...
Qed.

Lemma wf_typ_fv_tt_from_env : forall E T z,
  wf_typ E T ->
  z `notin` dom E ->
  z `notin` fv_tt T.
Proof with eauto.
  intros. apply (proj2 fvar_from_env_aux) with (E := E)...
Qed.

Lemma sub_fv_tp_from_env : forall E T U z,
  sub E T U ->
  z `notin` dom E ->
  z `notin` fv_tp T /\ z `notin` fv_tp U.
Proof with eauto.
  intros. pose proof (proj2 (proj2 fvar_from_env_aux)).
  specialize (H1 E T U H z H0)...
Qed.

Lemma sub_fv_tt_from_env : forall E T U z,
  sub E T U ->
  z `notin` dom E ->
  z `notin` fv_tt T /\ z `notin` fv_tt U.
Proof with eauto.
  intros. pose proof (proj2 (proj2 fvar_from_env_aux)).
  specialize (H1 E T U H z H0)...
Qed.

Hint Resolve wf_typ_fv_tp_from_env wf_typ_fv_tt_from_env sub_fv_tp_from_env sub_fv_tt_from_env : core.
