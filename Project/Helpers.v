Require Import SystemMP.Project.Inversion.
Require Import Coq.Program.Equality.

(* Well-formedness *)

Lemma sub_env_wf : forall E T U,
  sub E T U ->
  wf_env E.
Proof with eauto.
  intros. dependent induction H...
Qed.

Lemma wf_env_strengthen_head : forall E F,
  wf_env (E ++ F) ->
  wf_env F.
Proof with eauto.
  intros. dependent induction E...
  simpl in H. inversion H; subst...
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

Lemma subst_pp_path : forall z p q,
  path p ->
  path q ->
  path (subst_pp z p q).
Proof with eauto.
  intros. dependent induction H0; simpl...
  destruct (x == z)...
Qed.

(* Substitution lemmas *)

Lemma open_path_ident : forall p q k,
  path p ->
  open_pp_rec p q k = p.
Proof with eauto.
  intros. dependent induction p; simpl in *; try f_equal...
  destruct v... inversion H...
  inversion H...
  inversion H...
Qed.

Lemma subst_pp_fresh : forall z p q,
  z `notin` fv_pp q ->
  subst_pp z p q = q.
Proof with eauto.
  intros. dependent induction q; simpl in *; try f_equal...
  destruct v...
  destruct (a == z)...
  fsetdec.
Qed.

Lemma subst_tp_fresh : forall z p T,
  z `notin` fv_tp T ->
  subst_tp z p T = T.
Proof with eauto using subst_pp_fresh.
  intros. dependent induction T; simpl in *; try f_equal...
Qed.

Lemma subst_tp_open_tv_rec : forall z k x (p: pth) T,
  path p ->
  x `notin` fv_tp T `union` {{ z }} ->
  subst_tp z p (open_tv_rec T x k) = open_tv_rec (subst_tp z p T) x k.
Proof with eauto.
  intros.
  generalize dependent k.
  dependent induction T; simpl; intros; try (simpl in H0;f_equal;eauto)...
  destruct p0...
  destruct v; simpl...
  + destruct (n == k)...
    simpl.
    destruct (x == z)...
    fsetdec.
  + destruct (a == z)...
    inversion H...
Lemma subst_pp_open_pv_is_open_pp : forall z (p q: pth) k,
  z `notin` fv_tp q ->
  subst_pp z p (open_pv q z k) = open_pp_rec q p k.
Proof with eauto.
  intros. generalize dependent k.
  dependent induction q; simpl in *; intros; try f_equal...
  destruct v; simpl in *...
  destruct (n == k)...
  simpl...
  destruct (z == z); try fsetdec.
  destruct (a == z); try fsetdec.
Qed.

Lemma subst_tp_open_tpv_is_open_tp : forall z p T k,
  z `notin` fv_tp T ->
  subst_tp z p (open_tpv_rec T z k) = open_tp_rec T p k.
Proof with eauto using subst_pp_open_pv_is_open_pp.
  intros. generalize dependent k.
  dependent induction T; simpl in *; intros; try f_equal...
Qed.

Lemma subst_pp_open_pp_rec : forall z k (p q p0 : pth),
  path p ->
  subst_pp z p (open_pp_rec p0 q k) = open_pp_rec (subst_pp z p p0) (subst_pp z p q) k.
Proof with eauto.
  intros.
  generalize dependent k.
  dependent induction p0; simpl in *; intros; try f_equal...
  destruct v; simpl in *...
  destruct (n == k)...
  destruct (a == z)...
  rewrite open_path_ident...
Qed.

Lemma subst_tp_open_tp_rec : forall z k (p q : pth) T,
  path p ->
  subst_tp z p (open_tp_rec T q k) = open_tp_rec (subst_tp z p T) (subst_pp z p q) k.
Proof with eauto using subst_pp_open_pp_rec.
  intros.
  generalize dependent k.
  dependent induction T; simpl in *; intros; try f_equal...
Qed.

(* fv subset lemmas *)

Lemma fv_pp_open_pp_sub_fv_pp : forall p q z k,
  z `notin` fv_pp q `union` fv_pp p ->
  z `notin` fv_pp (open_pp_rec p q k).
Proof with eauto.
  intros.
  dependent induction p; simpl in *; try fsetdec...
  destruct v...
  destruct (n == k)...
Qed.

Lemma fv_tp_open_tp_sub_fv_tp_pp : forall T p k z,
  z `notin` fv_tp T `union` fv_pp p ->
  z `notin` fv_tp (open_tp_rec T p k).
Proof with eauto.
  intros.
  dependent induction T; simpl in *; try fsetdec...
  - eapply fv_pp_open_pp_sub_fv_pp...
  - eapply fv_pp_open_pp_sub_fv_pp...
Qed.

Lemma fv_tp_sub_fv_tp_open_tv : forall T x z k,
  z `notin` fv_tp (open_tv_rec T x k) ->
  z `notin` fv_tp T.
Proof with eauto.
  intros. dependent induction T; simpl in *; try fsetdec...
  destruct p...
  destruct v...
Qed.

(* fvars_from env *)

Lemma fvar_from_env_aux :
  (forall E,
    wf_env E ->
    forall z x T,
      binds x (bind_val T) E \/ binds x (bind_typ T) E ->
      z `notin` dom E ->
      z `notin` fv_tp T) /\
  (forall E T,
    wf_typ E T ->
    forall z,
      z `notin` dom E ->
      z `notin` fv_tp T) /\
  (forall E T U,
    sub E T U ->
    forall z,
      z `notin` dom E ->
      z `notin` fv_tp T /\ z `notin` fv_tp U).
Proof with eauto 4.
  apply wf_env_typ_sub_ind; intros; simpl in *...

  (* wf_env *)
  {
   simpl in *. destruct H1; subst.
    + analyze_binds H1...
      inversion BindsTacVal; subst...
    + analyze_binds H1...
      }

  {
  simpl in *. destruct H1; subst.
    + analyze_binds H1...
    + analyze_binds H1...
      inversion BindsTacVal; subst...
      }

  (* wf_typ *)
  2: rename X into x.
  1,2: enough (z <> x) by fsetdec;
       eapply binds_In in b; fsetdec.

  1-4: pose proof (proj1 (H _ H0)); simpl in *; fsetdec.

  1-4: pick fresh x;
       specialize (H z H1);
       enough (z `notin` fv_tp T) by (clear - H H2; fsetdec);
       assert (Temp: z `notin` dom ((x, bind_val S) :: E)) by (simpl; fsetdec);
       specialize (H0 x ltac:(fsetdec) z Temp);
       eapply fv_tp_sub_fv_tp_open_tv...

  (* sub *)
  specialize (H z H1). specialize (H0 z H1).
  split; fsetdec.

  specialize (H z H0). simpl in H...

  pose proof (wf_env_binds_val_wf _ _ _ w b).
  2: rename X into x;
     pose proof (wf_env_binds_typ_wf _ _ _ w b).
  1,2: split; [apply binds_In in b; fsetdec | apply (H z x T); eauto].

  1,2: destruct (H z H0); simpl in *; fsetdec.

  1,2: destruct (H z H0); split; try fsetdec; eapply fv_tp_open_tp_sub_fv_tp_pp; simpl; fsetdec.

  all: pick fresh x; 
       assert (z `notin` dom ((x, bind_val S2) :: E))
          by (destruct_notin; clear - H1 NotInTac; simpl; fsetdec);
       destruct (H0 x ltac:(fsetdec) z H2) as [T1Open T2Open];
       destruct (H z H1) as [NotinS2 NotinS1];
       apply fv_tp_sub_fv_tp_open_tv in T1Open;
       apply fv_tp_sub_fv_tp_open_tv in T2Open;
       clear - NotinS1 NotinS2 T1Open T2Open; fsetdec.
Admitted.

Lemma wf_typ_fvar_from_env : forall E T z,
  wf_typ E T ->
  z `notin` dom E ->
  z `notin` fv_tp T.
Proof with eauto.
  intros. apply (proj2 fvar_from_env_aux) with (E := E)...
Qed.

Lemma sub_fvar_from_env : forall E T U z,
  sub E T U ->
  z `notin` dom E ->
  z `notin` fv_tp T /\ z `notin` fv_tp U.
Proof with eauto.
  intros. apply (proj2 fvar_from_env_aux) with (E := E)...
Qed.
