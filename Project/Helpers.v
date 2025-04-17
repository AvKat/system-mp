Require Export SystemMP.Project.Core.
Require Import Coq.Program.Equality.
Require Import Lia.

Lemma open_pp_path_ident : forall p q k,
  path p ->
  open_pp_rec p q k = p.
Proof with eauto.
  intros. dependent induction p; simpl in *; try f_equal...
  destruct v... inversion H...
  inversion H...
  inversion H...
Qed.

Lemma open_pv_path_ident : forall p x k,
  path p ->
  open_pv p x k = p.
Proof with eauto.
  intros. dependent induction p; simpl in *; try f_equal...
  destruct v... inversion H...
  inversion H...
  inversion H...
Qed.

(* Machinery for open_tv_type_ident *)

Hint Extern 1 => lia : core.

Inductive varN : nat -> var -> Prop :=
  | varN_b : forall n (m : nat),
      m < n ->
      varN n (var_b m)
  | varN_f : forall n (x : atom),
      varN n x.

Inductive pathN : nat -> pth -> Prop :=
  | pathN_var : forall n v,
      varN n v ->
      pathN n (pth_var v)
  | pathN_proj1 : forall n p,
      pathN n p ->
      pathN n (pth_proj1 p)
  | pathN_proj2 : forall n p,
      pathN n p ->
      pathN n (pth_proj2 p).

Inductive typeN : nat -> typ -> Prop :=
  | typeN_tvar : forall n v,
      varN n v ->
      typeN n (typ_tvar v)
  | typeN_top : forall n,
      typeN n typ_top
  | typeN_bot : forall n,
      typeN n typ_bot
  | typeN_arr : forall n T1 T2,
      typeN n T1 ->
      typeN (S n) T2 ->
      typeN n (typ_arr T1 T2)
  | typeN_all : forall n T1 T2,
      typeN n T1 ->
      typeN (S n) T2 ->
      typeN n (typ_all T1 T2)
  | typeN_path : forall n p,
      pathN n p ->
      typeN n (typ_path p)
  | typeN_path_Snd : forall n p,
      pathN n p ->
      typeN n (typ_path_Snd p)
  | typeN_vpair : forall n T1 T2,
      typeN n T1 ->
      typeN (S n) T2 ->
      typeN n (typ_pair T1 T2)
  | typeN_tpair : forall n T1 T2,
      typeN n T1 ->
      typeN (S n) T2 ->
      typeN n (typ_tpair T1 T2).

Hint Constructors varN typeN pathN : core.

Lemma varN_weakening : forall n m v,
  varN n v ->
  n <= m ->
  varN m v.
Proof with eauto.
  intros.
  induction H; constructor; lia.
Qed.

Lemma pathN_weakening : forall n m p,
  pathN n p ->
  n <= m ->
  pathN m p.
Proof with eauto.
  intros.
  induction H; constructor; eauto using varN_weakening.
Qed.

Lemma typeN_weakening : forall n m T,
  typeN n T ->
  n <= m ->
  typeN m T.
Proof with eauto using varN_weakening, pathN_weakening.
  intros. generalize dependent m.
  induction H; try constructor...
  all: apply IHtypeN2; lia.
Qed.

Lemma open_pv_pathN_aux : forall n x p,
  pathN n (open_pv p x n) ->
  pathN (S n) p.
Proof with eauto.
  intros. generalize dependent n.
  dependent induction p; intros; simpl in *; inversion H; subst...
  all: destruct v; eauto; destruct (n0 == n)...
  all: inversion H; subst; inversion H4; subst...
Qed.

Lemma open_tv_rec_typeN_aux : forall n x T,
  typeN n (open_tv_rec T x n) ->
  typeN (S n) T.
Proof with eauto using open_pv_pathN_aux.
  intros. generalize dependent n.
  dependent induction T; intros; simpl in *; inversion H; subst...
  inversion H2; subst...
  all: constructor...
  all: apply IHT2; replace (n + 1) with (S n) in H4 by lia...
Qed.

Lemma open_pv_pathN : forall n m v p,
  pathN n p ->
  m >= n ->
  p = open_pv p v m.
Proof with eauto using open_pv_pathN_aux, pathN_weakening.
  intros.
  generalize dependent m.
  generalize dependent n.
  induction p; intros; simpl in *; try f_equal...

  destruct v0...
  destruct (n0 == m); subst...
  inversion H; subst...
  inversion H3; subst...

  all: inversion H...
Qed.

Lemma open_tv_rec_typeN : forall n m v T,
  typeN n T ->
  m >= n ->
  T = open_tv_rec T v m.
Proof with eauto using open_tv_rec_typeN_aux, typeN_weakening, open_pv_pathN.
  intros.
  generalize dependent m.
  generalize dependent n.
  induction T; intros; simpl in *; try f_equal...
  all: inversion H; subst...
Qed.

Lemma open_tt_rec_typeN_aux : forall n T1 T2,
  typeN n (open_tt_rec T1 T2 n) ->
  typeN (S n) T1.
Proof with eauto using pathN_weakening.
  intros.
  dependent induction H; dependent induction T1; inversion x...

  destruct v0...
  destruct (n0 == n); subst...
  inversion H1; subst...
  constructor. constructor...
  inversion H; subst...

  all: try destruct v...
  all: try destruct (n0 == n); subst...
  all: try constructor...
  all: try solve [inversion H0; eauto];
        try solve [inversion H1; eauto];
        try solve [inversion H2; eauto].

  all: eapply IHtypeN2;
       replace (S n) with (n + 1) by lia...
Qed.

Lemma open_tt_rec_typeN : forall n m S T,
  typeN n T ->
  m >= n ->
  T = open_tt_rec T S m.
Proof with eauto using open_tt_rec_typeN_aux.
  intros n m S T.
  generalize dependent m.
  generalize dependent n.
  induction T; intros * H1 H2; simpl; inversion H1; inversion H; subst; f_equal...

  destruct v; simpl in *...
  destruct (n0 == m); subst...
  inversion H3; subst...

  all: eapply IHT2...
Qed.

Lemma path_to_path0 : forall p,
  path p ->
  pathN 0 p.
Proof with eauto using open_pv_pathN_aux.
  intros. dependent induction p; simpl in *; try constructor...
  all: inversion H; subst...
Qed.

Lemma type_to_type0 : forall T,
  type T -> typeN 0 T.
Proof with eauto using open_tv_rec_typeN_aux, path_to_path0, open_tt_rec_typeN_aux.
  intros. dependent induction H...
  all: constructor; pick fresh x...
Qed.

Lemma open_tt_type_indent : forall T U k,
  type T ->
  T = open_tt_rec T U k.
Proof with eauto using open_tt_rec_typeN.
  intros.
  apply type_to_type0 in H.
  eapply open_tt_rec_typeN in H...
Qed.

Lemma open_tv_type_ident : forall T x k,
  type T ->
  open_tv_rec T x k = T.
Proof with eauto using open_tv_rec_typeN.
  intros. apply type_to_type0 in H.
  eapply open_tv_rec_typeN in H...
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

Lemma subst_pp_open_pv_commute_fresh : forall z x (p q: pth) k,
  path p ->
  x `notin` fv_pp q `union` {{ z }} ->
  subst_pp z p (open_pv q x k) = open_pv (subst_pp z p q) x k.
Proof with eauto.
  intros. generalize dependent k.
  dependent induction q; simpl in *; intros; try f_equal...
  destruct v; simpl in *...
  - destruct (n == k)...
    simpl...
    destruct (x == z); try fsetdec.
  - destruct (a == z)...
    rewrite open_pv_path_ident...
Qed.

Lemma subst_tp_open_tv_commute_fresh : forall z k x (p: pth) T,
  path p ->
  x `notin` fv_tp T `union` {{ z }} ->
  subst_tp z p (open_tv_rec T x k) = open_tv_rec (subst_tp z p T) x k.
Proof with eauto using subst_pp_open_pv_commute_fresh.
  intros.
  generalize dependent k.
  dependent induction T; simpl; intros; try (simpl in H0;f_equal;eauto)...
Qed.

Lemma subst_tt_open_tv_commute_fresh : forall Z S T x k,
  type S ->
  subst_tt Z S (open_tv_rec T x k) = open_tv_rec (subst_tt Z S T) x k.
Proof with eauto.
  intros. generalize dependent k.
  dependent induction T; simpl in *; intros; try f_equal...
  destruct v; simpl in *...
  destruct (a == Z); try fsetdec...
  rewrite open_tv_type_ident...
Qed.

Lemma subst_tp_open_tt_commute : forall z X k (p : pth) T,
  subst_tp z p (open_tt_rec T (typ_tvar X) k) = open_tt_rec (subst_tp z p T) (typ_tvar X) k.
Proof with eauto.
  intros. generalize dependent k.
  dependent induction T; simpl; intros; try f_equal...
  destruct v; simpl in *...
  destruct (n == k)...
Qed.

Lemma subst_pp_open_pp_commute : forall z k (p q : pth) T,
  path p ->
  subst_pp z p (open_pp_rec T q k) = open_pp_rec (subst_pp z p T) (subst_pp z p q) k.
Proof with eauto.
  intros. generalize dependent k.
  dependent induction T; simpl; intros; try f_equal...
  destruct v; simpl in *...
  - destruct (n == k)...
  - destruct (a == z); try fsetdec.
    rewrite open_pp_path_ident...
Qed.

Lemma subst_tp_open_tp_commute : forall z k (p q : pth) T,
  path p ->
  subst_tp z p (open_tp_rec T q k) = open_tp_rec (subst_tp z p T) (subst_pp z p q) k.
Proof with eauto using subst_pp_open_pp_commute.
  intros. generalize dependent k.
  dependent induction T; simpl; intros; try f_equal...
Qed.

Lemma subst_pp_open_pv_is_open_pp : forall z p q k,
  z `notin` fv_pp q ->
  subst_pp z p (open_pv q z k) = open_pp_rec q p k.
Proof with eauto.
  intros. generalize dependent k.
  dependent induction q; intros; simpl; try f_equal...
  destruct v; simpl in *...
  - destruct (n == k)...
    simpl...
    destruct (z == z); try fsetdec.
  - destruct (a == z); try fsetdec.
Qed.

Lemma subst_tp_open_tv_is_open_tp : forall z p T k,
  z `notin` fv_tp T ->
  subst_tp z p (open_tv_rec T z k) = open_tp_rec T p k.
Proof with eauto using subst_pp_open_pv_is_open_pp.
  intros. generalize dependent k.
  dependent induction T; intros; simpl in *; try f_equal...
Qed.

(* Well-formedness *)

Lemma wf_env_strengthen_head : forall E F,
  wf_env (E ++ F) ->
  wf_env F.
Proof with eauto.
  intros. dependent induction E...
  simpl in H. inversion H; subst...
Qed.
