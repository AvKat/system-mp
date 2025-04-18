Require Export SystemMP.Project.Infrastructure.
Require Export SystemMP.Project.Narrowing.
Require Import Coq.Program.Equality.

(* Lemma 4.1 *)
Theorem inversion_sub_top : forall E T,
  sub E typ_top T ->
  T = typ_top.
Proof with eauto.
  intros. dependent induction H...
Qed.

(* Lemma 4.2 *)
Theorem inversion_sub_fun : forall E S T U,
  sub E (typ_arr S T) U ->
  U = typ_top \/
  exists L S' T',
    U = typ_arr S' T' /\
    sub E S' S /\
    (forall z, z `notin` L ->
      sub ((z, bind_val S') :: E) (open_tp T z) (open_tp T' z)).
Proof with eauto.
  intros.
  dependent induction H...
  - inversion H0; subst...
    right.
    exists L, S, T; repeat split...
  - destruct (IHsub1 S T ltac:(auto)) as [Htop | Hfun]; subst...
    { apply inversion_sub_top in H0; subst... }
    destruct Hfun as (L' & S' & T' & H1 & H2 & H3); subst...
    destruct (IHsub2 S' T' ltac:(auto)) as [Htop' | Hfun']...
    right.
    destruct Hfun' as (L'' & S'' & T'' & H4 & H5 & H6); subst...
    exists (L' `union` L''), S'', T''...
    repeat split...
    intros.
    specialize (H3 z ltac:(fsetdec)).
    specialize (H6 z ltac:(fsetdec)).
    eauto using sub_narrow_val.
  - right.
    exists L, S2, T2; repeat split...
Qed.

(* Lemma 4.5 *)
Theorem inversion_typing_path : forall E (p: pth) T,
  typing E p T ->
  wf_typ E p /\ sub E p T.
Proof with eauto.
  intros. dependent induction H...
  specialize (IHtyping p ltac:(auto)).
  crush.
  eapply sub_trans...
Qed.
