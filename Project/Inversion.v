Require Export SystemMP.Project.Infrastructure.
Require Import Coq.Program.Equality.

(* Lemma 4.1 *)

Theorem inversion_sub_top : forall E T,
  sub E typ_top T ->
  T = typ_top.
Proof with eauto.
  intros. dependent induction H...
Qed.

(* Lemma 4.2 *)
(* Theorem inversion_sub_fun : forall E S T U, *)
(*   sub E (typ_arr S T) U -> *)
(*   U = typ_top \/ *)
(*   exists S' T', *)
(*     U = typ_arr S' T' /\ *)
(*     sub E S' S /\ *)
(*     (forall z, z `notin` dom E -> sub ((z, bind_val S) :: E) T T'). *)
(* Proof with eauto using wf_env_weaken_val, wf_typ_weaken_val, sub_weaken_val. *)
(*   intros. dependent induction H... *)
(*   - right. *)
(*     inversion H0; subst. *)
(*     exists S, T; crush. *)
(*     eapply sub_refl; rewrite_env (nil ++ (z, bind_val S):: E)... *)
(*     apply wf_typ_weaken_val... *)

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
