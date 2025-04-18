Require Export SystemMP.Meta.MetatheoryAtom.
Require Export SystemMP.Meta.Metatheory.

Inductive var : Set :=
  | var_b : nat -> var
  | var_f : atom -> var.

Coercion var_f : atom >-> var.

Inductive pth : Set :=
  | pth_var : var -> pth
  | pth_proj1 : pth -> pth
  | pth_proj2 : pth -> pth.

Coercion pth_var : var >-> pth.

Inductive typ : Type :=
  | typ_tvar : var -> typ
  | typ_top : typ
  | typ_bot : typ
  | typ_arr : typ -> typ -> typ
  | typ_all : typ -> typ -> typ
  | typ_pair : typ -> typ -> typ
  | typ_tpair : typ -> typ -> typ
  | typ_path : pth -> typ
  | typ_path_Snd : pth -> typ.

Coercion typ_path : pth >-> typ.

Inductive exp : Type :=
  | exp_path : pth -> exp
  | exp_app : pth -> pth -> exp
  | exp_tapp : pth -> typ -> exp
  | exp_abs : typ -> exp -> exp
  | exp_tabs : typ -> exp -> exp
  | exp_pair : var -> var -> exp
  | exp_tpair : var -> typ -> exp
  | exp_let : exp -> exp -> exp.

Coercion exp_path : pth >-> exp.

(* Opening functions *)
(* Convention: open_xy "puts" y in x *)

(* Open with a path *)

Fixpoint open_pp (p : pth) (q : pth) (k : nat) : pth :=
  match p with
  | pth_var (var_b n) => if n === k then q else p
  | pth_var (var_f _) => p
  | pth_proj1 p => pth_proj1 (open_pp p q k)
  | pth_proj2 p => pth_proj2 (open_pp p q k)
  end.

Fixpoint open_tp_rec (T : typ) (p : pth) (k : nat) : typ :=
  match T with
  | typ_tvar _ => T
  | typ_top => T
  | typ_bot => T
  | typ_arr R T => typ_arr (open_tp_rec R p k) (open_tp_rec T p (k+1))
  | typ_all R T => typ_all (open_tp_rec R p k) (open_tp_rec T p (k+1))
  | typ_pair R T => typ_pair (open_tp_rec R p k) (open_tp_rec T p (k+1))
  | typ_tpair R T => typ_tpair (open_tp_rec R p k) (open_tp_rec T p (k+1))
  | typ_path p' => typ_path (open_pp p' p k)
  | typ_path_Snd p' => typ_path_Snd (open_pp p' p k)
  end.

(* Open with a type *)

Fixpoint open_tt_rec (T : typ) (U : typ) (k : nat) : typ :=
  match T with
  | typ_tvar (var_f _) => T
  | typ_tvar (var_b n) => if n === k then U else T
  | typ_top => T
  | typ_bot => T
  | typ_arr R T => typ_arr (open_tt_rec R U k) (open_tt_rec T U (k+1))
  | typ_all R T => typ_all (open_tt_rec R U k) (open_tt_rec T U (k+1))
  | typ_pair R T => typ_pair (open_tt_rec R U k) (open_tt_rec T U (k+1))
  | typ_tpair R T => typ_tpair (open_tt_rec R U k) (open_tt_rec T U (k+1))
  | typ_path _ => T
  | typ_path_Snd _ => T
  end.

(* Open with a variable *)

Definition open_vv (x : var) (V : var) (k : nat) : var :=
  match x with
  | var_f _ => x
  | var_b n => if n === k then V else x
  end.

Fixpoint open_ev_rec (E : exp) (V : var) (k : nat) : exp :=
  match E with
  | exp_path p => exp_path (open_pp p V k)
  | exp_app p1 p2 => exp_app (open_pp p1 V k) (open_pp p2 V k)
  | exp_tapp p T => exp_tapp (open_pp p V k) (open_tp_rec T V k)
  | exp_abs T e => exp_abs (open_tp_rec T V k) (open_ev_rec e V (k+1))
  | exp_tabs T e => exp_tabs (open_tp_rec T V k) (open_ev_rec e V (k+1))
  | exp_pair x y => exp_pair (open_vv x V k) (open_vv y V k)
  | exp_tpair x T => exp_tpair (open_vv x V k) (open_tp_rec T V k)
  | exp_let e1 e2 => exp_let (open_ev_rec e1 V k) (open_ev_rec e2 V (k+1))
  end.

(* Definition open_pp p q := open_pp_rec p q 0. *)
Definition open_tp T p := open_tp_rec T p 0.
Definition open_tt (T : typ) (U : typ) : typ := open_tt_rec T U 0.
Definition open_ev (e : exp) (V : var) := open_ev_rec e V 0.

Inductive path : pth -> Prop :=
  | path_var : forall (x: atom), path (pth_var x)
  | path_proj1 : forall p, path p -> path (pth_proj1 p)
  | path_proj2 : forall p, path p -> path (pth_proj2 p).

Inductive type : typ -> Prop :=
  | type_tvar : forall (X : atom), type (typ_tvar X)
  | type_top : type typ_top
  | type_bot : type typ_bot
  | type_arr : forall T1 T2 L,
      type T1 ->
      (forall x, x `notin` L -> type (open_tp T2 x)) ->
      type (typ_arr T1 T2)
  | type_all : forall T1 T2 L,
      type T1 ->
      (forall X, X `notin` L -> type (open_tt T2 (typ_tvar X))) ->
      type (typ_all T1 T2)
  | type_path : forall p, path p -> type p
  | type_path_Snd : forall p, path p -> type (typ_path_Snd p)
  | type_vpair : forall T1 T2 L,
      type T1 ->
      (forall x, x `notin` L -> type (open_tp T2 x)) ->
      type (typ_pair T1 T2)
  | type_tpair : forall T1 T2 L,
      type T1 ->
      (forall x, x `notin` L -> type (open_tp T2 x)) ->
      type (typ_tpair T1 T2).

Inductive expr : exp -> Prop :=
  | expr_path : forall p, path p -> expr (exp_path p)
  | expr_app : forall p1 p2, path p1 -> path p2 -> expr (exp_app p1 p2)
  | expr_tapp : forall p T, path p -> type T -> expr (exp_tapp p T)
  | expr_abs : forall T e L,
      type T ->
      (forall x, x `notin` L -> expr (open_ev e x)) ->
      expr (exp_abs T e)
  | expr_tabs : forall T e L,
      type T ->
      (forall X, X `notin` L -> expr (open_ev e X)) ->
      expr (exp_tabs T e)
  | expr_vpair : forall x y, expr (exp_pair x y)
  | expr_tpair : forall x T, type T -> expr (exp_tpair x T)
  | expr_let : forall e1 e2 L,
      expr e1 ->
      (forall x, x `notin` L -> expr (open_ev e2 x)) ->
      expr (exp_let e1 e2).

(* Defining environments, well-formdness and subtyping *)

Inductive binding : Set :=
  | bind_val : typ -> binding
  | bind_typ : typ -> binding.

Definition env := list (atom * binding).
Definition emap (f : binding -> binding) (E : env) : env := @EnvImpl.map _ _ f E.

Inductive wf_typ : env -> typ -> Prop :=
  | w_var : forall E x T,
      wf_env E ->
      binds x (bind_val T) E ->
      wf_typ E x
  | w_tvar : forall E X T,
      wf_env E ->
      binds X (bind_typ T) E ->
      wf_typ E (typ_tvar X)
  | w_fst : forall (p: pth) S T E,
      path p ->
      sub E p (typ_pair S T) ->
      wf_typ E (pth_proj1 p)
  | w_tfst : forall (p: pth) S T E,
      path p ->
      sub E p (typ_tpair S T) ->
      wf_typ E (pth_proj1 p)
  | w_snd : forall (p: pth) S T E,
      path p ->
      sub E p (typ_pair S T) ->
      wf_typ E (pth_proj2 p)
  | w_tsnd : forall E (p : pth) S T,
      path p ->
      sub E p (typ_tpair S T) ->
      wf_typ E (typ_path_Snd p)
  | w_top : forall E,
      wf_env E ->
      wf_typ E typ_top
  | w_bot : forall E,
      wf_env E ->
      wf_typ E typ_bot
  | w_fun : forall L E S T,
      wf_typ E S ->
      (forall x, x `notin` L -> wf_typ ((x, bind_val S) :: E) (open_tp T x)) ->
      wf_typ E (typ_arr S T)
  | w_tfun : forall L E S T,
      wf_typ E S ->
      (forall X, X `notin` L -> wf_typ ((X, bind_typ S) :: E) (open_tt T (typ_tvar X))) ->
      wf_typ E (typ_all S T)
  | w_pair : forall L E S T,
      wf_typ E S ->
      (forall x, x `notin` L -> wf_typ ((x, bind_val S) :: E) (open_tp T x)) ->
      wf_typ E (typ_pair S T)
  | w_tpair : forall L E S T,
      wf_typ E S ->
      (forall x, x `notin` L -> wf_typ ((x, bind_val S) :: E) (open_tp T x)) ->
      wf_typ E (typ_tpair S T)

with wf_env : env -> Prop :=
  | w_nil : wf_env nil
  | w_val : forall E x T,
      wf_env E ->
      wf_typ E T ->
      x `notin` dom E ->
      wf_env ((x, bind_val T) :: E)
  | w_typ : forall E X T,
      wf_env E ->
      wf_typ E T ->
      X `notin` dom E ->
      wf_env ((X, bind_typ T) :: E)

with sub : env -> typ -> typ -> Prop :=
  | sub_refl : forall E T,
      wf_env E ->
      wf_typ E T ->
      sub E T T
  | sub_trans : forall E S T U,
      sub E S T ->
      sub E T U ->
      sub E S U
  | sub_symm : forall E p q,
      path p ->
      path q ->
      sub E p q ->
      sub E q p
  | sub_var : forall E x T,
      wf_env E ->
      binds x (bind_val T) E ->
      sub E x T
  | sub_tvar : forall E X T,
      wf_env E ->
      binds X (bind_typ T) E ->
      sub E (typ_tvar X) T
  | sub_fst : forall E (p : pth) S T,
      path p ->
      sub E p (typ_pair S T) ->
      sub E (pth_proj1 p) S
  | sub_tfst : forall E (p : pth) S T,
      path p ->
      sub E p (typ_tpair S T) ->
      sub E (pth_proj1 p) S
  | sub_snd : forall E (p : pth) S T,
      path p ->
      sub E p (typ_pair S T) ->
      sub E (pth_proj2 p) (open_tp T (pth_proj1 p))
  | sub_tsnd : forall E (p : pth) S T,
      path p ->
      sub E p (typ_tpair S T) ->
      sub E (typ_path_Snd p) (open_tp T (pth_proj1 p))
  | sub_bot : forall E T,
      wf_env E ->
      wf_typ E T ->
      sub E typ_bot T
  | sub_top : forall E T,
      wf_env E ->
      wf_typ E T ->
      sub E T typ_top
  | sub_fun : forall L E S1 S2 T1 T2,
      sub E S2 S1 ->
      wf_typ E (typ_arr S1 T1) ->
      (forall x, x `notin` L -> sub ((x, bind_val S2) :: E) (open_tp T1 x) (open_tp T2 x)) ->
      sub E (typ_arr S1 T1) (typ_arr S2 T2)
  | sub_tfun : forall L E S1 S2 T1 T2,
      sub E S2 S1 ->
      wf_typ E (typ_all S1 T1) ->
      (forall X, X `notin` L -> sub ((X, bind_typ S2) :: E) (open_tt T1 (typ_tvar X)) (open_tt T2 (typ_tvar X))) ->
      sub E (typ_all S1 T1) (typ_all S2 T2)
  | sub_pair : forall L E S1 S2 T1 T2,
      sub E S1 S2 ->
      (forall x, x `notin` L -> sub ((x, bind_val S2) :: E) (open_tp T1 x) (open_tp T2 x)) ->
      sub E (typ_pair S1 T1) (typ_pair S2 T2)
  | sub_tpair : forall L E S1 S2 T1 T2,
      sub E S1 S2 ->
      (forall x, x `notin` L -> sub ((x, bind_val S2) :: E) (open_tp T1 x) (open_tp T2 x)) ->
      sub E (typ_tpair S1 T1) (typ_tpair S2 T2).

Inductive typing : env -> exp -> typ -> Prop :=
  | t_path : forall E (p: pth),
      wf_env E ->
      wf_typ E p ->
      typing E (exp_path p) p
  | t_sub : forall E e S T,
      typing E e S ->
      sub E S T ->
      typing E e T
  | t_abs : forall L E S T e,
      wf_typ E S ->
      (forall x, x `notin` L -> typing ((x, bind_val S) :: E) (open_ev e x) (open_tp T x)) ->
      typing E (exp_abs S e) (typ_arr S T)
  | t_app : forall E (p q : pth) S T,
      typing E p (typ_arr S T) ->
      typing E q S ->
      typing E (exp_app p q) (open_tp T q)
  | t_tabs : forall L E S T e,
      wf_typ E S ->
      (forall X, X `notin` L -> typing ((X, bind_typ S) :: E) (open_ev e X) (open_tt T (typ_tvar X))) ->
      typing E (exp_tabs S e) (typ_all S T)
  | t_tapp : forall E (e : pth) R S T,
      typing E e (typ_all S T) ->
      sub E R S ->
      typing E (exp_tapp e R) (open_tt T R)
  | t_pair : forall L E (x y : atom) S T,
      typing E (exp_path x) S ->
      (forall z, z `notin` L -> wf_typ ((z, bind_val S) :: E) (open_tp T z)) ->
      typing E (exp_path y) (open_tp T x) ->
      typing E (exp_pair x y) (typ_pair S T)
  | t_tpair : forall L E (x : atom) R S T,
      typing E (exp_path x) S ->
      (forall z, z `notin` L -> wf_typ ((z, bind_val S) :: E) (open_tp T z)) ->
      sub E R (open_tp T x) ->
      typing E (exp_tpair x R) (typ_tpair S T)
  | t_let : forall L E e1 e2 S T,
      typing E e1 S ->
      wf_typ E T ->
      (forall x, x `notin` L -> typing ((x, bind_val S) :: E) (open_ev e2 x) (open_tp T x)) ->
      typing E (exp_let e1 e2) T.

Hint Constructors path type expr wf_typ wf_env sub typing : core.

Scheme wf_env_all_mutind := Induction for wf_env Sort Prop
  with wf_typ_all_mutind := Induction for wf_typ Sort Prop
  with sub_all_mutind := Induction for sub Sort Prop.

Combined Scheme wf_env_typ_sub_ind from wf_env_all_mutind, wf_typ_all_mutind, sub_all_mutind.

(* Substitution functions *)

Fixpoint subst_pp (z : atom) (p1 p : pth) {struct p} : pth :=
  match p with
  | pth_var (var_b _) => p
  | pth_var (var_f x) => if x == z then p1 else p
  | pth_proj1 p => pth_proj1 (subst_pp z p1 p)
  | pth_proj2 p => pth_proj2 (subst_pp z p1 p)
  end.

Fixpoint subst_tp (z : atom) (p : pth) (T : typ) {struct T} : typ :=
  match T with
  | typ_tvar _ => T
  | typ_top => T
  | typ_bot => T
  | typ_arr T1 T2 => typ_arr (subst_tp z p T1) (subst_tp z p T2)
  | typ_all T1 T2 => typ_all (subst_tp z p T1) (subst_tp z p T2)
  | typ_pair T1 T2 => typ_pair (subst_tp z p T1) (subst_tp z p T2)
  | typ_tpair T1 T2 => typ_tpair (subst_tp z p T1) (subst_tp z p T2)
  | typ_path p' => typ_path (subst_pp z p p')
  | typ_path_Snd p' => typ_path_Snd (subst_pp z p p')
  end.

Fixpoint subst_tt (z : atom) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_tvar (var_f x) => if x == z then U else T
  | typ_tvar (var_b _) => T
  | typ_top => T
  | typ_bot => T
  | typ_arr T1 T2 => typ_arr (subst_tt z U T1) (subst_tt z U T2)
  | typ_all T1 T2 => typ_all (subst_tt z U T1) (subst_tt z U T2)
  | typ_pair T1 T2 => typ_pair (subst_tt z U T1) (subst_tt z U T2)
  | typ_tpair T1 T2 => typ_tpair (subst_tt z U T1) (subst_tt z U T2)
  | typ_path _ => T
  | typ_path_Snd _ => T
  end.

Definition subst_vv (z : atom) (V : var) (x : var) : var :=
  match x with
  | var_f y => if y == z then V else x
  | var_b n => x
  end.

Fixpoint subst_ev (z : atom) (V : var) (e : exp) {struct e} : exp :=
  match e with
  | exp_path p => exp_path (subst_pp z V p)
  | exp_app p1 p2 => exp_app (subst_pp z V p1) (subst_pp z V p2)
  | exp_tapp p T => exp_tapp (subst_pp z V p) (subst_tp z V T)
  | exp_abs T e => exp_abs (subst_tp z V T) (subst_ev z V e)
  | exp_tabs T e => exp_tabs (subst_tp z V T) (subst_ev z V e)
  | exp_pair x y => exp_pair (subst_vv z V x) (subst_vv z V y)
  | exp_tpair x T => exp_tpair (subst_vv z V x) (subst_tp z V T)
  | exp_let e1 e2 => exp_let (subst_ev z V e1) (subst_ev z V e2)
  end.

Fixpoint subst_et (z : atom) (T : typ) (e : exp) {struct e} : exp :=
  match e with
  | exp_path _ => e
  | exp_app _ _ => e
  | exp_tapp p T' => exp_tapp p (subst_tt z T T')
  | exp_abs T' e => exp_abs (subst_tt z T T') (subst_et z T e)
  | exp_tabs T' e => exp_tabs (subst_tt z T T') (subst_et z T e)
  | exp_pair x y => exp_pair x y
  | exp_tpair x T' => exp_tpair x (subst_tt z T T')
  | exp_let e1 e2 => exp_let (subst_et z T e1) (subst_et z T e2)
  end.

Definition subst_bp (z : atom) (p : pth) (b : binding) : binding :=
  match b with
  | bind_typ T => bind_typ (subst_tp z p T)
  | bind_val T => bind_val (subst_tp z p T)
  end.

Definition subst_bt (z : atom) (T : typ) (b : binding) : binding :=
  match b with
  | bind_typ T' => bind_typ (subst_tt z T T')
  | bind_val T' => bind_val (subst_tt z T T')
  end.

(* Free variables *)

Definition fv_vv (x : var) : atoms :=
  match x with
  | var_f y => singleton y
  | var_b n => {}
  end.

Fixpoint fv_tt (T : typ) : atoms :=
  match T with
  | typ_tvar v => fv_vv v
  | typ_top => {}
  | typ_bot => {}
  | typ_arr T1 T2 => (fv_tt T1) `union` (fv_tt T2)
  | typ_all T1 T2 => (fv_tt T1) `union` (fv_tt T2)
  | typ_pair T1 T2 => (fv_tt T1) `union` (fv_tt T2)
  | typ_tpair T1 T2 => (fv_tt T1) `union` (fv_tt T2)
  | typ_path p => {}
  | typ_path_Snd p => {}
  end.

Fixpoint fv_pp (p : pth) : atoms :=
  match p with
  | pth_var v => fv_vv v
  | pth_proj1 p => fv_pp p
  | pth_proj2 p => fv_pp p
  end.

Fixpoint fv_tp (T : typ) : atoms :=
  match T with
  | typ_tvar _ => {}
  | typ_top => {}
  | typ_bot => {}
  | typ_arr T1 T2 => (fv_tp T1) `union` (fv_tp T2)
  | typ_all T1 T2 => (fv_tp T1) `union` (fv_tp T2)
  | typ_pair T1 T2 => (fv_tp T1) `union` (fv_tp T2)
  | typ_tpair T1 T2 => (fv_tp T1) `union` (fv_tp T2)
  | typ_path p => fv_pp p
  | typ_path_Snd p => fv_pp p
  end.

Fixpoint fv_ep (e : exp) : atoms :=
  match e with
  | exp_path p => fv_pp p
  | exp_app p1 p2 => (fv_pp p1) `union` (fv_pp p2)
  | exp_tapp p T => (fv_pp p) `union` (fv_tp T)
  | exp_abs T e => (fv_tp T) `union` (fv_ep e)
  | exp_tabs T e => (fv_tp T) `union` (fv_ep e)
  | exp_pair x y => fv_vv x `union` fv_vv y
  | exp_tpair x T => fv_vv x `union` (fv_tp T)
  | exp_let e1 e2 => (fv_ep e1) `union` (fv_ep e2)
  end.

(* Tactics *)

Ltac gather_atoms :=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : env => dom x) in
  let D := gather_atoms_with (fun x : typ => fv_tt x) in
  let E := gather_atoms_with (fun x : typ => fv_tp x) in
  let F := gather_atoms_with (fun x : exp => fv_ep x) in
  constr:(A `union` B `union` C `union` D `union` E `union` F).

Tactic Notation "pick" "fresh" ident(x) :=
  let L := gather_atoms in (pick fresh x for L).

Tactic Notation
      "pick" "fresh" ident(atom_name) "and" "apply" constr(lemma) :=
  let L := gather_atoms in
  pick fresh atom_name excluding L and apply lemma.
