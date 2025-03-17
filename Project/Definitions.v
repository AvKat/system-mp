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

Definition open_vt (V : var) (T : typ) (k : nat) : typ :=
  match V with
  | var_b n => if n === k then T else V
  | var_f _ => V
  end.

Fixpoint open_pv (P : pth) (V : var) (k : nat) : pth :=
  match P with
  | pth_var (var_b n) => if n === k then (pth_var V) else P
  | pth_var (var_f _) => P
  | pth_proj1 p => pth_proj1 (open_pv p V k)
  | pth_proj2 p => pth_proj2 (open_pv p V k)
  end.

Fixpoint open_tt_rec (T : typ) (U : typ) (k : nat) : typ :=
  match T with
  | typ_tvar a => open_vt a U k
  | typ_top => typ_top
  | typ_bot => typ_bot
  | typ_arr R T => typ_arr (open_tt_rec R U k) (open_tt_rec T U (k+1))
  | typ_all R T => typ_all (open_tt_rec R U k) (open_tt_rec T U (k+1))
  | typ_path _ => T
  | typ_path_Snd _ => T
  | typ_pair R T => typ_pair (open_tt_rec R U k) (open_tt_rec T U k)
  | typ_tpair R T => typ_tpair (open_tt_rec R U k) (open_tt_rec T U k)
  end.

Fixpoint open_tv_rec (T : typ) (V : var) (k : nat) : typ :=
  match T with
  | var_b n => if n === k then V else T
  | typ_arr R T => typ_arr (open_tv_rec R V k) (open_tv_rec T V (k+1))
  | typ_all R T => typ_arr (open_tv_rec R V k) (open_tv_rec T V (k+1))
  | typ_pair R T => typ_pair (open_tv_rec R V k) (open_tv_rec T V (k+1))
  | typ_tpair R T => typ_tpair (open_tv_rec R V k) (open_tv_rec T V (k+1))
  | _ => T
  end.

Fixpoint open_ev_rec (E : exp) (V: var) (k : nat) : exp :=
  match E with
  | exp_path p => exp_path (open_pv p V k)
  | exp_app p1 p2 => exp_app (open_pv p1 V k) (open_pv p2 V k)
  | exp_tapp p T => exp_tapp (open_pv p V k) (open_tt_rec T V k)
  | exp_abs T t => exp_abs (open_tt_rec T V k) (open_ev_rec t V (k+1))
  | exp_tabs T t => exp_tabs (open_tt_rec T V k) (open_ev_rec t V (k+1))
  | exp_let x t => exp_let (open_ev_rec x V k) (open_ev_rec t V (k+1))
  | _ => E
  end.

Fixpoint open_et_rec (E : exp) (U : typ) (k : nat) : exp :=
  match E with
  | exp_tapp p T => exp_tapp p (open_tt_rec T U k)
  | exp_abs T t => exp_abs (open_tt_rec T U k) (open_et_rec t U (k+1))
  | exp_tabs T t => exp_tabs (open_tt_rec T U k) (open_et_rec t U (k+1))
  | exp_tpair x T => exp_tpair x (open_tt_rec T U k)
  | exp_let x t => exp_let (open_et_rec x U k) (open_et_rec t U (k+1))
  | _ => E
  end.

Definition open_tt (T : typ) (U : typ) : typ := open_tt_rec T U 0.
Definition open_tv (T : typ) (V : var) : typ := open_tv_rec T V 0.
Definition open_ev (E : exp) (V : var) : exp := open_ev_rec E V 0.
Definition open_et (E : exp) (U : typ) : exp := open_et_rec E U 0.

Inductive path : pth -> Prop :=
  | path_var : forall x, path (pth_var x)
  | path_proj1 : forall p, path p -> path (pth_proj1 p)
  | path_proj2 : forall p, path p -> path (pth_proj2 p).

Inductive type : typ -> Prop :=
  | type_tvar : forall (X : atom), type X
  | type_top : type typ_top
  | type_bot : type typ_bot
  | type_arr : forall T1 T2 L,
      (forall x, x `notin` L -> type (open_tv T2 x)) ->
      type (typ_arr T1 T2)
  | type_all : forall T1 T2 L,
      (forall X, X `notin` L -> type (open_tt T2 X)) ->
      type (typ_all T1 T2)
  | type_path : forall p, path p -> type p
  | type_path_Snd : forall p, path p -> type (typ_path_Snd p)
  | type_vpair : forall T1 T2 L,
      type T1 ->
      (forall x, x `notin` L -> type (open_tv T2 x)) ->
      type (typ_pair T1 T2)
  | type_tpair : forall T1 T2 L,
      type T1 ->
      (forall x, x `notin` L -> type (open_tv T2 x)) ->
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
      (forall X, X `notin` L -> expr (open_et e X)) ->
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

Inductive wf_typ : env -> typ -> Prop :=
  | w_var : forall E x T,
      binds x (bind_val T) E ->
      wf_typ E (pth_var x)
  | w_tvar : forall E X T,
      binds X (bind_typ T) E ->
      wf_typ E X
  | w_fst : forall (p: pth) S T E,
      (* wf_typ E p -> *)
      sub E p (typ_pair S T) ->
      wf_typ E (pth_proj1 p)
  | w_tfst : forall (p: pth) S T E,
      (* wf_typ E p -> *)
      sub E p (typ_tpair S T) ->
      wf_typ E (pth_proj1 p)
  | w_snd : forall (p: pth) S T E,
      (* wf_typ E p -> *)
      sub E p (typ_pair S T) ->
      wf_typ E (pth_proj2 p)
  | w_tsnd : forall E (p : pth) S T,
      (* wf_typ E p -> *)
      sub E p (typ_tpair S T) ->
      wf_typ E (typ_path_Snd p)
  | w_top : forall E, wf_typ E typ_top
  | w_bot : forall E, wf_typ E typ_bot
  | w_fun : forall L E S T,
      wf_typ E S ->
      (forall x, x `notin` L -> wf_typ ((x, bind_val S) :: E) (open_tv T x)) ->
      wf_typ E (typ_arr S T)
  | w_tfun : forall L E S T,
      wf_typ E S ->
      (forall X, X `notin` L -> wf_typ ((X, bind_typ S) :: E) (open_tt T X)) ->
      wf_typ E (typ_all S T)
  | w_pair : forall L E S T,
      wf_typ E S ->
      (forall x, x `notin` L -> wf_typ ((x, bind_val S) :: E) (open_tv T x)) ->
      wf_typ E (typ_pair S T)
  | w_tpair : forall L E S T,
      wf_typ E S ->
      (forall x, x `notin` L -> wf_typ ((x, bind_val S) :: E) (open_tv T x)) ->
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
      sub E X T
  | sub_fst : forall E (p : pth) S T,
      sub E p (typ_pair S T) ->
      sub E (pth_proj1 p) S
  | sub_tfst : forall E (p : pth) S T,
      sub E p (typ_tpair S T) ->
      sub E (pth_proj1 p) S
  (* TODO: Confim the next two rules *)
  | sub_snd : forall E (p : pth) S T,
      sub E p (typ_pair S T) ->
      sub E (pth_proj2 p) (open_tt T (pth_proj1 p))
  | sub_tsnd : forall E (p : pth) S T,
      sub E p (typ_tpair S T) ->
      sub E (typ_path_Snd p) (open_tt T (pth_proj1 p))
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
      (forall x, x `notin` L -> sub ((x, bind_val S2) :: E) (open_tv T1 x) (open_tv T2 x)) ->
      sub E (typ_arr S1 T1) (typ_arr S2 T2)
  | sub_tfun : forall L E S1 S2 T1 T2,
      sub E S2 S1 ->
      (forall X, X `notin` L -> sub ((X, bind_typ S2) :: E) (open_tt T1 X) (open_tt T2 X)) ->
      sub E (typ_all S1 T1) (typ_all S2 T2)
  | sub_pair : forall L E S1 S2 T1 T2,
      sub E S1 S2 ->
      (forall x, x `notin` L -> sub ((x, bind_val S2) :: E) (open_tv T1 x) (open_tv T2 x)) ->
      sub E (typ_pair S1 T1) (typ_pair S2 T2)
  | sub_tpair : forall L E S1 S2 T1 T2,
      sub E S1 S2 ->
      (forall x, x `notin` L -> sub ((x, bind_val S2) :: E) (open_tv T1 x) (open_tv T2 x)) ->
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
      (forall x, x `notin` L -> typing ((x, bind_val S) :: E) (open_ev e x) (open_tv T x)) ->
      typing E (exp_abs S e) (typ_arr S T)
  | t_app : forall E (p q : pth) S T,
      typing E p (typ_arr S T) ->
      typing E q S ->
      typing E (exp_app p q) (open_tt T q)
  | t_tabs : forall L E S T e,
      wf_typ E S ->
      (forall X, X `notin` L -> typing ((X, bind_typ S) :: E) (open_et e X) (open_tt T X)) ->
      typing E (exp_tabs S e) (typ_all S T)
  | t_tapp : forall E (e : pth) R S T,
      typing E e (typ_all S T) ->
      sub E R S ->
      typing E (exp_tapp e R) (open_tt T R)
  | t_pair : forall L E (x y : atom) S T,
      typing E (exp_path x) S ->
      (forall z, z `notin` L -> wf_typ ((z, bind_val S) :: E) (open_tv T z)) ->
      typing E (exp_path y) (open_tv T x) ->
      typing E (exp_pair x y) (typ_pair S T)
  | t_tpair : forall L E (x : atom) R S T,
      typing E (exp_path x) S ->
      (forall z, z `notin` L -> wf_typ ((z, bind_val S) :: E) (open_tv T z)) ->
      sub E R (open_tv T x) ->
      typing E (exp_tpair x R) (typ_tpair S T)
  | t_let : forall L E e1 e2 S T,
      typing E e1 S ->
      wf_typ E T ->
      (forall x, x `notin` L -> typing ((x, bind_val S) :: E) (open_ev e2 x) (open_tv T x)) ->
      typing E (exp_let e1 e2) T.

Hint Constructors path type expr wf_typ wf_env sub typing : core.

Scheme wf_env_all_mutind := Induction for wf_env Sort Prop
  with wf_typ_all_mutind := Induction for wf_typ Sort Prop
  with sub_all_mutind := Induction for sub Sort Prop.

Combined Scheme wf_env_typ_sub_ind from wf_env_all_mutind, wf_typ_all_mutind, sub_all_mutind.

Scheme wf_typ_mutind := Induction for wf_typ Sort Prop
  with sub_mutind := Induction for sub Sort Prop.

Combined Scheme wf_typ_sub_ind from wf_typ_mutind, sub_mutind.

