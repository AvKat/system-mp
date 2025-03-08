import SystemMp.Assoc

namespace SystemMP

-- Syntactic definitions and notations

inductive Pth where
  | pvar : Var → Pth
  | pproj1 : Pth → Pth
  | pproj2 : Pth → Pth
deriving BEq, DecidableEq, Repr
open Pth

instance : Coe Var Pth where
  coe a := Pth.pvar a

inductive Typ where
  | typ_var : Var → Typ
  | typ_top : Typ
  | typ_bot : Typ
  | typ_arr : Typ → Typ → Typ
  | typ_all : Typ → Typ → Typ
  -- using De Bruijn indice to bind
  | typ_vpair : Typ → Typ → Typ
  | typ_tpair : Typ → Typ → Typ
  | typ_path : Pth → Typ
  | typ_path_Snd : Pth → Typ
deriving BEq, DecidableEq, Repr
open Typ

namespace Typ
  instance : Coe Var Typ where
    coe a := typ_var a
  instance : Coe Pth Typ where
    coe a := typ_path a

  notation "⊤" => typ_top
  notation "⊥" => typ_bot
  notation:50 "∀(" S ")" T => typ_arr S T
  notation:50 "∀[" S "]" T => typ_all S T
  notation:50 "∃(" S ")" T => typ_vpair S T
  notation:50 "∃[" S "]" T => typ_tpair S T
end Typ

inductive Exp where
  | exp_path : Pth → Exp
  | exp_app : Pth → Pth → Exp
  | exp_tapp : Pth → Typ → Exp
  | exp_abs : Typ → Exp → Exp
  | exp_tabs : Typ → Exp → Exp
  | exp_vpair : Var → Var → Exp
  | exp_tpair : Var → Typ → Exp
  | exp_let : Exp → Exp → Exp
deriving BEq, DecidableEq, Repr
open Exp

namespace Exp
  instance : Coe Var Exp where
    coe a := exp_path a
  instance : Coe Pth Exp where
    coe a := exp_path a

  notation p1".("p2")" => exp_app p1 p2
  notation p".["T"]" => exp_tapp p T
  notation "λ("T")" t => exp_abs T t
  notation "Λ["T"]" t => exp_tabs T t
  notation "⟨"x","y"⟩" => exp_vpair x y
  notation "t⟨"x","T"⟩" => exp_tpair x T
  notation "let" t1 "in" t2 => exp_let t1 t2
end Exp

-- Opening functions
-- Convention: open_xy opens type x with y

def open_vt (V : Var) (T : Typ) (k : Nat) : Typ :=
  match V with
  | Var.var_b n => if n = k then T else V
  | Var.var_f _ => V

def open_pv (P : Pth) (V : Var) (k : Nat) : Pth :=
  match P with
  | pvar (Var.var_b n) => if n = k then V else P
  | pvar (Var.var_f _) => P
  | pproj1 p => pproj1 (open_pv p V k)
  | pproj2 p => pproj2 (open_pv p V k)

def open_tt_rec (T : Typ) (U : Typ) (k : Nat) : Typ :=
  match T with
  | typ_var a => open_vt a U k
  | ⊤ => ⊤
  | ⊥ => ⊥
  | ∀(S) T => ∀(open_tt_rec S U k) (open_tt_rec T U (k+1))
  | ∀[S] T => ∀[open_tt_rec S U k] (open_tt_rec T U (k+1))
  | typ_path _ => T
  | typ_path_Snd _ => T
  | ∃(S) T => ∃(open_tt_rec S U k) (open_tt_rec T U k)
  | ∃[S] T => ∃[open_tt_rec S U k] (open_tt_rec T U k)

def open_tv_rec (T : Typ) (V : Var) (k : Nat) : Typ :=
  match T with
  | Var.var_f _ => T
  | Var.var_b n => if n = k then V else T
  | ⊤ => ⊤
  | ⊥ => ⊥
  | ∀(S) T => ∀(open_tv_rec S V k) (open_tv_rec T V (k+1))
  | ∀[S] T => ∀[open_tv_rec S V k] (open_tv_rec T V k)
  | typ_path _ => T
  | typ_path_Snd _ => T
  | ∃(S) T => ∃(open_tv_rec S V k) (open_tv_rec T V (k+1))
  | ∃[S] T => ∃[open_tv_rec S V k] (open_tv_rec T V (k+1))

def open_ev_rec (E : Exp) (V : Var) (k : Nat) : Exp :=
  match E with
  | exp_path p => open_pv p V k
  | p1.(p2) => (open_pv p1 V k).(open_pv p2 V k)
  | p.[T] => (open_pv p V k).[open_tt_rec T V k]
  | λ(T) t => λ(open_tt_rec T V k) (open_ev_rec t V (k+1))
  | Λ[T] t => Λ[open_tt_rec T V k] (open_ev_rec t V (k+1))
  | ⟨_, _⟩ => E
  | t⟨_, _⟩ => E
  | let t1 in t2 => let (open_ev_rec t1 V k) in (open_ev_rec t2 V (k+1))

def open_et_rec (E : Exp) (U : Typ) (k : Nat) : Exp :=
  match E with
  | exp_path _ => E
  | _.(_) => E
  | p.[T] => p.[open_tt_rec U T k]
  | λ(T) t => λ(open_tt_rec U T k) (open_et_rec t U (k+1))
  | Λ[T] t => Λ[open_tt_rec U T k] (open_et_rec t U (k+1))
  | ⟨_, _⟩ => E
  | t⟨x, _⟩ => t⟨x, open_tt_rec U x k⟩
  | let t1 in t2 => let (open_et_rec t1 U k) in (open_et_rec t2 U (k+1))

def open_tt (T : Typ) (U : Typ) : Typ := open_tt_rec T U 0
def open_tv (T : Typ) (V : Var) : Typ := open_tv_rec T V 0
def open_ev (E : Exp) (V : Var) : Exp := open_ev_rec E V 0
def open_et (E : Exp) (U : Typ) : Exp := open_et_rec E U 0

-- Locally nameless representation

inductive Path : Pth → Prop
  | path_var : ∀ x : Atom, Path x
  | path_proj1 : ∀ p : Pth, Path p → Path (pproj1 p)
  | path_proj2 : ∀ p : Pth, Path p → Path (pproj2 p)

inductive TType : Typ → Prop
  | type_var : (a : Atom) → TType a
  | type_top : TType ⊤
  | type_bot : TType ⊥
  | type_arr : ∀ S T : Typ, ∀ L: List Atom,
    (∀ x : Atom, x ∉ L → TType (open_tv S x)) →
    TType (∀(S) T)
  | type_all : ∀ S T : Typ, ∀ L : List Atom,
    (∀ x : Atom, x ∉ L → TType (open_tt S x)) →
    TType (∀[S] T)
  | type_path : ∀ p : Pth,
    Path p →
    TType (typ_path p)
  | type_path_Snd : ∀ p : Pth,
    Path p →
    TType (typ_path_Snd p)
  | type_vpair : ∀ S T : Typ, ∀ L: List Atom,
    (∀ x : Atom, x ∉ L → TType (open_tv S x)) →
    TType (∃(S) T)
  | type_tpair : ∀ S T : Typ, ∀ L: List Atom,
    (∀ x : Atom, x ∉ L → TType (open_tt S x)) →
    TType (∃[S] T)

inductive Expr : Exp -> Prop
  | expr_path : ∀ p : Pth, Path p → Expr p
  | expr_app : ∀ p1 p2 : Pth,
    Path p1 → Path p2 →
    Expr (p1.(p2))
  | expr_tapp : ∀ p : Pth, ∀ T : Typ,
    Path p → TType T →
    Expr (p.[T])
  | expr_abs : ∀ T : Typ, ∀ e : Exp, ∀ L : List Atom,
    TType T →
    (∀ x : Atom, x ∉ L → Expr (open_ev e x)) →
    Expr (λ(T) e)
  | expr_tabs : ∀ T : Typ, ∀ e : Exp, ∀ L : List Atom,
    TType T →
    (∀ X : Atom, X ∉ L → Expr (open_et e X)) →
    Expr (Λ[T] e)
  | expr_vpair : ∀ x y : Atom, Expr ⟨x, y⟩
  | expr_tpair : ∀ x : Atom, ∀ T : Typ, TType T → Expr (t⟨x, T⟩)

-- Defining Environments using Assoc.lean
inductive binding : Type
  | bind_val : Typ → binding
  | bind_typ : Typ → binding
deriving BEq, DecidableEq, Repr
open binding

open SystemMP.Assoc
def Env := List (@Pair binding)

-- Well-formedness and subtyping
mutual

-- NOTE: Might have to add Wf_Path Γ p as a premise to most cases
inductive Wf_Path : Env → Pth → Prop
  | W_var : ∀ (Γ : Env) (x : Atom) T,
      Γ.contains (x, bind_val T) →
      Wf_Path Γ x
  | W_fst : ∀ Γ (p : Pth),
      Sub Γ p (typ_vpair _ _) →
      Wf_Path Γ (Pth.pproj1 p)
  | W_tfst : ∀ Γ (p : Pth),
      Sub Γ p (typ_tpair _ _) →
      Wf_Path Γ (Pth.pproj1 p)
  | W_snd : ∀ Γ (p : Pth),
      Sub Γ p (typ_vpair _ _) →
      Wf_Path Γ (pproj2 p)

inductive Wf_Typ : Env → Typ → Prop
  | W_top : ∀ Γ, Wf_Typ Γ ⊤
  | W_bot : ∀ Γ, Wf_Typ Γ ⊥
  | W_tvar : ∀ Γ (X : Atom),
      X ∈ dom Γ →
      Wf_Typ Γ (typ_var X)
  | W_tsnd : ∀ Γ (p : Pth),
      Wf_Path Γ p →
      Sub Γ p (typ_path _) →
      Wf_Typ Γ (typ_path_Snd p)
  | W_fun : ∀ Γ x (S T : Typ),
      Wf_Typ Γ S →
      Wf_Typ ((x, bind_val S) :: Γ) T →
      Wf_Typ Γ (∀(S) T)
  | W_tfun : ∀ Γ X (S T : Typ),
      Wf_Typ Γ S →
      Wf_Typ ((X, bind_typ S) :: Γ) T →
      Wf_Typ Γ (∀[S] T)
  | W_pair : ∀ Γ x (S T : Typ),
      Wf_Typ Γ S →
      Wf_Typ ((x, bind_val S) :: Γ) T →
      Wf_Typ Γ (∃(S) T)
  | W_tpair : ∀ Γ X (S T : Typ),
      Wf_Typ Γ S →
      Wf_Typ ((X, bind_typ S) :: Γ) T →
      Wf_Typ Γ (∃[S] T)

inductive Wf_Env : Env → Prop
  | W_nil : Wf_Env []
  | W_val : ∀ Γ (x : Atom) (T : Typ),
      x ∉ dom Γ →
      Wf_Typ Γ T →
      Wf_Env ((x, bind_val T) :: Γ)
  | W_typ : ∀ Γ (X : Atom) (T : Typ),
      X ∉ dom Γ →
      Wf_Typ Γ T →
      Wf_Env ((X, bind_typ T) :: Γ)

inductive Sub : Env -> Typ → Typ → Prop
  | S_bot : ∀ Γ T,
      Wf_Env Γ →
      Wf_Typ Γ T →
      Sub Γ ⊥ T
  | S_top : ∀ Γ T,
      Wf_Env Γ →
      Wf_Typ Γ T →
      Sub Γ T ⊤
  | S_refl : ∀ Γ T,
      Wf_Env Γ →
      Wf_Typ Γ T →
      Sub Γ T T
  | S_trans : ∀ Γ S T U,
      Sub Γ S T →
      Sub Γ T U →
      Sub Γ S U
  | S_symm : ∀ Γ (p q : Pth),
      Sub Γ p q →
      Sub Γ q p
  | S_var : ∀ Γ x T,
      Wf_Env Γ →
      Γ.contains (x, bind_val T) →
      Sub Γ x T
  | S_tvar : ∀ Γ X T,
      Wf_Env Γ →
      Γ.contains (X, bind_typ T) →
      Sub Γ (typ_var X) T
  | S_fst : ∀ Γ (p : Pth) S T,
      Sub Γ p (typ_vpair S T) →
      Sub Γ (pproj1 p) S
  | S_tfst : ∀ Γ (p : Pth) S T,
      Sub Γ p (typ_tpair S T) →
      Sub Γ (pproj1 p) S
  | S_snd : ∀ Γ (p : Pth) S T,
      Sub Γ p (typ_vpair S T) →
      Sub Γ (pproj2 p) (open_tt T (pproj1 p))
  | S_tsnd : ∀ Γ (p : Pth) S T,
      Sub Γ p (typ_tpair S T) →
      Sub Γ (typ_path_Snd p) (open_tt T (pproj1 p))
  | S_fun : ∀ Γ S1 S2 T1 T2,
      Sub Γ S2 S1 →
      Sub ((x, bind_val S2) :: Γ) T1 T2 →
      Sub Γ (∀(S1) T1) (∀(S2) T2)
  | S_tfun : ∀ Γ S1 S2 T1 T2,
      Sub Γ S2 S1 →
      Sub ((X, bind_typ S2) :: Γ) T1 T2 →
      Sub Γ (∀[S1] T1) (∀[S2] T2)
  | S_pair : ∀ Γ S1 S2 T1 T2,
      Sub Γ S1 S2 →
      Sub ((x, bind_val S1) :: Γ) T1 T2 →
      Sub Γ (∃(S1) T1) (∃(S2) T2)
  | S_tpair : ∀ Γ S1 S2 T1 T2,
      Sub Γ S1 S2 →
      Sub ((X, bind_val S2) :: Γ) T1 T2 →
      Sub Γ (∃[S1] T1) (∃[S2] T2)
end

end SystemMP
