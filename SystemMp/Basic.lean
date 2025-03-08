import Lean.Data.AssocList

namespace SystemMP

open Lean

def Atom : Type := String deriving BEq, DecidableEq, Repr

inductive Var where
  | var_b : Nat → Var
  | var_f : Atom → Var
deriving BEq, DecidableEq, Repr
open Var

instance : Coe Atom Var where
  coe a := Var.var_f a

end SystemMP
