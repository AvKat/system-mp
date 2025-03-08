import SystemMp.Basic
import Aesop

namespace SystemMP

open SystemMP

namespace Assoc

def Pair.{u} {α : Type u} := (Atom × α)

def dom(Γ : List (@Pair α)) : List Atom := Γ.map Prod.fst

instance [BEq α] : BEq (@Pair α) where
  beq x y := x.1 == y.1 && x.2 == y.2

