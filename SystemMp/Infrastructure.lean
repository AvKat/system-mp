import «SystemMp».Definitions
import Aesop

open SystemMP
open binding

theorem env_binds_equal_var {Γ : Env} {x : Atom} {U T : Typ} :
    Wf_Env Γ →
    Γ.contains (x, bind_val U) →
    Γ.contains (x, bind_val T) →
    U = T := by 
      intro wf bu bt
      match wf with
      | .W_nil => cases bu
      | .W_val Γ2 x' T' x'notinΓ2 T'wf =>
        sorry
        -- cases bu
        -- · cases bt
        --   · rfl
        --   · sorry
        -- · cases bt
        --   · sorry
        --   · sorry
      | .W_typ Γ2 X T' XnotinΓ2 T'wf =>
        sorry

