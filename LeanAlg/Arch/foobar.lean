import Mathlib.Tactic.Common

import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs

namespace Pi

-- The indexing type
variable {f : I → Type v}


theorem single_smul_a {α} [Monoid α] [∀ i, AddMonoid <| f i] [∀ i, DistribMulAction α <| f i]
    [DecidableEq I] (i : I) (r : α) (x : f i) : single i (r • x) = r • single i x :=
  single_op (fun i : I => (r • · : f i → f i)) (fun _ => smul_zero _) _ _

-- Porting note: Lean4 cannot infer the non-dependent function `f := fun _ => β`
/-- A version of `Pi.single_smul` for non-dependent functions. It is useful in cases where Lean
fails to apply `Pi.single_smul`. -/
theorem single_smul' {α β} [Monoid α] [AddMonoid β] [DistribMulAction α β] [DecidableEq I] (i : I)
    (r : α) (x : β) : single (M := fun _ => β) i (r • x) = r • single (M := fun _ => β) i x :=
  single_smul_a (f := fun _ => β) i r x

