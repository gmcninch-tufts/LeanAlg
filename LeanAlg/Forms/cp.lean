import Mathlib

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

open Polynomial

-- reminder: check that Sahan provides a proof of this, based on his work of 2025-07

theorem cassels_pfister (φ : QuadraticForm F V) [Invertible (2 : F)]
  (f : F[X]) (v : TensorProduct F (RatFunc F) V) (h : φ.baseChange (RatFunc F) v = f)
  : ∃ (w : TensorProduct F F[X] V), φ.baseChange F[X] w = f := by sorry
  
