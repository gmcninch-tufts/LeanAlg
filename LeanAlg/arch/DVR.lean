import Mathlib.Tactic

import Mathlib.RingTheory.DiscreteValuationRing.Basic

variable { A : Type } [CommRing A] [IsDomain A] 
         [ IsDiscreteValuationRing A ]

example ( π : A) (hirr : Irreducible π) ( m : Ideal A ) 
  (hh : m = Submodule.span A { π }) 
  : Submodule.IsPrincipal m  ∧ Ideal.IsMaximal m := by 
  constructor 
  · apply (Submodule.isPrincipal_iff m).mpr
    use π
  · 


example  (m:Ideal A) :  CommRing (A⧸m) := inferInstance

example (m:Ideal A) (hmax : Ideal.IsMaximal m) : Field (A⧸m) :=
  have : IsField (A⧸m) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient m).mp hmax
inferInstance
