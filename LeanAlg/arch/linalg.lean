
import Mathlib.Tactic

import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Module.Basic
--import Mathlib.LinearAlgebra.Basic

--import Mathlib.Algebra.Module.LinearMap

--import Mathlib.Algebra.BigOperators
import Mathlib.Data.Finset.Basic

import Mathlib.Data.Multiset.Basic

import Mathlib.Data.Finsupp.Basic


universe u

variable (α : Type u)

variable (K : Type u) [Field K]

variable (M : Type u) [AddCommGroup M] [ Module K M ]

example {K : Type*} [Field K] (x : K) : K := x

open SMul
example [Module K M] (r : K) (m : M) : M := smul r m

example : K → M → M := by
  intro a v
  exact (smul a v)

-- example (g : AddHom M M) : g (x + y) = g x + g y := g.map_add'

--variable (g : AddHom M M)
variable ( g : M →ₗ[K] M)

#check g.toFun

#check g.map_add

example ( x y : M) : g (x + y) = g x + g y := by 
  rw [g.map_add]

example (x y z : M) (f : M →ₗ[K] M) : f (x + y + z) = f x + f y + f z:= by
  simp 
  -- or e.g.: 
  -- repeat
  -- rw [f.map_add]

#check Finset M


open BigOperators

example (s : Finset M) (f:M → M) : M := by
  exact ∑ x ∈ s, f x

variable (vv : Vector M (n:ℕ))

variable (ss : Vector K (n:ℕ))


variable (a : Finset M)

#check (Finset.attach a)

example : Finset ℕ := Finset.range 5

--example { n : ℕ} : Finset (Fin n) := Fin n

--example { n: ℕ} : Finset (Fin n) := Finset.attachFin Finset.range(n)


def mth {n:ℕ} (m : Fin n) (ss : Vector K n) (vv : Vector M n ) : M := 
  smul (Vector.get ss m) (Vector.get vv m)

--example (n:ℕ) : M := ∑ n in range(n), 

-- example {n:ℕ} : Finset (Fin n) := by
--   sorry



-- example : α →₀ M  → M :=  sum x in M, f x




example {X : Type} {k : Type} [Field k] {f:X →₀ k} {x:X} :  (h:¬ x ∈ f.support) → f x = 0  := by                
   contrapose
   intro k l
   have z : x ∈ f.support := Finsupp.mem_support_iff.mpr k
   exact l z
    
--  have _: f.(mem_support_toFun x)

variable (α β : Type)

example (f:α → β) : ∀ ⦃a₁ a₂ : α⦄, f a₁ = f a₂ → a₁ = a₂ := by 
  ?apply
