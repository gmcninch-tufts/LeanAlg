import Init.Prelude
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Vector.Defs
import Mathlib.Data.Vector.Basic
import Mathlib.Control.Traversable.Basic
import Mathlib.Data.List.Defs


def weaken {d:ℕ} (i:Fin d) : Fin (d+1) := 
  Fin.mk i.val (Nat.lt_succ_of_lt i.isLt)
  
def allFins (d:ℕ): List (Fin d) := 
  match d with
  | Nat.zero => []
  | Nat.succ k => List.cons (Fin.last k) $ Functor.map weaken (allFins k)

def sbv {d:ℕ} (i:Fin d) : Vector ℚ d := 
  let zero : Vector ℚ d := Vector.replicate d 0
  Vector.set zero i 1

instance qvs_tostring : ToString (Vector ℚ (d:ℕ)) where
  toString (x:Vector ℚ d) := toString $ Vector.toList x

def main : IO Unit := do
  IO.println "foobar"
  IO.println $ toString $ (sbv 1:Vector ℚ 3)
  let results : List String := Functor.map toString $ Functor.map sbv $ allFins 30
  _ <- traverse IO.println results
  pure ()

#check IO.println ∘ toString

#check sbv 5 2
