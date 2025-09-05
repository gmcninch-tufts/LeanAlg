
import Mathlib.Tactic

variable (K:Type) [ Field K ]

variable (m n : ℕ)

def Mat (K:Type) [Field K] (m n: ℕ) := Matrix (Fin m) (Fin n) K

--example {m n : ℕ} : Matrix (Fin m) (Fin n) K := sorry

open Matrix
example {K:Type} [Field K] {m n: ℕ}  (A B : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2) (Fin 2) K := A + B

example {K:Type} [Field K] {m n: ℕ}  (A : Matrix (Fin 2) (Fin 5) K) (B: Matrix (Fin 5) (Fin 2) K): Matrix (Fin 2) (Fin 2) K := 
 A * B


def mm : ℕ := 3
def nn : ℕ := 3

def f { mm nn : ℕ} (A : Matrix (Fin (mm+1)) (Fin (nn+1)) ℕ) : ℕ :=
  A 0 0

example {n m : ℕ} { h : n = Nat.succ m} :  Fin n :=  by
  rw [ h] 
  exact 1

def ff (n:ℕ) : Fin (Nat.succ n) := Fin.ofNat 0


example (A : Matrix (Fin 2) (Fin 2) ℕ) : ℕ :=
  A 0 0

example : Fin 1 := Fin.ofNat 2

def check (a:Fin 2) (b:Fin 2) : Bool :=
 if a = b then True else False

set_option pp.explicit true
#print check
#eval check 0 17
  

