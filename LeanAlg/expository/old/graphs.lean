


import Mathlib.Order.Defs.Unbundled

/- --------------------------------------------------------------------------------
   Let's give a defintion of an (undirected) graph in Lean
   --------------------------------------------------------------------------------
-/

/- First of all, we need to formulate a notion of unordered pair. 

   Given any type `α`, `α × α` is the type of "ordered pairs of terms of type `α`.
   
   So for example, ` ⟨1,2⟩ : Nat × Nat `
   
   We define a relation `symmpair` as follows:
-/

example (hnp : ¬ P) (hor : P ∨ Q) : Q := by
  match hor with
  | Or.inl hp =>  
     exfalso
     exact hnp hp
  | Or.inr hq =>  
     exact hq


variable {α : Type} 

@[simp]
def flipPair (x : α × α) : α × α := 
  ⟨Prod.snd x, Prod.fst x⟩


def flipPairSquared (x : α × α) : flipPair (flipPair x ) = x := by
  simp

def flipPairSwitch {x y : α × α} : x = flipPair y → y = flipPair x := by
  intro h
  rw [←flipPairSquared y ]
  apply symm
  apply congrArg flipPair h

@[simp]
def symmPair (x : α × α) (y : α × α) :  Prop :=
   x = y ∨ x = flipPair y

infix:50 " ~ " => symmPair

lemma symmPairNotEq (x y : α × α) (h : x ~ y) (hne : ¬ x = y) : 
    x = flipPair y := by
  match h with
  | Or.inl heq => exfalso; exact hne heq
  | Or.inr hfl => exact hfl

--@[simp]
lemma symmPair.self {x : α × α} : x ~ x :=
  Or.inl rfl
  
--@[simp]
lemma symmPair.flip {x : α × α} : x ~ (flipPair x) :=
  Or.inr rfl

lemma symmPair.toggle (x y : α × α) (h : x ~ y) : x ~ (flipPair y) := by
  by_cases he : x = y
  · rw [he]
    exact symmPair.flip 
  · have : x = flipPair y := by
      exact symmPairNotEq x y h he
    rw [ ← this]
    exact symmPair.self 
      
example : ⟨0,1⟩ ~ ⟨1,0⟩ ∧ ⟨0,1⟩ ~ ⟨0,1⟩ := by
  simp

example : ¬ (⟨0,1⟩ ~ ⟨0,2⟩) := by
  simp  
  
-- we next need to convince `Lean` that `symmPair` is an equivalence relation.

theorem symmPair.refl : (x : α × α) → x ~ x := by
    intro (a,b)
    apply Or.inl
    rfl
  
theorem symmPair.symm : {x y : α × α} → x ~ y → y ~ x := by  
    intro x y hxy 
    by_cases he : x = y
    · rw [ he ]
      exact symmPair.self 
    · rw [ symmPairNotEq x y hxy he ]
      exact symmPair.flip 

theorem symmPair.trans : {x y z : α × α} → x ~ y → y ~ z → x ~ z := by
  intro x y z hxy hyz
  by_cases he : x = y
  · rw [he] 
    exact hyz
  · have : x = flipPair y := symmPairNotEq x y hxy he
    rw [ this ]
    apply symmPair.symm
    apply symmPair.toggle
    apply symmPair.symm
    exact hyz
  

theorem symmPairIsEquiv : Equivalence (@symmPair α) where
  refl := symmPair.refl
  symm := symmPair.symm
  trans := symmPair.trans

-- now, they type of unordered pairs from `α` is a so-called `quotient` of the type `α × α`

-- For the construction of a quotient, Lean needs to use a type that
-- has the `setoid` attribute.

instance unordProdSetoid (α : Type) : Setoid (α × α) where
  r := symmPair
  iseqv := symmPairIsEquiv

-- now the   quotient is constructed from a type which is a setoid:

def UnordProd (α : Type) : Type := Quotient (unordProdSetoid α)
  

def mk (a b : α) : UnordProd α :=
  Quotient.mk' ⟨a,b⟩ 

def mk' (x : α × α) : UnordProd α :=
  Quotient.mk' x

notation "{ " a ", " b " }" => mk a b

example :  {(1 : Nat), 2} = { 2, 1 } := 
  Quotient.sound (Or.inr rfl)

@[simp]
def mem (a : α) : UnordProd α -> Prop :=
  let f : α × α -> Prop :=
    fun x => a = x.fst ∨ a = x.snd
  let test (x : α × α) : f (flipPair x) = f x := by
    simp
    grind
  let hf (x y : α × α) : x ~ y → (f x = f y) := by 
    intro he
    match he with 
    | Or.inl k => simp_all
    | Or.inr k => 
        rw [ k, test y] 
  Quot.lift f hf

example : {1,2} ≠ {1,3} := by
  intro h
  have k₁: mem 2 { 1,2 } := by sorry
  have k₂: ¬ mem 2 { 1,3 } := by 
    rw [ h ] at k₁
    intro h'
    unfold mem at k₁
  exact k₂ k₁

theorem mk_eq_mk (a₁ a₂ : α) : {a₁, a₂} = {a₂, a₁} :=
  Quot.sound (Or.inr rfl)    
  
theorem mk_eq_mk' (x : α × α) : mk' x = mk' (flipPair x) :=
  Quot.sound (Or.inr rfl)
