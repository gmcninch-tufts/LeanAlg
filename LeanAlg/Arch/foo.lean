-- exercises

variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := 
  ⟨fun hpq => ⟨hpq.right,hpq.left⟩,
   fun hqp => ⟨hqp.right,hqp.left⟩⟩

example : p ∨ q ↔ q ∨ p := 
  ⟨ fun hpq => hpq.elim
                 (fun hp => show q ∨ p from Or.inr hp)
                 (fun hq => show q ∨ p from Or.inl hq)
    ,
    fun hqp => hqp.elim
                 (fun hq => Or.inr hq)
                 (fun hp => Or.inl hp)
  ⟩


-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := 
  ⟨ fun hpqr => ⟨ hpqr.left.left , ⟨hpqr.left.right , hpqr.right ⟩⟩
   ,
    fun hpqr => ⟨ ⟨hpqr.left, hpqr.right.left⟩, hpqr.right.right ⟩
  ⟩


example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := 
  ⟨ fun hpqr => hpqr.elim
                (fun hpq => hpq.elim
                            (fun hp => (Or.intro_left (q ∨ r) hp))
                            (fun hq => Or.inr (Or.intro_left r hq)))
                (fun hr => Or.inr (Or.inr hr))
    ,
    fun hpqr => hpqr.elim
                (fun hp => Or.inl (Or.inl hp))
                (fun hqr => hqr.elim
                            (fun hq => Or.inl (Or.inr hq )) -- Or.inl _
                            (fun hr => Or.inr hr))
  ⟩

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := 
  Iff.intro
  (fun h => h.right.elim
            (fun hq => Or.inl ⟨h.left, hq⟩)
            (fun hr => Or.inr ⟨h.left, hr⟩) 
            )
  (fun k => k.elim
            (fun hpq => And.intro
                        hpq.left
                        (Or.inl hpq.right))
            (fun hpr => And.intro
                        hpr.left
                        (Or.inr hpr.right))
            )
 




example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry


