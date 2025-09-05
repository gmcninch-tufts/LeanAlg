import Mathlib.Tactic

variable { a : Type} 

variable { k : Type } [Field k]


def list_to_set {a:Type} (xs : List a) : Set a :=
  match xs with
    | [] => ∅
    | y :: ys => insert y (list_to_set ys)

def sources { a:Type} (e:Set (a×a)) : Set a := Prod.fst '' e
def ends { a:Type} (e:Set (a×a)) : Set a := Prod.snd '' e

def endpoints { a:Type} (e:Set (a×a)) : Set a := (sources e) ∪ (ends e)


structure FiniteDirGraph (a : Type) where
  verts : Set a 
  edges : Set (a × a)
  edgemem : endpoints edges ⊆ verts

structure GPath {a : Type} {G:FiniteDirGraph a} (x y : G.verts) where
  gpath (v:G.verts) (gp:GPath x y) : GPath v y
  p : 
  startP : (Functor.map Prod.fst (List.head? gpath)) = some x
  endP   : (Functor.map Prod.snd (List.getLast? gpath)) = some y

def has_path? {a:Type} (G:FiniteDirGraph a) (x y :G.verts) : ∃ GPath x y, True 

def path_concat { a:Type} {G:FiniteDirGraph a} (x y z : G.verts) :
  GPath x y → GPath y z -> GPath x z := by
    rintro gp hp

-- remember that for S:Set a and f:a → b,  (f '' S :Set b) is the image of S.
   

example : FiniteDirGraph ℕ := by
  let vertl := ([1,2,3]:List ℕ)
  let edgel := ([(1,1), (2,2)]:List (ℕ×ℕ))
  have hs : endpoints edges ⊆ verts := by
    unfold endpoints
    unfold verts
    intro x hx
    rcases hx with ⟨y,hse,hsl⟩
    · unfold edges at hse
      rw [←hsl]
      
  
def foo (a b:ℕ) : Prop := ∃c:ℕ, True
 
#check foo 2 3
    
  

-- (Prod.fst x ∈ V) ∧ (Prod.snd x ∈ V)

example (x : a × a) : a := Prod.fst x

example  : 1 ∈ ({1,2,3}:Finset ℕ):= by 
  exact Finset.mem_insert_self 1 {2, 3}

example : {1,2,3} = insert 1 ({2,3}:Finset ℕ) := rfl


example (A:Set a) (x y : a) (hx:x ∈ A) (hy:y∈ A) : A×A := (Subtype.mk x hx, Subtype.mk y hy)


example (x:a) (A:Set a) (hx: x ∈ A) : { x:a // x ∈ A } := Subtype.mk x hx

variable (A:Set a) (x:a)

#check ((_,_):A × A)

#check (z:a × a) → a

#check 1 ∈ {1,2,3}

#check A

#check A x

variable (x:a)

#check ((fun (y:a) => (y = x)) : Set a)

example (A:Set a) (b : A) : A := b

example : FiniteGraph ℕ := 
  FiniteGraph.mk {1,2,3} {}
