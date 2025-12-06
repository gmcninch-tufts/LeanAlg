import Mathlib

structure Edge (β : Type) where
  id : Option ℕ
  endpoints : Multiset β
  pf : Multiset.card endpoints = 2
deriving DecidableEq

-- we can construct loops or ordinary edges...
example : Edge ℕ := Edge.mk (Option.none) {1,1} (by norm_num)
example : Edge ℕ := Edge.mk (Option.none) {1,2} (by norm_num)

-- here is a maybe easier way of constructing an edge
@[simp]
def mkedge (id : Option ℕ) (a b : α) : Edge α :=
  Edge.mk id {a,b} (by norm_num)

@[simp]
def edge_from_pair (id : Option ℕ) (x : α × α) : Edge α :=
  match x with
  | ⟨ a,b ⟩ => mkedge id a b

def vertex1 : Edge String := mkedge Option.none "a" "b"
def vertex2 : Edge String := mkedge Option.none "a" "bb"

example : vertex1 ≠ vertex2 := by decide

/- `incident a e` is the proposition that
the edge `e` is incident to the vertex `a`.
-/
@[simp]
def incident (a : α) (e : Edge α) : Prop :=
  a ∈ e.endpoints

-- Create a decidable instance for `incident`
instance incidentDecPred [DecidableEq α] (v : α) :
    DecidablePred (incident v : Edge α → Prop) :=
  fun e =>
     Multiset.decidableMem v e.endpoints

example : incident "bb" vertex2 := by decide

structure Graph' (α : Type) where
  vertices : Finset α
  edges : Finset (Edge α)
  p : ∀ e ∈ edges, ∀ a:α, incident a e → a ∈ vertices
deriving DecidableEq

def incident_edges [DecidableEq α] (G : Graph' α) (v : α) : Finset (Edge α) :=
  { e ∈ G.edges | (incident v) e }

def degree [DecidableEq α] (G : Graph' α) (v : α) (pv : v ∈ G.vertices) : ℕ :=
  Finset.card (incident_edges G v)

def complete_graph {α} [DecidableEq α] (S : Finset α) {n : ℕ} {_ : Finset.card S = n} :
    Graph' α where
  vertices := S
  edges := Finset.image (edge_from_pair Option.none) (Finset.product S S)
  p := by sorry
    -- intro e he a hae
    -- simp at he
