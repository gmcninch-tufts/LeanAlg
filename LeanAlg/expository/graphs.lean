import Mathlib

variable {α : Type} [DecidableEq α]

structure Edge (α : Type) [DecidableEq α] where
  endpoints : Multiset α
  pf : Multiset.card endpoints = 2


-- we can construct loops or ordinary edges...
example : Edge ℕ := Edge.mk {1,1} (by norm_num)
example : Edge ℕ := Edge.mk {1,2} (by norm_num)

-- here is a maybe easier way of constructing an edge
@[simp]
def mkedge (a b : α) : Edge α :=
  Edge.mk {a,b} (by norm_num)

def vertex1 : Edge String := mkedge "a" "b"
def vertex2 : Edge String := mkedge "aa" "aa"

#eval vertex2.endpoints
#check vertex2.pf

/- `incident a e` is the proposition that
the edge `e` is incident to the vertex `a`.
-/
@[simp]
def incident (a : α) (e : Edge α) : Prop :=
  a ∈ e.endpoints

noncomputable
def incidentBool (a : α) (e : Edge α) : Bool :=
  List.elem a (Multiset.toList e.endpoints)

example : incident "aa" vertex2 := by
  unfold vertex2
  simp

structure Graph' (α : Type) [DecidableEq α] where
  vertices : List α
  edges : List (Edge α)
  p : ∀ e ∈ edges, (Multiset.toList e.endpoints) ⊆ vertices

noncomputable
def incident_edges (G:Graph' α) (v : α) : List (Edge α) :=
  List.filter (incidentBool v) G.edges

noncomputable
def degree (G : Graph' α) (v : α) (pv : v ∈ G.vertices) : ℕ :=
  List.length (incident_edges G v)
