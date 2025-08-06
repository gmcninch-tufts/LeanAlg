import Mathlib.Tactic

def append {a:Type u} (xs ys : List a) : List a :=
  match xs with
  | [] => ys
  | x :: xs => x :: append xs ys

#eval append ["a", "b"] ["c", "d"]

theorem append_length (xs ys : List a)
      : (append xs ys).length = xs.length + ys.length := by
  induction xs with
  | nil => simp [append]
  | cons z zs ih => 
     simp [append, ih]
     linarith

def x : List ℕ := [1, 2, 3]

#eval append x x

example :  6 = (append x x).length := by
 rw [append_length] --append_length x x
 unfold List.length
 unfold x
 simp


#check List.length_cons


def zip_safe (xs : List a) (ys : List a) (p: xs.length = ys.length) : (List (Prod a a)) :=
  match xs,ys with
  | [],[] => []
  | z :: zs, w :: ws => by
    have hp : zs.length = ws.length := by 
      repeat rw [List.length_cons ] at p
      linarith
    exact (z,w) :: zip_safe zs ws  hp


#check zip_safe [0,1,2,3] [4,5,6,7] (by rfl)

def vcons { n:ℕ} {a:Type u} (x:a) (xs:Vector a n) : Vector a (Nat.succ n) := by
  let l : Array a := List.toArray $ x :: xs.toList
  let h : l.size = n + 1 := by
    unfold l
    rw [ List.size_toArray, List.length_cons ]
    simp
  exact Vector.mk l h

--  exact ⟨ List.toArray (x :: xs.toList), simp ⟩

def zip_vect {n : ℕ} {a b:Type u} (xs : Vector a n) (ys : Vector b n) : Vector (a × b) n := 
    ⟨ Array.zip xs.toArray ys.toArray , by simp ⟩

def add (a: List ℕ) (b: List ℕ) : Option (List ℕ) :=
   if a.length == b.length then 
     match a,b with
     | [],_ => some []
     | _,[] => some []
     | (c::cs), (d::ds) => do
       let rest ← add cs ds
       pure $ (c+d)::rest
   else
     none


#eval add [1,2,0] [3,4,5+8]

def add_safe (a:List ℕ) (b:List ℕ) (p:a.length = b.length) : List ℕ :=
  match a,b with
  | [],[] => []
  | z::zs, w::ws =>  by
    have h : zs.length = ws.length := by
       repeat rw [List.length_cons]  at p
       linarith
    exact (z+w)::add_safe zs ws h

#eval add_safe [ 1,2,3] [1,2,4] rfl


#eval (Multiset.ofList [1,2,3]).card

inductive vect : Type → ℕ →  Type where
 | vnil : vect a 0
 | vcons (x:a) (v:vect a n) : vect a (Nat.succ n)

infixr:67 " ::: " => vect.vcons

def add_vect {n :ℕ} (av : vect ℕ n)
                     (bv : vect ℕ n)
    : vect ℕ n := 
  match av,bv with
  | vect.vnil,vect.vnil => vect.vnil
  | a ::: ar, b ::: br => (a+b) ::: add_vect ar br

#eval add_vect (1 ::: 2 ::: vect.vnil) (2 ::: 1 ::: vect.vnil)
