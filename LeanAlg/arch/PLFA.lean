def Idx : Type := String

inductive MyTerm : Type where
  | var (id:Idx) : MyTerm
  | func (id:Idx) (b:Term) : MyTerm
  | compose (a b:Term) : MyTerm
  | succ (a : MyTerm) : MyTerm
  | case (L:Term) (M:Term) (id:Idx) (T:Term) : MyTerm
  | fixpt (id:Idx) (T:Term) : MyTerm
  | zero : MyTerm


open MyTerm

notation:50 "%" e => var e
notation:50 "λ" id "⇒" term => func id term
notation:50 "μ" id "⇒" term => fixpt id term
notation:70 f "∘" g => compose f g
notation:80 "case" L "[zero⇒" M "::suc" id "⇒" T "]"=> case L M id T


def two : MyTerm := succ $ succ zero

def plus : MyTerm := μ "+" ⇒ λ "n" ⇒ 
                       case (% "m")
                       [zero⇒ % "n"
                       ::suc "m" ⇒ 1 
-- plus : Term
-- plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
--          case ` "m"
--            [zero⇒ ` "n"
--            |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]
