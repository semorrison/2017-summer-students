namespace ch1

constant and : Prop -> Prop -> Prop
constant or : Prop -> Prop -> Prop
constant not : Prop -> Prop
constant implies : Prop -> Prop -> Prop

variables p q r : Prop
#check and p q
#check or (and p q) r
#check implies (and p q) (and q p)

constant Proof : Prop -> Type

constant and_comm : Π p q : Prop,
  Proof (implies (and p q) (and q p))

#check and_comm p q

constant modus_ponens : Π p q : Prop,
  Proof (implies p q) -> Proof p -> Proof q

constant implies_intro : Π p q: Prop,
  (Proof p -> Proof q) -> Proof (implies p q)
end ch1

-- Working with Propositions as Types
namespace ch2
constants p q : Prop

theorem t1 : p -> q -> p := λ hp : p, λ hq : q, hp

-- SUGAR
theorem t2 : p -> q -> p :=
assume hp : p, -- equiv to 'λ hp : p'
assume hq : q,
show p, from hp -- equiv to just writing 'hp'

axiom hp : p -- equiv to 'constant hp : p'
theorem t3 : q -> p := t1 hp -- function application (woah)

theorem t4 (p q : Prop) (hp : p) (hq : q) : p := hp
#check t4

theorem t5 : ∀ (p q : Prop), p -> q -> p := -- ∀ is sugar for Π
  λ (p q : Prop) (hp : p) (hq : q), hp

end ch2

-- Propositional Logic
namespace ch3
variables p q r :  Prop
#check p ↔ q

example (h : p ∧ q) : q ∧ p :=  and.intro (and.right h) (and.left h)

variables (hp : p) (hq : q)
example : p ∧ q := (|hp,hq|)

example (h : p ∧ q) : q ∧ p :=
  ⟨h.right, h.left⟩

#check or.elim
#check false

example (h : p ∨ q) : q ∨ p :=
or.elim h
  (assume hp : p,
   show q ∨ p, from or.intro_right q hp)
  (assume hq : q,
   show q ∨ p, from or.intro_left p hq)

-- ¬p is syntactic sugar for p → false
example (hpq : p -> q) (hnq : ¬q) : ¬p :=
assume hp : p,
show false, from hnq (hpq hp) -- this gives an object p → false

theorem contra (hp : p) (hnp : ¬p) : q := false.elim (hnp hp) -- false.elim takes false and shows whatever you want
#print contra 
end ch3

-- Classical Logic
section ch5

open classical

variable p : Prop
#check em p

end ch5
