/- 8.1 -- Pattern Matching -/

open nat

def sub1 : ℕ → ℕ
| zero := zero
| (succ x) := x

def sub2 : ℕ → ℕ
| 0 := 0
| (x+1) := x

universes u v
variables {α : Type u} {β : Type v}

def swap_pair : α × β → β × α 
| (a, b) := (b,a)

def bar : option ℕ → ℕ 
| (some n) := n + 1
| none := 0

def bnot' : bool → bool
| tt := ff
| ff := tt

theorem bnot_bnot' : ∀ b : bool, bnot (bnot b) = b
| tt := rfl
| ff := rfl

example (p q : Prop) : p ∧ q → q ∧ p
| (and.intro h1 h2) := and.intro h2 h1

example (p q : Prop) : p ∨ q → q ∨ p
| (or.inl hp) := or.inr hp
| (or.inr hq) := or.inl hq

def sub3 : ℕ → ℕ
| zero := 0
| (succ zero) := 0
| (succ (succ a)) := a

#print sub3
#print sub3._main 

example {α : Type u} (p q : α → Prop) :
    (∃ x, p x ∨ q x) → (∃ x, p x) ∨ (∃ x, q x)
| (exists.intro x (or.inl px)) := or.inl (exists.intro x px) 
| (exists.intro x (or.inr qx)) := or.inr (exists.intro x qx)

def foo : ℕ × ℕ → ℕ
| (0, n) := 0
| (m+1, 0) := 1
| (m+1, n+1) := 2

def foo' : ℕ → ℕ → ℕ
| 0 n := 0
| (m+1) 0 := 1
| (m+1) (n+1) := 2

def lists : list ℕ → list ℕ → ℕ
| [] [] := 0
| (a :: l) [] := a
| [] (b :: l) := b
| (a :: l) (b :: m) := a + b

def band' : bool → bool → bool
| tt a := a
| ff _ := ff -- wildcard pattern

/- 8.2 -- Wildcards and Overlapping Patterns -/
