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

-- lean pattern matches overlapping patterns in order (like haskell)

/- 8.3 Structural Recursion and Induction -/

def fib : nat → nat
| 0 := 1
| 1 := 1
| (n +2) := fib (n+1) + fib n
-- automatically memoized (see nat.below and nat.brec_on)

/- 8.4 -- Well-Founded Recursion and Induction -/

variable γ : Sort u 
variable r : γ → γ → Prop

#check (acc r : γ → Prop)
-- acc r x says that x is accessible from below, in the sense that all its predecessors are accessible

#check (well_founded r : Prop)
#print well_founded
-- well_founded r says that every element of the type (?) is accessible

/-https://en.wikipedia.org/wiki/Well-founded_relation
    In mathematics, a binary relation, R, is called well-founded (or wellfounded) on a class X if every
    non-empty subset S ⊆ X has a minimal element with respect to R; that is, some element m not
    related by sRm (for instance, "m is not smaller than s") for any s ∈ S.
    ∀ S ⊆ X (S ≠ ∅ → ∃ m ∈ S, ∀ s ∈ S (s, m) ∉ R)

    Equivalently, assuming some choice, a relation is well-founded if it contains no countable infinite
    descending chains: that is, there is no infinite sequence x0, x1, x2, ... of elements of X such that
    xn+1 R xn for every natural number n.

    If R is a well-founded relation then to show that P(x) holds for all elements x of X, it suffices to show that:
    If x is an element of X and P(y) is true for all y such that y R x, then P(x) must also be true. 
    if we want to construct a function G on X, we may define G(x) using the values of G(y) for y R x.
-/

variable α' : Sort u
variable r' : α' → α' → Prop
variable h : well_founded r'

variable C : α' → Sort v
variable F : Π x, (Π (y : α'), r' y x → C y) → C x

def f : Π (x : α'), C x := well_founded.fix h F
-- What's going on here?

open nat

def div_rec_lemma {x y : ℕ} : 0 < y ∧ y ≤ x → x - y < x :=
λ h, sub_lt (lt_of_lt_of_le h.left h.right) h.left

def div.F (x : ℕ) (f : Π x₁, x₁ < x → ℕ → ℕ) (y : ℕ) : ℕ :=
if h : 0 < y ∧ y ≤ x then
    f  (x - y) (div_rec_lemma h) y + 1
else
    zero
-- div.F x f : ℕ → ℕ returns the "divide by y" function for that fixed x

def div := well_founded.fix lt_wf div.F

def div' : ℕ → ℕ → ℕ
| x y :=
    if h : 0 < y ∧ y ≤ x then
        have x - y < x, -- do similar thing for abs?
            from sub_lt (lt_of_lt_of_le h.left h.right) h.left,
        div (x - y) y + 1
    else
        0

example (x y : ℕ) (h : 0 < y ∧ y ≤ x) :
    div' x y = div (x-y) y + 1 :=
by rw [div', if_pos h]

def nat_to_bin : ℕ → list ℕ
| 0 := [0]
| 1 := [1]
| (n+2) :=
    have (n+2)/2 < n + 2, from sorry,
    nat_to_bin ((n+2)/2) ++ [n % 2]

#eval nat_to_bin 123456

def ack : nat → ℕ → nat
| 0 y := y + 1
| (x+1) 0 := ack x 1
| (x+1) (y+1) := ack x (ack (x+1) y)

#eval ack 3 5

/- 8.5 -- Mutual Recursion -/

mutual def even, odd
with even : ℕ → bool
| 0 := tt
| (a + 1) := odd a
with odd : ℕ → bool
| 0 := ff
| (a + 1) := even a

example (a : nat) : even (a + 1) = odd a :=
by simp [even]

lemma even_eq_not_odd : ∀ a, even a = bnot (odd a) :=
begin
    intro a, induction a,
    simp [even, odd],
    simp [*, even, odd], -- how does this work?
end

mutual inductive even_pred, odd_pred
with even_pred : ℕ → Prop
| even_zero : even_pred 0
| even_succ : ∀ n, odd n → even_pred (n + 1)
with odd_pred : ℕ → Prop
| odd_succ : ∀ n, even n → odd_pred (n + 1)

-- theorem not_odd_zero : ¬ odd_pred 0.
/-
mutual theorem even_of_odd_succ, odd_of_even_succ
with even_of_odd_succ : ∀ n, odd_pred (n+1) → even_pred n
| _ (odd_succ n h) := h
with odd_of_even_succ : ∀ n, even_pred (n + 1) → odd_pred n
| _ (even_succ n h) := h
-/

inductive term
| const : string → term
| app : string → list term → term

open term

mutual def num_consts, num_consts_lst
with num_consts : term → nat
| (const n) := 1
| (app n ts) := num_consts_lst ts 
with num_consts_lst : list term → nat
| [] := 0
| (x :: xs) := num_consts x + num_consts_lst xs

/- 8.6 -- Dependent Pattern Matching -/

