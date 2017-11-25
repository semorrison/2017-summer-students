/- temporary namespace to override default nat -/
namespace hide
inductive nat : Type
| zero : nat
| succ : nat → nat

def one : nat := nat.succ nat.zero

def add : nat → nat → nat
| m nat.zero := m
| m (nat.succ n) := nat.succ (add m n)

def double (n : nat) : nat := add n n

end hide

/-  -/
constants c d e : ℕ 
constants f : ℕ → ℕ
axiom     cd_eq : c = d

def foo : ℕ := 5
def bar := 6
def baz (x y : ℕ) (s : list ℕ) := [x, y] ++ s

theorem foo_eq_five : foo = 5 := rfl
theorem baz_theorem (x y : ℕ) : baz x y [] = [x, y] := rfl
lemma baz_lemma (x y : ℕ) : baz x y [] = [x, y] := rfl

example (x y : ℕ) : baz x y [] = [x, y] := rfl

/- recursion -/

def fib : ℕ → ℕ 
| 0 := 1
| 1 := 1
| (n + 2) := fib n + fib (n + 1)

universes u v
def list_add {α : Type u} [has_add α] : list α → list α → list α 
| [] _ := []
| _ [] := []
| (a :: l) (b :: m) := (a + b) :: list_add l m

section
parameters (x y : ℕ)
def bar2 : ℕ → ℕ := λ c, c + x + y
#check bar2
#print bar2
end 

#check Sort 0
#check Sort 1
#check Sort (u + 1)
#check Prop
#check Type 0
#check Type (u + 1)
#check Type 1 → Sort 0
#check Sort 0

#check list -- polymorphic over type universes
#check prod -- polymorphic over type universes
/- -/

theorem and_commutative (p q : Prop) : p ∧ q → q ∧ p := 
begin
    assume hpq : p ∧ q,
    have hp : p, from and.left hpq,
    have hq : q, from and.right hpq,
    show q ∧ p, from and.intro hq hp
end

#reduce and_commutative
constants a1 a2 : Prop
#check and_commutative a1 a2
#reduce and_commutative a1 a2

constant tuple : ℕ × ℕ × ℕ × ℕ
#check tuple.2.2.2 -- × associates to the right 
#check (1,2,3)

#check λ (α β γ : Type) (f : α → β) (g : β → γ) (x : α), g (f x)

/- curry time -/
section 
variables (α β : Type)
variable γ : Type

def curry  (f : α × β → γ) : α → β → γ := 
    λ (x : α) (y : β), f (x, y)

#check α 
#check curry
def uncurry (f : α → β → γ) : α × β → γ := 
    λ (p : α × β), f p.1 p.2

open list
#check cons
end
#check α -- variable's scope is its local section/namespace
#check cons -- open's scope is its local section/namespace
#check curry -- not just in the section

/- dependent types -/
namespace hide 
universe w 
constant list : Type w → Type w

constant nil : Π {α : Type w}, list α
constant cons : Π {α : Type w}, list α → α
constant map : Π {α β : Type w}, (α → β) → list α → α
#check map
def ident {α : Type u} (x : α) := x

constant vec : Type w → ℕ → Type w
constant nil_vec : Π (α : Type w), vec α 0
constant append_vec : Π (α : Type w) (m n : ℕ), vec α m →  vec α n →  vec α (m + n)
constant vec_add : Π {n : ℕ}, vec ℕ n → vec ℕ n → vec ℕ n
constant vec_reverse : Π {n : ℕ}, vec ℕ n → vec ℕ n
#check vec_add

end hide

#check id
#check @id -- make the implicit arguments explicit
#check @id ℤ 2

#print and
#check @and.intro
#check @and.elim
#check @and.left
#check @and.right
#check @or.inl
#check @or.inr
#check @or.elim
#check @exists.intro
#check @exists.elim
#check @eq.refl
#check @eq.subst

/- -/
variables p q r s : Prop
example p → q → p := 
    assume hp : p,
    assume hq : q, 
    show p, from hp

theorem modus_ponens (h₂ : p → q) (h₁ : q → r) (h₃ : p) : r := h₁ (h₂ h₃)
#check modus_ponens

theorem reverse_implication : (p → q) → ¬q → ¬p := modus_ponens p q false
#check reverse_implication

theorem double_negation : p → ¬¬p :=
    assume hp : p, assume hnp : ¬p, hnp hp

theorem ex_falso (hp : p) (hnp : ¬p) : q := false.elim (hnp hp)
-- or @false.elim q (hnp hp)
-- or absurd hp hnp
example : (true → p) → p := assume hp : true → p, hp trivial
#check trivial -- "trivial" is the proof of the proposition "true"

example p → q → p ∧ q := 
    assume hp : p,
    assume hq : q,
    show p ∧ q, from and.intro hp hq
example (hp : p) (hq : q) : p ∧ q := and.intro hp hq 
#check λ (hp : p) (hq : q), and.intro hp hq

example : p → p ∨ q := λ (hp : p), or.inl hp
example : q → p ∨ q := 
    assume hq : q, 
    show p ∨ q, from or.intro_right p hq
example : p ∨ q → q ∨ p :=
    assume h : p ∨ q,
    or.elim h 
        (assume hp : p, or.inr hp)
        (assume hq : q, or.inl hq)


theorem and_swap : p ∧ q ↔ q ∧ p :=
    ⟨(λ h, ⟨h.right, h.left⟩), (λ h, ⟨h.right, h.left⟩)⟩
example (h : p ∧ q) : q ∧ p := (and_swap p q).elim_left h

example : p ∧ q → q ∧ p :=
    assume h : p ∧ q,
    have hp : p, from h.left, -- prove subgoal
    suffices hq : q, from ⟨hq, hp⟩, -- replace main goal
    show q, from h.right -- prove main goal

/- intuitionistic logic playground -/

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := ⟨(λ h, ⟨h.right, h.left⟩), (λ h, ⟨h.right, h.left⟩)⟩
example : p ∨ q ↔ q ∨ p := 
    have h1 : p ∨ q → q ∨ p, from 
        assume h, or.elim h or.inr or.inl,
    have h2 : q ∨ p → p ∨ q, from 
        assume h, or.elim h or.inr or.inl,
    ⟨h1, h2⟩

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := 
    ⟨(λ h, ⟨h.left.left, h.left.right, h.right⟩), 
     (λ h, ⟨⟨h.left, h.right.left⟩, h.right.right⟩)⟩
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := 
    have h1 : (p ∨ q) ∨ r → p ∨ (q ∨ r), from 
        assume h, or.elim h 
            (λ hporq, or.elim hporq or.inl
                (λ hq, or.inr (or.inl hq)))
            (λ hr, or.inr (or.inr hr)),
    have h2 : p ∨ (q ∨ r) → (p ∨ q) ∨ r, from 
        assume h, or.elim h 
            (λ hp, or.inl (or.inl hp))
            (λ hqorr, or.elim hqorr (λ hq, or.inl (or.inr hq)) or.inr),
    ⟨h1, h2⟩

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := 
    have h1 : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r), from 
        assume h11 : p ∧ (q ∨ r), 
        have h111 : p, from h11.left,
        have h112 : q ∨ r, from h11.right,
        or.elim h112 
            (λ hq : q, or.inl ⟨h111, hq⟩)
            (λ hr : r, or.inr ⟨h111, hr⟩),
    have h2 : (p ∧ q) ∨ (p ∧ r) → p ∧ (q ∨ r), from 
        assume h21 : (p ∧ q) ∨ (p ∧ r),
        or.elim h21 
            (λ hp, ⟨hp.left, or.inl hp.right⟩)
            (λ hp, ⟨hp.left, or.inr hp.right⟩),
    ⟨h1, h2⟩

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := 
    have h1 : p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r), from 
        assume h11 : p ∨ (q ∧ r),
        or.elim h11 
            (λ hp, ⟨or.inl hp, or.inl hp⟩) 
            (λ hqr, ⟨or.inr (hqr.left), or.inr (hqr.right)⟩),
    have h2 : (p ∨ q) ∧ (p ∨ r) → p ∨ (q ∧ r), from 
        assume h21 : (p ∨ q) ∧ (p ∨ r),
        have hpq : p ∨ q, from h21.left,
        have hpr : p ∨ r, from h21.right,
        or.elim hpq or.inl
            (λ hq, or.elim hpr or.inl (λ hr, or.inr ⟨hq, hr⟩)),
    ⟨h1, h2⟩

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := 
    have h1 : (p → (q → r)) → (p ∧ q → r), from
        assume h11 : p → (q → r), assume hpq : p ∧ q,
        h11 hpq.left hpq.right,
    have h2 : (p ∧ q → r) → (p → (q → r)), from
        assume h21 : p ∧ q → r, assume hp : p, assume hq : q,
        h21 ⟨hp, hq⟩,
    ⟨h1, h2⟩

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := 
    have h1 : ((p ∨ q) → r) → (p → r) ∧ (q → r), from
        assume h11 : (p ∨ q) → r,
        ⟨(λ hp : p, h11 (or.inl hp)), (λ hq : q, h11 (or.inr hq))⟩,
    have h2 : (p → r) ∧ (q → r) → (p ∨ q) → r, from
        assume h21 : (p → r) ∧ (q → r), assume h22 : p ∨ q,
        or.elim h22 h21.left h21.right,
    ⟨h1, h2⟩

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := 
    have h1 : ¬(p ∨ q) → ¬p ∧ ¬q, from
        assume h11 : ¬(p ∨ q), 
        have h12 : ¬p, from 
            assume hp : p, absurd (or.inl hp) h11,
        have h13 : ¬q, from 
            assume hq : q, absurd (or.inr hq) h11,
        ⟨h12, h13⟩,
    have h2 : ¬p ∧ ¬q → ¬(p ∨ q), from
        assume h21 : ¬p ∧ ¬q, assume h22 : p ∨ q,
        or.elim h22 
            (λ hp : p, absurd hp h21.left) 
            (λ hq : q, absurd hq h21.right),
    ⟨h1, h2⟩

example : ¬p ∨ ¬q → ¬(p ∧ q) := 
    assume h1 : ¬p ∨ ¬q, assume h2 : p ∧ q,
    or.elim h1 (λ hnp : ¬p, absurd h2.left hnp) (λ hnq : ¬q, absurd h2.right hnq)

example : ¬(p ∧ ¬p) := λ h, h.right h.left

example : p ∧ ¬q → ¬(p → q) := 
    assume h1 : p ∧ ¬q, assume h2 : p → q, h1.right (h2 h1.left)

example : ¬p → (p → q) := λ hnp hp, false.elim (hnp hp)

example : (¬p ∨ q) → (p → q) := 
    assume h : ¬p ∨ q, assume hp : p,
    or.elim h (λ hnp, absurd hp hnp) id

example : p ∨ false ↔ p := 
    have h1 : p ∨ false → p, from
        assume h11 : p ∨ false, 
        or.elim h11 id false.elim,
    ⟨h1, or.inl⟩

example : p ∧ false ↔ false := ⟨and.elim_right, false.elim⟩

example : ¬(p ↔ ¬p) :=
    have h1 : (p → ¬p) → ¬p, from 
        assume h11 : p → ¬p,
        assume h12 : p,
        h11 h12 h12,
    have h2 : (¬p → p) → ¬¬p, from 
        assume h21 : ¬p → p,
        assume h22 : ¬p,
        h22 (h21 h22),
    assume h : p ↔ ¬p, absurd (h1 h.elim_left) (h2 h.elim_right)

example : (p → q) → (¬q → ¬p) := 
    assume h1 : p → q, assume hnq : ¬q, assume hp : p,
    absurd (h1 hp) hnq

theorem or_not_left : p ∨ q → ¬p → q := 
    assume h : p ∨ q, assume hnp : ¬p,
    or.elim h (λ hp : p, absurd hp hnp) id
#check or_not_left

/- classical logic playground -/
open classical 

example : p ∨ ¬p := em p

theorem classical_double_negation : ¬¬p → p :=
    or.elim (em p)
        (λ hp _, hp)
        (λ hnp hnnp, absurd hnp hnnp)

example : ¬(p ∧ q) → ¬p ∨ ¬q := 
    assume h1 : ¬(p ∧ q),
    have hpnp : p ∨ ¬p, from em p,
    or.elim hpnp 
        (λ hp : p, or.inr (λ hq : q, absurd (and.intro hp hq) h1))
        or.inl

theorem classical_reverse_implication : ¬(p → q) → p ∧ ¬q := 
    assume h : ¬(p → q),
    have hnnp : ¬¬p, from   
        assume hnp : ¬p, 
        have hpq : p → q, from λ hp : p, absurd hp hnp,
        absurd hpq h,
    have hp : p, from classical_double_negation p hnnp,
    have hnq : ¬q, from 
        assume hq : q, absurd (λ _, hq) h,
    ⟨hp, hnq⟩

#check classical_reverse_implication (p → q) p

example : (p → q) → (¬p ∨ q) := 
    assume h : p → q,
    have hpnp : p ∨ ¬p, from em p,
    or.elim hpnp (λ hp : p, or.inr (h hp)) or.inl

example : (¬q → ¬p) → (p → q) := 
    assume h1 : ¬q → ¬p, assume hp : p, 
    have hqnq : q ∨ ¬q, from em q,
    or.elim hqnq id (assume hnq : ¬q, absurd hp (h1 hnq))

example : (((p → q) → p) → p) := 
    assume h : (p → q) → p,
    have hnpq : (p → q) ∨ ¬(p → q), from em (p → q),
    or.elim hnpq (λ h1 : p → q, h h1) 
        (λ h2 : ¬(p → q), 
            have h21 : p ∧ ¬q, from classical_reverse_implication p q h2,
            h21.left)

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := 
    assume h : p → r ∨ s,
    have hn : (p → r) ∨ ¬(p → r), from em (p → r),
    or.elim hn or.inl 
        (λ h2 : ¬(p → r), 
            have h21 : p ∧ ¬r, from classical_reverse_implication p r h2,
            have hp : p, from h21.left,
            have hnr : ¬r, from h21.right,
            have hrs : r ∨ s, from h hp,
            have hs : s, from or_not_left r s hrs hnr,
            have hps : p → s, from (λ _, hs),
            or.inr hps)