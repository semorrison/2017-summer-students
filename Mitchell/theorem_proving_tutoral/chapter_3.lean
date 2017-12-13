-- Section 3.5. To use the law of the excluded middle (p ∨ ¬p), you need to open classical

section
open classical

-- Double negation elimination
-- or.elim takes 3 arguments, with types p ∨ q, p → r, q → r; this gives a proof of r
theorem dne {p : Prop} (h : ¬¬p) : p :=
or.elim (em p)                          -- em p : p ∨ ¬ p
  (assume hp : p, hp)                   -- : p → p
  (assume hnp : ¬p, absurd hnp h)       
  -- : ¬ p → p, since we have already assumed ¬ ¬ p, so using absurd we can derive anything from h and hnp

-- This proof by cases uses em since we need to know that these are the only two cases possible - i.e. that p ∨ ¬ p
example {p : Prop} (h : ¬¬p) : p :=
by_cases
  (assume h1 : p, h1)
  (assume h1 : ¬p, absurd h1 h)
end

-- Exercise: Prove that em can be proved from double negation elimination
theorem em {p : Prop} (dne : ¬¬p → p) : p ∨ ¬ p := sorry
-- TODO

-- Exercises
variables p q r s : Prop

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := ⟨(λ h, ⟨h.right, h.left⟩), (λ h, ⟨h.right, h.left⟩)⟩
example : p ∨ q ↔ q ∨ p := 
    have h1 : p ∨ q → q ∨ p, from 
        assume h, h.elim or.inr or.inl,
    have h2 : q ∨ p → p ∨ q, from 
        assume h, h.elim or.inr or.inl,
    ⟨ h1, h2 ⟩


-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
    ⟨(λ h, ⟨h.left.left, h.left.right, h.right⟩), 
     (λ h, ⟨⟨h.left, h.right.left⟩, h.right.right⟩)⟩

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := 
    have h1 : (p ∨ q) ∨ r → p ∨ (q ∨ r), from
        assume h, h.elim
            (λ hpq, hpq.elim or.inl (λ hq, or.inr (or.inl hq)))
            (λ hr, or.inr (or.inr hr)),
    have h2 : p ∨ (q ∨ r) → (p ∨ q) ∨ r, from
        assume h, h.elim
            (λ hp, or.inl (or.inl hp))
            (λ hqr, hqr.elim (λ hq, or.inl (or.inr hq)) or.inr),
    ⟨ h1, h2 ⟩ 

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
    have h1 : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r), from
        assume h, h.right.elim
            (λ hq, or.inl ⟨ h.left, hq ⟩)
            (λ hr, or.inr ⟨ h.left, hr ⟩),
    have h2 : (p ∧ q) ∨ (p ∧ r) → p ∧ (q ∨ r), from
        assume h, h.elim
            (λ hpq, ⟨hpq.left, or.inl hpq.right⟩)
            (λ hpr, ⟨hpr.left, or.inr hpr.right⟩),
    ⟨ h1, h2 ⟩

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
    have h1 : p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r), from
        assume h, ⟨h.elim or.inl (λ hqr, or.inr hqr.left),
             h.elim or.inl (λ hqr, or.inr hqr.right) ⟩,
    have h2 : (p ∨ q) ∧ (p ∨ r) → p ∨ (q ∧ r), from
        assume h, h.left.elim or.inl (λ hq, h.right.elim or.inl (λ hr, or.inr (and.intro hq hr))),
    ⟨ h1, h2 ⟩ 

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
    have h1 : (p → (q → r)) → (p ∧ q → r), from
        assume h, assume hpq : p ∧ q,
        h hpq.left hpq.right,
    have h2 : (p ∧ q → r) → (p → (q → r)), from
        assume h, (λ hp, (λ hq, h ⟨hp, hq⟩)),
    ⟨ h1, h2 ⟩
    

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
    have h1 : ((p ∨ q) → r) → (p → r) ∧ (q → r), from
        assume h, ⟨λ hp, h (or.inl hp), (λ hq, h (or.inr hq)) ⟩,
    have h2 : (p → r) ∧ (q → r) → ((p ∨ q) → r), from
        assume h, (λ hpq, hpq.elim h.left h.right),
    ⟨ h1, h2 ⟩

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
    have h1 : ¬(p ∨ q) → ¬p ∧ ¬q, from
        assume h, ⟨assume hp : p, h (or.inl hp), assume hq : q, h (or.inr hq)⟩,
    have h2 : ¬p ∧ ¬q → ¬(p ∨ q), from
        assume h, assume hpq : p ∨ q,
        hpq.elim h.left h.right,
    ⟨ h1, h2 ⟩ 

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
    assume h, assume hpq : p ∧ q,
    h.elim (absurd hpq.left) (absurd hpq.right)

example : ¬(p ∧ ¬p) := 
    assume h : p ∧ ¬p,
    absurd h.left h.right

example : p ∧ ¬q → ¬(p → q) := 
    assume h, assume piq : p → q,
    absurd (piq h.left) h.right

example : ¬p → (p → q) := 
    assume h : ¬p, assume hp : p,
    absurd hp h 

example : (¬p ∨ q) → (p → q) :=
    assume h : ¬p ∨ q, assume hp : p,
    h.elim (absurd hp) id

example : p ∨ false ↔ p :=
    ⟨ (λ h : p ∨ false, h.elim id false.elim), or.inl ⟩ 

example : p ∧ false ↔ false := 
    ⟨ (λ h, h.right), (λ h, ⟨ h.elim, h⟩ ) ⟩ 

example : ¬(p ↔ ¬p) := 
    have h1 : (p → ¬p) → ¬p, from
        assume h, assume hp : p,
        h hp hp,
    have h2 : (¬p → p) → ¬¬p, from
        assume h, assume hnp : ¬p,
        hnp (h hnp),
    assume h, 
    absurd (h1 h.mp) (h2 h.mpr)

example : (p → q) → (¬q → ¬p) := 
    assume h, assume hnq : ¬q,
    assume hp : p,
    absurd (h hp) hnq

-- these require classical reasoning
open classical

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := sorry
    

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
    assume h,
    (em p).elim (λ hp : p, or.inr (λ hq : q, absurd (and.intro hp hq) h)) or.inl

example : ¬(p → q) → p ∧ ¬q := sorry
example : (p → q) → (¬p ∨ q) := sorry
example : (¬q → ¬p) → (p → q) := sorry

example : p ∨ ¬p :=
    em p

example : (((p → q) → p) → p) := sorry
