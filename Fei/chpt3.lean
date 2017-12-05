open classical

variables p q r s : Prop

/- commutativity of ∧ and ∨ -/
-- (1)
example : p ∧ q ↔ q ∧ p := 
iff.intro
  (assume hpq : p ∧ q,
  have hp : p, from hpq.left,
  have hq : q, from hpq.right,
    show q ∧ p, from ⟨hq, hp⟩
  )
  (assume hqp : q ∧ p,
  have hq : q, from hqp.left,
  have hp : p, from hqp.right,
    show p ∧ q, from ⟨hp, hq⟩
  )

-- (2)
example : p ∨ q ↔ q ∨ p := 
iff.intro
  (assume hpq : p ∨ q,
  or.elim hpq
    (assume hp : p, 
    show q ∨ p, from or.inr hp)
    (assume hq : q, 
    show q ∨ p, from or.inl hq)
  )
  (assume hqp : q ∨ p,
  or.elim hqp
    (assume hq : q, 
    show p ∨ q, from or.inr hq)
    (assume hp : p, 
    show p ∨ q, from or.inl hp)
  )


/- associativity of ∧ and ∨ -/

-- (1)
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := 
iff.intro
  (assume h : (p ∧ q) ∧ r,
    have hpq : p ∧ q, from h.left,
      have hp : p, from hpq.left,
      have hq : q, from hpq.right,
    have hr : r, from h.right,
    show p ∧ (q ∧ r), from ⟨hp, ⟨hq, hr⟩⟩
  )
  (assume h : p ∧ (q ∧ r),
    have hp : p, from h.left,
    have hqr : q ∧ r, from h.right,
      have hq : q, from hqr.left,
      have hr : r, from hqr.right,
    show (p ∧ q) ∧ r, from ⟨⟨hp, hq⟩, hr⟩
  )

-- (2)
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := 
iff.intro
  (assume h : (p ∨ q) ∨ r,
    or.elim h
      (assume hpq : p ∨ q,
      or.elim hpq 
        (assume hp : p,
        show p ∨ (q ∨ r), from or.inl hp)
        (assume hq : q,
        show p ∨ (q ∨ r), from or.inr (or.inl hq))
      )
      (assume hr : r,
      show p ∨ (q ∨ r), from or.inr (or.inr hr))
  )
  (assume h : p ∨ (q ∨ r),
    or.elim h
      (assume hp : p,
      show (p ∨ q) ∨ r, from or.inl (or.inl hp))
      (assume hqr : q ∨ r,
        or.elim hqr
          (assume hq : q,
          show (p ∨ q) ∨ r, from or.inl (or.inr hq))
          (assume hr : r,
          show (p ∨ q) ∨ r, from or.inr hr)
      )
  )
      

/- distributivity -/

-- (1)
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
iff.intro
  (assume h : p ∧ (q ∨ r),
    have hp : p, from h.left,
    or.elim (h.right)
      (assume hq : q,
        show (p ∧ q) ∨ (p ∧ r), from or.inl ⟨hp, hq⟩)
      (assume hr : r,
        show (p ∧ q) ∨ (p ∧ r), from or.inr ⟨hp, hr⟩)
  )
  (assume h : (p ∧ q) ∨ (p ∧ r),
    or.elim h
      (assume hpq : p ∧ q,
        have hp : p, from hpq.left,
        have hq : q, from hpq.right,
        show p ∧ (q ∨ r), from ⟨hp, or.inl hq⟩)
      (assume hpr : p ∧ r,
        have hp : p, from hpr.left,
        have hr : r, from hpr.right,
        show p ∧ (q ∨ r), from ⟨hp, or.inr hr⟩)
  )

-- (2)
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := 
iff.intro
  (assume h : p ∨ (q ∧ r),
    or.elim h
    (assume hp : p,
      show (p ∨ q) ∧ (p ∨ r), from ⟨or.inl hp, or.inl hp⟩)
    (assume hqr : q ∧ r, 
      have hq : q, from hqr.left,
      have hr : r, from hqr.right,
      show (p ∨ q) ∧ (p ∨ r), from ⟨or.inr hq, or.inr hr⟩)
  )
  (assume h : (p ∨ q) ∧ (p ∨ r),
    have hpq : p ∨ q, from h.left,
    have hpr : p ∨ r, from h.right,
    or.elim hpq
      (assume hp : p,
        show p ∨ (q ∧ r), from or.inl hp )
      (assume hq : q,
      or.elim hpr
        (assume hp : p, or.inl hp)
        (assume hr : r, 
        show p ∨ (q ∧ r), from or.inr ⟨hq,hr⟩)
      )
  )


/- other properties -/

-- (1)
example : (p → (q → r)) ↔ (p ∧ q → r) := 
iff.intro
  (assume h : (p → (q → r)),
    (assume hpq : p ∧ q,
      have hp : p, from hpq.left,
      have hq : q, from hpq.right,
      show r, from h hp hq))
  (assume h : (p ∧ q → r),
    (assume hp: p,
      (assume hq : q,
      show r, from h ⟨hp, hq⟩)
    )
  )

-- (2)
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := 
iff.intro
  (assume h : (p ∨ q) → r,
    and.intro
    (assume hp : p, 
    show r, from h (or.inl hp))
    (assume hq : q,
    show r, from h (or.inr hq))
  )
  (assume h : (p → r) ∧ (q → r),
    have hpr : p → r, from h.left,
    have hqr : q → r, from h.right,
    (assume hpq : p ∨ q,
      or.elim hpq
      (assume hp : p,
      show r, from hpr hp)
      (assume hq : q,
      show r, from hqr hq)
    )
  )

-- (3)
-- (p ∨ q) → false ↔ (p → false) ∧ (q → false)
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := 
iff.intro
  (assume h : ¬(p ∨ q),
    and.intro 
    (assume hp : p,
    show false, from h (or.inl hp))
    (assume hq : q,
    show false, from h (or.inr hq))
  )
  (assume h : ¬p ∧ ¬q, 
    have hnp : ¬p, from h.left,
    have hnq : ¬q, from h.right,
    (assume hpq : p ∨ q,
      or.elim hpq
      (assume hp : p, 
      show false, from hnp hp)
      (assume hq : q,
      show false, from hnq hq)
    )
  )

-- (4)
example : ¬p ∨ ¬q → ¬(p ∧ q) := 
(assume h : ¬p ∨ ¬q, 
  or.elim h
  (assume hnp : ¬p,
    (assume hpq : p ∧ q,
    show false, from hnp hpq.left)
  )
  (assume hnq : ¬q,
    (assume hpq : p ∧ q,
    show false, from hnq hpq.right)
  )
)

-- (5)
example : ¬(p ∧ ¬p) := 
(assume h : p ∧ ¬p,
  have hp : p, from h.left,
  have hnp : ¬p, from h.right,
  show false, from hnp hp)

-- (6)
example : p ∧ ¬q → ¬(p → q) := 
(assume h : p ∧ ¬q,
  have hp : p, from h.left,
  have hnq : ¬q, from h.right,
  (assume hpq : p → q,
   show false, from hnq (hpq hp))
)

-- (7)
example : ¬p → (p → q) := 
(assume h : ¬p,
  (assume hp : p,
  show q, from absurd hp h))

-- (8)
example : (¬p ∨ q) → (p → q) := 
(assume h : ¬p ∨ q, 
  or.elim h
  (assume hnp : ¬p, 
    (assume hp : p,
    show q, from absurd hp hnp))
  (assume hq : q,
    (assume hp : p,
    show q, from hq))
)
 
-- (9)
example : p ∨ false ↔ p := 
iff.intro
  (assume h : p ∨ false,
    or.elim h
    (assume hp : p,
    show p, from hp)
    (assume hf : false,
    show p, from false.elim hf)
  )
  (assume h : p,
  show p ∨ false, from or.inl h)

-- (10)
example : p ∧ false ↔ false := 
iff.intro
  (assume h : p ∧ false,
    have hp : p, from h.left,
    have hf : false, from h.right,
    show false, from hf)
  (assume h : false,
    and.intro
    (show p, from false.elim h)
    (show false, from h)
  )

-- (11) A
-- (p ↔ ¬p) → false
example : ¬(p ↔ ¬p) := 
(assume h : p ↔ ¬p,
    by_cases 
    (assume hp : p,
      have hpnp : p → ¬p, from h.mp,
      have hnp : ¬p, from hpnp hp,
      show false, from hnp hp)
    (assume hnp : ¬p,
      have hnpp : ¬p → p, from h.mpr,
      have hp : p, from hnpp hnp,
      show false, from hnp hp)
)

-- (11) B
-- How to prove it without classical logic?
example : ¬(p ↔ ¬p) := 
  assume h : p ↔ ¬p,
  have hpnp : p → ¬p, from h.mp,
  have hnpp : ¬p → p, from h.mpr,
  
  show false, from sorry


-- (12)
example : (p → q) → (¬q → ¬p) := 
(assume h : p → q,
  (assume hnq : ¬q,
    assume hp : p,
    have hq : q, from h hp,
    show false, from hnq hq
  )
)
    

/- these require classical reasoning -/

-- (1)
example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := 
assume h : p → r ∨ s,
  by_cases
  (assume hp : p,
    have hrs : r ∨ s, from h hp,
      or.elim hrs 
      (assume hr : r,
        have hpr : p → r, from (assume hp, hr),
        show (p → r) ∨ (p → s), from or.inl hpr)
      (assume hs : s,
        have hps : p → s, from (assume hp, hs),
        show (p → r) ∨ (p → s), from or.inr hps)
  )
  (assume hnp : ¬p,
    show (p → r) ∨ (p → s), from sorry)

-- (2)
example : ¬(p ∧ q) → ¬p ∨ ¬q := 
assume h : ¬(p ∧ q), 
  by_cases
  (assume hp : p,
    by_cases 
    (assume hq : q, show ¬p ∨ ¬q, from false.elim (h ⟨hp, hq⟩))
    (assume hnq : ¬q, show ¬p ∨ ¬q, from or.inr hnq)
  )
  (assume hnp : ¬p,
    show ¬p ∨ ¬q, from or.inl hnp)

-- (3)
example : ¬(p → q) → p ∧ ¬q := 
assume h : ¬(p → q), 
  by_cases
  (assume hp : p,
    by_cases 
    (assume hq : q, 
      have hpq : p → q, from (assume hp, hq),
      show p ∧ ¬q, from false.elim (h hpq))
    (assume hnq : ¬q, show p ∧ ¬q, from ⟨hp, hnq⟩)
  )
  (assume hnp : ¬p, 
    show p ∧ ¬q, from sorry
  )

-- (4)
example : (p → q) → (¬p ∨ q) := 
assume h : p → q, 
  by_cases
  (assume hp : p, 
    have hq : q, from h hp,
    show ¬p ∨ q, from or.inr hq)
  (assume hnp : ¬p,
    show ¬p ∨ q, from or.inl hnp)


-- (4)
example : (¬q → ¬p) → (p → q) := 
assume h : ¬q → ¬p, 
  by_cases
  (assume hq : q, 
    assume hp : p,
    show q, from hq)
  (assume hnq : ¬q,
    have hnp : ¬p, from h hnq,
    assume hp : p,
    show q, from absurd hp hnp)

-- (5)
example : p ∨ ¬p := em p

-- (6)
example : (((p → q) → p) → p) := 
assume h : (p → q) → p,
  by_cases 
  (assume hpq : p → q,
    show p, from h hpq)
  (assume hnpq : ¬(p → q),
    by_cases
    (assume hp : p,
    show p, from hp)
    (assume hnp : ¬p,
      by_cases 
      (assume hq : q,
      have hn : ¬p → q, from (assume hnp, hq),
      show p, from sorry)
      (assume hnq : ¬q,
      have hnn : ¬p → ¬q, from (assume hnp, hnq),
      show p, from sorry)
    )
  )

-- (7) example
example : ¬(p ∧ ¬q) → (p → q) :=
assume h : ¬(p ∧ ¬q),
assume hp : p,
show q, from
  or.elim (em q)
    (assume hq : q, show q, from hq)
    (assume hnq : ¬q, show q, from absurd (and.intro hp hnq) h)
