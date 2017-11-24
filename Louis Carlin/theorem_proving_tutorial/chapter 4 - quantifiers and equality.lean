
-- 4.1
namespace universal

-- ∀ x : α, p x
-- "for every x : α, p x holds"

/- introduction rule:
    Given a proof of p x, where x : α is arbitrary, we obtain a proof of ∀ x : α, p x
-/

/- elimination rule:
    Given a proof ∀ x : α, p x and any term t : α, we obtain a proof of p t
 -/

 -- ∀ x : α, p x is notation for Π x : α, p
 -- literally a function which takes any x : α and gives an element (proof) of p x

 variables (α : Type) (p q : α → Prop)

 example : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
 assume h : ∀ x : α, p x ∧ q x,
 assume y : α,
 show p y, from (h y).left

 variable (r : α → α → Prop)  

 variable (trans_r : ∀ {x y z}, r x y → r y z → r x z) -- expresses that r is transitive
 variable refl_r : ∀ {x}, r x x
 variable symm_r : ∀ {x y}, r x y → r y x
end universal

-- 4.2
namespace equality

 #check eq.refl
 #check eq.symm
 #check eq.trans
 #check eq.subst

 universe u

 example (α : Type u) (a b : α) (p : α → Prop)
    (h1: a = b) (h2 : p a) : p b :=
    eq.subst h1 h2

 example (α : Type u) (a b : α) (p : α → Prop)
    (h1: a = b) (h2 : p a) : p b :=
    h1 ▸ h2

variable α : Type
variables a b : α
variables f g : α → ℕ 
variable h1 : a = b
variable h2 : f = g

-- from eq.subst
example : f a = f b := congr_arg f h1
example : f a = g a := congr_fun h2 a
example : f a = g b := congr h2 h1

end equality

-- 4.3
namespace calculation

variables (a b c d e : ℕ)
variable h1 : a = b
variable h2 : b = c + 1
variable h3 : c = d 
variable h4 : e = 1 + d

theorem T1 : a = e :=
calc
    a = b : h1
    ... = c + 1 : h2
    ... = d + 1 : congr_arg _ h3
    ... = 1 + d : add_comm d 1
    ... = e : eq.symm h4

end calculation

-- 4.4
namespace existence
-- exists x : α, p x
-- ∃ x : α, p x

-- Introduction rule:
open nat

example : ∃ x : ℕ, x > 0 :=
have h : 1 > 0, from zero_lt_succ 0,
exists.intro 1 h

example (x y z : ℕ) (hxy : x < y) (hyz : y < z) :
    ∃ w, x < w ∧ w < z :=
exists.intro y (and.intro hxy hyz)

-- Elimination rule:

variables (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
exists.elim h
    (assume w,
        assume hw : p w ∧ q w,
        show ∃ x, q x ∧ p x, from ⟨w, hw.right, hw.left⟩)

#check exists.elim

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
match h with ⟨w, hw⟩ :=
    ⟨w, hw.right, hw.left⟩
end

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
let ⟨w, hpw, hqw ⟩ := h in ⟨ w, hqw, hpw⟩

def is_even (a : nat) := ∃ b, a = 2 * b

theorem even_plus_even {a b : nat}
    (h1 : is_even a) (h2: is_even b) : is_even (a+b) :=
match h1, h2 with
    ⟨w1, hw1⟩, ⟨w2, hw2⟩ := ⟨w1+w2, by rw [hw1, hw2, mul_add]⟩
end

-- Excercises
variable a : α 
variable r : Prop

example : (∃ x : α, r) → r :=
assume hx : ∃ x : α, r,
let ⟨x, hr ⟩ := hx in hr 

example : r → (∃ x : α, r) :=
assume hr : r,
exists.intro a hr


-- TODO: Can this be made more readable?
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
iff.intro 
    (
        assume hx : ∃ x, p x ∧ r,
        let ⟨ x, hpxr ⟩ := hx in 
        and.intro (exists.intro x hpxr.left) hpxr.right  
    )
    (
        assume hx : (∃ x, p x) ∧ r,
        let ⟨x, hpx⟩ := hx.left in 
        exists.intro x (and.intro hpx hx.right)
    )

#check ¬ p a

open classical

example : (∀ x, p x) ↔  ¬ (∃ x, ¬ p x) :=
iff.intro
    (
        assume hx : (∀ x, p x),
        assume hny : ∃ y, ¬ p y,
        let ⟨y, hnpy⟩ := hny in hnpy (hx y)
    )
    (
        assume hnx : ¬ (∃ x, ¬ p x), -- hnx : (∃ x, ¬ p x) → false
        assume x : α,
        -- WTS: p x
        or.elim (em (p x)) -- Do I need the excluded middle?
            (
                assume hpx : p x, 
                hpx
            )
            (
                assume hnpx : ¬ p x,
                absurd (exists.intro x hnpx) hnx
            )
    )


end existence

#check 1.2

