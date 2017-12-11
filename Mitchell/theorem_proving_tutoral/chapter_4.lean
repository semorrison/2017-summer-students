-- Exercise 1. Prove these equivalences:
section
variables (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := 
    have h1 : (∀ x, p x ∧ q x) → (∀ x, p x) ∧ (∀ x, q x), from
        assume h, 
        ⟨ λ x : α, (h x).left ,  λ x : α, (h x).right ⟩,
    have h2 : (∀ x, p x) ∧ (∀ x, q x) → (∀ x, p x ∧ q x), from
        assume h, assume x : α,
        ⟨ h.left x, h.right x ⟩,
    ⟨ h1, h2 ⟩

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := 
    assume h, assume hp : (∀ x, p x), assume x : α,
    h _ (hp x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := 
    assume h, assume x : α,
    h.elim (λ h1, or.inl (h1 x)) (λ h2, or.inr (h2 x))
end

-- Exercise 2. It is often possible to bring a component of a formula outside a universal quantifier, 
-- when it does not depend on the quantified variable. 
-- Try proving these (one direction of the second of these requires classical logic):
section
open classical

variables (α : Type) (p q : α → Prop)
variable r : Prop

example : α → ((∀ x : α, r) ↔ r) := 
    assume ha,
    have h1 :  (∀ x : α, r) → r, from
        assume hx, 
        hx ha,
    have h2 : r → (∀ x : α, r), from
        assume hr,
        assume hx, id hr,
    ⟨ h1, h2 ⟩

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := 
    have h1 : (∀ x, p x ∨ r) → (∀ x, p x) ∨ r, from
        assume h,
        by_cases
        or.inr
        (assume hnr : ¬r, 
        have (∀ x, p x), from (assume hx : α,
        have p hx ∨ r, from h hx,
        this.elim id (λ hr : r, absurd hr hnr)),
        or.inl this),
    have h2 : (∀ x, p x) ∨ r → (∀ x, p x ∨ r), from
        assume h, assume hx,
        h.elim (λ hp, or.inl (hp hx)) or.inr,
    ⟨ h1 , h2 ⟩

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := 
    have h1 : (∀ x, r → p x) → (r → ∀ x, p x), from
        assume h,
        assume hr : r, assume hx : α,
        h hx hr,
    have h2 : (r → ∀ x, p x) → (∀ x, r → p x), from
        assume h,
        assume hx : α, assume hr : r,
        h hr hx,
    ⟨ h1 , h2 ⟩

end

-- Exercise 3. Consider the “barber paradox,” that is, the claim that in a certain town 
-- there is a (male) barber that shaves all and only the men who do not shave themselves. 
-- Prove that this is a contradiction:
section
open classical

variables (men : Type) (barber : men)
variable  (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) :
  false :=
  by_cases
  (assume hb : shaves barber barber,
  absurd hb ((h barber).elim_left hb))
  (assume hnb : ¬shaves barber barber,
  absurd ((h barber).elim_right hnb) hnb)

end

-- Exercise 4.

namespace hide

def divides (m n : ℕ) : Prop := ∃ k, m * k = n

instance : has_dvd nat := ⟨divides⟩

def even (n : ℕ) : Prop := 2 ∣ n

section
  variables m n : ℕ

  #check m ∣ n
  #check m^n
  #check even (m^n +3)
end

def prime (n : ℕ) : Prop := n > 1 ∧ ∀ m : ℕ, m ∣ n → m = 1 ∨ m = n

def infinitely_many_primes : Prop := ∀ m : ℕ, ∃ n > m, prime n 

def Fermat_prime (n : ℕ) : Prop := prime n ∧ ∃ k, n = 2^(2^k) + 1

def infinitely_many_Fermat_primes : Prop := ∀ m : ℕ, ∃ n > m, Fermat_prime n 

def goldbach_conjecture : Prop := ∀ n : ℕ, even n ∧ n > 2 → ∃ m k : ℕ, prime m ∧ prime k ∧ n = m + k

def Goldbach's_weak_conjecture : Prop := ∀ n : ℕ, ¬even n ∧ n > 5 → ∃ m k l : ℕ, 
    prime m ∧ prime k ∧ prime l ∧ n = m + k + l

def Fermat's_last_theorem : Prop := ∀ x y z n : ℕ, 
  x > 0 ∧ y > 0 ∧ z > 0 ∧ x^n + y^n = z^n → n <= 2

end hide


open classical

variables (α : Type) (p q : α → Prop)
variable a : α
variable r : Prop

example : (∃ x : α, r) → r := assume ⟨ hx, hr ⟩, hr

example : r → (∃ x : α, r) := assume hr, ⟨ a, hr ⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := 
    have h1 : (∃ x, p x ∧ r) → (∃ x, p x) ∧ r, from
        assume ⟨ hx, hp, hr ⟩, ⟨ ⟨ hx, hp ⟩ , hr ⟩,
    have h2 : (∃ x, p x) ∧ r → (∃ x, p x ∧ r), from
        assume ⟨ ⟨ hx, hp ⟩ , hr ⟩, ⟨ hx, hp, hr ⟩,
    ⟨ h1, h2 ⟩

section

variables (real : Type) [ordered_ring real]
variables (log exp : real → real)
variable  log_exp_eq : ∀ x, log (exp x) = x
variable  exp_log_eq : ∀ {x}, x > 0 → exp (log x) = x
variable  exp_pos    : ∀ x, exp x > 0
variable  exp_add    : ∀ x y, exp (x + y) = exp x * exp y

-- this ensures the assumptions are available in tactic proofs
include log_exp_eq exp_log_eq exp_pos exp_add

example (x y z : real) :
  exp (x + y + z) = exp x * exp y * exp z :=
by simp [exp_add]

example (y : real) (h : y > 0)  : exp (log y) = y :=
exp_log_eq h

theorem log_mul {x y : real} (hx : x > 0) (hy : y > 0) :
  log (x * y) = log x + log y :=
calc
    log (x * y) = log (exp (log x) * y)             : by rw exp_log_eq hx
    ...         = log (exp (log x) * exp (log y))   : by rw exp_log_eq hy
    ...         = log (exp (log x + log y))         : by rw exp_add
    ...         = log x + log y                     : by rw log_exp_eq
end

#check sub_self

example (x : ℤ) : x * 0 = 0 :=
calc
    x * 0 = x * (1 - 1)        : by rw sub_self
    ...   = x*1 - x*1          : by rw mul_sub
    ...   = x - x              : by rw mul_one
    ...   = 0                  : by rw sub_self