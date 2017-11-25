/-
Π notation is fundamental.
p → q is Π x : p, q
α → β is Π x : α, β
-/

universe u

section
variables (α : Type) (p q : α → Prop)

example : (∀ x : α, p x ∧ q x) → ∀ y : α, p y  :=
  assume h : ∀ x : α, p x ∧ q x,
  assume y : α,
  show p y, from (h y).left
end

section
variables (α : Type u) (r : α → α → Prop)

variable refl_r : ∀ x, r x x -- "r is a reflexive relation"
variable symm_r : ∀ {x y}, r x y → r y x
variable trans_r : ∀ {x y z}, r x y → r y z → r x z
-- x y z : α by type inferrence from r
#check refl_r

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) :
  r a d :=
trans_r (trans_r hab (symm_r hcb)) hcd

variables (a b c : α)
variables (hab : r a b) (hbc : r b c)

#check @trans_r
#check trans_r hab
#check trans_r hab hbc
end

section 

-- @ .{u} instantiates the metavariables in the universe u
#print =
#check eq.refl        -- ∀ (a : ?M_1), a = a
#check @eq.refl.{u}   -- ∀ {α : Sort u} (a : α), a = a
#check @eq.symm.{u}   -- ∀ {α : Sort u} {a b : α}, a = b → b = a
#check @eq.trans.{u}

variables (α β: Type u) (a b c d : α)
variables (hab : a = b) (hcb : c = b) (hcd : c = d)

example : a = d := eq.trans (eq.trans hab hcb.symm) hcd

-- rfl is eq.refl _
example (f : α → β) (a : α) : (λ x, f x) a = f a := rfl
example (a : α) (b : α) : (a, b).1 = a := rfl
example : 2 + 3 = 5 := rfl

/- terms in the Calculus of Constructions have a computational interpretation, 
   terms with a common reduct are definitionally equal. 
   to check a = a, for kernel must compute both sides, to know if they have
   a common reduct. -/

variables (e : add_comm_semigroup ℕ) (f g: ℕ)
#check @add_comm ℕ e f g

example (f : α → β) (a : α) : (λ x, f x) a = f a := rfl
example (a : α) (b : α) : (a, b).1 = a := rfl
example : 2 + 3 = 5 := rfl

-- Compare the following two...
#check @eq.subst.{u}

example (p : α → Prop) : a = b → p a → p b :=
  assume h1 : a = b, assume h2 : p a, 
  h1 ▸ h2

example : Π (p : α → Prop), a = b → p a → p b :=
  assume p : α → Prop, assume h1 : a = b, assume h2 : p a, 
  h1 ▸ h2

#check @congr.{u u}
#check @congr_arg.{u u}
#check @congr_fun.{u u}
#check @imp_congr_eq
end

section
variables x y z : ℤ
#check mul_add x y z 
#check add_assoc x y z

-- expand (x + y)² 
example (x y : ℕ) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y,
    from mul_add (x + y) x y,
  have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y),
    from (add_mul x y x) ▸ ((add_mul x y y) ▸ h1), 
    -- ▸ assoc to right, as usual
  eq.trans h2 (add_assoc (x * x + y * x) (x * y) (y * y)).symm
  -- + assoc to left, thus 
  -- add_assoc (x * x + y * x) (x * y) (y * y) gives
  -- x * x + y * x + x * y + y * y = x * x + y * x + (x * y + y * y)
  -- then use eq.symm to flip it around, then chain with h2.
end

/- Calculational Proofs -/
section 
-- a chain of results composed by basic principles such as transitivity.
-- best used with simp and rewrite tactics.
variables (a b c d e : ℕ)
variable h1 : a = b
variable h2 : b = c + 1
variable h3 : c = d
variable h4 : e = 1 + d

theorem T1 : a = e :=
calc
  a     = b      : h1
    ... = c + 1  : h2
    ... = d + 1  : congr_arg nat.succ h3
    -- ∀ (f : α → β), a₁ = a₂ → f a₁ = f a₂
    -- Here, (congr_arg _ h3) is supposed to be (c + 1 = d + 1)
    -- so f a₁ is c + 1, f a₂ is d + 1
    -- h3 is supposed to be a₁ = a₂, so c is a₁, d is a₂ 
    -- so f c is c + 1, which expands to (succ c), so f is succ
    -- Thus, the following line would also work:
    -- ... = d + 1  : congr_arg nat.succ h3
    ... = 1 + d  : add_comm d (1 : ℕ)
    -- add_comm _ _ would work too.
    ... = e      : eq.symm h4
-- that type inference is "higher-order unification" which is in general 
-- undecidable. So it might fail sometimes.

include h1 h2 h3 h4 -- by default, tactics don't include variables
theorem T2 : a = e :=
calc
  a     = b      : by rw h1
    ... = c + 1  : by rw h2
    ... = d + 1  : by rw h3
    ... = 1 + d  : by rw add_comm -- specialize to add_comm d (1 : ℕ) 
    ... =  e     : by rw h4
-- rw uses a given equality (or a theorem about equality, like add_comm) 
-- to “rewrite” the goal. If it reduces it to t = t, it uses reflexivity.

theorem T3 : a = e := by rw [h1, h2, h3, add_comm, h4]

-- simplifies main goal or non-dependent hypotheses. 
theorem T4 : a = e := by simp [h1, h2, h3, h4]

omit h4
-- include h4
-- Somehow, this will not work unless h4 is omitted??
theorem T5 (a b c d : ℕ)
  (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
calc
  a     = b     : h1
    ... < b + 1 : nat.lt_succ_self b
    ... ≤ c + 1 : nat.succ_le_succ h2
    ... < d     : h3
#check T5

example (x y : ℕ) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by rw [mul_add, add_mul, add_mul, ←add_assoc]
example (x y : ℕ) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by simp [add_mul, mul_add]
end

/- ∃ -/
section
open nat

example : ∃ x : ℕ, 0 < x :=
  exists.intro 1 (zero_lt_succ 0)

example (x z : ℕ) (h : x > z) : ∃ y, y < x := 
  exists.intro z h

example (x y z : ℕ) (hxy : x < y) (hyz : y < z) :
  ∃ w, x < w ∧ w < z := 
  exists.intro y (and.intro hxy hyz)

#check @exists.intro

variables (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  exists.elim h
    (assume w, assume hw : p w ∧ q w,
      show ∃ x, q x ∧ p x, from ⟨w, hw.right, hw.left⟩)
-- match statement, and some constructor patter matching
-- with optional type annotation
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with ⟨w, (hw : p w ∧ q w)⟩ :=
    ⟨w , hw.right, hw.left⟩
  end
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with ⟨(w : α), (hwl : p w), (hwr : q w)⟩ :=
    ⟨w , hwr, hwl⟩
  end
-- let pattern matching
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  let ⟨w, hpw, hqw⟩ := h in ⟨w, hqw, hpw⟩
-- implicit pattern matching. 
-- (h : ∃ x, p x ∧ q x) is moved to the right of the colon, to allow 
-- assume pattern matching.
example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
  assume ⟨w, hpw, hqw⟩, ⟨w, hqw, hpw⟩
end

section
variable f : ℕ → ℕ 
variable h : ∀ x : ℕ, f x ≤ f (x + 1)

-- without labels, use ‹ › to ask Lean to find a hypothesis that is equal 
-- to that statement. It's equivalent to "show by assumption".
-- notation `‹` p `›` := show p, by assumption
example : f 0 ≥ f 1 → f 1 ≥ f 2 → f 0 = f 2 :=
  assume : f 0 ≥ f 1, assume : f 1 ≥ f 2,
  have f 0 ≥ f 2, from le_trans ‹f 2 ≤ f 1› ‹f 1 ≤ f 0›,
  have f 0 ≤ f 2, from le_trans (h 0) (h 1),
  show f 0 = f 2, from le_antisymm this ‹f 0 ≥ f 2›
end

/- exercises -/

section
open classical

variables (α : Type) (p q : α → Prop)
variable r : Prop

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := assume : _,
  or.elim this 
    (assume h : ∀ (x : α), p x, assume hx, 
    show p hx ∨ q hx, from or.inl (h hx))
    (assume h : ∀ (x : α), q x, assume hx, 
    show p hx ∨ q hx, from or.inr (h hx))

example : α → ((∀ x : α, r) ↔ r) := assume ha : α, 
  have h1 : (∀ x : α, r) → r, from
    assume : ∀ x : α, r, this ha,
  have h2 : r → (∀ x : α, r), from
    assume : r, (λ _, this),
  ⟨h1, h2⟩

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := 
  have h1 : (∀ x, p x ∨ r) → (∀ x, p x) ∨ r, from
    assume haxpxr : (∀ x, p x ∨ r), by_cases -- classical
      or.inr
      (assume hnr : ¬r, 
      have ∀ (x : α), p x, from (assume ha : α, 
      have p ha ∨ r, from haxpxr ha, 
      or.elim this id (λ hr, absurd hr hnr)),
      show (∀ (x : α), p x) ∨ r, from or.inl this),
  have h2 : (∀ x, p x) ∨ r → (∀ x, p x ∨ r), from
    assume : (∀ x, p x) ∨ r, or.elim this 
      (assume haxpx : ∀ x, p x, (λ hx, or.inl (haxpx hx)))
      (assume : r, (λ _, or.inr this)),
  ⟨h1, h2⟩ -- h1 is classical

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := 
  have h1 : (∀ x, r → p x) → r → ∀ x, p x, from
    assume haxrpx : (∀ x, r → p x), assume hr : r, assume hx,
    haxrpx hx hr,
  have h2 : (r → ∀ x, p x) → (∀ x, r → p x), from
    assume hraxpx : (r → ∀ x, p x), assume hx, assume hr : r,
    hraxpx hr hx,
  ⟨h1, h2⟩
end

section
-- barber paradox, proven in intuitionistic logic
variables (men : Type) (barber : men)
variable  (shaves : men → men → Prop)
variable (p : Prop)

lemma npiffnp : ¬(p ↔ ¬p) :=
    have h1 : (p → ¬p) → ¬p, from 
        assume h11 : p → ¬p, assume h12 : p,
        h11 h12 h12,
    have h2 : (¬p → p) → ¬¬p, from 
        assume h21 : ¬p → p, assume h22 : ¬p,
        h22 (h21 h22),
    assume h : p ↔ ¬p, absurd (h1 h.elim_left) (h2 h.elim_right)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) :
  false := npiffnp (shaves barber barber) (h barber)
end

namespace hide

def divides (m n : ℕ) : Prop := ∃ (k : ℕ), m * k = n
instance : has_dvd nat := ⟨divides⟩
def even (n : ℕ) : Prop := 2 ∣ n
-- to type ∣, use \|, or \mid

section
  variables m n : ℕ

  #check m ∣ n
  #check m^n
  #check even (m^n +3)
end

def prime (n : ℕ) : Prop := n > 2 ∧ ∀ m : ℕ, m ∣ n → m = 1 ∨ m = n

def infinitely_many (p : ℕ → Prop) : Prop := 
  ∀ m : ℕ, ∃ n : ℕ, n > m ∧ p n

def infinitely_many_primes : Prop := infinitely_many prime

def Fermat_prime (n : ℕ) : Prop := prime (2 ^ (2 ^ n))
-- ^ assoc to left

def infinitely_many_Fermat_primes : Prop := infinitely_many Fermat_prime

def goldbach_conjecture : Prop := ∀ n : ℕ, even n ∧ n > 2 → 
  (∃ a b : ℕ, prime a ∧ prime b ∧ a + b = n)
-- all even numbers greater than 2 is the sum of two primes

def Goldbach's_weak_conjecture : Prop := ∀ n : ℕ, ¬even n ∧ n > 7 → 
  (∃ a b c : ℕ, prime a ∧ prime b ∧ prime c ∧ 
   ¬even a ∧ ¬even b ∧ ¬even c ∧ 
   a + b + c = n)
-- all odd numbers greater than 7 are the sum of three odd primes

def Fermat's_last_theorem : Prop := ∀ x y z n : ℕ, 
  x > 0 ∧ y > 0 ∧ z > 0 ∧ x^n + y^n = z^n → n <= 2

end hide

section
open classical

variables (α : Type) (p q : α → Prop)
variable a : α
variable r : Prop

example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
by_contradiction -- classical step
  (assume h1 : ¬ ∃ x, p x,
    have h2 : ∀ x, ¬ p x, from
      assume x,
      assume h3 : p x,
      have h4 : ∃ x, p x, from  ⟨x, h3⟩,
      show false, from h1 h4,
    show false, from h h2)

example : (∃ x : α, r) → r := assume ⟨hx, hr⟩ , hr

example : r → (∃ x : α, r) := assume hr, ⟨a, hr⟩
-- there has to actually exist such an element a : α 

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := 
  have h1 : (∃ x, p x ∧ r) → (∃ x, p x) ∧ r, from 
    assume ⟨hx, hpx, hr⟩, ⟨⟨hx, hpx⟩, hr⟩,
  have h2 : (∃ x, p x) ∧ r → (∃ x, p x ∧ r), from 
    assume ⟨⟨hx, hpx⟩, hr⟩, ⟨hx, hpx, hr⟩,
  ⟨h1, h2⟩ 

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := 
  have h1 : (∃ x, p x ∨ q x) → (∃ x, p x) ∨ (∃ x, q x), from 
    assume ⟨_, hpqx⟩, or.elim hpqx 
      (assume hpx, or.inl ⟨_, hpx⟩) -- p x → (∃ x, p x) ∨ (∃ x, q x)
      (assume hqx, or.inr ⟨_, hqx⟩), -- q x → (∃ x, p x) ∨ (∃ x, q x)
  have h2 : (∃ x, p x) ∨ (∃ x, q x) → (∃ x, p x ∨ q x), from 
    assume : (∃ x, p x) ∨ (∃ x, q x), or.elim this
      (assume ⟨_, hp⟩, ⟨_, or.inl hp⟩) -- (∃ x, p x) → (∃ x, p x ∨ q x)
      (assume ⟨_, hq⟩, ⟨_, or.inr hq⟩), -- (∃ x, q x) → (∃ x, p x ∨ q x)
  ⟨h1, h2⟩ 

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := 
  have h1 : (∀ x, p x) → ¬ (∃ x, ¬ p x), from 
    assume hapx, assume ⟨hx, hnpx⟩, 
    have p hx, from hapx hx,
    show false, from hnpx this,
  have h2 : ¬ (∃ x, ¬ p x) → (∀ x, p x), from 
    assume hnenpx : ¬ (∃ x, ¬ p x), 
    assume hx, 
    show p hx, from by_contradiction (assume : ¬p hx,
      have (∃ x, ¬ p x), from ⟨hx, this⟩,
      show false, from hnenpx this), -- classical
  ⟨h1, h2⟩ -- h2 is classical

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := 
  have h1 : (∃ x, p x) → ¬ (∀ x, ¬ p x), from 
    assume ⟨hx, hpx⟩, 
    assume : (∀ x, ¬ p x),
    have hnpx : ¬ p hx, from this hx,
    show false, from hnpx hpx,
  have h2 : ¬ (∀ x, ¬ p x) → (∃ x, p x), from 
    assume hnaxnpx : ¬ (∀ x, ¬ p x), 
    show ∃ x, p x, from by_contradiction (assume hnexpx : ¬(∃ x, p x), 
      have ∀ x, ¬ p x, from (assume hx, assume hpx : p hx,
        show false, from hnexpx ⟨hx, hpx⟩), -- classical
      show false, from hnaxnpx this),
  ⟨h1, h2⟩ -- h2 is classical

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := 
  have h1 : (∀ x, p x → r) → (∃ x, p x) → r, from 
    assume haxpxr : (∀ x, p x → r), assume ⟨hx, hpx⟩,
    haxpxr hx hpx,
  have h2 : ((∃ x, p x) → r) → (∀ x, p x → r), from 
    assume hexpxr : (∃ x, p x) → r, assume hx, assume hpx,
    hexpxr ⟨hx, hpx⟩,
  ⟨h1, h2⟩ 

example : (∃ x, p x → r) ↔ ((∀ x, p x) → r) := 
  have h1 : (∃ x, p x → r) → (∀ x, p x) → r, from 
    assume ⟨hx, (hpxr : p hx → r)⟩, assume haxpx : ∀ x, p x,
    have p hx, from haxpx hx,
    show r, from hpxr this,
  have h2 : ((∀ x, p x) → r) → (∃ x, p x → r), from 
    assume haxpxr : (∀ x, p x) → r,
    show ∃ x, p x → r, from by_cases -- classical
      (assume : (∀ x, p x), ⟨a, λ _, haxpxr this⟩)
      (assume hnaxpx : ¬(∀ x, p x), 
      have ∃ x, ¬p x, from by_contradiction (assume hnexnpx : ¬∃ x, ¬p x,
        have ∀ (x : α), p x, from 
          (assume hx, 
          show p hx, from by_contradiction (assume : ¬p hx, 
            have ∃ x, ¬p x, from ⟨hx, this⟩,
            show false, from hnexnpx this)),
        show false, from hnaxpx this),
      exists.elim this (assume ha, assume hnpa : ¬p ha,
        have p ha → r, from (assume hpha, absurd hpha hnpa),
        ⟨ha, this⟩)),
  ⟨h1, h2⟩ -- h2 is classical

example : (∃ x, r → p x) ↔ (r → ∃ x, p x) := 
  have h1 : (∃ x, r → p x) → r → ∃ x, p x, from 
    assume ⟨hx, hrpx⟩, assume hr : r, 
    ⟨hx, hrpx hr⟩,
  have h2 : (r → ∃ x, p x) → ∃ x, r → p x, from 
    assume hrexpx : r → ∃ x, p x,
    by_cases
      (assume hr : r, 
      have ∃ x, p x, from hrexpx hr,
      exists.elim this (assume ha, assume hpa, 
        have r → p ha, from (λ _, hpa),
        ⟨ha, this⟩))
      (assume hnr : ¬r, 
      have r → p a, from (assume hr, absurd hr hnr),
      ⟨a, this⟩),
  ⟨h1, h2⟩ 
end

section 
variables (real : Type) [ordered_ring real]
variables (log exp : real → real)
variable  log_exp_eq : ∀ x, log (exp x) = x
variable  exp_log_eq : ∀ {x}, x > 0 → exp (log x) = x
variable  exp_pos    : ∀ x, exp x > 0
variable  exp_add    : ∀ x y, exp (x + y) = exp x * exp y

include log_exp_eq exp_log_eq exp_pos exp_add

example (x y z : real) :
  exp (x + y + z) = exp x * exp y * exp z :=
by rw [exp_add, exp_add]

example (y : real) (h : y > 0)  : exp (log y) = y :=
exp_log_eq h

theorem log_mul {x y : real} (hx : x > 0) (hy : y > 0) :
  log (x * y) = log x + log y := 
    have hxy : x * y > 0, from (mul_pos hx hy),
    calc
    log (x * y) = log (exp (log (x * y))) : by rw log_exp_eq
    ...         = log (x * y) : by simp [exp_log_eq, hxy, hx]
    ...         = log (exp (log x) * exp (log y)) : 
      by simp [exp_log_eq hx, exp_log_eq hy]
    ...         = log (exp (log x  + log y)) : by rw exp_add
    ...         = log x  + log y : by rw log_exp_eq

example (x : ℤ) : x * 0 = 0 := 
    calc x * 0 = x * (0 - 0)   : by simp
         ...   = x * 0 - x * 0 : by rw mul_sub
         ...   = 0             : by rw sub_self
end