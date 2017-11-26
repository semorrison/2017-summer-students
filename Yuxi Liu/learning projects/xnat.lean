inductive xnat 
| zero : xnat
| succ : xnat → xnat

namespace xnat
def one := succ zero
def two := succ one
def drei := succ two
def vier := succ drei

/- basics of add -/

def add : xnat → xnat → xnat
| x zero := x
| x (succ y) := succ (add x y)
notation a + b := add a b
theorem zero_ne_succ (a : xnat) : zero ≠ succ a := by apply xnat.no_confusion
/- "no_confusion" proves that the inductive type is freely generated, 
i.e. that the constructors are injective and that distinct constructors 
produce distinct objects -/
theorem succ_ne_zero (a : xnat) : succ a ≠ zero :=
  by { apply ne.symm, apply zero_ne_succ }

theorem ne_zero_iff_succ (a : xnat) : zero ≠ a ↔ ∃ t, succ t = a :=
begin
  constructor,
    intro,
    cases a,
      contradiction,
    existsi a, refl,
  intro,
  apply exists.elim a_1,
  intros,
  rw ←a_3,
  apply zero_ne_succ
end

theorem principia_mathematica_54_43 : one + one = two := by refl
-- The above proposition is occasionally useful
-- It is used at least three times, in ✸113.66 and ✸120.123.472.

theorem add_zero (x : xnat) : x + zero = x := by refl
-- or "unfold add"

/-meta def trivial_induction : xnat → tactic unit := λ n,
`[ induction n with t Ht, refl, unfold add, rw Ht ]-/

theorem zero_add (n : xnat) : zero + n = n :=
begin
  induction n with t Ht,
  refl,
  unfold add,
  rw Ht
end

theorem add_assoc (a b c : xnat) : (a + b) + c = a + (b + c) :=
begin
  induction c with t Ht,
  refl,
  unfold add,
  rw Ht
end

theorem zero_add_eq_add_zero (n : xnat) : zero + n = n + zero := 
by rw [zero_add, add_zero]

theorem add_one_eq_succ (n : xnat) : n + one = succ n := by refl

theorem one_add_eq_succ (n : xnat) : one + n = succ n :=
begin
  induction n with t Ht,
  refl,
  unfold add,
  rw Ht
end

theorem add_comm (a b : xnat) : a + b = b + a :=
begin
  induction a with t Ht,
  apply zero_add_eq_add_zero,
  unfold add,
  rw [←Ht, ←add_one_eq_succ, add_assoc, one_add_eq_succ],
  refl
end

/- constructors of inductive data types are injections. That means that 
if c is a constructor of an inductive datatype, and if (c t₁) and (c t₂) 
are two terms that are equal, then t₁ and t₂ are equal too.
-/
#check @succ.inj
theorem eq_iff_succ_eq_succ (a b : xnat) : succ a = succ b ↔ a = b :=
begin
  constructor,
  induction a with t Ht; apply succ.inj,
  intro hab,
  rw hab
end

theorem add_cancel_right (a b t : xnat) :  a = b ↔ a + t = b + t :=
begin
  constructor,
  intro hab,
    rw hab,
  induction t with t Ht,
    intro hab,
    rw [add_zero, add_zero] at hab,
    assumption,
  intro hab,
  unfold add at hab,
  have hatbt : a + t = b + t,
    apply succ.inj, 
    assumption,
  exact Ht hatbt
end

/- basics of mul -/

definition mul : xnat → xnat → xnat
| n zero := zero
| n (succ p) := (mul n p) + n
notation a * b := mul a b

example : two * two = vier := by refl

theorem mul_zero (a : xnat) : a * zero = zero := by refl

theorem mul_one (a : xnat) : a * one = a := 
begin
  unfold one,
  unfold mul,
  apply zero_add
end

theorem zero_mul (a : xnat) : zero * a = zero := 
begin
  induction a with t Ht,
  refl,
  unfold mul,
  rw Ht,
  refl
end

theorem one_mul (a : xnat) : one * a = a := 
begin -- copy paste the last proof
  induction a with t Ht,
  refl,
  unfold mul,
  rw Ht,
  refl
end

theorem right_distrib (a b c : xnat) : a * (b + c) = a * b + a * c := 
begin
  induction c with t Ht,
    rw [add_zero, mul_zero, add_zero],
  rw [add, mul, mul, Ht, add_assoc]
end

theorem left_distrib (a b c : xnat) : (a + b) * c = a * c + b * c :=
begin
  induction c with t Ht,
    repeat { rw mul_zero },
    rw add_zero,
  repeat { rw mul },
  rw Ht,
  rw [add_assoc, add_assoc], -- going halfway so that "simp" gets the hint 
  simp [add_comm, add_assoc] 
end

theorem mul_assoc (a b c : xnat) : (a * b) * c = a * (b * c) := 
begin
  induction c with t Ht,
    repeat { rw mul_zero },
  unfold mul,
  rw [right_distrib, Ht]
end

theorem mul_comm (a b : xnat) : a * b = b * a := 
begin
  induction b with t Ht,
    rw [mul_zero, zero_mul],
  unfold mul,
  rw [←add_one_eq_succ, left_distrib, one_mul, Ht]
end

/- inequalities -/
def less : xnat → xnat → Prop 
| zero zero := false
| (succ m) zero := false
| zero (succ p) := true 
| (succ m) (succ p) := less m p
notation a < b := less a b
example : zero < one := by trivial 
-- It's like refl, since when it's fully unfolded, it just yields "true".

-- and its friends
def greater : xnat → xnat → Prop := λ a b, less b a
notation a > b := greater a b
def leq : xnat → xnat → Prop := λ a b, a < b ∨ a = b
notation a <= b := leq a b
def geq : xnat → xnat → Prop := λ a b, leq b a
notation a >= b := geq a b

theorem inequality_A1 (a b t : xnat) : a < b → a + t < b + t := 
begin
  induction t with t Ht,
    rw [add_zero, add_zero],
    intro, assumption,
  intro halb,
  unfold add,
  unfold less,
  exact Ht halb
end

theorem a_not_less_zero (a : xnat) : ¬(a < zero) :=
begin
  induction a with a Ha,
    unfold less, trivial,
  unfold less, trivial
end

theorem zero_less_b_iff_ne_zero (b : xnat) : zero < b ↔ zero ≠ b :=
begin
  constructor,
    intro, intro,
    rw ←a_1 at a, unfold less at a, contradiction,
  intro,
  have h1 : zero ≠ b → ∃ t, succ t = b, from (ne_zero_iff_succ b).elim_left,
  have h2 : ∃ (t : xnat), succ t = b, from h1 a,
  cases h2,
  rw ←a_2,
  unfold less
end

theorem zero_less_succ (b : xnat) : zero < succ b :=
begin
  have : zero ≠ succ b, 
    apply zero_ne_succ,
  exact (zero_less_b_iff_ne_zero (succ b)).elim_right this
end

-- why is this not in the library
theorem iff_congruence {a b c : Prop} : (a ↔ b) → (b ↔ c) → (a ↔ c) :=
begin
  intros,
  constructor; intro,
  exact a_2.elim_left (a_1.elim_left a_3),
  exact a_1.elim_right (a_2.elim_right a_3)
end

-- whyyyyyyyyyyy
universe u
theorem any_then_exists_iff {α : Type u} {p q : α → Prop} : 
  (∀ (t : α), p t ↔ q t) → ((∃ (t : α), p t) ↔ ∃ (t : α), q t) :=
begin
  intro,
  apply iff.intro; intro,
  cases a_1,
  have : q a_1, from (a a_1).elim_left a_2,
  existsi a_1, assumption,
  cases a_1,
  have : p a_1, from (a a_1).elim_right a_2,
  existsi a_1, assumption,
end

theorem ne_symm {α : Type u} (a b : α) : a ≠ b ↔ b ≠ a :=
  by constructor; { intro, intro, exact a_1 a_2.symm }

-- why can't Lean rewrite inside ∃ 
theorem zero_less_b_iff_succ (b : xnat) : zero < b ↔ ∃ t : xnat, b = succ t :=
begin 
  have h1 : zero < b ↔ zero ≠ b, from zero_less_b_iff_ne_zero b,
  have h2 : zero ≠ b ↔ ∃ t, succ t = b, from ne_zero_iff_succ b,
  have h3 : zero < b ↔ ∃ (t : xnat), succ t = b, from iff_congruence h1 h2,
  have h4 : ∀ (t : xnat), succ t = b ↔ b = succ t, 
    intro,
    constructor; { intro, apply a.symm },
  have h5 : (∃ (t : xnat), succ t = b) ↔ (∃ (t : xnat), b = succ t), 
    apply any_then_exists_iff, assumption,
  apply iff_congruence h3 h5,
end

meta def solve_disjunction : tactic unit :=
`[ {left, assumption} <|> right <|> assumption ]

-- the central lemma
lemma total_order_lemma (a b : xnat) : 
  (∃ (t : xnat), a = b + succ t) ∨ a = b ∨ (∃ (t : xnat), b = a + succ t) :=
begin
  induction b with b Hb,
    cases a,
      right, left, refl,
    left, existsi a, rw zero_add,
  cases Hb with halb h1,
    cases halb,
    cases a_1,
      have : a = succ b, from
        calc a   = b + succ zero : a_2
             ... = succ (b + zero) : by unfold add
             ... = succ b : by rw add_zero _,
      right, left, assumption,
    have : a = succ b + (succ a_1), from 
      calc a   = b + succ (succ a_1) : a_2
           ... = b + ((succ a_1) + one) : by rw (add_one_eq_succ _)
           ... = b + (one + (succ a_1)) : by rw (add_comm (succ a_1) one)
           ... = (b + one) + (succ a_1) : by rw (add_assoc _ _ _)
           ... = succ b + succ a_1 : by rw (add_one_eq_succ _),
    left, existsi a_1, assumption,
  cases h1 with haeb hbla,
    have : succ b = a + succ zero, from 
      calc succ b = succ a : by rw haeb.symm
              ... = succ (a + zero) : by rw (add_zero _)
              ... = a + succ zero : by unfold add,
    right, right, existsi zero, assumption,
  cases hbla, 
  have : succ b = a + succ (succ a_1), from
    calc succ b =  succ (a + succ a_1) : by rw a_2
            ... = a + succ (succ a_1) : by unfold add,
  right, right, existsi (succ a_1), assumption
end

-- I can't believe how stupid Lean is.
theorem a_less_b_then_succ (a b : xnat) : a < b → ∃ t : xnat, b = succ t :=
begin
  intro hb,
  cases b,
    have h1 : ¬(a < zero), apply a_not_less_zero,
    contradiction,
  existsi a_1, refl
end

lemma a_less_b_succ (a b : xnat) : 
  (succ a < b → a < b) ∧ (a < b → a < succ b) := 
begin
  induction b with b Hb,
    apply and.intro,
      intro,
      cases a,
        apply (a_not_less_zero (succ zero)), assumption,
        have : false, apply (a_not_less_zero (succ (succ a))), assumption,
        exfalso, assumption,
    intro, 
    have : false, apply (a_not_less_zero a), assumption,
    exfalso, assumption,
  apply and.intro,
    intro,
    unfold less at a_1,
    exact (Hb.elim_right a_1),
  induction a with a Ha,
    intro, apply zero_less_succ,
  intro, unfold less at a_1, unfold less,
end

theorem a_less_b_iff_add (a b : xnat) : a < b ↔ ∃ t : xnat, b = a + succ t :=
begin
  constructor,
  intro halb,
  induction a with a Ha,
    induction b with b Hb,
      have : false, from halb, contradiction,
    existsi b, rw zero_add,
  induction b with b Hb,
    have : false, from halb, contradiction,
  
end


theorem inequality_A2 (a b c : xnat) : a < b → b < c → a < c := 
begin
  intros halb hblc,
  
end

theorem inequality_A3 (a b : xnat) : 
  (a < b ∨ a = b ∨ b < a) ∧ (a < b → ¬ (a = b))
  ∧ (a < b → ¬ (b < a))   ∧ (a = b → ¬ (b < a)) := sorry

theorem inequality_A4 (a b : xnat) : zero < a → zero < b → zero < a * b := sorry

-- theorem division_theorem : ∀ n m : ℕ, ∃! q r : ℕ, n = m * q + r ∧ r < m := 
end xnat