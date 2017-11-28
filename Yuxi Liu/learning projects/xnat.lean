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

theorem add_cancel_left (a b t : xnat) :  a = b ↔ t + a = t + b :=
begin
  constructor,
    intro hab,
    have hatbt: a + t = b + t, 
      apply (add_cancel_right _ _ _).elim_left, assumption,
    exact calc t + a = a + t : by rw add_comm
                 ... = b + t : hatbt
                 ... = t + b : by rw add_comm,
  intro htatb,
  have : a + t = b + t, from 
    calc a + t = t + a : by rw add_comm
           ... = t + b : htatb
           ... = b + t : by rw add_comm,
  apply (add_cancel_right _ _ _).elim_right, assumption
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
notation a ≤ b := leq a b
def geq : xnat → xnat → Prop := λ a b, leq b a
notation a ≥ b := geq a b

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

theorem less_cancel (a b t : xnat) : a + t < b + t → a < b := 
begin
  induction t with t Ht,
    rw [add_zero, add_zero],
    intro, assumption,
  intro halb,
  unfold add at halb,
  unfold less at halb,
  exact Ht halb
end

theorem leq_cancel (a b t : xnat) : a + t ≤ b + t → a ≤ b := 
begin
  unfold leq, 
  intro,
  cases a_1 with h1 h2,
    left, apply less_cancel, assumption,
  right, apply (add_cancel_right _ _ _).elim_right, assumption
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

-- 0 < b + 1
theorem zero_less_succ (b : xnat) : zero < succ b :=
begin
  have : zero ≠ succ b, 
    apply zero_ne_succ,
  exact (zero_less_b_iff_ne_zero (succ b)).elim_right this
end

/- Some prop logic theorems that ought to be in the library -/
theorem iff_congruence {a b c : Prop} : (a ↔ b) → (b ↔ c) → (a ↔ c) :=
begin
  intros,
  constructor; intro,
  exact a_2.elim_left (a_1.elim_left a_3),
  exact a_1.elim_right (a_2.elim_right a_3)
end

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

theorem false_iff_false {a b : Prop} : ¬a → ¬b → (a ↔ b) :=
begin
  intros, constructor,
  intro, contradiction, intro, contradiction
end

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

theorem less_irrefl (a : xnat) : ¬(a < a) :=
begin
  induction a with a Ha,
    apply a_not_less_zero,
  unfold less, assumption
end

theorem less_asymm : ∀ (a b : xnat), a < b → ¬(b < a) := 
begin
  intro a, -- It can't be expanded out completely! The induction would fail.
  induction a with a Ha,
    intro b,
    intros halb,
    have : ¬(b < zero), apply a_not_less_zero, 
    assumption,
  -- now induct!
  intro b,
  induction b with b Hb,
    intro hsa0,
    have : ¬(succ a < zero), apply a_not_less_zero,
    contradiction,
  intro hsasb, intro hsbsa,
  unfold less at hsasb,
  unfold less at hsbsa,
  exact (Ha b) hsasb hsbsa,
end

theorem a_less_b_iff_add (a b : xnat) : a < b ↔ ∃ t : xnat, b = a + succ t :=
begin
  revert b,
  induction a with a Ha, -- first induction
    intro b,
    constructor,
      intro halb,
      induction b with b Hb,
        have : false, from halb, contradiction,
      existsi b, rw zero_add, -- (0, b) case, one direction.
    intro h, cases h with a b',
    rw [b', zero_add],
    apply zero_less_succ, -- (0, b) case, other direction.
  intro b,
  induction b with b Hb,
    have h1 : ¬ succ a < zero, apply a_not_less_zero,
    have h2 : ¬∃ (t : xnat), zero = succ a + succ t,
      intro h21, cases h21 with t, unfold add at a_1,
      apply zero_ne_succ (succ a + t), assumption,
    apply false_iff_false, assumption, assumption, -- (a + 1, 0) case
  -- first simplify both sides of the conclusion
  have h1 : succ a < succ b ↔ a < b, by unfold less,
  suffices : a < b ↔ (∃ (t : xnat), succ b = succ a + succ t), 
    by apply iff_congruence h1 this,
  -- Hb, h1 are useless now.
  have h2 : (∃ (t : xnat), b = a + succ t)
          ↔ (∃ (t : xnat), succ b = succ a + succ t),
    admit,
  suffices : a < b ↔ (∃ (t : xnat), b = a + succ t),
    by apply iff_congruence this h2,
  apply Ha
end

theorem less_trans (a b c : xnat) : a < b → b < c → a < c := 
begin
  intros halb hblc,
  apply (a_less_b_iff_add a c).elim_right,
  have hab, from (a_less_b_iff_add a b).elim_left halb,
  have hbc, from (a_less_b_iff_add b c).elim_left hblc,
  cases hab, cases hbc,
  have : c = a + succ (succ a_1 + a_3), from
    calc c = b + succ a_3 : a_4
       ... = a + succ a_1 + succ a_3 : by rw a_2
       ... = a + (succ a_1 + succ a_3) : by rw (add_assoc _ _ _)
       ... = a + succ (succ a_1 + a_3) : by unfold add,
  existsi (succ a_1 + a_3), assumption
end

theorem less_add (a b c d : xnat) : a < b → c < d → a + c < b + d := 
begin
  intros hab hcd,
  have hab' : ∃ t : xnat, b = a + succ t, 
    apply (a_less_b_iff_add _ _).elim_left, assumption,
  have hcd' : ∃ t : xnat, d = c + succ t, 
    apply (a_less_b_iff_add _ _).elim_left, assumption,
  cases hab', cases hcd',
  have hac0 : a + c = zero + (a + c), by rw (zero_add (a + c)),
  have hbdac : b + d = succ (succ a_3 + a_1) + (a + c), from
    calc b + d = a + succ a_1 + (c + succ a_3) : by rw [a_2, a_4]
           ... = a + (succ a_1 + (c + succ a_3)) : by apply add_assoc
           ... = a + ((c + succ a_3) + succ a_1) : by rw (add_comm (succ a_1) (c + succ a_3))
           ... = a + (c + (succ a_3 + succ a_1)) : by rw (add_assoc c (succ a_3) (succ a_1))
           ... = (a + c) + (succ a_3 + succ a_1) : by rw  (add_assoc a c (succ a_3 + succ a_1))
           ... = (a + c) + succ (succ a_3 + a_1) : by unfold add
           ... = succ (succ a_3 + a_1) + (a + c) : by apply add_comm,
  rw hac0, rw hbdac,
  apply inequality_A1, unfold less
end

theorem less_leq (a b c : xnat) : a < b → b ≤ c → a < c := 
begin
  unfold leq,
  intros, cases a_2,
    apply less_trans, assumption, assumption,
  rw ←a_2, assumption
end

theorem leq_less (a b c : xnat) : a ≤ b → b < c → a < c := 
begin
  unfold leq,
  intros, cases a_1,
    apply less_trans, assumption, assumption,
  rw a_1, assumption
end

theorem leq_refl (a : xnat) : a ≤ a := by { unfold leq, right, refl }

theorem leq_trans (a b c : xnat) : a ≤ b → b ≤ c → a ≤ c := 
begin
  intro,
  cases a_1,
    intro,
    have : a < c, from (less_leq a b c) a_1 a_2,
    unfold leq, left, assumption,
  rw a_1, intro, assumption
end

theorem leq_then_add (a b : xnat) : a ≤ b → ∃ (t : xnat), b = a + t :=
begin
  unfold leq,
  intro h, 
  cases h with h1 h2,
    have : ∃ (t : xnat), b = a + succ t, 
    from (a_less_b_iff_add a b).elim_left h1,
    cases this, existsi succ a_1, assumption,
  rw h2, existsi zero, apply add_zero,
end

theorem leq_add (a b c d : xnat) : a ≤ b → c ≤ d → a + c ≤ b + d := 
begin
  unfold leq,
  intros hab hcd,
  cases hab with halb haeb,
    cases hcd with hcld hced,
      left, apply less_add, assumption, assumption,
    left, rw hced, apply inequality_A1, assumption,
  cases hcd with hcld hced,
    left, rw [haeb, (add_comm b c), (add_comm b d)],
    apply inequality_A1, assumption,
  right, rw [haeb, hced]
end

attribute [trans] less_trans less_leq leq_less leq_trans

-- < is a total order
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

lemma A31 (a b : xnat) : (a < b ∨ a = b ∨ b < a) := 
begin
  have : (∃ (t : xnat), a = b + succ t) ∨ a = b ∨ (∃ (t : xnat), b = a + succ t),
    apply total_order_lemma,
  cases this with h1 h23,
    right, right, apply (a_less_b_iff_add b a).elim_right, assumption,
  cases h23 with h2 h3,
    right, left, assumption, 
  left, apply (a_less_b_iff_add a b).elim_right, assumption
end

lemma A32 (a b : xnat) : a < b → ¬ (a = b) := 
begin
  intro halb, intro haeb,
  have halb' : ∃ (t : xnat), b = a + succ t, 
    apply (a_less_b_iff_add _ _).elim_left, assumption,
  cases halb',
  have : zero + a = succ a_1 + a, from
    calc zero + a = a : by rw zero_add
       ... = b : haeb
       ... = a + succ a_1 : a_2
       ... = succ a_1 + a : by rw add_comm,
  have : zero = succ a_1, 
    apply (add_cancel_right _ _ _).elim_right, assumption,
  apply zero_ne_succ, assumption
end

lemma A33 (a b : xnat) : (a < b → ¬ (b < a)) := 
begin 
  intro halb, intro hbla,
  have halb' : ∃ (t : xnat), b = a + succ t, 
    apply (a_less_b_iff_add _ _).elim_left, assumption,
  cases halb',
  have hbla' : ∃ (t : xnat), a = b + succ t, 
    apply (a_less_b_iff_add _ _).elim_left, assumption,
  cases hbla',
  have : a + zero = a + succ (succ a_1 + a_3), from
    calc a + zero = a : by apply add_zero
              ... = b + succ a_3 : by rw a_4
              ... = (a + succ a_1) + succ a_3 : by rw a_2
              ... = a + (succ a_1 + succ a_3) : by apply add_assoc
              ... = a + succ (succ a_1 + a_3) : by unfold add,
  have : zero = succ (succ a_1 + a_3),
    apply (add_cancel_left _ _ _).elim_right, assumption,
  apply zero_ne_succ, assumption
end

lemma A34 (a b : xnat) : (a = b → ¬ (b < a)) := 
begin
  intro haeb, intro hbla,
  have hbla' : ∃ (t : xnat), a = b + succ t, 
    apply (a_less_b_iff_add _ _).elim_left, assumption,
  cases hbla',
  have : b + zero = b + succ a_1, from
    calc b + zero = b : by apply add_zero
              ... = a : haeb.symm
              ... = b + succ a_1 : a_2,
  have : zero = succ a_1,
    apply (add_cancel_left _ _ _).elim_right, assumption,
  apply zero_ne_succ, assumption
end

theorem leq_antisymm (a b : xnat) : a ≤ b → b ≤ a → a = b := 
begin
  unfold leq,
  intros aleqb bleqa,
  cases aleqb, 
    cases bleqa,
      exfalso,
      apply A33, assumption, assumption, 
    exact a_2.symm, 
  assumption
end

theorem less_total_order (a b : xnat) : 
  (a < b ∨ a = b ∨ b < a) ∧ (a < b → ¬ (a = b))
  ∧ (a < b → ¬ (b < a))   ∧ (a = b → ¬ (b < a)) := 
  ⟨A31 a b, A32 a b, A33 a b, A34 a b⟩

theorem zero_less_mult : ∀ (a b : xnat), zero < a → zero < b → zero < a * b := 
begin
  intro a,
  induction a with a Ha,
    intro b,
    induction b with b Hb,
    repeat { intro, exfalso, apply a_not_less_zero zero, assumption },
  intro b,
  induction b with b Hb,
    intros, exfalso, apply a_not_less_zero zero, assumption,
  -- the only non-trivial step, essentially "0 < 1"
  intros, unfold mul
end

theorem less_mul (a b c d : xnat) : a < b → c < d → a * c < b * d := 
begin
  intros halb hcld,
  have halb' : ∃ t : xnat, b = a + succ t, 
    exact (a_less_b_iff_add a b).elim_left halb,
  have hcld' : ∃ t : xnat, d = c + succ t, 
    exact (a_less_b_iff_add c d).elim_left hcld,
  cases halb', cases hcld',
  rw [a_2, a_4],
  have h0ac : a * c = zero + a * c, by rw zero_add,
  have h : (a + succ a_1) * (c + succ a_3) = succ (a * succ a_3 + succ a_1 * c + succ a_1 * a_3 + a_1) + a * c, from
    calc (a + succ a_1) * (c + succ a_3)
          = a * (c + succ a_3) + (succ a_1) * (c + succ a_3) : by apply left_distrib
      ... = (a * c + a * succ a_3) + (succ a_1 * c + succ a_1 * succ a_3) : by rw [right_distrib, right_distrib]
      ... = a * c + (a * succ a_3 + succ a_1 * c + succ a_1 * succ a_3) : by rw [add_assoc, add_assoc]
      ... = a * c + (a * succ a_3 + succ a_1 * c + (succ a_1 * a_3 + succ a_1)) : by unfold mul
      ... = a * c + (a * succ a_3 + succ a_1 * c + succ a_1 * a_3 + succ a_1) : 
        by rw add_assoc (a * succ a_3 + succ a_1 * c) (succ a_1 * a_3) (succ a_1)
      ... = a * c + succ (a * succ a_3 + succ a_1 * c + succ a_1 * a_3 + a_1) : by unfold add
      ... = _ : by apply add_comm,
  rw [h0ac, h],
  apply inequality_A1, apply zero_less_succ
end

theorem zero_leq (a : xnat) : zero ≤ a := sorry
-- requires decidable "= zero" theorem

theorem leq_mul (a b c d : xnat) : a ≤ b → c ≤ d → a * c ≤ b * d := 
begin
  unfold leq,
  intros hab hcd, 
  cases hab with hab1 hab2,
    cases hcd with hcd1 hcd2,
      left, apply less_mul, assumption, assumption,
    admit,
    -- by_cases (c = zero), 
  cases hcd with hcd1 hcd2,
    admit,
  admit
end

-- now that we've proven < is a total order, we can easily prove
-- cancellation laws. Just easy calculations and trivial prop logic.
theorem mul_cancel_right (a b c : xnat) : 
  (a * (succ c) = b * (succ c)) → a = b := 
begin
  intro h,
  have nalb : ¬(∃ (t : xnat), a = b + succ t), 
    intro h1, cases h1 with t h1,
    have : b * succ c + zero = b * succ c + succ (succ t * c + t), from
      calc b * succ c + zero = b * succ c : by apply add_zero
           ... = a * succ c : h.symm
           ... = (b + succ t) * succ c : by rw h1
           ... = b * succ c + succ t * succ c : by apply left_distrib
           ... = b * succ c + (succ t * c + succ t) : by unfold mul
           ... = b * succ c + succ (succ t * c + t) : by unfold add,
    have : zero = succ (succ t * c + t), 
      apply (add_cancel_left _ _ _).elim_right, assumption,
    apply zero_ne_succ, assumption,
  have nbla : ¬(∃ (t : xnat), b = a + succ t), 
    intro h2, cases h2 with t h2,
    have : a * succ c + zero = a * succ c + succ (succ t * c + t), from
      calc a * succ c + zero = a * succ c : by apply add_zero
           ... = b * succ c : h
           ... = (a + succ t) * succ c : by rw h2
           ... = a * succ c + succ t * succ c : by apply left_distrib
           ... = a * succ c + (succ t * c + succ t) : by unfold mul
           ... = a * succ c + succ (succ t * c + t) : by unfold add,
    have : zero = succ (succ t * c + t), 
      apply (add_cancel_left _ _ _).elim_right, assumption,
    apply zero_ne_succ, assumption,
  -- trivial prop logic
  have triple : (∃ (t : xnat), a = b + succ t) ∨ a = b ∨ (∃ (t : xnat), b = a + succ t), 
    apply total_order_lemma,
  cases triple with h1 h23, contradiction,
  cases h23 with h2 h3, assumption, contradiction
end

theorem mul_cancel_left (a b c : xnat) : 
  ((succ c) * a = (succ c) * b) → a = b := 
begin
  intro,
  apply (mul_cancel_right a b c),
  exact calc a * succ c = succ c * a : by apply mul_comm
             ... = succ c * b : a_1
             ... = b * succ c : by apply mul_comm
end

-- more order theorems
theorem less_discrete : ∀ (a b : xnat), ¬(a < b) ∨ ¬(b < succ a) :=
begin
  intro a,
  induction a with a Ha,
    intro b,
    induction b with b Hb,
      unfold less, simp,
    right, unfold less,
    apply a_not_less_zero,
  intro b,
  induction b with b Hb,
    unfold less, simp,
  unfold less, 
  exact Ha b
end

-- A rephrasing of the previous theorem, used to prove division theorem.
theorem less_succ_leq (a b : xnat) : (a < b → succ a ≤ b) :=
begin
  intro halb, 
  have h : ¬(a < b) ∨ ¬(b < succ a), from less_discrete a b,
  cases h with h1 h2,
    contradiction,
  unfold leq,
  have tri : succ a < b ∨ succ a = b ∨ b < succ a, 
    from (less_total_order _ _).elim_left,
  cases tri with h1 hrest, 
    left, assumption,
  cases hrest with h2 h3,
    right, assumption,
  contradiction
end

/- power -/

def pow : xnat → xnat → xnat
| _ zero := one  -- 0^0 = 1
| n (succ m) := (pow n m) * n
notation a ^ b := pow a b

theorem power_add (a b c : xnat) : a ^ (b + c) = a ^ b * a ^ c :=
begin
  induction c with c Hc,
    unfold add, unfold pow, unfold one, unfold mul,
    exact (zero_add (a ^ b)).symm,
  unfold add, unfold pow, rw Hc, apply mul_assoc
end

/- even, odd-/
def even (a : xnat) : Prop := ∃ (t : xnat), a = t + t
def odd (a : xnat) : Prop := ∃ (t : xnat), a = succ (t + t)
theorem even_or_odd (a : xnat) : even a ∨ odd a :=
begin
  induction a with a Ha,
    left, unfold even, existsi zero, unfold add,
  unfold even, unfold odd,
  cases Ha with Ha1 Ha2,
    right,
    unfold even at Ha1, cases Ha1,
    existsi a_1, rw a_2,
  left, 
  unfold odd at Ha2, cases Ha2,
  have : succ a = succ a_1 + succ a_1, from
    calc succ a = succ (succ (a_1 + a_1)) : by rw a_2
            ... = succ (a_1 + succ a_1) : by unfold add
            ... = succ (succ a_1 + a_1) : by rw (add_comm _ _)
            ... = succ a_1 + succ a_1 : by unfold add,
  existsi succ a_1, assumption
end

theorem even_nand_odd (a : xnat) : ¬(even a ∧ odd a) :=
begin
  unfold even, unfold odd,
  induction a with a Ha,
    intro h,
    have h1 : ∃ (t : xnat), zero = succ (t + t), from h.elim_right,
    cases h1, 
    apply zero_ne_succ, assumption,
  intro h, cases h.elim_left with t1, cases h.elim_right with t2, 
  have ht1ne0 : zero ≠ t1, 
    intro ht1e0, rw ←ht1e0 at a_1, rw zero_add at a_1,
    exact (zero_ne_succ a) a_1.symm,
  cases (ne_zero_iff_succ t1).elim_left ht1ne0 with t3 h3,
  have aeven : ∃ (t : xnat), a = t + t,
    existsi t2,
    exact (eq_iff_succ_eq_succ a (t2 + t2)).elim_left a_2,
  have aodd : ∃ (t : xnat), a = succ (t + t),
    have h3 : succ a = succ (succ (t3 + t3)), from
      calc succ a = t1 + t1 : a_1
              ... = succ t3 + succ t3 : by rw h3
              ... = succ (succ t3 + t3) : by unfold add
              ... = succ (t3 + succ t3) : by rw add_comm
              ... = succ (succ (t3 + t3)) : by unfold add,
    existsi t3,
    exact (eq_iff_succ_eq_succ a (succ (t3 + t3))).elim_left h3,
  exact (Ha ⟨aeven, aodd⟩)
end

lemma m1f_1_1 (n : xnat) : even n ↔ even (n * n) :=
begin
  constructor; intro h,
    unfold even,
    cases h, rw a_1,
    existsi (a + a) * a,
    apply right_distrib,
  have noddn : ¬(odd n), admit,
  have h : even n ∨ odd n, apply even_or_odd,
  cases h, assumption, contradiction
end

theorem division_theorem_exist : 
  ∀ n m : xnat, m ≠ zero → ∃ q r : xnat, n = m * q + r ∧ r < m := 
begin
  intro n,
  induction n with n Hn,
    intros m hmne0, 
    existsi zero, existsi zero,
    constructor, unfold mul, unfold add,
    apply (zero_less_b_iff_ne_zero _).elim_right,
    apply (ne_symm _ _).elim_right, assumption,
  intros m hmne0, 
  have : ∃ (q r : xnat), n = m * q + r ∧ r < m, from Hn m hmne0,
  cases this with q0 rh,
  cases rh with r0 h,
  cases h with hnemqr hrlm,
  have hsrlem : succ r0 ≤ m, exact (less_succ_leq r0 m) hrlm,
  cases hsrlem with hsrlm hsrem,
    existsi q0, existsi (succ r0), constructor,
    show succ r0 < m, assumption,
    exact calc succ n = succ (m * q0 + r0) : by rw ←hnemqr
                ... = m * q0 + succ r0 : by unfold add,
  existsi (succ q0), existsi zero, constructor,
  show zero < m, rw ←hsrem, unfold less,
  exact calc succ n = succ (m * q0 + r0) : by rw ←hnemqr
                ... = m * q0 + succ r0 : by unfold add
                ... = m * q0 + m : by rw hsrem
                ... = m * succ q0 : by unfold mul
                ... = m * succ q0 + zero : by apply add_zero
end

theorem division_theorem_unique :
  ∀ n m : xnat, m ≠ zero → 
  ∀ q0 r0 : xnat, n = m * q0 + r0 ∧ r0 < m →
  ∀ q1 r1 : xnat, n = m * q1 + r1 ∧ r1 < m →
  r0 = r1 ∧ q0 = q1 := 
begin
intros,
have h : m * q0 + r0 = m * q1 + r1, from
  (eq.trans a_1.elim_left.symm a_2.elim_left),
suffices : q0 = q1, 
  constructor, 
    rw this at h,
    apply (add_cancel_left _ _ _).elim_right, assumption,
  assumption,
have tri : (∃ (t : xnat), q0 = q1 + succ t) ∨ q0 = q1 ∨ ∃ (t : xnat), q1 = q0 + succ t,
  by apply total_order_lemma,
have nmq0r0 : n = m * q0 + r0, from a_1.elim_left,
have r0lm : r0 < m, from a_1.elim_right,
have nmq1r1 : n = m * q1 + r1, from a_2.elim_left,
have r1lm : r1 < m, from a_2.elim_right,
cases tri with h1 h23,
  admit,
cases h23 with h2 h3, assumption,
exfalso,
have h11 : n < m * succ q0, 
  unfold mul,
  rw nmq0r0,
  rw [add_comm (m * q0) r0, add_comm (m * q0) m],
  apply inequality_A1, assumption,
have h12 : m * succ q0 ≤ m * q1, 
  apply leq_mul,
    unfold leq, right, refl,
    cases h3, rw a_4,
    have h13 : zero + succ q0 = succ q0, by apply zero_add,
    have h14 : q0 + succ a_3 = a_3 + succ q0, from
      calc q0 + succ a_3 = succ (q0 + a_3) : by unfold add
                     ... = succ (a_3 + q0) : by rw add_comm
                     ... = a_3 + succ q0 : by unfold add,
    rw ←h13, rw h14, apply (leq_add zero a_3 (succ q0)), 
      apply zero_leq, apply leq_refl,
  admit
end
#check total_order_lemma
theorem fermat : 
  ¬∃ (x y z n : xnat), x > zero ∧ y > zero ∧ z > zero ∧ n > two ∧ 
    (x ^ n) + (y ^ n) = (z ^ n) := sorry 
    -- I have found a truly marvelous proof but the margin is too small to cont
end xnat