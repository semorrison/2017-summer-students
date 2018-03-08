import data.int.basic
import tactic.ring

class euclidean_domain (α : Type) extends integral_domain α :=
( quotient : α → α → α )
( remainder : α → α → α )
( witness : ∀ a b, (quotient a b) * b + (remainder a b) = a ) -- this should probably be changed to the same order as int.mod_add_div
(valuation : α → ℕ)
(val_mod : ∀ a b, b = 0 ∨  valuation (remainder a b) <  valuation b)
(val_mul : ∀ a b, b = 0 ∨ valuation a ≤ valuation (a*b))
/-
val_mul is often not a required in definitions of a euclidean domain since given the other properties we can show there is a (noncomputable) euclidean domain α with the property val_mul.
So potentially this definition could be split into two different ones (euclidean_domain_weak and euclidean_domain_strong) with a noncomputable function from weak to strong
I've currently divided the lemmas depending on whether they require val_mul or not
-/

class decidable_euclidean_domain (α : Type) extends euclidean_domain α:=
(decidable_eq_zero : ∀ a : α, decidable (a = 0))
/-
We use this for basically everything.
It might be worth making it part of the original definition?
-/

instance decidable_eq_zero {α : Type} [ed : decidable_euclidean_domain α] (a : α) : decidable (a = 0) :=
 decidable_euclidean_domain.decidable_eq_zero a

namespace euclidean_domain

instance euclidean_domain_has_div {α : Type} [euclidean_domain α] : has_div α := {
    div := quotient
}

instance euclidean_domain_has_mod {α : Type} [euclidean_domain α] : has_mod α := {
    mod := remainder
}

instance ed_has_sizeof {α : Type} [euclidean_domain α] : has_sizeof α := {
    sizeof := λ x : α, valuation x,
}

definition gcd_decreasing  {α : Type} [euclidean_domain α] (x y : α) (w : x ≠ 0) : has_well_founded.r (y % x) x := 
begin
cases val_mod y x,
                { contradiction },
                { exact h }
end

def gcd {α : Type} [decidable_euclidean_domain α] : α → α → α
| x y := if x_zero : x = 0 then y
         else have h : has_well_founded.r (y % x) x := gcd_decreasing x y x_zero,
              gcd (y%x) x

/- weak lemmas -/

@[simp] lemma mod_zero {α : Type} [ed : euclidean_domain α] (a : α)  : a % 0 = a :=
begin
    have := euclidean_domain.witness a 0,
    simp at this,
    exact this,
end

/- strong lemmas -/

lemma val_lt_one {α : Type} [decidable_euclidean_domain α] (x : α) : 
valuation x < valuation (1:α) → x = 0 :=
begin
    intro x_lt,
    cases val_mul (1:α) x,
        {exact h,},
        {
            simp at h,
            have := not_le_of_lt x_lt,
            contradiction
        }
end

lemma val_dvd_le {α : Type} [decidable_euclidean_domain α] (a b : α) :
    b ∣ a → a ≠ 0 → valuation b ≤ valuation a :=
begin
    intros b_dvd ha,
    induction b_dvd with x hx, rw hx,
    cases val_mul b x,
        {
            rw h at hx, simp at hx,
            contradiction,
        },
        {
            exact h,
        }
end

@[simp] lemma mod_one {α : Type} [decidable_euclidean_domain α] (x : α) : x % 1 = 0 :=
begin
    cases val_mod x 1,
    { 
        have := one_ne_zero, 
        contradiction,
    },
    {
        exact val_lt_one (x % 1) h,
    }
end 

@[simp] lemma zero_mod  {α : Type} [ed : decidable_euclidean_domain α] (b : α) : 0 % b = 0 :=
begin
    have h1 := witness 0 b,
    have h2 : remainder 0 b = b * (-quotient 0 b ), from sorry,
    -- have h2' : 0 % b = b * (- 0/b ), from sorry,
    cases val_mul b (-euclidean_domain.quotient 0 b),
    {
        simp at h, rw h at h1, simp at h1,
        exact h1,
    },
    {
        rw [←h2] at h,
        cases val_mod 0 b,
        {
            rw h_1, exact mod_zero (0:α),
        },
        {
            have := not_le_of_lt h_1,
            contradiction,
        }
    }
    
end

@[simp] lemma zero_div {α : Type} [decidable_euclidean_domain α] (b : α) : b = 0 ∨ 0 / b = 0 :=
begin
    have h1 := zero_mod b, dsimp [(%)] at h1,
    have h2 := euclidean_domain.witness 0 b,
    rw h1 at h2,
    simp at h2,
    dsimp [(/)],
    cases decidable.em (b=0),
    {left, exact h},
    {
        right,
        cases eq_zero_or_eq_zero_of_mul_eq_zero h2,
        {exact h_1},
        {contradiction}
    }
end

@[simp] lemma mod_self {α : Type} [ed : decidable_euclidean_domain α] (x : α) : x % x = 0 :=
begin
    have := witness x x,
    have divides : x ∣ x % x, from sorry,
    induction divides with m x_mul,
    cases val_mul x m,
    {
        rw h at x_mul,
        rw mul_zero at x_mul,
        exact x_mul,
    },
    {
        cases  val_mod x x, 
        {rw h_1, exact mod_zero (0:α)},
        {
            have := not_le_of_lt h_1,
            dsimp [(%)] at x_mul,
            rw x_mul at this,
            contradiction,
        }
    }

end 

/- weak gcd lemmas -/

@[simp] theorem gcd_zero_left {α : Type} [decidable_euclidean_domain α] (x : α) : gcd 0 x = x := 
begin
    rw gcd,
    simp,
end

lemma mod_lt {α : Type} [decidable_euclidean_domain α]  :
                     ∀ (x : α) {y : α}, valuation y > valuation (0:α) →  valuation (x%y) < valuation y :=
begin
    intros,
    cases decidable.em (y=0),
    {
        rw h at a,
        have := lt_irrefl (valuation (0:α)),
        contradiction,
    },
    {
        cases val_mod x y with h h',
        { contradiction },
        { exact h' }
    }
end

lemma neq_zero_lt_mod_lt {α : Type} [decidable_euclidean_domain α] : ∀ a b : α, b ≠ 0 → valuation (a%b) < valuation b :=
begin
    intros a b hnb,
    cases val_mod a b,
        {contradiction},
        {exact h}
end

lemma dvd_mod {α} [decidable_euclidean_domain α] {a b c : α} : c ∣ a → c ∣ b → c ∣ a % b :=
begin
    intros dvd_a dvd_b,
    have : remainder a b = a - quotient a b * b, from
    calc 
        a%b = quotient a b * b + a%b - quotient a b * b : by ring
        ... = a - quotient a b * b : by {dsimp[(%)]; rw (witness a b)},
    dsimp [(%)], rw this,
    exact dvd_sub dvd_a (dvd_mul_of_dvd_right dvd_b (a/b)),
end

@[elab_as_eliminator]
theorem gcd.induction {α : Type} [decidable_euclidean_domain α] 
                    {P : α → α → Prop}
                    (m n : α)
                    (H0 : ∀ x, P 0 x)
                    (H1 : ∀ m n, m ≠ 0 → P (n%m) m → P m n) :
                P m n := 
@well_founded.induction _ _ (has_well_founded.wf α) (λm, ∀n, P m n) m (λk IH,
    by {cases decidable.em (k=0), rw h, exact H0,
        exact λ n, H1 k n (h) (IH (n%k) (neq_zero_lt_mod_lt n k h) k)}) n


/- more gcd stuff (generalized mathlib/data/nat/gcd.lean) -/

theorem gcd_dvd {α : Type} [decidable_euclidean_domain α] (a b : α) : (gcd a b ∣ a) ∧ (gcd a b ∣ b) :=
gcd.induction a b
    (λ b, by simp)
    (λ a b aneq,
    begin
        intro h_dvd,
        rw gcd, simp [aneq],
        cases h_dvd,
        split,
            {exact h_dvd_right},
            {
                conv {for b [2] {rw ←(witness b a)}},
                have h_dvd_right_a:= dvd_mul_of_dvd_right h_dvd_right (b/a),
                exact dvd_add h_dvd_right_a h_dvd_left
            }
    end )

theorem gcd_dvd_left {α : Type} [decidable_euclidean_domain α] (a b : α) :
    gcd a b ∣ a := (gcd_dvd a b).left

theorem gcd_dvd_right {α : Type} [decidable_euclidean_domain α] (a b : α) :
    gcd a b ∣ b := (gcd_dvd a b).right

theorem dvd_gcd {α : Type} [decidable_euclidean_domain α] {a b c : α} : c ∣ a → c ∣ b → c ∣ gcd a b :=
gcd.induction a b
    (λ b,
    begin
        intros dvd_0 dvd_b,
        simp, exact dvd_b
    end)
    (λ a b hna,
    begin
        intros d dvd_a dvd_b,
        rw gcd, simp [hna],
        exact d (dvd_mod dvd_b dvd_a) dvd_a,
    end)