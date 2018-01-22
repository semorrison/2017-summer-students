import data.int.basic
-- TODO
-- examples
-- polynomials with ED coefficients are a ED
-- make sure I'm using standard code style

/-
class integral_domain (α : Type u) extends comm_ring α, no_zero_divisors α, zero_ne_one_class α

class no_zero_divisors (α : Type u) extends has_mul α, has_zero α :=
(eq_zero_or_eq_zero_of_mul_eq_zero : ∀ a b : α, a * b = 0 → a = 0 ∨ b = 0)

-/

universes u v -- what are universes actually doing?


class euclidean_domain (α : Type u) extends integral_domain α :=

( quotient : α → α → α )

( remainder : α → α → α )

( witness : ∀ a b, (quotient a b) * b + (remainder a b) = a )

( valuation : ∃ f : α → ℕ, ∀ a b, b = 0 ∨ f(remainder a b) < f b ) -- is using an or statement the nicest way to define this?

set_option trace.class_instances true

example : integral_domain ℤ := by apply_instance

def a : integral_domain ℤ := by apply_instance
#reduce a.one
#check a.mul
#reduce a.zero

set_option trace.class_instances false

/- nat_abs lemmas -/
open int


-- theorem mod_lt (a : ℤ) {b : ℤ} (H : b ≠ 0) : a % b < abs b :=
-- by rw [← int.mod_abs]; exact int.mod_lt_of_pos _ (abs_pos_of_ne_zero H)

#check nat_abs_of_nat


-- lemma bar (b : ℕ) : -of_nat b ≤ of_nat b :=
-- begin
-- transitivity (0 : ℤ),
-- simp,
-- simp,
-- end

-- @[simp] lemma foo (b : ℕ) : abs (of_nat b) = of_nat b :=
-- begin
-- unfold abs,
-- apply max_eq_left,
-- exact bar b,
-- end

-- -- set_option pp.notation false

-- lemma qux (b : ℕ ) : abs (int.neg_succ_of_nat b) = b + 1 :=
-- begin
-- unfold abs,
-- apply max_eq_right,
-- transitivity (0 : ℤ),
-- simp,
-- simp,
-- end
-- #check int.nat_abs_abs
-- lemma nat_abs_abs (b : ℤ) : nat_abs (abs b) = nat_abs b := 
-- begin
--     cases b,
--     {
--         simp,
--     },
--     {
--         simp,
--         rw qux,
--         erw ← of_nat_succ,
--         simp,
--     }
-- end


lemma lt_nat_abs {a : ℤ} (b : ℤ) (H : a ≥ 0) : a < b → nat_abs a < nat_abs b := 
begin
    intro,
    cases a,
    {
        cases b,
        {
            simp,
            exact lt_of_coe_nat_lt_coe_nat a_1
        },
        {
            exact false.elim (by assumption),
        }
    },
    {
        exact false.elim (by assumption),
    }
end


lemma nat_abs_mod_lt_abs (a : ℤ) {b : ℤ} (H : b ≠ 0) : nat_abs (a % b) < nat_abs b := 
begin
    have h1 : a % b < abs b, from mod_lt a H,
    have h2 : a % b ≥ 0, from mod_nonneg a H,
    have p := lt_nat_abs (abs b) h2 h1,
    rw nat_abs_abs at p,
    exact p
end


/- Euclidean Domain instances-/




open classical


-- theorem mod_lt_of_pos (a : ℤ) {b : ℤ} (H : b > 0) : a % b < b

example : (5:int) > -5 := dec_trivial
-- example (n : nat) : of_nat n > -n := dec_trivial

#reduce abs (-5:int) 

#reduce (-5:int)/(2:int)
#reduce ((-5):int)%(2:int)

-- lemma abs_equiv_nat_abs (z : ℤ) : of_nat (nat_abs z) = abs z :=
-- begin
--     cases z,
--     simp,
--     have h : of_nat z > -z, from dec_trivial, 
-- end

instance int_euclidean_domain : euclidean_domain ℤ :=
{
    ((by apply_instance) : integral_domain ℤ) with 
        quotient := λ x y, x / y,
        remainder := λ x y, x % y,
        witness := begin
                    intros,
                    rw [add_comm, mul_comm],
                    exact mod_add_div a b,
                   end,
        valuation := begin
                        existsi (λ x, nat_abs x),
                        intros,
                        simp,
                        cases em (b=0), 
                        {
                            left,
                            exact h
                        },
                        {
                            right,
                            apply nat_abs_mod_lt_abs,
                            assumption,                        
                        }
                     end
}  


