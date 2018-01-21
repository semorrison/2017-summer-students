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

universe u -- what are universes actually doing?


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

open int
open classical

-- theorem mod_lt_of_pos (a : ℤ) {b : ℤ} (H : b > 0) : a % b < b

#reduce (5:int)/(0:int)
#reduce (5:int)%(0:int)

instance int_euclidean_domain : euclidean_domain ℤ :=
{
    a with 
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
                            admit
                        -- mod_lt a h,
                        
                        }

                     end
}  


