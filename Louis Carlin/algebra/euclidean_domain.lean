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

( valuation : ∃ f : α → ℕ, ∀ a b, f(remainder a b) < f b )

example : integral_domain ℤ := by apply_instance


instance int_euclidean_domain : euclidean_domain ℤ :=
{
    
}  

