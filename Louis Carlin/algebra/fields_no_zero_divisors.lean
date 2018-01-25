/- Fields should be infered to not have zero divisors 
Is this the correct way to do things?
-/

/- 

class field (α : Type u) extends division_ring α, comm_ring α

class division_ring (α : Type u) extends ring α, has_inv α, zero_ne_one_class α :=
(mul_inv_cancel : ∀ {a : α}, a ≠ 0 → a * a⁻¹ = 1)
(inv_mul_cancel : ∀ {a : α}, a ≠ 0 → a⁻¹ * a = 1)

class has_inv      (α : Type u) := (inv : α → α)

class no_zero_divisors (α : Type u) extends has_mul α, has_zero α :=
(eq_zero_or_eq_zero_of_mul_eq_zero : ∀ a b : α, a * b = 0 → a = 0 ∨ b = 0)

-/

import logic.basic


open classical

-- local attribute classical.prop_decidable [instance]
instance div_ring_no_zero_divisors {α : Type} [division_ring α] : no_zero_divisors α := {
    mul := division_ring.mul,
    zero := division_ring.zero α,
    eq_zero_or_eq_zero_of_mul_eq_zero := begin
                                            intros,
                                            -- by_contradiction,
                                            cases  em (a = 0 ∨ b = 0),
                                            
                                            exact h,

                                            cases not_or_distrib.elim_left h,
                                            right,
                                            calc
                                                 b = 1 * b : eq.symm (one_mul b)
                                                 ... = (a⁻¹ * a) * b : by rw inv_mul_cancel left
                                                 ... = a⁻¹ * (a * b) : by rw mul_assoc
                                                 ... = a⁻¹ * 0 : by admit --rw a_1 -- why doesn't this work???
                                                 ... = 0 : by rw mul_zero,
                                            
                                         end

}