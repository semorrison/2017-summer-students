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

universes u v


class euclidean_domain (α : Type u) extends integral_domain α :=

( quotient : α → α → α )

( remainder : α → α → α )

( witness : ∀ a b, (quotient a b) * b + (remainder a b) = a )

( valuation : ∃ f : α → ℕ, ∀ a b, b = 0 ∨ f(remainder a b) < f b ) -- is using an or statement the nicest way to define this?

/- nat_abs lemmas -/
open int

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

instance field_euclidean_domain {α : Type} [fa: field α] : euclidean_domain α:= 
{
    fa with
    eq_zero_or_eq_zero_of_mul_eq_zero := begin -- why doesn't lean infer this property if it is true of all fields?
                                            intros,
                                            
                                            
                                         end,
    quotient := λ x y, x / y,
    remainder := λ _ _, fa.zero,
    
    witness := begin
                intros,
                admit
               end,
    valuation := begin
                    existsi (λ x : α,
                    match x with
                    | 0 := (0:ℕ),
                    | _ := (1:ℕ)
                    end
                    ),
                    simp,
                 end
}

example : ∃ f : ℕ → ℕ, ∀ n : ℕ, f n > 1 :=
begin
    existsi (λ x:ℕ, match x with
    | 0 := 1
    | _ := 0
    end)
end

/- gcd stuff -/

structure common_divisor {α : Type} [R: comm_ring α] (a b : α) :=

(value : α)

(divides_a : value ∣ a) -- better names?

(divides_b : value ∣ b)


structure greatest_common_divisor {α : Type} [R: comm_ring α] (a b : α) extends common_divisor a b :=

(greatest : ∀ d : common_divisor a b, d.value ∣ value)


theorem cd_comm {α : Type} [R: comm_ring α] {a b : α}(d : common_divisor a b) : common_divisor b a :=
{
    value := d.value,
    divides_a := common_divisor.divides_b d,
    divides_b := common_divisor.divides_a d,
}

theorem gcd_comm {α : Type} [R: comm_ring α] {a b : α}(d : greatest_common_divisor a b) : greatest_common_divisor b a :=
{
    cd_comm d with 
}



