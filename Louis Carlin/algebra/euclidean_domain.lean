import data.int.basic
-- TODO
-- examples
-- polynomials with ED coefficients are a ED
-- make sure I'm using standard code style
-- euclid's algorithm (extended)
-- should euclidean domain fill out has_div (and possibly other things)

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

( valuation : ∃ f : α → ℕ, ∀ a b, b = 0 ∨ f(remainder a b) < f b )

-- (euclidean_function : α → ℕ)

-- (witness_2 : ∀ a b, b=0 ∨ euclidean_function (remainder a b) < euclidean_function b)


#reduce 2/5
#reduce 2%5
#reduce (-3:int)/(3)
#reduce (3:int)%(-3)

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
    divides_a := d.divides_b,
    divides_b := d.divides_a,
}

theorem gcd_comm {α : Type} [R: comm_ring α] {a b : α}(d : greatest_common_divisor a b) : greatest_common_divisor b a :=
{
    -- cd_comm d.to_common_divisor with -- This is hard
    value := d.value,
    divides_a := d.divides_b,
    divides_b := d.divides_a,
    greatest := begin
                    admit,
                end
}

-- theorem nat_gcd_gcd -- prove equivalence of definitions


/- euclidean algorithm -/

structure bezout_identity {α : Type} [R: comm_ring α] (a b : α):= 
-- gcd = ax + by

(x y : α) -- coefficients

(gcd : greatest_common_divisor a b)

(witness : gcd.value = a * x + b * y)



meta def nat_euclidean_algorithm_no_proof : nat → nat → nat
| n 0 := n
| n m := nat_euclidean_algorithm_no_proof m (n%m) -- problem: how to show well-founded?

#eval nat_euclidean_algorithm_no_proof 21 14
#eval nat_euclidean_algorithm_no_proof 14 22
#reduce nat_euclidean_algorithm_no_proof 14 22

structure bezout_int :=
(gcd x y : int)

instance bezout_int_print : has_repr bezout_int := {
    repr := λ bi : bezout_int, "gcd: " ++ to_string bi.gcd ++ "\n" 
                                ++ "a coeff: " ++ to_string bi.x ++ "\n"
                                ++ "b coeff: " ++ to_string bi.y 
}

meta structure eea_int_input :=
(rp rc xp xc yp yc: ℤ)

/- nat implementation of Extended Euclid's Algorithm (without proof of validity) -/
-- at each step we need:
-- two previous remainders
-- two previous coefficients
meta def int_eea_no_proof : eea_int_input → bezout_int
| ⟨rp, 0, xp, xc, yp, yc⟩  := {bezout_int . gcd := rp, x := xp, y := yp}
| ⟨rp, rc, xp, xc, yp, yc⟩  := let q := (rp/rc) in int_eea_no_proof (eea_int_input.mk rc (rp%rc) xc (xp-q*xc) yc (yp -q*yc))

meta def int_eea_initial (a b : int) : bezout_int :=
int_eea_no_proof (eea_int_input.mk a b 1 0 0 1)

#eval int_eea_initial 240 46
#eval int_eea_initial 46 240 -- very clever :^)


meta structure eea_np_input (α : Type) [euclidean_domain α]:= -- do we need to specify α is a euclidean domain?
(rp rc xp xc yp yc: α)

structure eea_np_output (α : Type) :=
(gcd x y: α)

meta def eea_no_proof {α : Type} [ed :euclidean_domain α] : eea_np_input α → eea_np_output α
| ⟨ rp, 0, xp, xc, yp, yc⟩  := {eea_np_output . gcd := rp, x := xp, y := yp}
| ⟨rp, rc, xp, xc, yp, yc⟩  := let q := (euclidean_domain.quotient rp rc) in eea_no_proof ⟨ rc, (euclidean_domain.quotient rp rc), xc, (xp-q*xc), yc, (yp -q*yc)⟩

def eea_no_proof_initial 

def extended_euclidean_algorithm {α : Type} [euclidean_domain α] (a b : α) : bezout_identity a b :=
sorry

lemma foo : ∃ n : nat, n = 5 := by {existsi 5, refl}


