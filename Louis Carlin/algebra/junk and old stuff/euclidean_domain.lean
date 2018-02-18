import data.int.basic
import tactic.ring

/- euclidean domain definitions and instances -/

--universes u v (what do these do?)
--definition valuation {α} [has_zero α] (r : α → α → α) {β} [has_well_founded β] := { f : α → β // ∀ a b, b = 0 ∨ has_well_founded.r ( f(r a b))  (f b) }
definition valuation {α} [has_zero α] (r : α → α → α) := { f : α → ℕ // ∀ a b, b = 0 ∨ f(r a b) < f b }

class euclidean_domain (α : Type) extends integral_domain α :=
( quotient : α → α → α )
( remainder : α → α → α )
( witness : ∀ a b, (quotient a b) * b + (remainder a b) = a )
( valuation : trunc (valuation remainder))


class decidable_euclidean_domain (α : Type) extends euclidean_domain α := -- change this
(decidable_eq : decidable_eq α)


instance decidable_eq_ab {α : Type} [decidable_euclidean_domain α] (a b : α) : decidable (a = b) := -- why does this have to have a different name?
decidable_euclidean_domain.decidable_eq α a b

instance euclidean_domain_has_div {α : Type} [euclidean_domain α] : has_div α := {
    div := euclidean_domain.quotient
}

instance euclidean_domain_has_mod {α : Type} [euclidean_domain α] : has_mod α := {
    mod := euclidean_domain.remainder
}

-- open int

-- lemma lt_nat_abs {a : ℤ} (b : ℤ) (H : a ≥ 0) : a < b → nat_abs a < nat_abs b := 
-- begin
--     intro,
--     cases a,
--     {
--         cases b,
--         {
--             exact lt_of_coe_nat_lt_coe_nat a_1,
--         },
--         {
--             exact false.elim (by assumption),
--         }
--     },
--     {
--         exact false.elim (by assumption),
--     }
-- end


-- lemma nat_abs_mod_lt_abs (a : ℤ) {b : ℤ} (H : b ≠ 0) : nat_abs (a % b) < nat_abs b := 
-- begin
--     have h1 : a % b < abs b, from mod_lt a H,
--     have h2 : a % b ≥ 0, from mod_nonneg a H,
--     have p := lt_nat_abs (abs b) h2 h1,
--     rw nat_abs_abs at p,
--     exact p
-- end

/- Euclidean Domain instances-/

-- instance int_euclidean_domain : euclidean_domain ℤ :=
-- {
--     ((by apply_instance) : integral_domain ℤ) with 
--         quotient := λ x y, x / y,
--         remainder := λ x y, x % y,
--         witness := begin
--                     intros,
--                     rw [add_comm, mul_comm],
--                     exact mod_add_div a b,
--                    end,
--         valuation := 
--             begin
--                 split, split, simp, -- order is wrong?
--                 {
--                     intros,
--                     cases decidable.em (b = 0),
--                     left, assumption,
--                     right,
--                     exact nat_abs_mod_lt_abs a h,
--                 },
--             end
                    
--                     /-
--                     begin
--                         existsi (λ x, nat_abs x),
--                         intros,
--                         cases decidable.em (b=0), 
--                         {
--                             left,
--                             exact h
--                         },
--                         {
--                             right,
--                             apply nat_abs_mod_lt_abs,
--                             assumption,                        
--                         }
--                      end-/
-- }  

#check inv_mul_self

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

@[simp] lemma cd_comm_value {α : Type} [R: comm_ring α] {a b : α}(d : common_divisor a b) : (cd_comm d).value = d.value :=
begin
  dunfold cd_comm,
  refl
end

theorem gcd_comm {α : Type} [R: comm_ring α] {a b : α}(d : greatest_common_divisor a b) : greatest_common_divisor b a :=
{
    cd_comm d.to_common_divisor with
    greatest := begin
                  intro d', 
                  have p := d.greatest (cd_comm d'), 
                  dunfold cd_comm at p, 
                  dsimp at p, 
                  simp,
                  exact p
                end
}


/- euclidean algorithm -/

structure bezout_identity {α : Type} [R: comm_ring α] (a b : α):= 
(x y : α) -- coefficients
(gcd : greatest_common_divisor a b)
(bezout : gcd.value = a * x + b * y)


structure eea_input {α : Type} (a b : α) [euclidean_domain α] := 
(rp rc xp xc yp yc: α)
(bezout_prev : rp = a * xp + b * yp)
(bezout_curr : rc = a * xc + b * yc)
(divides : ∀ x : α, x∣rp ∧ x∣rc → x∣a ∧ x∣b)
(greatest_divisor : ∀ d : common_divisor a b, d.value ∣ rp ∧ d.value ∣ rc)