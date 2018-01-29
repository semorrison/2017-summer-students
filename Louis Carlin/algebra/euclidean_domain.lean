import data.int.basic

-- TODO
-- examples
-- polynomials with ED coefficients are a ED
-- make sure I'm using standard code style
-- euclid's algorithm (extended)

/- euclidean domain definitions and instances -/

universes u v

class euclidean_domain (α : Type u) extends integral_domain α :=
( decidable_equality : decidable_eq α . tactic.apply_instance )

( quotient : α → α → α )

( remainder : α → α → α )

( witness : ∀ a b, (quotient a b) * b + (remainder a b) = a )

( valuation : ∃ f : α → ℕ, ∀ a b, b = 0 ∨ f(remainder a b) < f b )


class decidable_euclidean_domain (α : Type) extends euclidean_domain α := -- ask Scott about this implementation (we only really need to be able to compare with zero)

(decidable_eq : decidable_eq α)



instance decidable_eq_ab {α : Type} [decidable_euclidean_domain α] (a b : α) : decidable (a = b) := -- why does this have to have a different name?
decidable_euclidean_domain.decidable_eq α a b


instance euclidean_domain_has_div {α : Type} [euclidean_domain α] : has_div α := {
    div := euclidean_domain.quotient
}

instance euclidean_domain_has_mod {α : Type} [euclidean_domain α] : has_mod α := {
    mod := euclidean_domain.remainder
}


/- nat_abs lemmas -/
open int

lemma lt_nat_abs {a : ℤ} (b : ℤ) (H : a ≥ 0) : a < b → nat_abs a < nat_abs b := 
begin
    intro,
    cases a,
    {
        cases b,
        {
            exact lt_of_coe_nat_lt_coe_nat a_1,
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
                        --simp,
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

instance field_euclidean_domain {α : Type}  [ decidable_eq α ][fa: field α] : euclidean_domain α:= 
{
    fa with
    eq_zero_or_eq_zero_of_mul_eq_zero := by admit,-- apply_instance,
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

-- theorem nat_gcd_gcd -- prove equivalence of definitions


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


meta def extended_euclidean_algorithm_internal {α : Type}  [ed : decidable_euclidean_domain α]  {a b : α } : eea_input a b → bezout_identity a b :=
λ ⟨ rp, rc, xp, xc, yp, yc, bezout_prev, bezout_curr, divides_curr, greatest_divisor ⟩, if rc = 0 then 
    {bezout_identity . x := xp, y := yp, gcd := 
        {
        greatest_common_divisor .
        value := rp,

        divides_a := 
        begin
            have h1 : rc = 0, by admit, -- TODO, why doesn't lean give us this
            have h2 : rp ∣ 0, by apply dvd_zero,
            rw [←h1] at h2,
            exact (divides_curr rp (and.intro (dvd_refl rp) h2)).left,
        end,

        divides_b :=
        begin
            have h1 : rc = 0, by admit, -- TODO, why doesn't lean give us this
            have h2 : rp ∣ 0, by apply dvd_zero,
            rw [←h1] at h2,
            exact (divides_curr rp (and.intro (dvd_refl rp) h2)).right,
        end,

        greatest := 
        begin
            intro,
            exact (greatest_divisor d).left,
        end 
        },
        bezout := bezout_prev}
    else 
        let q := (rp/rc) in extended_euclidean_algorithm_internal ⟨ rc, ( rp%rc) , xc, (xp-q*xc), yc, (yp -q*yc), bezout_curr,
        
        begin -- proof that rp % rc = a * (xp - q * xc) + b * (yp - q * yc). Used to show gcd = a*x + b*y at end                                                       
            have : q * rc + (rp%rc) = rp, by apply ed.witness,                                                  
            calc
            rp%rc = rp%rc + 0 : by rw add_zero 
            ... = rp%rc + q*rc - q*rc : by admit --rw ←(add_neg_self (q*rc))
            ... = q*rc + rp%rc - q *rc : by admit -- add_comm
            ... = rp - q*rc : by {rw [this]}
            ... = (a*xp + b*yp) - q* (a*xc + b*yc) : by {rw [bezout_prev,bezout_curr]} 
            -- ... = a*xp + b*yp - (a*xc*q + b*yc*q) : by admit -- {rw mul_add}
            ... = a*xp + b*yp - a*xc*q - b*yc*q : by admit -- {erw [mul_add,neg_add],}
            ... = a*xp - a*xc*q + b*yp - b*yc*q : by admit --{rw [add_comm],}
            ... = a * (xp -xc *q) + b*yp - b*yc*q : by admit-- {rw [←mul_add],}
            ... = a * (xp -xc *q) + b * (yp -  yc * q) : by admit -- rw mul_add
            ... = a * (xp - q * xc) + b * (yp - yc * q) : by admit-- {erw mul_comm,} -- this is rewriting the wrong thing
            ... = a * (xp - q * xc) + b * (yp - q * yc) : by admit -- {rw mul_comm,} -- same thing happens
        end,
        
        begin -- proof that if something divides the divisor (rc) and the remainder (rp%/rc) then it divides a and b. Used to show gcd divides a and b 
            intros,
            cases a_1,
            have := divides_curr x,
            have h1 : q * rc + rp%rc = rp, by apply ed.witness,
            have h2 := dvd_mul_of_dvd_right a_1_left q, 
            have h3 := dvd_add h2 a_1_right,
            rw [h1] at h3,
            exact this (and.intro h3 a_1_left),
        end,

        begin
            intro,
            have := greatest_divisor d,
            have h1 : q * rc + rp%rc = rp, by apply ed.witness,
            rw add_comm at h1,
            have h2 := eq_add_neg_of_add_eq h1,
            cases this,
            have h3 := dvd_mul_of_dvd_right this_right q,
            have := dvd_neg_of_dvd h3,
            have := dvd_add this_left this,
            rw ←h2 at this,
            exact and.intro this_right this,
        end⟩ 

meta def extended_euclidean_algorithm {α : Type} [decidable_euclidean_domain α] (a b : α) : bezout_identity a b :=
extended_euclidean_algorithm_internal ⟨ a, b, 1, 0, 0, 1,
    begin 
        calc
        a = a * 1 : by rw mul_one
        ... = a * 1 + 0 : by rw add_zero
        ... = a * 1 + b * 0 : by rw mul_zero
    end,
    begin
        calc
        b = b * 1 : by rw mul_one
        ... = 0 + b * 1 : by rw zero_add
        ... = a * 0 + b * 1 : by rw mul_zero
    end,
    begin
        intros,
        cases a_1,
        split,
        assumption,
        assumption,
    end,
    begin
        intro,
        exact and.intro d.divides_a d.divides_b,
    end ⟩ 