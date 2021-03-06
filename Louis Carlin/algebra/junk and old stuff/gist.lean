import data.int.basic
import tactic.ring

universes u v
definition valuation {α} [has_zero α] (r : α → α → α) := { f : α → ℕ // ∀ a b, b = 0 ∨ f(r a b) < f b }

class euclidean_domain (α : Type u) extends integral_domain α :=
( quotient : α → α → α )
( remainder : α → α → α )
( witness : ∀ a b, (quotient a b) * b + (remainder a b) = a )
( valuation : trunc (valuation remainder) )

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

structure common_divisor {α : Type} [R: comm_ring α] (a b : α) :=
(value : α)
(divides_a : value ∣ a) -- better names?
(divides_b : value ∣ b)


structure greatest_common_divisor {α : Type} [R: comm_ring α] (a b : α) extends common_divisor a b :=
(greatest : ∀ d : common_divisor a b, d.value ∣ value)

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


noncomputable instance eea_input_has_sizeof {α : Type} (a b : α) [ed:decidable_euclidean_domain α] : has_sizeof (eea_input a b) := {
    sizeof := λ e, ed.valuation.out.val e.rc, 
}


def extended_euclidean_algorithm_internal' {α : Type}  [ed : decidable_euclidean_domain α]  {a b : α } : eea_input a b → bezout_identity a b
| input := begin
    cases h0 : input,
    exact (if h : rc = 0 then 
    {
    bezout_identity . x := xp, y := yp, gcd := 
        {
        greatest_common_divisor .
        value := rp,

        divides_a := 
        begin
            have h2 : rp ∣ 0, by apply dvd_zero,
            rw [←h] at h2,
            exact (divides rp (and.intro (dvd_refl rp) h2)).left,
        end,

        divides_b :=
        begin
            have h2 : rp ∣ 0, by apply dvd_zero,
            rw [←h] at h2,
            exact (divides rp (and.intro (dvd_refl rp) h2)).right,
        end,

        greatest := 
        begin
            intro,
            exact (greatest_divisor d).left,
        end 
        },
    bezout := bezout_prev
    }
    else 
        let q : α:= (rp/rc) in
        let next_input : eea_input a b := ⟨ rc, ( rp%rc) , xc, (xp-q*xc), yc, (yp -q*yc), bezout_curr,
        
        begin -- proof that rp % rc = a * (xp - q * xc) + b * (yp - q * yc). Used to show gcd = a*x + b*y at end                                                       
            have : q * rc + (rp%rc) = rp, by apply ed.witness,                                                  
            calc
            rp%rc = q*rc + rp%rc - q *rc : by ring
            ...   = rp - q*rc : by {rw [this]}
            ...   = (a*xp + b*yp) - q* (a*xc + b*yc) : by {rw [bezout_prev,bezout_curr]} 
            ...   = a * (xp - q * xc) + b * (yp - q * yc) : by ring 
        end,
        
        begin -- proof that if something divides the divisor (rc) and the remainder (rp%/rc) then it divides a and b. Used to show gcd divides a and b 
            intros,
            cases a_1,
            have := divides x,
            have h1 : q * rc + rp%rc = rp, by apply ed.witness,
            have h2 := dvd_mul_of_dvd_right a_1_left q, 
            have h3 := dvd_add h2 a_1_right,
            rw [h1] at h3,
            exact this (and.intro h3 a_1_left),
        end,

        begin
            intro, -- TODO this proof is ugly, make it cleaner
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
        in 
        have has_well_founded.r next_input input, {
            unfold has_well_founded.r,
            unfold sizeof_measure,
            unfold sizeof,
            unfold has_sizeof.sizeof,
            unfold measure,
            unfold inv_image, simp,
            let ov_val : α → ℕ := ed.valuation.out.val,
            --have  : ov_val = optimal_valuation.val, by {dsimp [ov_val], refl},
            have := ed.valuation.out.property rp rc,
            cases this,
            {
                exact absurd this h,
            },
            {   
                dsimp [(%)],
                have rci : input.rc = rc, by {
                    exact congr_arg eea_input.rc h0
                },
                rw rci,
                exact this,
            },
        },
        extended_euclidean_algorithm_internal' next_input)
end

