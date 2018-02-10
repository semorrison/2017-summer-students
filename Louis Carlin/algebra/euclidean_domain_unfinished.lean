--TODO
-- theorem nat_gcd_gcd -- prove equivalence of definitions
-- examples
-- polynomials with ED coefficients are a ED
-- make sure I'm using standard code style
-- euclid's algorithm (extended)

import Louis.euclidean_domain
import order.order_iso

/-
ed1__to_integral_domain : integral_domain α,
ed1_quotient ed1_remainder : α → α → α,
ed1_witness : ∀ (a b : α), ed1_quotient a b * b + ed1_remainder a b = a,
ed1_valuation : trunc (valuation ed1_remainder),
-/


/-
lemma euclidean_domains_component_equality
{α : Type} (ed1 ed2 : euclidean_domain α)
(w1 : ed1.to_integral_domain = ed2.to_integral_domain)
--(w2 : ∀ a b : α, ed1.quotient a b = ed2.quotient a b) -- what is going on here?
(w3 : ed1.remainder = ed2.remainder) :
ed1 = ed2 :=
begin
induction ed1,
induction ed2,
end
-/


#check nat.find
#check well_founded
#check (∅ : set ℕ) 

def foo : inhabited ℕ := ⟨ 5⟩

def bar : inhabited ℕ := ⟨6⟩ 

example : foo = bar :=
begin
unfold foo,
unfold bar,
admit, -- I don't think this is true
end 

#check eq
#check trunc
#check subtype
#check has_well_founded

-- def lt_wf : (well_founded nat.lt) := -- will need to be replaced by more general well_founded
--     begin
--       split, intro a, induction a with b h,
--       {
--           split,
--           intro y,
--           intro h,
--           cases h,
--       },
--       {
--         split,
--         intro y,
--         intro h,
--         cases h,
--         {
--             assumption
--         },
--         {
--             have p : y < b, by sorry,
--             cases h,
--             exact h_h y p,
--         }
--       }
--     end

#check well_founded.min
-- well_founded β (this needs a proof that some function is well-founded)
-- p : set β
-- proof p ≠ ∅ 

#check set.univ ℕ -- the set containing all natural numbers
#check set.image

-- notation `∅`   := has_emptyc.emptyc _
example : ((λ x : ℕ, x = 4) : set ℕ) ≠ (∅ : set ℕ) :=
begin
    have h1 : (λ x : ℕ, x = 4) 4 = true,
    simp,
    have h2 : (∅ : set ℕ) 4 = false,
    split,
    admit, -- WTS : f a ≠ g a → f ≠ g
end
#check funext


#check set.eq_empty_iff_forall_not_mem

-- show non-empty set of functions applied to a value is non-empty
-- show transitivity-esque property of well-founded relations
-- noncomputable definition optimal_valuation {α} [ed : decidable_euclidean_domain α] : valuation (ed.remainder) := {
--     val := λ a, well_founded.min 
--         lt_wf -- the wf relation we are finding the minimum for 
--         ((λ f : valuation (ed.remainder), f.val a) '' (set.univ)) -- map the valuation application function over the set of all valuations
--     (
--         begin
--         admit,
--         end
--     ),
--     property := λ a b,
--     begin
--     cases decidable.em (b = 0), 
--     {
--         left, assumption
--     }, 
--     {
--         right,

--         let S_f : set (valuation ed.remainder) := set.univ,
--         let S_b := ((λ (f : valuation euclidean_domain.remainder), f.val b) '' S_f),

--         have nonempty_b : S_b ≠ ∅ := trunc.lift
--         (
--             assume (f : valuation ed.remainder),
--             (
--                 begin
--                     have f_in : f ∈ S_f, from set.eq_univ_iff_forall.elim_left  (by {dsimp [S_f], refl}) f,
--                     have := set.ne_empty_of_mem f_in,

--                     have fb_in : f.val b ∈ S_b, by {
--                         have : S_b (f.val b), by {
--                             dsimp [S_b],
--                             simp,
--                             dsimp [set.range],
--                             unfold set_of,
--                             existsi f,
--                             refl,
--                         },
--                         exact set.mem_def.elim_right this,
--                     },
--                     exact set.ne_empty_of_mem fb_in,
--                 end
--             )
--         )
--         (
--             begin
--             intros,
--             refl,
--             end
--         )
--         ed.valuation,


--         have h1 := well_founded.min_mem lt_wf S_b nonempty_b,
--         simp at h1,
--         have p : ∃ g : valuation (ed.remainder), well_founded.min lt_wf S_b nonempty_b = g.val b, 
--         {
--             dsimp [S_b],
--             simp,
--             induction h1 with y hy,
--             existsi y,
--             symmetry,
--             dsimp [S_b] at hy, simp at hy,
--             exact hy,
--         },

--         induction p with g h,
--         rw h,

--         let S_rem := ((λ (f : valuation euclidean_domain.remainder), f.val (a %b)) '' S_f),

--         have gab_in : g.val (a%b) ∈ S_rem, by {
--             have : S_rem (g.val (a%b)), by {
--                 dsimp [S_rem],
--                 simp,
--                 dsimp [set.range],
--                 unfold set_of,
--                 existsi g,
--                 refl,
--             },
--             exact set.mem_def.elim_right this,
--         },
--         have nonempty_rem : S_rem ≠ ∅, from set.ne_empty_of_mem gab_in,
        
--         have q := well_founded.not_lt_min 
--             lt_wf 
--             S_rem
--             nonempty_rem gab_in,
--         dsimp [S_rem] at q,
--         --  ¬nat.lt (g.val (a % b)) fmin.val (a % b)

--         have q_i : nat.le (well_founded.min -- probs don't need this
--             lt_wf 
--             S_rem
--             (nonempty_rem)) /- ≤ -/ 
--         (g.val (a % b)), by sorry, -- the minimum possible f (a%b) is less than or equal to g (a%b)
        
--         have r : g.val (a % b) < g.val b, begin
--                                             have s := g.property a b,
--                                             induction s,
--                                             contradiction,
--                                             exact s,
--                                           end,
--         rw ←h at r,
--         sorry --- put together q and r
--       }
--     end
-- }

-- well_founded.min_mem {α} {r : α → α → Prop} (H : well_founded r) (p : set α) (h : p ≠ ∅) : H.min p h ∈ p
-- well_founded.not_lt_min {α} {r : α → α → Prop} (H : well_founded r) (p : set α) (h : p ≠ ∅) {x} (xp : x ∈ p) : ¬ r x (H.min p h)


/- lemmas -/
@[simp] lemma mod_zero {α : Type} [ed : euclidean_domain α] (a : α)  : a % 0 = a :=
begin
    have := ed.witness,
    have := this a 0,
    simp at this,
    exact this,
end

lemma zero_value_implies_zero {α : Type} [ed : euclidean_domain α] : ∀ (a : α), ∀ (f : α → ℕ) (hf : ∀ s t, t = 0 ∨ f(s % t) < f t), f a = 0 → a = 0 :=
begin
    intros,
    have := ed.witness,
    have := hf 0 a,
    cases this,
    assumption,
    rw [a_1] at this_1,
    cases this_1,
end

/-
lemma zero_lowest (α : Type) [ed : decidable_euclidean_domain α] : ∀ (a : α), ∀ (f : α → ℕ) (hf : ∀ s t, t = 0 ∨ f(s % t) < f t), a = 0 ∨ f 0 < f a :=
begin
    intros,
    have := hf 0 a,
    cases this,
    left, exact this,
    
    by_contradiction, -- possible without this (on non-decidable ed)?
    rw [not_or_distrib] at a_1,
    cases a_1,
    have := ed.valuation,

    have h1 := mod_zero a,
    exact exists.elim this (assume (f : α → ℕ), 
    begin
        intros,
        have := a_1 0 a,
        cases this,
        exact a_1_left this_1,

    end)
end
#check not_or_distrib


@[simp] lemma zero_div_ed {α : Type} [ed : euclidean_domain α] (b : α) : 0 / b = 0 :=
begin
    have := ed.witness,
    have := this 0 b,
end 

@[simp] lemma zero_mod {α : Type} [ed : euclidean_domain α] (b : α) : 0 % b = 0 :=
begin
    have := ed.witness,
    have := this 0 b,
    simp at this,
    have := zero_div b,
end
-/


/- misc gcd/ed stuff -/


/- Well founded stuff -/
--set_option trace.class_instances true

-- noncomputable instance optimal_valuation_as_sizeof {α} [ed : decidable_euclidean_domain α] : has_sizeof α := {
--   sizeof := optimal_valuation.val
-- }

/-
instance eea_input_has_sizeof {α : Type} (a b : α) [euclidean_domain α] : has_sizeof (eea_input a b) := {
    sizeof := λ e, sizeof e.rc
}-/

noncomputable instance eea_input_has_sizeof {α : Type} (a b : α) [ed:decidable_euclidean_domain α] : has_sizeof (eea_input a b) := {
    --sizeof := λ e, optimal_valuation.val e.rc
    sizeof := λ e, ed.valuation.out.val e.rc, 
}

--noncomputable instance 

/- Euclidean algorithm stuff -/


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
        let q : α := (rp/rc),
            next_input : eea_input a b := ⟨ rc, ( rp%rc) , xc, (xp-q*xc), yc, (yp -q*yc), bezout_curr,
        
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
<<<<<<< HEAD
                    
                    sorry,
=======
                    exact congr_arg eea_input.rc h0
>>>>>>> 36458a280f17c573e960e4bc413ae16e9b8d5fc9
                },
                rw rci,
                exact this,
            },
        },
<<<<<<< HEAD
        extended_euclidean_algorithm_internal' next_input
end
=======
        extended_euclidean_algorithm_internal' next_input)
end

>>>>>>> 36458a280f17c573e960e4bc413ae16e9b8d5fc9
