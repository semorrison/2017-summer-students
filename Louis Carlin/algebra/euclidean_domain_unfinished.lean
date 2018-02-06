import Louis.euclidean_domain


definition least_element : set ℕ → ℕ := sorry
definition least_element_least { U : set ℕ } ( x ∈ U ) : least_element U ≤ x := sorry
definition least_element_in ( U : set ℕ ) : least_element U ∈ U := sorry
-- nat.find
-- well_founded.min

#check well_founded.min

definition optimal_valuation {α} [ed : decidable_euclidean_domain α] : valuation (ed.remainder) := {
    val := λ a, least_element ((λ f : valuation (ed.remainder), f.val a) '' (set.univ)),
    property := λ a b,
    begin
      cases decidable.em (b = 0), {
        left, assumption
      }, 
      {
        right,
        have p : ∃ g : valuation (ed.remainder), least_element ((λ (f : valuation euclidean_domain.remainder), f.val b) '' set.univ) = g.val b, by sorry,
        induction p with g h,
        rw h,
        have q : least_element ((λ (f : valuation euclidean_domain.remainder), f.val (euclidean_domain.remainder a b)) '' set.univ) ≤ g.val (a % b), by sorry,
        have r : g.val (a % b) < g.val b, begin
                                            have s := g.property a b,
                                            induction s,
                                            contradiction,
                                            exact s,
                                          end,
        sorry --- put together q and r
      }      
    end
}

instance optimal_valuation_as_sizeof {α} [ed : decidable_euclidean_domain α] : has_sizeof α := {
  sizeof := optimal_valuation.val
}

instance default_valuation_as_sizeof {α} [ed : decidable_euclidean_domain α] : has_sizeof α := {
  sizeof := begin
  have := ed.valuation,
  induction this, -- how do I do this without entering tactics?
  induction this,
  exact this_val,
  end
}

instance eea_input_has_sizeof {α : Type} (a b : α) [euclidean_domain α] : has_sizeof (eea_input a b) := {
    sizeof := λ e, sizeof e.rc
}

example {α : Type} (a b : α) [euclidean_domain α] : has_well_founded (eea_input a b) := by apply_instance

/- nat_abs lemmas -/



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



#check euclidean_domain_has_div.div




/- misc gcd/ed stuff -/
/-
instance field_euclidean_domain {α : Type}  [ decidable_eq α ][fa: field α] : euclidean_domain α:= 
{
    fa with
    eq_zero_or_eq_zero_of_mul_eq_zero := by admit,-- apply_instance,
    quotient := λ x y, x / y,
    remainder := λ _ _, fa.zero,
    
    witness := begin
                intros,
                ring,
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
-/

-- theorem nat_gcd_gcd -- prove equivalence of definitions


/- Well founded stuff -/

-- example (p: Prop) [decidable p] : p ∨ ¬ p := if p then (assume hp : p, or.inl hp) else begin admit end -- theorem proving tutorial claims this is dite (page 143), but it is actually ite

example (p : Prop) [decidable p] : p ∨ ¬ p := dite p (assume hp :p, or.inl hp) (assume hnp :¬p, or.inr hnp)

-- It looks like the major hurdle now is convincing Lean this is a well-founded recursion. You will need to define an ordering on eea_input,
-- and use "have" to give yourself a hypothesis showing that the argument of the recursive call is smaller than the current argument.


/-

inductive acc {α : Sort u} (r : α → α → Prop) : α → Prop
| intro (x : α) (h : ∀ y, r y x → acc y) : acc x

inductive well_founded {α : Sort u} (r : α → α → Prop) : Prop
| intro (h : ∀ a, acc r a) : well_founded
-/

definition nat_has_well_founded : has_well_founded ℕ := { 
    r := λ (n m : nat), n < m,
    wf :=
    begin
      split, intro a, induction a with b h,
      {
          split,
          intro y,
          intro h,
          cases h,
      },
      {
        split,
        intro y,
        intro h,
        cases h,
        {
            assumption
        },
        {
            have p : y < b, by sorry,
            cases h,
            exact h_h y p
        }
      }
    end
}

def exists_well_founded : inhabited (has_well_founded ℕ) := begin 
  split,
  exact nat_has_well_founded
end


structure test_struct :=
(n m : nat)
(x : int)

example : has_well_founded test_struct := {
    r := λ e1 e2, e1.n < e2.n,
    wf :=
    begin
        split,
        intro a,
        exact let ⟨ n, m, x ⟩ := a in
        begin
            induction n,
            {
                split,
                intros y hy,
                simp at hy,
                cases hy,
            },
            {
                split,
                intros y hy,
                simp at hy,
                have := nat.succ_le_of_lt hy,
                cases this,
                {
                    cases n_ih,
                    split,
                    simp at n_ih_h,
                    assumption,
                },
                {
                    cases n_ih,
                    have h1 := nat.lt_of_succ_le this_a,
                    have h2 := n_ih_h y,
                    exact h2 h1,
                }
                
            }
        end 
    end
}


#check acc


/- Euclidean algorithm stuff -/
/-
example {α : Type} [decidable_euclidean_domain α] : has_add α := by apply_instance 

def foo {α : Type} [has_well_founded α] (f: α → α) (h : ∀ b : α, has_well_founded.r (f b) b) : α → false
| a := 
    have h : has_well_founded.r (f a) a,
    from h a,
    foo (f a) using_well_founded
-/

def extended_euclidean_algorithm_internal' {α : Type}  [ed : decidable_euclidean_domain α]  {a b : α } : eea_input a b → bezout_identity a b
| input := 
match input with ⟨ rp, rc, xp, xc, yp, yc, bezout_prev, bezout_curr, divides_curr, greatest_divisor ⟩ :=
    if h : rc = 0 then 
    {
    bezout_identity . x := xp, y := yp, gcd := 
        {
        greatest_common_divisor .
        value := rp,

        divides_a := 
        begin
            have h2 : rp ∣ 0, by apply dvd_zero,
            rw [←h] at h2,
            exact (divides_curr rp (and.intro (dvd_refl rp) h2)).left,
        end,

        divides_b :=
        begin
            have h2 : rp ∣ 0, by apply dvd_zero,
            rw [←h] at h2,
            exact (divides_curr rp (and.intro (dvd_refl rp) h2)).right,
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
            have := divides_curr x,
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
            admit,
        },
        extended_euclidean_algorithm_internal' next_input
end

