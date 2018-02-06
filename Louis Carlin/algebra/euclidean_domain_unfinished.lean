import Louis.euclidean_domain


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

example : well_founded int.lt := by admit

/-

inductive acc {α : Sort u} (r : α → α → Prop) : α → Prop
| intro (x : α) (h : ∀ y, r y x → acc y) : acc x

inductive well_founded {α : Sort u} (r : α → α → Prop) : Prop
| intro (h : ∀ a, acc r a) : well_founded
-/

#check acc

set_option trace.class_instances true

example : has_well_founded ℕ := by apply_instance

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

instance eea_input_has_well_founded' {α :Type} (a b :α) [ed : euclidean_domain α]  : has_well_founded (eea_input a b) := {
    r := λ e1 e2, ∀ (f : α → ℕ) (w : ∀ s t, t = 0 ∨ f(s % t) < f t), f(e1.rc) < f(e2.rc),
    wf := 
    begin
        split,
        intro x,

        exact exists.elim ed.valuation (assume g : α → ℕ, assume hg : ∀ p q : α, q = 0 ∨ g (p % q) < g q,
        begin 
        /- problem: We want to do induction on (g x.rc) for all (x : eea_input a b)
        If we introduce such an x, then the induction becomes specific to that x

        -/
   

        split,
        intros y hy,
        have := hy g,
        have := this hg, -- we really want things to be for all y here
        induction (g x.rc),
        admit,
        end)
        
        
    end
}

instance eea_input_has_well_founded'' {α :Type} (a b :α) [ed : euclidean_domain α]  : has_well_founded (eea_input a b) := {
    r := λ e1 e2, ∀ (f : α → ℕ) (w : ∀ s t, t = 0 ∨ f(s % t) < f t), f(e1.rc) < f(e2.rc),
    wf := 
    begin
        split,
        exact exists.elim ed.valuation (assume g : α → ℕ, assume hg : ∀ p q : α, q = 0 ∨ g (p % q) < g q,
        begin 
        /- problem: We want to do induction on (g x.rc) for all (x : eea_input a b)
        If we introduce such an x, then the induction becomes specific to that x

        -/

        intro x,
        have h : g x.rc < 0 → 
        (acc (λ (e1 e2 : eea_input a b), -- why is this a type mismatch?
        ∀ (f : α → ℕ), (∀ (s t : α),
        t = 0 ∨ f (s % t) < f t) → f (e1.rc) < f (e2.rc)) x), from sorry,

        have n : ℕ,
        have : (g x.rc < n → 
        (acc (λ (e1 e2 : eea_input a b),
        ∀ (f : α → ℕ), (∀ (s t : α),
        t = 0 ∨ f (s % t) < f t) → f (e1.rc) < f (e2.rc)) x)) → (g x.rc < n+1 → 
        (acc (λ (e1 e2 : eea_input a b),
        ∀ (f : α → ℕ), (∀ (s t : α),
        t = 0 ∨ f (s % t) < f t) → f (e1.rc) < f (e2.rc)) x))
        end)
        
        
    end
}

/-
instance eea_input_has_well_founded {α :Type} (a b :α) [ed : euclidean_domain α]  : has_well_founded (eea_input a b) := {
    r := λ e1 e2, ∃ (f : α → ℕ) (w : ∀ s t, t = 0 ∨ f(s % t) < f t), f(e1.rc) < f(e2.rc),
    wf := 
    begin
        split,
        intro x,
        have := ed.valuation,
        simp,
        exact exists.elim this (assume (f : α → ℕ), assume h : ∀ (a' b' : α), b' = 0 ∨ f ( a' % b') < f b',
            let ⟨ rp, rc, xp, xc, yp, yc, bezout_prev, bezout_curr, divides_curr, greatest_divisor⟩ := x in 
            begin
                
                have h1 := (f x.rc),
                induction h1,
                {
                    admit
                },
                {
                    
                    admit,
                }
            end)
    end
}
-/

-- ( valuation : ∃ f : α → ℕ, ∀ a b, b = 0 ∨ f(remainder a b) < f b )
/-
instance eea_input_has_well_founded {α :Type} (a b :α) [ed :euclidean_domain α]  : has_well_founded (eea_input a b) :=
begin
exact exists.elim ed.valuation (assume f : α → ℕ,
    assume hf : (∀ (a' b' : α), b' = 0 ∨ f (a' %  b') < f b'),
{
    r := sorry,
    wf := sorry,

}
)
end
-/

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
        in extended_euclidean_algorithm_internal' next_input
end

