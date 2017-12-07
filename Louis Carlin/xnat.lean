-- https://xenaproject.wordpress.com/2017/10/31/building-the-non-negative-integers-from-scratch/

namespace xena

inductive xnat
| zero : xnat
| succ : xnat → xnat

open xnat

definition one := succ zero
definition two := succ one

#check zero

definition add : xnat → xnat → xnat
| n zero := n
| n (succ p) := succ ( add n p)

-- is this definition equivalent?
definition addx : xnat → xnat → xnat
| n zero := n
| n (succ p) := addx (succ n) p

#reduce addx (succ zero) (succ (succ zero))

notation a + b := add a b

theorem add_zero (n : xnat) : n + zero = n :=
begin
unfold add
end

theorem zero_add (n : xnat) : zero + n = n :=
begin
induction n with t Ht,
    refl,
unfold add,
rewrite [Ht],
end

theorem add_assoc (a b c : xnat) : (a + b) + c = a + (b  + c) :=
begin
induction c with t Ht,
    refl,
unfold add,
rewrite [Ht],
end

theorem zero_add_eq_add_zero (n : xnat) : zero + n = n + zero :=
begin
rewrite [zero_add, add_zero],
end

theorem add_one_eq_succ (n : xnat) : n + one = succ n :=
begin
unfold one,
unfold add,
end

theorem one_add_eq_succ (n : xnat) : one + n = succ n :=
begin
induction n with t Ht,
    refl,
    --unfold one,
    unfold add,
    rewrite [Ht],
end

lemma add_succ ( t a : xnat) : succ (t + a) = succ t + a :=
begin
induction a with k Hk,
    refl,
    unfold add,
    rewrite [Hk]
end 

theorem add_comm (a b : xnat) : a + b = b + a :=
begin
induction b with t Ht,
    rw [<- zero_add_eq_add_zero],
    unfold add,
    rw [Ht],
    rw [add_succ],
end

theorem eq_iff_succ_eq_succ (a b : xnat) : succ a = succ b ↔ a = b :=
begin
split,
    exact succ.inj, -- what is succ.inj? (injectivity?)
assume H : a = b,
rw [H]
end

#check succ.inj

theorem add_cancel_right ( a b t : xnat) : a = b ↔ a + t = b + t :=
begin
split,
    assume hab : a = b,
    rw [hab],
    
    induction t with k Hk,
        --assume h1 : a + zero = b + zero
        intro h1, -- syntactic sugar to do the same thing
        rw eq.symm (add_zero a),
        rw eq.symm (add_zero b),
        exact h1,

        intro h2,
        unfold add at h2,
        rw eq_iff_succ_eq_succ at h2,
        exact Hk h2,
end

-- TODO: add_cancel_right

definition mul : xnat → xnat → xnat
| n zero := zero
| n (succ p) := n + mul n p

notation a * b := mul a b

#reduce one * one

theorem mul_zero (a : xnat) : a * zero = zero :=
begin
refl
end

theorem zero_mul (a: xnat) : zero * a = zero :=
begin
induction a with t ht,
    refl,
    unfold mul,
    rw [zero_add],
    exact ht
end

theorem mul_one (a : xnat) : a * one = a :=
begin
unfold one,
rw mul,
rw mul_zero,
rw add_zero
end

theorem one_mul (a : xnat) : one * a = a :=
begin
induction a with t ht,
refl,
unfold mul,
rw ht,
rw one_add_eq_succ,
end
/-
theorem right_distrib (a b c : xnat) : a * (b + c) = a*b +a*c :=
begin
induction a with t ht,
    rw [zero_mul, zero_mul, zero_mul, zero_add],

end
-/

theorem right_distrib (a b c : xnat) : a * (b + c) = a*b +a*c :=
begin
induction b with k hk,
    induction c with l hl,
        rw [zero_add, mul_zero, zero_add], -- refl works here
        rw [zero_add, mul_zero, zero_add], -- refl does not work here (invalid apply tactic, failed to unify)
        rw <- add_succ,
        unfold mul,
        rw hk,
        exact eq.symm (add_assoc a (a*k) (a*c))
end

theorem left_distrib (a b c : xnat) : (a + b) * c = a * c + b * c :=
begin
induction c with n hn,
    unfold mul,
    refl,
    rw [←add_one_eq_succ,right_distrib,hn,right_distrib,right_distrib],
    rw [mul_one,mul_one,mul_one],
    rw [add_assoc,←add_assoc (b*n),add_comm (b*n),←add_assoc,←add_assoc,←add_assoc],
end

theorem mul_assoc (a b c : xnat) : (a * b) * c = a * (b * c) :=
begin
induction c with t ht,
    rw [mul_zero, mul_zero, mul_zero],
    unfold mul,
    rw [right_distrib,ht]
end

theorem mul_comm (a b : xnat) : a * b = b * a :=
begin
induction b with t ht,
    rw [zero_mul, mul_zero],
    unfold mul,
    rw ht,
    -- rw <- one_mul, --(why doesn't this work?)
    have h2 : one * a = a, by rw one_mul, 
    have h3 : one * a + t * a = a + t * a, from (add_cancel_right  (one*a) a (t * a)).elim_left h2,
    rw <- left_distrib at h3,
    rw one_add_eq_succ at h3,
    exact eq.symm h3
end

--theorem add_cancel_right ( a b t : xnat) : a = b ↔ a + t = b + t :=

definition lt : xnat → xnat → Prop
| zero zero := false
| (succ m) zero := false
| zero (succ p) := true
| (succ m) (succ p) := lt m p


notation a < b := lt a b

theorem inequality_A1 (a b t : xnat) : a < b → a + t < b + t :=
begin
induction t with k hk,
    intro h1,
    rw [add_zero, add_zero],
    exact h1,

    intro h1,
    unfold add,
    unfold lt,
    exact hk h1
end

-- open classical -- is it possible without this?

lemma zero_or_not (a : xnat) : a = zero ∨ ∃ p : xnat, a = succ p := sorry 

open classical

lemma lt_succ (a : xnat) : zero < succ a :=
begin
unfold lt,
end

lemma gt_zero (a : xnat) : zero < a → a ≠ zero :=
begin
intros h1 h2,
rw h2 at h1,
exact h1
end

lemma lt_nrefl ( a : xnat) : ¬ a < a :=
begin
intro,
induction a with t ht,
exact a_1,
unfold lt at a_1,
exact ht a_1,
end

lemma lt_succ ( a b : xnat) : a < b → succ a < b ∨ succ a = b :=
begin
intro h1,
induction a with t ht,
cases b,
exact false.elim h1,
cases a,
have h2 : succ zero = succ zero, by refl,
exact or.intro_right (succ zero < succ zero) h2,
have h3 : succ zero < succ (succ a), by unfold lt,
exact or.intro_left (succ zero = succ (succ a)) h3,
-- succ (succ t) < succ b
cases b,
exact false.elim h1,


end



lemma succ_lt (a b : xnat) : succ a < b → a < b :=
begin
intro h1,
induction b with t ht,
exact false.elim h1,




    
    
    
end

/-induction a with t ht,
    cases b,
    exact false.elim h1,
    exact lt_succ a,-/

lemma less_than_zero (a : xnat) : a < zero → false :=
begin
intro h1,
cases a,
show false, from h1,
show false, from h1,
end

#check zero < zero

lemma inequality_lemma (a b : xnat) : a < b ↔ ∃ t : xnat, a + t = b :=
begin
apply iff.intro,
    intro hab,
    induction a with k hk,
    have h2 : zero + b = b, by rw zero_add,
    exact exists.intro b h2,
    have h3 : ∃ n : xnat, b = succ n,  cases b,
    exact false.elim hab,
    have h4 : succ a = succ a, by refl,
    exact exists.intro a h4,
    



end

/-induction a with k hk,
    intro h1,
    have h2 : zero + b = b, by rw zero_add,
    exact exists.intro b h2,

    intro h1,
    -- b = succ p
    cases b,
    admit,
    admit,-/

variable z : xnat
#reduce z < zero
#reduce one < zero

theorem inequality_A2 (a b c : xnat) : a < b → b < c → a < c :=
begin
intros h1 h2,


end

/-cases a,
cases b,
exact h2,
cases c,
exact absurd h2 (less_than_zero (succ a)),
unfold lt,
cases b,
exact false.elim h1,
cases c,
exact false.elim h2,

-/

#check absurd
variable b : xnat
#reduce zero < succ b

end xena

