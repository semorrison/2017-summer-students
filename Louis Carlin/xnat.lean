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


end xena
