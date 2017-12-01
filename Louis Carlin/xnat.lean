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





end xena
