inductive xnat
| zero : xnat
| succ : xnat → xnat

open xnat

#check zero -- it's an xnat

definition one := succ zero
definition two := succ one

definition add : xnat → xnat → xnat
| n zero := n
| n (succ p) := succ (add n p)

notation a + b := add a b

theorem one_add_one_equals_two : one + one = two :=
begin
unfold two,
unfold one,
unfold add,
end

#print one_add_one_equals_two

theorem add_assoc_ (a b c : xnat) : (a + b) + c = a + (b + c) :=
begin
induction c with t Ht,
  refl,
unfold add,
rewrite [Ht],
end

#print add_assoc_

definition lt : xnat → xnat → Prop 
| zero zero := false
| (succ m) zero := false
| zero (succ p) := true 
| (succ m) (succ p) := lt m p

notation a < b := lt a b

theorem inequality_A1 (a b t : xnat) : a < b → a + t < b + t :=
begin
induction b with k Hk,
    refl,
unfold add,
unfold lt,
rewrite [Ht],
end

