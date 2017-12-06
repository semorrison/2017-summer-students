namespace binomials


definition factorial : nat → nat
| 0 := 1
| (nat.succ n) := (nat.succ n) * (factorial n)

#reduce factorial 5

-- TODO: get this notation working (also see if you can infix ncr)
-- notation a ! := factorial a
-- postfix ! := factorial
-- #check (5 !)



definition ncr : nat → nat → nat
| n r := bool.cases_on (n < r) ((factorial n)/(factorial (n-r) * factorial r)) 0

#reduce ncr 4 2
#reduce ncr 3 2
-- #reduce ncr 25 14 -- [Lean] deep recursion was detected at 'replace' (potential solution: increase stack space in your system)
#reduce ncr 3 4

-- TODO: Prove some basic binomial identities, either by arithmetic with factorials, or by explicit bijections between sets being counted.


-- TODO: Prove that the number of subsets of {1,2,...,n} of size k is ncr n k

-- Construct an explicit bijection? (binary representation for inclusion/exclusion?)
-- injectivity: difference in digit produces different subset
-- surjectivity??? (explicit inverse?)

#check set nat

definition test1 : set nat := {1,2,3}
definition test2 : set nat := {n | n < 5}

#print test1
#reduce test1
#print test2
#reduce test2

-- How to define the set {1,...,n} ? 
-- Does it need to be more explicit that this so each element is computeable?
definition set_n : nat → set nat
--| n := {m | m <= n}
| 0 := {}
| (nat.succ n) := set.insert (nat.succ n) (set_n n)

definition test3 := set_n 3

#check test3
#reduce test3
#print test3

-- The proposition that one set is a subset of another (you need to supply the proof)
#reduce set.subset test1 test2 
#reduce set.subset test2 test2
#reduce set.subset test1 test1
#reduce set.subset test2 test1 

#reduce test3
-- A set is just a function which tells you whether a particular element is contained in the set?
-- It does this by producing a proposition which asserts the given element's membership of said set
-- set α is sugar for (α → Prop)
#reduce test3 2

definition test4 : set (set nat) := set.powerset test3
#reduce test4

-- Is this definition of set strong enough? Try namesets?


-- Define injective/surjective
definition inj  {α β : Type} (f : α → β) : Prop := ∀ x y : α, f x = f y → x = y
definition surj {α β : Type} (f : α → β) : Prop := ∀ y : β, ∃ x : α, f x = y

#check inj (λ n : nat, n) 
#reduce inj (λ n : nat, n) 

-- Show the id function on natural numbers is injective
example : inj (λ n : nat, n) :=
begin
unfold inj,
intros x y hxy,
exact hxy
end

-- Show the id function on natural numbers is surjective
example : surj (λ n : nat, n) :=
begin
unfold surj,
intro y,
have h1: y = y, by refl,
exact exists.intro y h1
end

-- Bijection
definition bij {α β : Type} (f : α → β) : Prop
:= inj f ∧ surj f

definition inj'  {γ δ : Type} {α : set γ} {β : set δ} (f : α → β) : Prop := ∀ x y, f x = f y → x = y ∧ α x ∧ α y
definition surj' {α β : Type} (f : α → β) : Prop := ∀ y : β, ∃ x : α, f x = y

theorem binomial_coefficients_subsets_bijection (n k : nat) : ∃ f :  →  := sorry
end binomials
