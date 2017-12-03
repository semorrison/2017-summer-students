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

definition test4 : set (set nat):= set.powerset test3
#reduce test4

theorem binomial_coefficients_subsets_bijection (n k : nat) : false := sorry

end binomials