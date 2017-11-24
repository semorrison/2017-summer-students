constants α β : Type
constants a1 a2 : α
constants b1 b2 : β

#check λ x y: ℕ, x + y -- addition

#reduce (λ x : α, x) a1 -- #reduce performs beta reduction

constants m n : nat
constant b : bool

#print "reducing pairs"
#reduce (m, n).1 -- m

#reduce tt && ff -- ff
#reduce tt || ff -- tt

#eval 12345 * 54321


