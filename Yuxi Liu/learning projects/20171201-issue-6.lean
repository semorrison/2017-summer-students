open nat

def f : ℕ → ℕ 
| 0 := 0
| 1 := 1
| (n + 2) := f n


example : ∀ n m : ℕ, (m < n → f m = f (m % 2)) :=
begin
  intro n,
  induction n with n Hn,
    intro m,
    induction m with m Hm, 
      intro, simp,
    intro, exfalso, apply not_lt_zero, assumption,
  intros m mlsn, 
  by_cases (m < 2),
    have m01: m = 0 ∨ m = 1, by admit, -- unpack < somehow. Help?
    cases m01 with m0 m1,
      rw m0, refl,
    rw m1, refl,
  have : ∃ t : ℕ, m = t + 2, by admit, -- unpack < somehow. Help?
  cases this with t hmt,
  rw hmt, 
  have : (t + 2) % 2 = t % 2, by simp,
    rw this,
  have : t < n, by calc t = t + (2 - 2) : by simp
                      ... = t + 2 - 2 : by simp
                      ... = m - 2 : by rw hmt
                      ... < succ n - 2 : by admit -- use (m < succ n) and (¬m < 2)
                      ... = n - 1 : by refl
                      ... ≤ n : by admit, -- help plz
  have ftft2 : f t = f (t % 2), from Hn t this,
  exact calc f (t + 2) = f t : by refl
                   ... = f (t % 2) : ftft2
end