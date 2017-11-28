open nat

/- summation -/
-- Is this already in the library?
def summation (f : ℕ → ℕ) : ℕ → ℕ -- starts at 0
| 0 := f 0
| (succ m) := f (succ m) + (summation m) -- why is type of summation changed?
example (n : ℕ) : summation (λ _, 1) n = n + 1 := sorry 
theorem arithmetic_sum (n : ℕ) : summation id n = (n + 1) * n / 2 := sorry

def summation_from_to (f : ℕ → ℕ) (m n : ℕ) : ℕ :=
  if (m = 0) 
  then summation f n
  else (summation f n) - (summation f (m - 1))

/- product, factorial -/
def product (f : ℕ → ℕ) : ℕ → ℕ -- starts at 1
| 0 := 1
| (succ m) := f (succ m) * (product m)
example (n m : ℕ) : product (λ _, n) m = n ^ m := sorry

def fact : ℕ → ℕ := product id

/- binomial coefficients -/
def binom (m n : ℕ) : ℕ :=
begin
  by_cases (n < m),
    exact 0,
  exact (fact n) / ((fact m) * (fact (n - m)))
end

example : binom 0 0 = 1 := rfl
example : binom 1 1 = 1 := rfl
example : binom 0 1 = 0 := rfl -- ??
example : binom 1 0 = 1 := rfl -- ??

theorem binom_divisible (m n : ℕ) : 
  ((fact (succ m)) * (fact ((succ n) - (succ m)))) ∣ (fact (succ n)) := 
begin
  admit
end

theorem binom_div (n m : ℕ) : 
  (succ m) * (binom (succ n) (succ m)) = (succ n) * (binom n m) := 
begin
  have binomfact2 : binom (succ n) (succ m) 
    = (fact (succ n)) / ((fact (succ m)) * (fact ((succ n) - (succ m)))), 
      by admit, -- use "match"?
  admit
end

-- TODO
theorem binom_rec (n m : ℕ) : 
  binom (succ n) (succ m) = (binom n m) + (binom n (succ m)) :=
begin
  by_cases (n < m),
    have nlsm : n < succ m,
      calc n < m : h
         ... < succ m : by apply nat.lt.base,
    have snlsm : succ n < succ m, 
      calc succ n = n + 1 : by simp
              ... < m + 1 : by simp [nat.add_lt_add_right h]
              ... = succ m : by simp,
    have bnm0 : binom n m = 0, by admit, -- use "match"?
    have bnsm0 : binom n (succ m) = 0, by admit,
    have bsnsm0 : binom (succ n) (succ m) = 0, by admit,
    exact calc binom (succ n) (succ m) = 0 : by rw bsnsm0
               ... = 0 + 0 : by simp
               ... = binom n m + binom n (succ m) : by rw [bnm0, bnsm0],
  have nsnlsm : ¬(succ n < succ m), by admit, 
    -- use the contrapositive of (@lt_of_succ_lt_succ n m)
  have binomfact1 : binom n m 
    = (fact n) / ((fact m) * (fact (n - m))), by admit, -- use "match"?
  admit
end

/- Prove the number of subsets of {1,2,...,n} of size k is (binom n k) -/
#check (set ℕ)
#check 𝒫
-- look for functions useful for showing bijections...
-- grep "subset" -r ../lean/library/ | less
-- grep "size_of" -r ../lean/library/ | less
-- grep "bijection" -r ../lean/library/ | less
-- grep "injection" -r ../lean/library/ | less

/- basic binomial identities -/
theorem binom_sum (n : ℕ) : summation (binom n) n = 2 ^ n := 
sorry

theorem vandemond_theorem (m n r : ℕ) : 
-- C(m+n, r) = Σ C(m, k) * C(n, r-k), k = 0 to r
  summation (λ k, (binom m k) * (binom n (r - k))) r = binom (m + n) r := 
sorry

theorem binom_hockey_stick (n m : ℕ) : 
  summation_from_to (λ k, binom k m) m n = binom (n + 1) (m + 1) := 
sorry

theorem binom_theorem (n r : ℕ) :
  summation (λ m, (binom n m) * (r ^ m)) n = (1 + r) ^ n := 
sorry

