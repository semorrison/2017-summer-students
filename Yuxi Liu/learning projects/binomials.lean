open nat

/- summation -/
def summation (f : ℕ → ℕ) : ℕ → ℕ
| 0 := f 0
| (succ m) := f (succ m) + (summation m) -- why is type of summation changed?
example (n : ℕ) : summation (λ _, 1) n = n + 1 := 
begin
  induction n with n Hn,
    refl,
  unfold summation,
  rw Hn, 
  simp
end

#print nat.div
#print nat.mod

theorem arithmetic_sum (n : ℕ) : summation id n = (n + 1) * n / 2 := 
begin
  induction n with n Hn,
    refl,
  unfold summation,
  rw Hn, simp,
  exact calc succ n + n * (n + 1) / 2 
        = ((succ n) * 2 + n * (n + 1)) / 2 : by admit
    ... = ((succ n) * 2 + n * succ n) / 2 : by simp
    ... = ((succ n) * 2 + succ n * n) / 2 : by rw (mul_comm (succ n) n)
    ... = ((succ n) * (2 + n)) / 2 : by rw left_distrib
    ... = ((succ n) * (succ n + 1)) / 2 : by simp,
end

def summation_from_to (f : ℕ → ℕ) (m n : ℕ) : ℕ :=
  if (m > n) 
  then summation f n
  else summation (λ x, f (x + m)) (n - m)

/- product, factorial -/
def product (f : ℕ → ℕ) : ℕ → ℕ
| 0 := f 0
| (succ m) := f (succ m) * (product m)
example (n m : ℕ) : product (λ _, n) m = n ^ (succ m) := 
begin
    induction m with m Hm,
      unfold product, 
      simp,
    unfold product,
    rw Hm, unfold pow, simp
end

def product_from_to (f : ℕ → ℕ) (m n : ℕ) : ℕ :=
  if (m > n) 
  then 1
  else product (λ x, f (x + m)) (n - m)
  -- unknown identifier?

def fact : ℕ → ℕ := product_from_to id 1

/- binomial coefficients -/
def binom (n m : ℕ) : ℕ :=
  if (n < m)
  then 0
  else (product_from_to id (n - m + 1) n) / (product_from_to id 1 m)

lemma zero_product (n : ℕ) : product_from_to id 0 n = 0 :=
begin
  unfold product_from_to, admit -- help
end

-- any product of k sequential integers is divisible by k!
-- thus, the definition of binomial coefficient is integer.
lemma binom_divisible (m k : ℕ) :
  (product_from_to id 1 k) ∣ (product_from_to id m (m + k - 1)) :=
begin
  revert m,
  induction k with k Hk,
    intro m,
    simp,
    have : product_from_to id 1 0 = 1, 
      unfold product_from_to, refl,
    rw this, simp,
  intro m, 
  induction m with m Hm,
    rw zero_product, simp,
  have h1 : product_from_to id (succ m) (succ m + succ k - 1) = 
    product_from_to id m (m + k) + (k + 1) * product_from_to id (m + 1) (m + k),
      simp,
      admit, -- help simplify
  have h2 : product_from_to id 1 (succ k) = (k + 1) * product_from_to id 1 k,
    admit, -- help simplify
  rw [h1, h2],
  have h3 : (k + 1) * product_from_to id 1 k ∣ product_from_to id m (m + k),
    rw ←h2,
    apply Hm,
  have h4 : (k + 1) * product_from_to id 1 k ∣ (k + 1) * product_from_to id (m + 1) (m + k),
    suffices h4' : product_from_to id 1 k ∣ product_from_to id (m + 1) (m + 1 + k - 1),
      admit, -- help simplify
    apply (Hk (m + 1)),
  admit, -- help find lemma : (∀ n a b, ℕ), n ∣ a → n ∣ b → n ∣ (a + b)
end

example : binom 0 0 = 1 := rfl
example : binom 1 0 = 1 := rfl
example : binom 0 1 = 0 := rfl
example : binom 10 5 = 252 := by admit
-- by refl
-- deep recursion was detected at 'replace' 
-- (potential solution: increase stack space in your system)

lemma 


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

