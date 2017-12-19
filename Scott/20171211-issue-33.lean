import tactic.norm_num

open nat

/- product, factorial -/
def product (f : ℕ → ℕ) : ℕ → ℕ
| 0 := f 0
| (m + 1) := f (m + 1) * (product m)

def product_from_to (f : ℕ → ℕ) (m n : ℕ) : ℕ :=
  if (m > n) 
  then 1
  else product (λ x, f (x + m)) (n - m)

def fact : ℕ → ℕ := product_from_to id 1

/- binomial coefficients -/
def binom (n m : ℕ) : ℕ :=
  if (n < m)
  then 0
  else (product_from_to id (n - m + 1) n) / (product_from_to id 1 m)

#eval binom 10 5

example : binom 10 5 = 252 :=
begin
unfold binom,
norm_num,
unfold product_from_to,
norm_num,
unfold product,
norm_num,
end

example : binom 10 5 = 252 :=
begin
refl
end

#eval binom 100 50

example : binom 10 5 = 252 :=
begin
unfold binom,
norm_num,
unfold product_from_to,
norm_num,
unfold product,
norm_num,
end
