import data.nat.prime
open nat

-- define a prime
#print prime
#print nat.less_than_or_equal
#print nat.dvd_add_iff_left

-- prove that 2 and 3 are primes, but 4 isn't
lemma enumerate_lt (n m : ℕ) : n < (succ m) → n = m ∨ n < m := 
sorry

lemma lt_1 (n : ℕ) : n < 1 → n = 0 :=
begin 
  intro,
  have h0 : n < 1 → n = 0 ∨ n < 0, by apply enumerate_lt,
  have h1 : n = 0 ∨ n < 0, by exact (h0 a),
  have h2 : ¬(n < 0), by admit,
  admit -- prop logic
end

lemma lt_2 (n : ℕ) : n < 2 → n = 1 ∨ n = 0 := 
begin 
  admit
end

lemma lt_3 (n : ℕ) : n < 3 → n = 2 ∨ n = 1 ∨ n = 0 := 
begin 
  admit
end

lemma zero_ndvd (n : ℕ) : n ≠ 0 → ¬(0 ∣ n) := 
begin 
  admit
end

#check prime_two
example : prime 2 := 
begin
  suffices : 2 ≥ 2 ∧ ∀ (m : ℕ), m < 2 → m ∣ 2 → m = 1,
    exact (@prime_def_lt 2).elim_right this,
  constructor,
    admit,
  intros m mlt2 mdvd2,
  have me01 : m = 1 ∨ m = 0, by exact ((lt_2 m) mlt2),
  have mne0 : m ≠ 0, by admit, -- use mdvd2, zero_ndvd
  admit -- use me01, mne0
end

#check prime_three
example : prime 3 := 
begin
  suffices : 3 ≥ 2 ∧ ∀ (m : ℕ), m < 3 → m ∣ 3 → m = 1,
    exact (@prime_def_lt 3).elim_right this,
  constructor,
    admit,
  intros m mlt3 mdvd3,
  have me012 : m = 2 ∨ m = 1 ∨ m = 0, by exact ((lt_3 m) mlt3),
  have mne0 : m ≠ 0, by admit, -- use mdvd3, zero_ndvd
  have mne2 : m ≠ 2, by admit, -- ¬(2 ∣ 3)
  admit -- use me012, mne0, mne2
end

example : ¬prime 4 := 
begin
  unfold prime,
  intro h1,
  have h2 : ∀ (m : ℕ), m ∣ 4 → m = 1 ∨ m = 4, by exact h1.elim_right,
  have h3 : 2 ∣ 4 → 2 = 1 ∨ 2 = 4, by exact h2 2,
  have h4 : 2 ∣ 4, by admit, -- please do this automatically
  have h5 : ¬(2 = 1 ∨ 2 = 4), by admit, -- seriously please
  exact (h5 (h3 h4))
end

-- prove that oddness and primality are decidable.
open decidable

def odd (n : ℕ) : Prop := ¬(2 ∣ n)
def odd_decidable_def : ℕ → Prop
| 0 := false
| 1 := true
| (m + 2) := odd_decidable_def m
lemma odd_eq_def {n : ℕ} : odd n ↔ odd_decidable_def n := sorry

instance decidable_odd (p : ℕ) : decidable (odd p) := sorry
  -- decidable_of_iff' _ odd_eq_def 
  -- not decidable enough?
-- prime_def_min_fac {p : ℕ} : prime p ↔ p ≥ 2 ∧ min_fac p = p
-- can be found in prime.lean

instance decidable_prime (p : ℕ) : decidable (prime p) := 
sorry

-- prove that every number greater than 1 has a prime factor.
theorem has_prime_factor (n : ℕ) : n > 1 → ∃ (m : ℕ), prime m ∧ m ∣ n :=
sorry

-- no rational square root of 2
theorem two_irrat : ¬∃ (m n : ℕ), n > 0 ∧ m^2 = 2 * n^2 := sorry

-- prime factorisation is unique

-- prove that every number can be written as a product of primes
-- first find a way to write lists.