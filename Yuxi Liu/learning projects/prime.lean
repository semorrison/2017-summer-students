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

-- prove that primality is decidable.
-- As a warmup, show that being odd is decidable.

-- prove that every number greater than 1 has a prime factor.
theorem has_prime_factor (n : ℕ) : n > 1 → ∃ (m : ℕ), prime m ∧ m ∣ n :=
sorry

-- prove that every number can be written as a product of primes
-- first find a way to write lists.

-- no rational square root of 2
theorem two_irrat : ¬∃ (m n : ℕ), n > 0 ∧ m^2 = 2 * n^2 := sorry

-- prime factorisation is unique