import tactic.norm_num

private lemma p1 (n : ℕ) : cond (to_bool (n % 2 = 1)) 1 0 = n % 2 :=
begin
  by_cases (n % 2 = 1),
  rw h,
  simp, 
  have q : n % 2 = 0,
  {
    have r := nat.mod_two_eq_zero_or_one n,
    induction r,
    assumption,
    contradiction
  },
  rw q,
  simp
end
lemma p2 (n : ℕ) : 2 * (n / 2) + cond (to_bool (n % 2 = 1)) 1 0 = n :=
begin
  rw p1,
  simp,
  rw nat.mod_add_div,
end
lemma p3 (n : ℕ) : 2 * ((n+2) / 2) + cond (to_bool (n % 2 = 1)) 1 0 = n + 2 :=
begin
  have q := p2 (n+2),
  rw nat.add_mod_right at q,
  exact q
end