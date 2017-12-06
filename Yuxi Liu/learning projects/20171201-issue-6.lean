import order.basic

open nat

def f : ℕ → ℕ 
| 0 := 0
| 1 := 1
| (n + 2) := f n

lemma not_zero_iff_succ (n : ℕ) : ¬n = 0 ↔ ∃ t : ℕ, n = succ t :=
begin
  constructor,
    intro h,
    cases n,
      exfalso, apply h, refl,
    existsi a, refl,
  intro, cases a, rw a_1, 
  apply succ_ne_zero
end

lemma le_add : ∀ (n m : ℕ), n ≤ m ↔ ∃ t : ℕ, m = n + t :=
begin
  intro n, 
  induction n with n Hn, 
    intro m,
    constructor, 
      intro, existsi m, simp,
    intro, apply zero_le,
  intro m,
  constructor,
    intro snlem, 
    have nlem : n ≤ m, from calc n ≤ succ n : by apply le_succ
                               ... ≤ m : snlem, 
    have : ∃ (t : ℕ), m = n + t, from (Hn m).elim_left nlem,
    cases this with t ment,
    by_cases (t = 0),
      rw h at ment,
      rw ment at snlem,
      exfalso,
      apply not_succ_le_self, assumption,
    have tet' : ∃ t' : ℕ, t = succ t', 
      rw ←not_zero_iff_succ, apply h,
    cases tet' with t' htet',
    existsi t',
    rw [ment, htet'],
    exact calc n + succ t' = succ (n + t') : by refl
                       ... = succ (t' + n) : by rw add_comm
                       ... = t' + succ n : by refl
                       ... = succ n + t' : by rw add_comm,
  intro etmsnt, cases etmsnt with t msnt,
  rw msnt, 
  apply le_add_right
end

lemma lt_le (n m : ℕ) : n < m → n ≤ m :=
λ h, less_than_or_equal.rec_on h
  (le_succ n) 
  (begin 
    intros b lesnb nleb,
    apply less_than_or_equal.step, assumption
  end)

lemma lt_add (n m : ℕ) : n < m ↔ ∃ t : ℕ, m = n + succ t :=
begin
  constructor,
    intro, 
    have nlem : n ≤ m, apply lt_le, assumption,
      rw le_add at nlem,
      cases nlem with t mnt,
      rw mnt at a,
      by_cases (t = 0),
        exfalso, 
        rw h at a,
        simp at a, apply nat.lt_irrefl, assumption,
    have : ∃ t' : ℕ, t = succ t', from ((not_zero_iff_succ t).elim_left h),
    cases this with t' ht',
    existsi t', 
    rw [mnt, ht'],
  intro h,
  cases h with t mnst,
  rw mnst,
  exact calc n ≤ n + t : by apply le_add_right
           ... < succ (n + t) : by apply lt_succ_self
           ... = n + succ t : by simp
end

lemma less_pred (n m : ℕ) : n < m → n ≤ pred m :=
begin
  intro nlm,
  have : ∃ t : ℕ, m = n + succ t, 
    rw ←lt_add, assumption,
  cases this with t mnst,
  rw mnst,
  simp, apply le_add_right
end

lemma less_cases (n m : ℕ) : n < m → n = pred m ∨ n < pred m :=
begin
  intro nlm,
  apply nat.eq_or_lt_of_le,
  exact (less_pred n m nlm)
end

lemma less_1 (n : ℕ) : n < 1 → n = 0 :=
begin
  intro nl1,
  have h : n = 0 ∨ n < 0, from (less_cases n 1 nl1),
  cases h,
    assumption,
  exfalso, apply not_succ_le_zero, assumption
end 

lemma less_2 (n : ℕ) : n < 2 → n = 0 ∨ n = 1 :=
begin
  intro nl2,
  have h : n = 1 ∨ n < 1, from (less_cases n 2 nl2),
  cases h,
    right,
    assumption,
  left, apply less_1, assumption
end

lemma not_less_then_geq (n m : ℕ) : ¬n < m → m ≤ n :=
begin
  intro nnlm,
  rw ←not_lt_iff, assumption
end

#check @sub_lt

lemma less_sub (n m t : ℕ) : n < m ∧ ¬(n < t) → n - t < m - t :=
begin
  intro h,
  have nlm : n < m, from h.elim_left,
  have tlen : t ≤ n, 
    apply not_less_then_geq, exact h.elim_right,
  have tlm : t < m, from calc t ≤ n : tlen
                            ... < m : nlm, 
  have mt0 : 0 < m - t, 
    apply nat.sub_pos_of_lt, assumption,
  have mn0 : 0 < m - n,
    apply nat.sub_pos_of_lt, assumption,
  have mtmnlmt : (m - t) - (m - n) < (m - t), 
    apply sub_lt, repeat { assumption },
  have ntmnemt : (n - t) + (m - n) = m - t, from calc
    (n - t) + (m - n) = (m - n) + (n - t) : by rw add_comm
                  ... = (m - n) + n - t : by {
                    rw nat.add_sub_assoc, assumption,
                  }
                  ... = n + (m - n) - t : by rw add_comm
                  ... = m - t : by {
                    rw add_sub_of_le, apply lt_le, assumption,
                  }, 
  have : n - t = (m - t) - (m - n), from calc
    n - t = (n - t) + (m - t) - (m - t) : by rw nat.add_sub_cancel
      ... = (n - t) + (m - t) - ((n - t) + (m - n)) : by rw ntmnemt
      ... = (n - t) + (m - t) - (n - t) - (m - n) : by rw nat.sub_sub
      ... = (m - t) + (n - t) - (n - t) - (m - n) : by rw add_comm
      ... = (m - t) - (m - n) : by rw nat.add_sub_cancel,
  rw this,
  apply sub_lt_of_pos_le,
    assumption,
  apply @nat.sub_le_sub_left, assumption
end

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
    have m01: m = 0 ∨ m = 1, 
      apply less_2, assumption,
    cases m01 with m0 m1,
      rw m0, refl,
    rw m1, refl,
  have hmt2 : ∃ t : ℕ, m = t + 2, 
    have h2leqm : 2 ≤ m,
      rw ←not_lt_iff, assumption,
    rw le_add at h2leqm,
    cases h2leqm with t ht,
    existsi t, rw ht, simp,
  cases hmt2 with t hmt,
  rw hmt, 
  have : (t + 2) % 2 = t % 2, by simp,
    rw this,
  have : t < n, by calc t = t + (2 - 2) : by simp
                      ... = t + 2 - 2 : by simp
                      ... = m - 2 : by rw hmt
                      ... < succ n - 2 : by { apply less_sub, cc }
                      ... = n - 1 : by refl
                      ... ≤ n : by apply pred_le,
  have ftft2 : f t = f (t % 2), from Hn t this,
  exact calc f (t + 2) = f t : by refl
                   ... = f (t % 2) : ftft2
end