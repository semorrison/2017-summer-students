inductive xnat : Type
| zero : xnat
| succ : xnat → xnat

namespace xnat

definition one := succ zero
definition two := succ one

@[simp]
-- def add (m n : xnat) : xnat := 
-- xnat.rec_on n m (λ x sum_m_n, succ sum_m_n)
-- n is the input to rec_on. If n is zero, return m. Otherwise, when n = succ x, define add m (succ n) to be
-- succ (add m n)
-- It's just induction!

-- Alternatively
definition add : xnat → xnat → xnat
| n zero := n
| n (succ p) := succ (add n p)

#reduce add (succ zero) (succ (succ zero))

instance : has_zero xnat := has_zero.mk zero
instance : has_add xnat := has_add.mk add

@[simp]
theorem add_zero (m : xnat) : m + zero = m := rfl

@[simp]
theorem add_succ (m n : xnat) : m + succ n = succ (m + n) := rfl

@[simp]
theorem zero_add (m : xnat) : zero + m = m :=
xnat.rec_on m rfl (λ x ih, by simp only [ih, add_succ])

@[simp]
theorem add_assoc (m n k : xnat) : m + n + k = m + (n + k) :=
xnat.rec_on k rfl (λ x ih, by simp [ih, add_succ])

@[simp]
theorem succ_add (m n : xnat) : succ m + n = succ (m + n) :=
xnat.rec_on n rfl (λ x ih, by simp only [ih, add_succ])

@[simp]
theorem add_comm (m n : xnat) : m + n = n + m :=
xnat.rec_on n (by simp only [add_zero, zero_add]) 
(λ x ih, by simp only [ih, succ_add, add_succ])

@[simp]
theorem eq_iff_succ_eq_succ (a b : xnat) : succ a = succ b ↔ a = b :=
begin
split,
    exact succ.inj,
assume H : a = b,
rw [H]
end

theorem add_cancel_right (a b t : xnat) :  a = b ↔ a+t = b+t :=
begin
split,
    assume h : a = b,
      rw h,
    
    induction t with k ih,
      intro h1,
      rw eq.symm (add_zero a),
      rw eq.symm (add_zero b),
      exact h1,
      
      intro h2,
      unfold add at h2,
      rw eq_iff_succ_eq_succ at h2,
      exact ih h2,
end








example : one + one = two := by refl

example (m n k : xnat) (h : succ (succ m) = succ (succ n)) :
  n + k = m + k :=
begin
  injections with h' h'',
  rw h''
end

example (n : xnat) : n + one = succ n := by refl
example (n : xnat) : one + n = succ n :=
begin
    induction n with n ih,
    refl,
    simp only [ih, add_succ]
end

end xnat
