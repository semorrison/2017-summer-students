inductive xnat : Type
| zero : xnat
| succ : xnat → xnat

namespace xnat

@[simp]
def add (m n : xnat) : xnat := 
xnat.rec_on n m (λ x sum_m_n, succ sum_m_n)
-- n is the input to rec_on. If n is zero, return m. Otherwise, when n = succ x, define add m (succ n) to be
-- succ (add m n)
-- It's just induction!

#reduce add (succ zero) (succ (succ zero))

instance : has_zero xnat := has_zero.mk zero
instance : has_add xnat := has_add.mk add

@[simp]
theorem add_zero (m : xnat) : m + zero = m := rfl

@[simp]
theorem add_succ (m n : xnat) : m + succ n = succ (m + n) := rfl

@[simp]
theorem zero_add (m : xnat) : zero + m = m :=
xnat.rec_on m rfl (λ x ih, by simp [ih])

@[simp]
theorem add_assoc (m n k : xnat) : m + n + k = m + (n + k) :=
xnat.rec_on k rfl (λ x ih, by simp [ih])

@[simp]
theorem succ_add (m n : xnat) : succ m + n = succ (m + n) :=
xnat.rec_on n rfl (λ x ih, by simp [ih])

@[simp]
theorem add_comm (m n : xnat) : m + n = n + m :=
xnat.rec_on n (by simp only [add_zero, zero_add]) (λ x ih, by simp [ih])

end xnat
