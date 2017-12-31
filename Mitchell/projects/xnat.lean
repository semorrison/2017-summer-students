inductive xnat : Type
| zero : xnat
| succ : xnat → xnat

namespace xnat

@[simp]
definition one := succ zero
definition two := succ one

@[simp]
definition add : xnat → xnat → xnat
| n zero := n
| n (succ p) := succ (add n p)

#reduce add (succ zero) (succ (succ zero))

instance : has_zero xnat := has_zero.mk zero
instance : has_one xnat := has_one.mk one
notation a + b := add a b

theorem add_zero (n : xnat) : n + zero = n := rfl

@[simp]
theorem add_succ (m n : xnat) : m + succ n = succ (m + n) := rfl

@[simp]
theorem zero_add (m : xnat) : zero + m = m :=
xnat.rec_on m rfl (λ x ih, by simp only [ih, add_succ])

theorem add_one_eq_succ (n : xnat) : n + one = succ n :=
begin
unfold one,
unfold add,
end

theorem one_add_eq_succ (n : xnat) : one + n = succ n :=
begin
induction n with n ih,
    refl,
    unfold add,
    rw ih,
end

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

@[simp]
definition mul : xnat → xnat → xnat
| n zero := zero
| n (succ p) := mul n p + n

notation a * b := mul a b

@[simp]
theorem mul_zero (a : xnat) : a * zero = zero := rfl

@[simp]
theorem zero_mul (a : xnat) : zero * a = zero := 
begin
induction a with k ih,
  refl,

  unfold mul,
  exact ih
end

@[simp]
theorem mul_one (a : xnat) : a * one = a := by simp

@[simp]
theorem one_mul (a : xnat) : one * a = a := 
begin
induction a with a ih,
  refl,

  unfold mul,
  rw ih,
  rw add_one_eq_succ
end

@[simp]
theorem right_distrib (a b c : xnat) : a * (b + c) = a * b + a * c := 
begin
  induction c with c ih,
    refl,

    rw add_succ,
    unfold mul,
    rw ih,
    rw add_assoc
end

@[simp]
theorem left_distrib (a b c : xnat) : (a + b) * c = a * c + b * c :=
begin
induction c with n Hn,
  unfold mul,
  refl,
rw [←add_one_eq_succ,right_distrib,Hn,right_distrib,right_distrib],
rw [mul_one,mul_one,mul_one],
rw [add_assoc,←add_assoc (b*n),add_comm (b*n),←add_assoc,←add_assoc,←add_assoc],
end

theorem mul_assoc (a b c : xnat) : (a * b) * c = a * (b * c) :=
begin
induction c with n Hn,
  refl,

  rw [mul, mul],
  rw right_distrib,
  rw Hn
end

theorem mul_comm (a b : xnat) : a * b = b * a :=
begin
induction b with n Hn,
  simp,

  rw mul,
  rw ←add_one_eq_succ,
  rw left_distrib,
  rw Hn,
  rw one_mul
end

def pred : xnat → xnat
| 0 := 0
| (succ x) := x

def sub : xnat → xnat → xnat
| 0 _ := 0
| n 0 := n
| (succ n) (succ m) := sub n m

def pow (b : xnat) : xnat → xnat
| 0 := 1
| (succ n) := pow n*b

infix `-` := sub
infix `^` := pow

@[simp]
definition lt : xnat → xnat → Prop 
| zero zero := false
| (succ m) zero := false
| zero (succ p) := true 
| (succ m) (succ p) := lt m p

notation a < b := lt a b

@[simp]
theorem inequality_A1 (a b t : xnat) : a < b → a + t < b + t :=
begin
  induction t with n Hn,
    simp,
    {intro h, exact h}, -- SCOTT. For some reason, this line is required in order to prove that a < b → a < b. Shouldn't this be contained in simp?

    rw [add_succ, add_succ],
    rw lt,
    exact Hn
end

@[simp]
theorem lt_cancel (a b t : xnat) : a + t < b + t → a < b :=
begin
induction t with n Hn,
  simp,
  {intro h, exact h},

  rw [add_succ, add_succ],
  rw lt,
  exact Hn,
end

theorem lt_then_sum (a b t : xnat) : a < b → ∃ t : xnat, b = a + succ t := sorry
theorem inequality_A2 (a b c : xnat) : a < b → b < c → a < c := sorry
theorem inequality_A3 (a b : xnat) : (a < b ∨ a = b ∨ b < a) 
                                   ∧ (a < b → ¬ (a = b))
                                   ∧ (a < b → ¬ (b < a))
                                   ∧ (a = b → ¬ (b < a)) := sorry
theorem inequality_A4 (a b : xnat) : zero < a → zero < b → zero < a * b := sorry


example : one + one = two := by refl

example : one * one = one := 
begin
refl
end

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

