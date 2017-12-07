import analysis.real

#check (5.4 : ℝ) 
#reduce 2^3

#check true

def nat.dvd (m n : ℕ) : Prop := ∃ k, n = m * k

instance : has_dvd nat := ⟨ nat.dvd ⟩

@[simp]
theorem nat.dvd_refl (n : ℕ) : n | n :=
⟨1, by simp⟩

#check 5 ∣ 5
#reduce 5 ∣ 5


notation [parsing_only] `[` a `**` b `]` := a * b + 1

#reduce [5**2]
-- variables (a b : ℕ)
-- #check [a ** b ]

def mul_square (a b : ℕ) := a * a * b * b

infix `<*>` : 50 := mul_square
--associates to the left
#reduce 2 <*> 3


prefix `//` := λ x : ℕ, x+1


section mod_m
    parameter (m : ℤ)

variables (a b c : ℤ)

definition mod_equiv := (m ∣ b - a)

local infix ≃ := mod_equiv

theorem mod_refl : a ≃ a :=
show m ∣ a - a, by simp

theorem mod_symm (h : a ≃ b) : b ≃ a :=
by cases h with c hc; apply dvd_intro (-c) ; simp [eq.symm hc] -- why doesn't this work

theorem mod_trans (h₁ : a ≃ b) (h₂ : b ≃ c) : a ≃ c :=
begin 
    cases h₁ with d hd, cases h₂ with e he,
    apply dvd_intro_left (d+e),
    simp [mul_add, eq.symm hd, eq.symm he]
end

end mod_m


variables m n : ℕ
variables i j : ℤ

#check i + m -- ℤ
#check i + m + j -- ℤ
#check i + m + n -- ℤ

#print notation

#check (5 : ℤ)
#check (5 : int)

#print fields ring
#print instances ring


#check nat.pred_succ
#check @nat.lt_of_succ_le