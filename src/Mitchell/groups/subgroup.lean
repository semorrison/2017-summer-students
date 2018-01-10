universe u
variables {α : Type u}

class subgroup [group α] (S : set α) := 
    (mul_closed : ∀ a b ∈ S, a * b ∈ S) (inv_closed : ∀ a ∈ S, a⁻¹ ∈ S) (one_closed : has_one.one α ∈ S)

theorem int_subgroups (S : set ℤ) [group ℤ] [subgroup S] : ∃ a ∈ S, ∀ b ∈ S, a ∣ b := sorry

