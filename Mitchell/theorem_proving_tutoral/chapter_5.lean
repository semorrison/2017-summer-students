section
variables p q r s : Prop

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by simp
example : p ∨ q ↔ q ∨ p := by simp

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by simp
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by simp

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
    split,
    {intro h,
    cases h.right,
    left, simp *,
    right, simp * },
    {intro h,
    cases h with hpq hpr,
    {show p ∧ (q ∨ r), exact ⟨hpq.left, or.inl hpq.right⟩},
    {show p ∧ (q ∨ r), exact ⟨hpr.left, or.inr hpr.right⟩ }}
end

end