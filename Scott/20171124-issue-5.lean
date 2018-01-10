variables (α : Type) (a b : α)
example : ∀ (p : α → Prop), a = b → p a → p b :=
begin
  intros p h1 h2,
  exact h1 ▸ h2
end

example (p : α → Prop) : a = b → p a → p b :=
begin
  intros h1 h2,
  exact h1 ▸ h2
end
