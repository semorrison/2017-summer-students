def foo : (ℕ → ℕ) → ℕ := λ f, f 0 -- function application at 0
#reduce foo (λ x : ℕ, x+1) -- 1
def foo' (f : ℕ → ℕ) : ℕ := f 0 -- equivalent

def curry (α β γ : Type) (f : α × β → γ) : α → β → γ := λ (a: α) (b: β), f (a,b)
def uncurry (α β γ : Type) (f : α → β → γ) : α × β → γ := λ ab: α × β, f ab.1 ab.2
