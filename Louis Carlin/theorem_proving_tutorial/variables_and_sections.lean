variables (α β γ : Type)

def compose (g : β → γ) (f: α → β) (x: α) : γ := g (f x)
def do_twice (h : α → α) (x : α) : α := h (h x)

variables n m: ℕ
#check n

-- section limits the scope of variables
section useful
  variables (α' β' γ' : Type)
  variables (g : β' → γ') (f : α' → β') (h : α' → α')
  variable x : α'

  def compose' := g (f x)
  def do_twice' := h (h x)
end useful
