
section A
variables α β γ : Type
def acurry : (α × β → γ) → α → β → γ := λ f x y, f (x,y)
#print acurry
end A
-- This is working!

section B
def bcurry (α β γ : Type) (f : α × β → γ) : α → β → γ := f(x,y)
#print bcurry
end B
-- I have no idea how to rewrite it this way...
-- (with local variables, no λ and as shown in the exercise)

section C
def curry (α β γ : Type) (f : α × β → γ) (g : γ → α → β → γ) (x : α) (y : β): α → β → γ := 
g (f(x,y))
#print curry
variables x y : ℕ
variable f : ℕ × ℕ → ℕ
variable g : ℕ → ℕ → ℕ → ℕ 
#reduce curry f g x y
end C
-- This is definitely not right...

section U
variables α β γ : Type
def uncurry : (α → β → γ) → α × β → γ := λ f (x,y) , f x y
#print uncurry
end U
-- Why is uncurry not working?

section V
def vuncurry (α β γ : Type) (f : α → β → γ): α × β → γ := f x y
#print bcurry
end V
-- Also not working


/- Another Question -/
-- How to have (x,y) as inputs of a definition? Do I need to write it out seperately?
-- ( (x,y) : α × β ) does not work.


