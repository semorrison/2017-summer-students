-- Section 2.4. Complete the following definitions of curry and uncurry
def curry (α β γ : Type) (f : α × β → γ) : α → β → γ := λ (a : α) (b : β), f (a,b)  

def uncurry (α β γ : Type) (f : α → β → γ) : α × β → γ := λ ( x : α × β), f x.1 x.2

#check curry
#check uncurry

-- Section 2.5. bar is not allowed because there is no assurance that addition will be defined for type a
def foo := let a := nat  in λ x : a, x + 2

­
-- def bar := (λ a, (λ x : a, x + 2)) nat

--- Exercise 3. vec_add adds two vectors of natural numbers of the same length
universe u
constant vec : Type u → ℕ → Type u

namespace vec
  constant empty : Π α : Type u, vec α 0
  constant cons :
    Π (α : Type u) (n : ℕ), α → vec α n → vec α (n + 1)
  constant append :
    Π (α : Type u) (n m : ℕ),  vec α m → vec α n → vec α (n + m)
  constant vec_add : Π {n : ℕ}, vec ℕ n → vec ℕ n → vec ℕ n
  constant vec_reverse : Π {n : ℕ}, vec ℕ n → vec ℕ n

#check vec_add
end vec

