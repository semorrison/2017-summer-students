variables p q : Prop

--  example p → q → (p → p) := λ (_ : p) (_ : q) (hp : p), hp -- not fine
-- example p → q → p → p := λ (_ : p) (_ : q) (hp : p), hp -- not fine

variables (α : Type) (a b : α)

example : ∀ (p : α → Prop) ,  (a = b) → p a → p b :=
  assume h1 : a = b,
  assume h2 : p a, 
  h1 ▸ h2


example  (p : α → Prop) : a = b → p a → p b :=
  assume h1 : a = b,
  assume h2 : p a, 
  h1 ▸ h2 


  inductive weekday : Type
| sunday : weekday
| monday : weekday
| tuesday : weekday
| wednesday : weekday
| thursday : weekday
| friday : weekday
| saturday : weekday

namespace weekday -- to save some typing
  def day_of_number : ℕ → weekday 
  | 0 := sunday
  | 1 := monday
  | 2 := tuesday
  | 3 := wednesday
  | 4 := thursday
  | 5 := friday
  | 6 := saturday
  | n  := day_of_number (n % 7)
 -- | (n + 7) := day_of_number n

#reduce 12 % 7

#reduce day_of_number 7
-- #reduce day_of_number 12 -- this times out

end weekday



variables  (d e : ℕ)
variable h4 : e = 1 + d
/-
include h4 --comment this out

theorem T5 (a b c d : ℕ)
  (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
calc
  a     = b     : h1
    ... < b + 1 : nat.lt_succ_self b
    ... ≤ c + 1 : nat.succ_le_succ h2
    ... < d     : h3
--/

inductive my_nat : Type
| zero : my_nat
| succ : my_nat -> my_nat 

def one : my_nat := my_nat.succ my_nat.zero

def add : my_nat -> my_nat -> my_nat
| m my_nat.zero := m
| m (my_nat.succ n) := my_nat.succ (add m n)

#eval add one one

variables p : Prop
example : ¬ (p ↔ ¬ p) :=
begin
intro h1,
have h2 : p → ¬ p, from h1.mp,
have h3: ¬ p → p, from h1.mpr,
end

example : (p ↔ ¬ p) → false :=
begin
intro h1,
have h2 : p → p → false, from h1.mp,
have h3: (p → false) → p, from h1.mpr,
end