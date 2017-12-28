-- Inductive Types

-- 1. Enumerated Types

inductive weekday : Type
| sunday : weekday
| monday : weekday
| tuesday : weekday
| wednesday : weekday
| thursday : weekday
| friday : weekday
| saturday : weekday

/-
rec_on associates a number with each day - now we can do maths!
cases_on is similar to rec_on (actually the same for enumerated types!)
-/
def number_of_day (d : weekday) : ℕ :=
weekday.rec_on d 1 2 3 4 5 6 7

#reduce number_of_day weekday.sunday
#reduce number_of_day weekday.monday
#reduce number_of_day weekday.tuesday

namespace weekday
  def next (d : weekday) : weekday :=
  weekday.cases_on d monday tuesday wednesday thursday friday
    saturday sunday

  def previous (d : weekday) : weekday :=
  weekday.cases_on d saturday sunday monday tuesday wednesday
    thursday friday

  #reduce next (next tuesday)
  #reduce next (previous tuesday)

  example : next (previous tuesday) = tuesday := rfl

-- We can concisely prove the above line for any day using the refl tactic
theorem next_previous (d: weekday) :
    next (previous d) = d :=
  by apply weekday.cases_on d; refl

­/-
Note that since propositions are types, we can uses cases_on and rec_on to construct proofs as well as define functions
-/

end weekday

universe u

namespace hide
-- BEGIN
inductive list (α : Type u)
| nil {} : list
| cons : α → list → list

namespace list

variable {α : Type}

notation h :: t  := cons h t

def append (s t : list α) : list α :=
list.rec t (λ x l u, x::u) s

#check @list.rec
#check @list.rec_on

notation s ++ t := append s t

theorem nil_append (t : list α) : nil ++ t = t := rfl

theorem cons_append (x : α) (s t : list α) :
  x::s ++ t = x::(s ++ t) := rfl

-- EXERCISE
theorem append_nil (t : list α) : t ++ nil = t :=
begin
  induction t with x xs Ht,
  refl,

  calc
    (x :: xs) ++ nil = x :: (xs ++ nil)   : by refl
    ...              = x :: xs            : by rw Ht
end

theorem append_assoc (r s t : list α) :
  r ++ s ++ t = r ++ (s ++ t) :=
  begin
  induction r with x xs Hr,
  rw [nil_append, nil_append],

  calc
    x :: xs ++ s ++ t = x :: (xs ++ s ++ t)   : by refl
    ...               = x :: (xs ++ (s ++ t)) : by rw Hr
    ...               = x :: xs ++ (s ++ t)   : by refl
  end

def length : Π {α : Type u}, list α → nat
| _ nil := 0
| _ (x :: xs) := 1 + length xs

theorem append_length (s t : list α) : 
  length (s ++ t) = length s + length t :=
  begin
  induction s with x xs Hs,
  simp only [nil_append, length, zero_add],
  
  simp [cons_append, length, Hs]
  end

end list
-- END
end hide