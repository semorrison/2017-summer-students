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

-- 5. Other Recursive Data Types