inductive weekday : Type
| sunday : weekday
| monday : weekday
| tuesday : weekday
| wednesday : weekday
| thursday : weekday
| friday : weekday
| saturday : weekday

open weekday

def day_of_number : ℕ → weekday 
| 0 := sunday
| 1 := monday
| 2 := tuesday
| 3 := wednesday
| 4 := thursday
| 5 := friday
| 6 := saturday
| (n + 7) := day_of_number n

lemma day_of_number_modulo_7 (n : ℕ) : day_of_number n = day_of_number (n % 7) :=
begin
  admit,
end