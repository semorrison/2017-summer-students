inductive weekday : Type
| sunday : weekday
| monday : weekday
| tuesday: weekday
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

-- WTS : n % 7 is one of 0,1,2,3,4,5,6

example  (n : ℕ) : (n % 7) = 0 ∨ (n % 7) = 1 ∨ (n % 7) = 2 ∨ (n % 7) = 3 ∨ (n % 7) = 4 ∨ (n % 7) = 5 ∨ (n % 7) = 6 :=


example (n : ℕ ) : day_of_number n = day_of_number (n % 7)
| 0 



#check quot
#check quot 