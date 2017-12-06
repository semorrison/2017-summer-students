inductive weekday : Type
| sunday : weekday
| monday : weekday
| tuesday: weekday
| wednesday : weekday
| thursday : weekday
| friday : weekday
| saturday : weekday

#check weekday.monday

def number_of_day (d: weekday) : ℕ :=
weekday.rec_on d 1 2 3 4 5 6 7

#reduce number_of_day weekday.sunday
#reduce weekday.rec_on weekday.sunday

namespace weekday
def next (d : weekday) : weekday :=
weekday.cases_on d monday tuesday wednesday thursday friday saturday sunday

#reduce next tuesday

def previous (d : weekday) : weekday :=
weekday.cases_on d saturday sunday monday tuesday wednesday thursday friday


theorem next_previous (d : weekday)  :
    next (previous d) = d :=
weekday.cases_on d 
    (show next (previous sunday) = sunday, from rfl)
    (show next (previous monday) = monday, from rfl)
    (show next (previous tuesday) = tuesday, from rfl)
    (show next (previous wednesday) = wednesday, from rfl)
    (show next (previous thursday) = thursday, from rfl)
    (show next (previous friday) = friday, from rfl)
    (show next (previous saturday) = saturday, from rfl)

theorem next_previous' (d : weekday) :
    next (previous d) = d :=
weekday.cases_on d rfl rfl rfl rfl rfl rfl rfl 

end weekday

universes u v

namespace products

inductive prod (α : Type u) (β : Type v)
| mk : α → β → prod

inductive sum (α : Type u) (β : Type v)
| inl {} : α → sum
| inr {} : β → sum

def fst {α : Type u} {β : Type v} (p : prod α β) : α :=
prod.rec_on p (λ a b, a)

#reduce fst (prod.mk 1 2)

end products



inductive nats : Type
| zero : nats
| succ : nats→ nats

def add (m n : nats) : nats :=
nats.rec_on n m (λ n add_m_n, nats.succ add_m_n)
-- n is the input (major premise)
-- m is the case for when n is zero
-- (λ n add_m_n, nat.succ add_m_n) is the case for when n is succ l, for some l : nat
-- the last argument defines add m (succ n) to be succ (add m n)


theorem add_succ' (m n : nats) : add m (nats.succ n) = nats.succ (add m  n) := rfl

theorem add_zero' (m : nats) : add m nats.zero = m := rfl 

theorem zero_add' (n : ℕ) : 0 + n = n :=
nat.rec_on n
    (show 0 +0 = 0, from rfl)
    (assume n,
        assume ih : 0 + n = n,
        show 0 + nat.succ n = nat.succ n, from
            calc
                0 + nat.succ n = nat.succ (0 + n) : rfl
                    ... = nat.succ n : by rw ih)

theorem commutativity (m n : nats) : add m n = add n m := sorry

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


#reduce day_of_number (12 % 7)

example (n : ℕ ) : day_of_number n = day_of_number (n % 7) :=
begin
exact weekday.cases_on
end




