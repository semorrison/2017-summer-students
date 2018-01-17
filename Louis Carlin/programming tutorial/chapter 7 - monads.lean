/- 7 - Monads


A monad is a type constructor "m : Type → Type" that comes equipped with two special 
operations: return and bind.
Think of m α as an α inside a box.

return : Π {α : Type}, α → m α    "puts a : α inside the box"

bind : Π {α β : Type}, m α → (α → m β ) → m β

eg we could define map f : m α → m β by
map f ma := bind ma (λ a, return (f a))


"ma >>= f" is sugar for "bind ma f" -- do ma, take the result and send it to f

"ma >> mb" is sugar for "bind ma (λ a, mb)" (ie it ignores whatever's in the box) -- do ma, do mb

"do a ← ma, t" is sugar for "ma >>= (λ a, t)"-/


/- 7.1 - The option monad -/
namespace one

def bind {α β : Type} (oa : option α) (f : α → option β) :
    option β :=
match oa with
| (some a) := f a
| none := none
end

universe u
variables {α β γ δ : Type.{u}} (oa : option α )
variables (f : α → option β ) (g : α → β → option γ) 
                 (h : α → β → γ → option δ)

example : option β :=
do a ← oa,
     b ← f a,
     return b

example : option δ :=
do a ← oa,
    b ← f a,
    c ← g a b,
    h a b c

end one

/- 7.2 - The list monad -/
namespace two

def bind {α β : Type} (la : list α ) (f : α → list β ) : list β :=
list.join (list.map f la)

universe u
variables {α β γ δ : Type.{u}} (la : list α )
variables (f : α → list β ) (g : α → β → list γ) 
                 (h : α → β → γ → list δ)


example : list δ :=
do a ← la,
    b ← f a,
    c ← g a b,
    h a b c

end two

/- 7.3 0 The state monad 

m α = registers → α × registers

Lean defines the state monad "state S" (for every type S) to be the monad that maps any type α to "S → α × S"

return a = λ s, (a, s)

sa : state S α
f : α → state S β 
bind sa f = λ s, match (sa s) with (a, s₀) := f a s₀
-/

def read {S : Type} : state S S :=
λ s, (s,s)

def write {S : Type} : S → state S unit :=
λ s₀ s, ((), s₀)

structure registers : Type := (x y z : ℕ)

def init_reg : registers := registers.mk 0 0 0

@[reducible] def reg_state := state registers

def read_x : reg_state ℕ :=
do s ← read, return (registers.x s)

def read_y : reg_state ℕ :=
do s ← read, return (registers.y s)

def read_z : reg_state ℕ :=
do s ← read, return (registers.z s)


def write_x (n : ℕ) : reg_state unit :=
do s ← read,
    write (registers.mk n (registers.y s) (registers.z s))

def write_y (n : ℕ) : reg_state unit :=
do s ← read,
    write (registers.mk (registers.x s)  n (registers.z s))

def write_z (n : ℕ) : reg_state unit :=
do s ← read,
    write (registers.mk (registers.x s) (registers.y s) n)

open nat

def foo : reg_state ℕ :=
do write_x 5,
    write_y 7,
    x ← read_x,
    write_z (x + 3),
    y ← read_y,
    z ← read_z,
    write_y (y + z),
    y ← read_y,
    return (y + 2)  

#reduce foo init_reg