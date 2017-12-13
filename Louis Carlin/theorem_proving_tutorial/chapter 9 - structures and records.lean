structure point (α : Type) :=
mk :: ( x : α) (y : α)

#print prefix point

open point

example (α : Type) (a b : α) : x (mk a b) = a :=
rfl

structure prody (α : Type) (β : Type) :=
(pr1 : α) (pr2 : β)

-- force α and β to be types from the same universe and return type in same universe
structure {u} proda (α : Type u) (β : Type u) :
    Type (max 1 u) :=
(pr1 : α) (pr2 : β)

set_option pp.universes true
#check proda.mk

example : prod nat nat := ⟨ 1, 2⟩ 

#check { point . x := 10, y := 20}
#check { point . y := 20, x := 10} -- alternative notation so we don't have to care about order

structure my_struct :=
mk :: {α : Type} {β : Type} (a : α) (b : β)

#check {my_struct . a := 10, b := true} -- inference

def p : point nat :=
point.mk 1 2

#reduce {p with y := 3}
#reduce {p with x := 2, y:=3} -- change fields

inductive color
| red | green | blue

structure color_point (α : Type) extends point α :=
mk :: (c : color)

#check color_point.mk


-- Multiple inheritence example
structure point3 (α : Type) :=
(x : α) (y : α) (z : α)

structure rgb_val :=
(red : nat) (green : nat) (blue : nat)

structure red_green_point (α : Type) extends point3 α, rgb_val :=
(no_blue : blue = 0)

def p1 : point3 nat := {x := 10, y := 10, z := 20}
def rgp : red_green_point nat := {p1 with red := 200, green := 40, blue := 0, no_blue := rfl}

