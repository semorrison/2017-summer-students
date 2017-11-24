#reduce let y := 2 + 2 in y * y --16

def t (x :  ℕ) : ℕ :=
let y := x + x in y * y
#reduce t 2 -- 16

#reduce let y := 2 + 2, z:= y+y in z * z -- note: order matters

def foo := let a := ℕ in λ x : a, x+2 -- order matters?
--def bar := (λ a : Type, λ x : a, x+2) ℕ
