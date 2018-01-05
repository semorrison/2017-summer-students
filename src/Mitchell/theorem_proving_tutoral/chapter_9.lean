structure point (α : Type) :=
mk :: ( x : α) (y : α)

#print prefix point

def p : point nat :=
{x := 1, y := 2}

#reduce {p with y := 3}
#reduce {p with x := 3}