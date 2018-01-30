/- fails with `unreachable code was reached` -/
def foo : ℕ → false
| x := 
match x with y :=
        let z := y in
        foo z
end

/- can't prove well-founded recursion -/
def bar : ℕ → false
| x := 
match x with y :=
        bar y
end

def baz : ℕ → false
| x := let z := x in baz z
