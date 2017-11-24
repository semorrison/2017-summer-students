namespace hide

universe u

constant list : Type u → Type u

constant cons : Π α : Type u, α → list α → list α
constant nil : Π α : Type u, list α

#check cons

end hide

-- Π x : α, β x
-- for a function f of this type we have that
-- for each x ∈ α we have (f a) ∈ β x

def ident {α : Type u} (x : α) := x
#check ident
#reduce ident 4
#reduce ident ident
