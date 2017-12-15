/- 2.3 -- Function Abstraction and Evaluation -/

constants α β : Type
constants a1 a2 : α
constants b1 b2 : β

#check λ x y: ℕ, x + y -- addition

#reduce (λ x : α, x) a1 -- #reduce performs beta reduction

constants m n : nat
constant b : bool

#print "reducing pairs"
#reduce (m, n).1 -- m

#reduce tt && ff -- ff
#reduce tt || ff -- tt

#eval 12345 * 54321


/- 2.4 -- Introducing Definitions -/

def foo : (ℕ → ℕ) → ℕ := λ f, f 0 -- function application at 0
#reduce foo (λ x : ℕ, x+1) -- 1
def foo' (f : ℕ → ℕ) : ℕ := f 0 -- equivalent

def curry (α β γ : Type) (f : α × β → γ) : α → β → γ := λ (a: α) (b: β), f (a,b)
def uncurry (α β γ : Type) (f : α → β → γ) : α × β → γ := λ ab: α × β, f ab.1 ab.2

/- 2.5 -- Local Definitions -/

namespace hide

#reduce let y := 2 + 2 in y * y --16

def t (x :  ℕ) : ℕ :=
let y := x + x in y * y
#reduce t 2 -- 16

#reduce let y := 2 + 2, z:= y+y in z * z -- note: order matters

def foo := let a := ℕ in λ x : a, x+2 -- order matters?
--def bar := (λ a : Type, λ x : a, x+2) ℕ

end hide

/- 2.6 -- Variables and Sections -/

variables (α β γ : Type)

def compose (g : β → γ) (f: α → β) (x: α) : γ := g (f x)
def do_twice (h : α → α) (x : α) : α := h (h x)

variables n m: ℕ
#check n

-- section limits the scope of variables
section useful
  variables (α' β' γ' : Type)
  variables (g : β' → γ') (f : α' → β') (h : α' → α')
  variable x : α'

  def compose' := g (f x)
  def do_twice' := h (h x)
end useful

/- 2.7 -- Namespaces -/

namespace foo
  def a : ℕ := 5
  def f (x : ℕ) : ℕ := x + 7

  def fa : ℕ := f a
  def ffa : ℕ := f (f a)

  #print "inside foo"

  #check a
  #check f
  #check fa
  #check ffa
  #check foo.fa
 end foo

#print "outside the namespace"
--#check a -- error
#check foo.a

open foo
#print "opened foo"
#check a

open list
#check nil
#check cons
#check append

-- namespaces can be nested

/- 2.8 -- Dependent Types -/
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

/- 2.9 -- Implicit Arguments -/
-- TODO (probably not)

