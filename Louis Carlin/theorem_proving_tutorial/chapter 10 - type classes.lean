-- any family of types can be marked as a type class
-- then we can declare particular elements of a type class (ie a type) to be instances

-- three steps :
-- 1) Declare family of inductive types to be a type class
-- 2) Declare instances
-- 3) mark implicit arguments with square brackets to inform that they should be infered

attribute [class] nat

instance nat_one : ℕ := 1 -- we are essentially declaring 1 to be a canonical instance of ℕ
/- The command instance is sugar for
def nat_one : ℕ :=1
attribute [instance, reducible] nat_one
-/

def foo [x : ℕ] : nat := x

#check @foo
#reduce foo

example : foo = 1 := rfl

instance nat_two : ℕ := 2

#reduce foo -- this is weird

example : foo ≠ 1 :=
λ h : 2 = 1, nat.no_confusion h (λ h : 1 = 0, nat.no_confusion h)
-- elaborator prefers most recent instance by default


namespace hide

class inhabited (α : Type) :=
(value : α)
/- Sugar for
@[class] structure inhabited (α : Type) :=
(value : α)
-/

instance Prop_inhabited : inhabited Prop := inhabited.mk true
-- instance Prop_inhabited : inhabited Prop := ⟨ true ⟩ -- doesn't like this?

instance bool_inhabited : inhabited bool := inhabited.mk tt

instance nat_inhabited : inhabited nat := inhabited.mk 0

instance unit_inhabited : inhabited unit := inhabited.mk ()

definition default (α : Type) [s : inhabited α] : α := @inhabited.value α s

#check default Prop -- Prop
#reduce default Prop -- true
-- arbitrary does the same thing but is marked as irreducible

-- Chaining!
instance prod_inhabited {α β : Type} [inhabited α] [inhabited β] 
    : inhabited (prod α β) 
:= ⟨(default α, default β)⟩ 

#reduce default (nat × bool)

instance inhabited_fun (α : Type) {β : Type} [inhabited β] :
    inhabited (α → β) :=
⟨ (λ a : α, default β) ⟩ 

end hide

#reduce arbitrary ℕ 

/- 10.3 -- Decidable Propositions -/
 namespace hide

class inductive decidable (p : Prop) : Type
| is_false : ¬ p → decidable
| is_true : p → decidable

def ite (c : Prop) [d : decidable c] {α : Type} (t e : α)
    : α :=
decidable.rec_on d (λ hnc, e) (λ hc, t)
-- if c then e else t
-- d is an instance of 'decidable c' which is inferred

def dite (c : Prop) [d : decidable c] {α : Type}
    (t : c → α) (e : ¬ c → α) : α :=
decidable.rec_on d (λ hnc : ¬ c, e hnc) (λ hc : c, t hc)
-- we can assume hc : c in the then branch and hnc : ¬ c in the if branch

end hide

#check and.decidable
#check @and.decidable

open nat

def step (a b x : ℕ) : ℕ :=
if x < a ∨ x > b then 0 else 1

#print definition step
set_option pp.implicit true
#print definition step

def as_true' (c : Prop) [decidable c] : Prop :=
if c then true else false
-- tries to infer a decision procedure for c and if successful evaluates to true or false

def of_as_true' {c : Prop} [h₁ : decidable c] (h₂ : as_true c) :
    c :=
match h₁, h₂ with
| (is_true h_c), h₂ := h_c
| (is_false h_c), h₂ := false.elim h₂
end
-- assuming (as_true c) holds produce a proof of c

notation `dec_trivial'` := of_as_true (by tactic.triv)
-- applies of_as_true then tries to prove (as_true c) with the triv tactic

example : 1 ≠ 0 ∧ (5 < 2 ∨ 3 < 7) := dec_trivial

/- 10.4 -- Overloading with Type Classes -/

universes u

class has_add' (α : Type u) :=
(add : α → α → α)

def add {α : Type u} [has_add' α ] : α → α → α := has_add'.add

local notation a `+` b := add a b

instance nat_has_add' : has_add' nat :=
⟨nat.add⟩ 

instance bool_has_add : has_add' bool :=
⟨bor⟩ 

#check 2 + 2
#check tt + ff

instance prod_has_add' {α : Type u} {β : Type u}
    [has_add' α] [has_add' β] :
    has_add' (α × β) :=
⟨ λ ⟨ a1, b1⟩ ⟨a2, b2⟩, ⟨a1+a2, b1+b2⟩⟩

instance fun_has_add' {α : Type u} {β : Type u} [has_add' β] :
    has_add' (α → β) :=
    ⟨ λ f g, λ x, (f x) + (g x)⟩ 

/- 10.5 -- Managing Type Class Inference -/

#print classes
#print instances inhabited

set_option trace.class_instances true
set_option class.instance_max_depth 32

@[priority std.priority.default+1]
instance i1 : prod nat nat :=
⟨ 1, 1 ⟩

/- 10.6 -- Coercions using Type Classes -/


