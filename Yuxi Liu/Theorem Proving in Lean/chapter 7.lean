inductive weekday : Type
| sunday : weekday
| monday : weekday
| tuesday : weekday
| wednesday : weekday
| thursday : weekday
| friday : weekday
| saturday : weekday
#check @weekday.rec
#check @weekday.rec_on 
-- rec, but with the "weekday" argument in the front.
#check @weekday.cases_on 
-- more restricted form of rec_on, but the same for enum types.

namespace weekday
  @[reducible]
  private def cases_on := @weekday.cases_on

  def number_of_day (d : weekday) : nat :=
  cases_on d 1 2 3 4 5 6 7

  def day_of_number : ℕ → weekday 
  | 0 := sunday
  | 1 := monday
  | 2 := tuesday
  | 3 := wednesday
  | 4 := thursday
  | 5 := friday
  | 6 := saturday
  | (n + 7) := day_of_number n
  -- should be n := day_of_number (n % 7) , but it doesn't compile.

  def next (d : weekday) : weekday :=
  weekday.cases_on d monday tuesday wednesday thursday friday
    saturday sunday

  def previous (d : weekday) : weekday :=
  weekday.cases_on d saturday sunday monday tuesday wednesday
    thursday friday

  theorem next_previous_weekday : 
    ∀ (d : weekday), next (previous d) = d := 
  by {intro d, cases d; refl}

  theorem previous_next_weekday (d : weekday) : 
    previous (next d) = d := 
  by apply weekday.rec_on d; refl

  example : next (previous tuesday) = tuesday := 
    next_previous_weekday tuesday
end weekday

namespace hide
inductive empty : Prop
-- empty has no constructors, so it cannot be introduced
-- it can be eliminated in anyway, vacuously.
theorem empty_is_false : empty ↔ false := 
  by constructor; { intro a, cases a }
-- if we have empty : Type u, then we still have empty → false

inductive unit : Prop
| star : unit
-- unit is an enum type with exactly one possible constructor, 
-- so it can be introduced, but only in exactly one way.
-- and it can be eliminated also in exactly one way.
-- it's equivalent to true.
theorem unit_is_true : unit ↔ true :=
begin 
  constructor,
  intro, trivial,
  intro, apply unit.star
end

inductive bool : Type
| ff : bool
| tt : bool

def bool_and : bool → bool → bool
| bool.ff := λ _, bool.ff
| bool.tt := id

def bool_or : bool → bool → bool
| bool.tt := λ _, bool.tt
| bool.ff := id

universes u v w

inductive my_prod (α : Type u) (β : Type v)
| mk : α → β → my_prod

#check @hide.my_prod.rec_on
def fst {α : Type u} {β : Type v} (p : my_prod α β) : α :=
  my_prod.rec_on p (λ a b, a)

def snd {α : Type u} {β : Type v} (p : my_prod α β) : β :=
  my_prod.rec_on p (λ a b, b)

-- "structure" keyword can define such record-like inductive types.
structure record_prod (α β : Type) :=
mk :: (fst : α) (snd : β)

def prod_example (p : _root_.bool × ℕ) : ℕ :=
prod.rec_on p (λ b n, cond b (2 * n) (2 * n + 1))
-- cond is similar to bool.rec_on
#check @cond


inductive sum (α : Type u) (β : Type v)
| inl {} : α → sum
| inr {} : β → sum

#check list.append_assoc
#check semigroup.mk list.append list.append_assoc

-- In dependent type theory, all functions are total.
-- to model partial functions, use these:
inductive option (α : Type u)
| none {} : option
| some    : α → option
-- a function of type α → option β is like 
-- a partial function of type α → β 

def partial_composition {α : Type u} {β : Type v} {γ : Type w}: 
  (α → option β) → (β → option γ) → (α → option γ) := 
begin
  intros f g,
  assume a,
  have opt_b : option β, by apply f a,
  cases opt_b with b _,
    apply option.none,
    apply g b
end

inductive inhabited (α : Type u)
| mk : α → inhabited

theorem nat_inhabited : inhabited ℕ := ⟨0⟩
theorem bool_inhabited : inhabited bool := ⟨bool.tt⟩
theorem prod_inhabited {α : Type u} {β : Type v} : 
  inhabited α → inhabited β → inhabited (α × β) :=
begin 
  intros ina inb,
  cases ina with a,
  cases inb with b,
  have ab : α × β,
  constructor, assumption, assumption, constructor, assumption
end
#check @prod_inhabited

/- The following doesn't work, because ∨ has type Prop → Prop → Prop, 
and inhabited lives in a possibly higher universe. But if it would work, 
its proof would be very similar to the previous one.
theorem sum_inhabited {α : Type u} {β : Type v} : 
  (inhabited α ∨ inhabited β) → inhabited (α ⊕ β)
-/
end hide

