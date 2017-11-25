-- add_sub_cancel is overloaded.
-- _root_ specifies the empty prefix 
#check @add_sub_cancel
#check @nat.add_sub_cancel
#check @_root_.add_sub_cancel

-- "protected def" prevents a name from being shortened.
-- It makes a name unlikely to be overloaded.
namespace foo
protected def bar : ℕ := 1
-- #check bar -- error
#check foo.bar
end foo

-- tricks with "open":

-- open nat (succ add sub)
-- this only aliases nat.succ, nat.add, nat.sub

-- open nat (renaming mul → times) (hiding sub)
-- this gives everything in nat a shortened alias, except nat.sub
--   and aliases nat.mul by times

-- export nat (succ add sub)
-- any time someone opens the current namesapace, these aliases
-- are made. All tricks with "open" apply for "export".



def nat.dvd (m n : ℕ) : Prop := ∃ k, n = m * k
instance : has_dvd nat := ⟨nat.dvd⟩

@[simp] theorem nat.dvd_multiple (n m : ℕ) : n ∣ (n * m) := 
  ⟨m, by simp⟩

@[simp] theorem nat.dvd_refl (n : ℕ) : n ∣ n := 
begin
  have h : n ∣ (n * 1), from nat.dvd_multiple n 1,
  rw (mul_one n) at h, assumption
end

#print axioms
