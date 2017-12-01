namespace list
  constant cons   : Π {α : Type u}, α → list α → list α
  constant nil    : Π {α : Type u}, list α
  constant append : Π {α : Type u}, list α → list α → list α
end list

open hide.list

variable  α : Type
variable  a : α
variables l1 l2 : list α

#check cons a nil
#check append (cons a nil) l1
#check append (append (cons a nil) l1) l2