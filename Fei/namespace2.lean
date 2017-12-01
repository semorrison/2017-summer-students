namespace hide

universe u
constant list : Type u → Type u

namespace lis
  constant cons   : Π {α : Type u}, α → list α → list α
  constant nil    : Π {α : Type u}, list α
  constant append : Π {α : Type u}, list α → list α → list α  
  
end lis

open hide.lis
#check hide.lis
#check hide.list
-- A namespace is not an identifier and could not be checked

variable  α : Type
variable  a : α
variables l1 l2 : list α

#check cons a nil
#check append (cons a nil) l1
#check append (append (cons a nil) l1) l2

end hide

-- Alternately, we have to work in our own namespace from the beginning to the end