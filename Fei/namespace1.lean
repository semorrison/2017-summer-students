namespace hide
universe u
constant list : Type u → Type u

namespace list
  constant cons   : Π α : Type u, α → list α → list α
  constant nil    : Π α : Type u, list α
  constant append : Π α : Type u, list α → list α → list α  
  
end list
end hide

open hide.list

variable  α : Type
variable  a : α
variables l1 l2 : hide.list α  
-- It was of type "list α" in the tutorial
-- And it had a error

#check cons α a (nil α)
#check append α (cons α a (nil α)) l1
#check append α (append α (cons α a (nil α)) l1) l2

#check cons _ a (nil _)
#check append _ (cons _ a (nil _)) l1
#check append _ (append _ (cons _ a (nil _)) l1) l2

-- Question: How to close an open namespace? 
-- (opened with command "open" but not "namespace")
