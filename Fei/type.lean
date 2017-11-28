constant α : Type
#check α                -- Type
#check prod α α         -- Type

universe u
constant β : Type u  
/-
universe u_1
constant β : Type u_1 
-/ -- gives the same thing

#check β                -- Type u_1
#check prod β           -- Type u_2 → Type (max u_1 u_2)
#check prod β β         -- Type (max u_1 u_2)

-- Where does the Type u_2 come from?