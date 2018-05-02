import data.set.basic


open function
open set

lemma surj_image_preimage {α β} (f : α → β) (s : set β) (w : surjective f) : f '' (f ⁻¹' s) = s := 
begin
  apply subset.antisymm,
  {
     exact image_preimage_subset f s,
  },
  { 
     intros b v,
     have q := w b, 
     have s : 1 = 2, 
     finish,
  }
end 
