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
