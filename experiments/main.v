(* TODO:
Express that true and false are relative rather than absolute
Define a new set of primitives to express the idea
- True means we have a unique explanation and it doesn't have a conflict 
- False means we have more than one explanation concluded, that are 
  contradicted to each others

takes of guess(?): 
- should we change how the arrow works by letting it a partial order?

p is true := p (as in constructive logic?)
p is false := exists p', forall q, (q -> p) -> (q -> p'). 
how to express further that p and p' are not equal?

primitives to set up:
- `distinct` or `conclude` operator
- partial order arrow
- 

*)