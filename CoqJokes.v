(* ******************************** *)
(* Project setups, general notes and etc *)
(* ******************************** *)
(* TODO:
- maybe set up a CI on git
- (persistent)think of useful predicates and how to implement them
- (future)make a distinguish between meta and object language
*)

(* NOTE: 
INTRODUCTION.
The biggest difference for informal logic to formal logic is that
informal logic is context based, and everything needs to be given an 
intrepretation manually,so its hard to formalize. This project is 
for entertainment only. 
*)

Require Export Coq.Strings.String.

(* ******************************** *)
(* General predicates, theorems, tools *)
(* ******************************** *)

(* Initial way to analyze the expressions *)
Inductive expr :=
| And : expr -> expr -> expr
| Or : expr -> expr -> expr

(* 
Adjective. Parameter :
- the adjective
- the thing to describe with
*)
| Adj : expr -> expr -> expr

(* Plain text without more meanings. *)
| Plain : string -> expr
.

(* Sentence here is expressions plus the action that someone speaks this expression *)
Inductive sentence : Set :=
(* Someone is asking a question. Parameter : 
- the person that speaks
- the person to speak with
- the content of the sentence *)
| Ask : string -> string -> expr -> sentence

(* Someone is replying. Parameter : 
- the person that speaks
- the person to reply with
- the content of the sentence *)
| Answer : string -> string -> expr -> sentence

(* Another sentence follows after this one. Similar to cons for lists.
  Should I just change into normal cons instead? *)
| Follow : sentence -> sentence -> sentence

(* Someone is just saying something.
- name of the person
- the expression that he says
 *)
| Say : string -> expr -> sentence
.

(* Predicate. A and B confilcts, therefore this story is a joke. *)
Definition is_joke (A : Prop) : A -> ~A -> Prop. Admitted.

(* NOTE that this is not a proposition for now *)
Parameter is : expr -> expr -> expr.

(* A predicate to show someone has said something in the sentence. Parameters:
- the expression to contain
- the whole expression 
Since it's too complicated to actually do the searching, I want to just leave it as a parameter
*)
Parameter contains : expr -> expr -> Prop.

(* ********Unused/wip stuffs******** *)

(* UNUSED.Predicate. For ambiguity on a single word 
- A: the sentence to be interpreted
- B, C: different contexts to interpret the sentence
*)
Definition ambiguity_word : Set. Admitted.

(* UNUSED.Predicate. Example: A under intrepretation A' means a' and A'' means a''. 
They have different meaning resulted into a joke 
parameters:
- original sentence or slice (undefined, not a clue)
- the context to make the interpretation
*)
Definition means (A : Set) : A -> A -> Prop. Admitted.

(* UNUSED.Predicate. Some sentence makes an ambiguity under different interpretation.
Parameter:
- A: the sentence to be interpreted
- B, C: different contexts to interpret the sentence
NOTE: did i define this predicate wrong?
*)
(* Definition ambiguity_meanings (T : Set) (A : T) (B C : T) : 
  is_joke expr (means T A B) (means T A C). Admitted. *)

(* UNUSED.Predicate. Example: "ab" consists of "a" and "b" *)
Parameter consists_of : Set.

(* TODO: theorem: If 
- we have predicate P(A), and
- some sentence contains A
- then we should conclude a more general claim on that sentence from A
*)

(* TODO: These functions are too complicated to implement with... *)
Definition talker_of (d : sentence) : string. Admitted.
Definition expr_of (d : sentence) : expr. Admitted.

(* TODO: think of a mechanic to destruct any words including predicates into list of characters *)

Require import CoqJokes.lib.