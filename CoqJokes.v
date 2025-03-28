(* ******************************** *)
(* Project setups, General notes, Etc *)
(* ******************************** *)
(* NOTE: 
INTRODUCTION.
The biggest difference for informal logic to formal logic is that
informal logic is context based. Everything needs to be given 
an intrepretation manually, which attributes to the difficulty to
prove informal logic.

Despite the work in writing the proofs, the actual work for formalizing
jokes is setting up a framework so that any jokes can be reasoned 
by this framework. What propositions can be identified as proving 
that this story is a joke? That is something totally written in your 
hypothesises, not in your deductions. TL;DR: we're developing a 
framework, not refining the steps of proofs.

If we assume the proof goal is true, we can already trivially prove 
that that goal is true. In contrast, I believe the most rigorous 
proof comes from the procedure of refining the assumptions, so that
they are becoming weaker and weaker.

Given the ambiguity of jokes, and the absence for so many contexts 
that should appear in jokes, syntactic considerations for English, 
and etc., this project is a personal attempt mostly for entertainment.

MID TERM TASKS.
1. Set up a CI on git
2. Set up a module of predicates, substitute all `is_xx` predicates 
   to `Is "xx" _` predicate

LONG TERM TASKS.
1. More refined proofs. Don't just rely on plain texts
2. More useful predicates
3. Distinguish between meta and object language
4. Refactor completed proofs whenever architecture update happens
*)

Require Export Coq.Strings.String.

(* ******************************** *)
(* Predicates, Theorems, Tools *)
(* ******************************** *)

(* Initial way to analyze the expressions *)
Inductive expr :=
| And : expr -> expr -> expr
| Or : expr -> expr -> expr
| Is : expr -> expr -> expr

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

(* Of course we could have narratives.
- just the expression that he says
*)
| Narrate : expr -> sentence
.

(* WIP: A module providing common tools to prove a joke, along with tools to 
  identify them 
  NOTE: This seems redundant, but it is raised from the proofs I have written 
  and seems to be necessary. Sometimes we just have to conclude on one specific 
  reason that looks pretty far from the dialogues.
  We mostly identify a joke by saying that there exists A and B being conflict.
*)
Module Joke.
  Module Default.
    Definition is_joke (A : Prop) : A -> ~A -> Prop. Admitted.
  End Default.
  (* 
  NOTE: how can we ensure that `joke` function should be a method under `T`?
  Class Joke (A : Prop) (T : Type) {
    joke : A -> ~A -> Prop;
  }.
  *)
  (* Jokes from unexpected events: uncommon behaviors happened *)
  Module UnexpectedEvent.
    Module Predicates.
      Inductive Event :=
      | MkEvent : expr -> Event
      .

      Parameter is_event : Prop.
      Parameter is_expected : Prop.
    End Predicates.

    Module Assumptions.
    End Assumptions.

    Module JokeProof.
      (* TODO: is_expected -> is_unexpected -> Prop *)
      Parameter event_is_joke : Prop.
    End JokeProof.
  End UnexpectedEvent.

  (* Jokes from abnormal identity: abnormal person, abnormal places or things, etc. *)
  Module AbnormalId.
  End AbnormalId.

  (* Jokes from significant logical errors for a sentence *)
  Module LogicalError.
  End LogicalError.
End Joke.

(* Predicate. Show someone has said something in the sentence. Parameters:
- the expression to contain
- the whole expression 
Since it's too complicated to actually do the searching, I want to just leave it as a parameter
*)
Parameter contains : expr -> expr -> Prop.

(* ******************************** *)
(* Unused, Unstable, WIP *)
(* ******************************** *)

(* TODO(important): 
- Define a predicate `reflect` to lift a type of joke to 
  another type of joke. Reflection is such a special sauce in showing the beauty
  of the jokes. 
- Clarify the relation between joke goals and the reflection operation.*)

(* UNUSED. Predicate. For ambiguity on a single word 
- A: the sentence to be interpreted
- B, C: different contexts to interpret the sentence
*)
Definition ambiguity_word : Set. Admitted.

(* UNUSED. Predicate. Example: A under intrepretation A' means a' and A'' means a''. 
They have different meaning resulted into a joke 
parameters:
- original sentence or slice (undefined, not a clue)
- the context to make the interpretation
*)
Definition means (A : Set) : A -> A -> Prop. Admitted.

(* UNUSED. Predicate. Some sentence makes an ambiguity under different interpretation.
Parameter:
- A: the sentence to be interpreted
- B, C: different contexts to interpret the sentence
NOTE: did i define this predicate wrong?
*)
(* Definition ambiguity_meanings (T : Set) (A : T) (B C : T) : 
  is_joke expr (means T A B) (means T A C). Admitted. *)

(* UNUSED. Predicate. Example: "ab" consists of "a" and "b" *)
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