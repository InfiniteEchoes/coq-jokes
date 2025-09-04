Require Import CoqJokes.CoqJokes.

(* 
- // Goal: What is living
- Living comes with a determined reason
  - without a determined reason there will be existential crisis
- // Soul between life and death as determined reason
- [Theorem]living with a soul is a determined reason and the eventual goal for people to pursue
-        - neither total life nor total death is a permanent goal
-        - permanent life means corpse
-        - permanent death means nothing
- // Death
- [Theorem]death is beautiful
- [Support]death means (an incoming of) relief, and relief is the context of precence time
- [Support]death means (an incoming of) convert
-        - conversion from death is beautiful
-        - conversion from death is common
- // Life
- [Theorem]life is beautiful
- [Support]life means (an incoming of) energy
-        - all penetrative events are energetic
- // Conclusion
- to live is to have soul
- to have soul is to appreciate the beauty
*)
Module Core.
  Definition _with (x : Set)
    (pattern : Set -> Prop) 
    (parameters : Set) : Prop :=
    pattern parameters.

  Parameter Between : Set -> Set -> Set.

  (* TODO: redesign so that living "comes with a reason" *)
  Parameter Living : Set.
  Parameter Life : Set.
  Parameter Death : Set.
  Parameter Soul : Set.
  Parameter Beauty : Set.
  Parameter Confirm : Set.

  (* TODO: resolve this *)
  Definition is_beautiful := _with Beauty _.
  Definition is_living := _with Living.
  Definition is_determined := _with Confirm.

  (* Unsatisfying:
  - the reason is unrelated to the person
  - is_living takes ambiguous parameters
  *)
  Lemma living_comes_with_a_reason : forall (person : Set) (reason : Set),
    is_determined reason -> is_living person.

  Parameter goal : forall (life : Life), exists (reason : Prop), 
    is_determined life reason.

  Parameter death_is_beautiful : forall (death : Death), is_beautiful death.

  Parameter live_is_beautiful : forall (live : Live), is_beautiful live.

End Core.

(* // Beauty
- Beauty is the absolute harmony of confirmation
- absolute harmony means the following component's total confirm:
  - mind
  - instinct
  - mood
  - anything else that I don't know
// TODO: use this 4 components to define `is_beautiful` or `with beauty`
*)