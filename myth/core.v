Require Import CoqJokes.CoqJokes.

(* 
- // Goal
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
  Inductive Item :=
  | Living
  | Life
  | Death
  | Soul
  | Between : Item -> Item -> Item
  .


  Parameter is_beautiful : Type -> Prop.

  (* unsatisfyiing *)
  Parameter is_determined : Set -> Prop.

  Parameter Goal : forall (life : Life), exists (reason : Prop), is_determined life reason.

  Parameter death_is_beautiful : forall (death : Death), is_beautiful death.

  Parameter live_is_beautiful : forall (live : Live), is_beautiful live.

End Core.