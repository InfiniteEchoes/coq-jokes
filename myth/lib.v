Require Import CoqJokes.CoqJokes.

(* ******************************** *)
(* General predicates, theorems, tools *)
(* ******************************** *)
Parameter is_extraction : expr -> expr -> Prop.

Definition extraction (origin : expr) (detail : expr) : expr * Prop :=
  (detail, is_extraction origin detail).

Parameter is_context_suggestion : expr -> expr -> Prop.