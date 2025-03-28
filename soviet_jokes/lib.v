Require Import CoqJokes.CoqJokes.

(* NOTE:
ARCHITECTURE.
Currently I design the following architecture for each jokes:
Module joke_n.
  (* predicates appeared in the joke *)
  Module Predicates.
  End Predicates.

  (* the whole dialogue in the joke *)
  Module Dialogue.
  End Dialogue.

  Module Assumptions.
  End Assumptions.

  Module Joke_proof.
  End Joke_proof.
End Joke_n.

TODO: add a `Language_extension` module?
*)

(* TODO:
- Can we show that a proof has covered the essence for 
  a full dialogue?
*)

(* ******************************** *)
(* Jokes collected online and to be proved *)
(* ******************************** *)

(* 
https://www.reddit.com/r/AskARussian/comments/n4qj1m/any_good_soviet_jokes/ 
https://www.johndclare.net/Russ12_Jokes.htm
https://en.wikipedia.org/wiki/Russian_political_jokes
*)

Module Joke_1.
  Module Predicates.
    Parameter is_poor : sentence -> Prop.
    Parameter is_answer : expr -> Prop.
    Parameter is_choosing : sentence -> Prop.
    Parameter is_providing_reason : sentence -> Prop.
    (* NOTE: Maybe this predicate can be expanded to contain more informations... *)
    Parameter unexpected_answer : sentence -> Prop.
    Parameter is_normal : string -> Prop.
  End Predicates.

  (* Looks like the easiest joke to fomalize! The joke here is about the poor finance situation for devils
  -- Would you choose a capitalist hell or a communist one?
  -- Of course, communist: they either don't have fuel, don't have enough pots for everyone or all devils are drunk.
  *)
  Module Dialogue.
    Definition d_1 := Ask "A" "B"
      (Or
        (Adj (Plain "capitalist") (Plain "hell"))
        (Adj (Plain "communist") (Plain "hell"))).

    Definition d_2 := 
      (Follow
        (Answer "B" "A" (Adj (Plain "communist") (Plain "hell")))
        (Say "B"
          (is (Adj (Plain "communist") (Plain "hell")) 
              (Or (Plain "don't have fuel")
                (Or (Plain "don't have enough pots for everyone")
                    (Plain "all devils are drunk")))))).
  End Dialogue.

  Module Assumptions.
    (* "don't have fuel, don't have enough pots for everyone or all devils are drunk" means poor *)
    Definition poor_description := 
      (Or (Plain "don't have fuel")
          (Or (Plain "don't have enough pots for everyone")
              (Plain "all devils are drunk"))).

    (* (Ignore computation)Assume that d_2 contains the description above. We ignore the computations *)
    Parameter d_2_contains_poor : contains poor_description (expr_of Dialogue.d_2).

    (* (Ignore computation)Assume that d_2 contains an answer. *)
    Parameter d_2_is_answer : Predicates.is_answer (expr_of Dialogue.d_2).

    (* (Ignore computation)Assume that talker of d_2 is "B". *)
    (* NOTE: %string Required for strings to work properly in propositions... *)
    Parameter b_speaks_d_2 : talker_of Dialogue.d_2 = "B"%string.

    Parameter contains_poor_implies_is_poor : 
      forall (d : sentence), contains poor_description (expr_of Dialogue.d_2) 
        -> Predicates.is_poor d.
    
    (* If there's a "poor" relation for a sentence, that implies the sentence is making a choice *)
    Parameter is_poor_implies_is_choosing : 
      forall (d : sentence), Predicates.is_poor d -> Predicates.is_choosing d.

    (* If a sentence is making a choice between two hells, it's providing a reason for d_1 *)
    Parameter is_choosing_implies_provide_reason :
      forall (d : sentence), Predicates.is_choosing d -> Predicates.is_providing_reason d.

    (* If a sentence is providing a reason and answering d_1, that sentence is a valid answer to d_1 
    NOTE: too complicated to design!... We ignore that it's answering d_1 *)
    Parameter answer_with_choice_is_valid :
      forall (d : sentence), Predicates.is_providing_reason d /\
        Predicates.is_answer (expr_of d) /\
        contains poor_description (expr_of d)
        -> Predicates.unexpected_answer d.

    (* If someone provides a valid answer, that person isn't normal *)
    Parameter valid_choice_is_not_normal :
      forall (d : sentence), Predicates.unexpected_answer d -> ~Predicates.is_normal (talker_of d).
    
    (* Everyone should be normal person *)
    Parameter everyone_is_normal :
      forall (p : string), Predicates.is_normal p.
  End Assumptions.

  (* Presumed steps for the proof:
  1.  [assumption] we assume that the description in sentence 2 means poor for simplicity
  2.  [assumption] we assume that if the poor description is in some sentence, that sentence
                   is making a choice. we want to prove someone is making an unexpected answer. 
  3.  [assumption] we assume that if some sentence is making a choice, that talker of the 
                   sentence is providing a reason
  4.  [assumption] if someone is providing a reason to that question, and that reason contains
                   the poor description, he is making an unexpected answer
  5.  [sentence 2, 1] 2nd sentence contains poor description
  6.  [5, 2] 2nd sentence is making a choice
  7.  [6, 3] 2nd sentence is providing a reason
  8.  [sentence 2, 4, 7] 2nd sentence is making an unexpected answer
  9.  [assumption] if someone is making an unexpected answer, he isn't normal
  10. [assumption] everyone should be normal
  11. [9, 8] the person that spoke the 2nd sentence isn't normal
  12. [10, 11] someone isn't normal, hence the joke

  Critics: I think setting up the "normal" person contradiction is too far(assuming that the joke is 
           caused by mad person). Stopping at "unexpected answer"(assume that the joke is caused by 
           unexpected behaviour) should be just enough, but I'm too lazy to change. 
           Assuming on "abnormal person" gets the advantage that we can easily attribute the contradiction
           to some person. For unexpected behavior we will attribute the contradiction to a sentence 
           maybe. 
           Actually on second thoughts, I think "what should be the benchmark for a joke?" should be
           the soul of the whole formalizarion: can we actually find a universal benchmark such that
           any jokes could be safely attributed to such claim. Only this will make the framework for 
           proving joke actually complete. *)
  Module Joke_proof.
    (* Prove that B isn't normal. *)
    Theorem b_is_not_normal : ~Predicates.is_normal "B".
    Proof.
      unfold not.
      pose proof (Assumptions.valid_choice_is_not_normal Dialogue.d_2) 
        as valid_choice_is_not_normal.
      pose proof Assumptions.b_speaks_d_2 as b_speaks_d_2.
      rewrite -> b_speaks_d_2 in valid_choice_is_not_normal.
      apply valid_choice_is_not_normal.
      apply Assumptions.answer_with_choice_is_valid.
      split.
      - apply Assumptions.is_choosing_implies_provide_reason.
        apply Assumptions.is_poor_implies_is_choosing.
        apply Assumptions.contains_poor_implies_is_poor.
        apply Assumptions.d_2_contains_poor.
      - split.
        + apply Assumptions.d_2_is_answer.
        + apply Assumptions.d_2_contains_poor.
    Qed.

    (* Generalize to prove that someone isn't normal. *)
    Theorem someone_is_not_normal :
      exists (p : string), ~Predicates.is_normal p. 
    Proof.
      unfold not.
      exists "B"%string.
      apply b_is_not_normal.
    Qed.
    
    (* Mad Mr.B makes the whole dialogue a soviet joke. *)
    Theorem abnormal_person_is_a_joke :
      exists (A : Prop) (a : A) (neg_a : ~A), is_joke A a neg_a.
    Proof.
      exists (forall (p : string), Predicates.is_normal p),
            Assumptions.everyone_is_normal.
      assert ((exists (p : string), ~Predicates.is_normal p)
            -> ~forall (p : string), Predicates.is_normal p). { 
        unfold not. intros.
        destruct H. unfold not in H.
        specialize (H0 x).
        specialize (H H0). 
        exact H.
      }
      specialize (H someone_is_not_normal).
      exists H.
      destruct H.
      exact Assumptions.everyone_is_normal.
    Qed.
  End Joke_proof.
End Joke_1.

Module Joke_2.
  Module Predicates.
    Inductive Event : Set :=
      | C : expr -> Event
      .
    (* Parameters:
    - the person being sentenced
    - the behavior
    *)
    Parameter summarize : sentence -> sentence -> sentence.
    Parameter is_sentenced : string -> expr -> Prop.
    Parameter is_forbidden : expr -> Prop.
    Parameter is_telling_joke : string -> Prop.
    Parameter is_joke : Event -> Prop.
    Parameter is_expected : Event -> Prop.
  End Predicates.

  (* 
  Two judges meet in a court and one is laughing hysterically.
  The other: what's so funny?
  The first one: i've just heard the most ridiculous anecdote of my life.
  The other: Care to share?
  The first: Can't, just gave a guy 15 years for it.
  *)
  Module Dialogue.
    Definition d_1 := Ask "B" "A" (Plain "funny").

    Definition d_2 := Answer "A" "B" 
      (Plain "heard the most ridiculous anecdote of my life").

    Definition d_3 := Ask "B" "A" (Plain "share").

    Definition d_4 := Follow 
      (Answer "A" "B" (Plain "No"))
      (Say "A" (Plain "just gave a guy 15 years for it")).
  End Dialogue.

  Module Assumptions.
    Import Predicates.
    (* TODO:
    - write an assumption that d2 & d4 summarizes into full meaning
    - clarify that some sentence contains the description
    - clarify `is_joke` parts since it's been never used
    *)
    Definition behavior_description := Plain "anecdote".

    Parameter summarize_sentence : summarize d_2 d_4 = 
      Say "A" (Plain "gave a guy 15 years for the most ridiculous anecdote of my life").

    Parameter analyze_meaning : forall (d : sentence), 
      contains "a guy" (expr_of d) /\ contains behavior_description (expr_of d) 
      -> is_sentenced "a guy" description. (* TODO: clarify on is_joke part *)

    (* If someont sentenced a person for a behavior, that behavior is forbidden by law *)
    Parameter sentenced_means_law_forbids : forall (person : string) (description : expr),
      is_sentenced person description -> is_forbidden description.

    (* If law forbids something, that something is expected *)
    Parameter law_forbids_means_exists : forall (description : expr), 
      is_forbidden description -> is_expected (Event.C description).

    (* If an event is a joke, that event is unexpected *)
    Parameter joke_event_is_unexpected : forall (e : Event), is_joke e -> ~ is_expected e.

    (* If an event is being sentenced, that event is expected *)
    Parameter sentenced_event_is_expected : forall (e : Event), is_forbedden e -> is_expected e.
  End Assumptions.

  (* NOTE: 
  Draft of the proof(unexpected event):
  1. [sentence 2] anon is telling a joke
  2. [sentence 4] anon has been sentenced 15 yrs
  3. [summarize 1, 2] anon is sentenced heavily because of telling a joke
  4. [assumption] if an event is a joke, that event is unexpected
  5. [1, 4] the content of joke is unexpected (TODO: expand further from joke to event)
  6. [assumption] if an event is forbidden, that event is expected 
  7. [2, 6] the content of the joke is expected
  8. [6, 7] there exists an expected event that is unexpected, henced the joke
  *)
  Module Joke_proof.
    (* TODO: from joke's def, such event is unexpected *)
    Theorem joke_event_not_exist : Prop. Admitted.

    (* TODO: from law's def, such event has already been expected *)
    Theorem forbidden_even_exist : Prop. Admitted.

    (* TODO:  *)
    Theorem unexpected_event_is_a_joke :
      exists (A : Prop) (a : A) (neg_a : ~A), is_joke A a neg_a.
    Admitted.


  End Joke_proof.
End Joke_2.

(* 
In the museum of Vasily Chapayev the guide shows the visitors a skeleton:
"And here you can see the skeleton of Vasily Chapayev."
"And what is this small skeleton next to him?"
"That's Vasily Chapayev in his childhood."
Draft for the proof(abnormal identity):
- one person could have only one skeleton
- for exhibition and bluffing purpose, Vasily got 2x in the museum
- Museum has done wrong on Vasily
- Museum being abnormal, hence the joke
*)
Module Joke_3.
  Module Predicates.
  End Predicates.

  Module Dialogue.
  End Dialogue.

  Module Assumptions.
  End Assumptions.

  Module Joke_proof.
  End Joke_proof.
End Joke_3.

(* NOTE: Now I like this joke. If you want to reason about the joke you have 
  to dig in for a lot and prove then all
Two soldiers on the North Pole:
- wanna hear a political joke?
- not really, afraid they’ll send me to some shithole then.
Draft for proof(abnormal identity):
- if someone shares about a political joke, both of the people will be discovered
  (as a simulation of "might be punished")
- if someone has been discovered, he will be punished
- if someone punished, he will be "sent to some shithole"
- "send to some shithole" means "send to syberia"
- if a situation is harder than the other situation, we call the situation "a punishment" 
  (or use "bad situation" for more refined reasoning?)
- everyone is currently in north pole
- [Assumption]north pole is the worst place in the world
- [Assumption]there could be no punishment outside north pole
- syberia is worse than north pole. "there are worse case than the worst"
- syberia being worse than north pole reflects a Russia being worse than any people normally expect
- "russia is worse than people that would nomally expect", hence the joke
*)

(* 
Andropov then head of KGB comes to see dying Brezhnev.
Brezhnev asks: Who do you think will be after me?
Andropov: I think, I will be.
B: But will the people follow you?
A: If they won't, they'll follow you!
NOTE: the difficulty here is to state what the 2nd sentence from Andropov claims
*)

(* 
Russian and American go to hell. Satan approaches them, says:
– Choose which hell you go to. There is Russian hell and American hell.
– What is the difference? Both ask.
– In American hell, you need to eat a bucket of shit once a day, and in Russian – 2 buckets of shit, – Satan answers.
– Why do I have another bucket of shit? – says the American, chooses the American hell.
– Well, I lived in Russia, into the Russian hell and I will go, what is it, – says the Russian, chooses the Russian hell.
They meet somehow after a while. Russian asks an American: 
– Well, how are you in hell? 
– Yes, good. I ate one bucket and walk all day. And you? 
– Yes, as usual: there are not enough buckets for all, then they will bring little shit.
NOTE: More complicated implications than the 1st joke...
*)
