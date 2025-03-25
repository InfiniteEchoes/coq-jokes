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
*)

(* 
TODO: create modules to set up some common goals to prove:
- jokes from uncommon behaviors
- jokes from abnormal person
- jokes from significant logical errors for a sentence
*)

(* TODO(progress):
- either make a nasty stub or finish the string related axiom
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
    (* Maybe this predicate can be expanded to contain more informations... *)
    Parameter unexpected_answer : sentence -> Prop.
    Parameter is_normal : string -> Prop.
  End Predicates.

  Module Dialogue.
    (* NOTE: This looks like the easiest joke to fomalize! The joke here is about the poor finance situation for devils
    -- Would you choose a capitalist hell or a communist one?
    -- Of course, communist: they either don't have fuel, don't have enough pots for everyone or all devils are drunk.
    *)
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

    (* (Ignore computation)Assume that talker of d_2 is "B".
    Lemma b_speaks_d_2 : talker_of Dialogue.d_2 = "B". *)

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
    Parameter valid_choice_is_nor_normal :
      forall (d : sentence), Predicates.unexpected_answer d -> ~Predicates.is_normal (talker_of d).
    
    (* Everyone should be normal person *)
    Parameter everyone_is_normal :
      forall (p : string), Predicates.is_normal p.
  End Assumptions.

  (* Presumed steps for the whole proof:
  1.  [assumption] we first assume that the description in sentence 2 means poor for simplicity
  2.  [assumption] we want to prove someone is making an unexpected answer. we assume
                   that if the poor description is in some sentence, that sentence is 
                   making a choice
  3.  [assumption] we assume that the behavior of making choice implies providing a reason
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

  Compute (Assumptions.valid_choice_is_nor_normal Dialogue.d_2).

    (* TODO: fix this *)
    (* Theorem b_is_not_normal : ~Predicates.is_normal "B".
    Proof.
      unfold not.
      pose proof Assumptions.valid_choice_is_nor_normal. *)


    (* TODO: prove that someone isn't normal *)
    (* NOTE: clarifying the relation between `talker_of p` and the sentence d is too tedious for me right now
       If I occur to proving such relation I'll just go brutal *)
    Theorem someone_is_not_normal :
      exists (p : string), ~Predicates.is_normal p. 
    Proof.
      unfold not.
      (* exists "B". *)
    Admitted.
    
    (* The whole dialogue is a soviet joke *)
    Theorem there_is_a_joke :
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

(* 
Two judges meet in a court and one is laughing hysterically.
The other: what's so funny?
The first one: i've just heard the most ridiculous anecdote of my life.
The other: Care to share?
The first: Can't, just gave a guy 15 years for it.
General idea:
- [assumption]if judge sent someone to jail for a reason, the reason with 
  the punishment constitutes to a rule
- Judge has made a rule that if someone tells a joke, he will be sent to prison
- If judge tells a joke, he will be sent to prison
- Judge cannot tell the joke
*)
Module Joke_2.
  Module Predicates.
  End Predicates.

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
    (* TODO:
    - all people are judges
    - all judges makes rules with judgements
    - there are texts that is a judgement
    *)
  End Assumptions.

  Module Joke_proof.
  End Joke_proof.
End Joke_2.

(* 
In the museum of Vasily Chapayev the guide shows the visitors a skeleton:
"And here you can see the skeleton of Vasily Chapayev."
"And what is this small skeleton next to him?"
"That's Vasily Chapayev in his childhood."
General idea:
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

(* 
Two soldiers on the North Pole:
- wanna hear a political joke?
- not really, afraid they’ll send me to some shithole then.
NOTE: hard to formalize. GPT says this is because they think Siberia could be worse than north pole
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
They meet somehow after a while. Russian asks an American: – Well, how are you in hell? – Yes, good. I ate one bucket and walk all day. And you? – Yes, as usual: there are not enough buckets for all, then they will bring little shit.
NOTE: More complicated implications than the 1st joke...
*)
