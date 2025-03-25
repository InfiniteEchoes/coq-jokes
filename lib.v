(* ******************************** *)
(* Project setups, general notes and etc *)
(* ******************************** *)
(* TODO:
- maybe set up a CI on git
- think of useful predicates and how to implement them
*)

(* NOTE: 
INTRODUCTION.
The biggest difference for informal logic to formal logic is that
informal logic is context based, and everything needs to be given an 
intrepretation manually,so its hard to formalize. This project is 
for entertainment only. 

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

Require Import Coq.Strings.String.

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
- [assumption]judge makes rules
- [assumption]if judge sent someone to jail for a reason, the reason with 
  the punishment constitutes to a rule
- Judge has made a rule that if someone tells a joke, he will be sent to prison
- If judge tells a joke, he will be sent to prison
- Judge cannot tell the joke
*)

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
