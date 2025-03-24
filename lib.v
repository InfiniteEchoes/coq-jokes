(* ******************************** *)
(* Project setups, general notes and etc *)
(* ******************************** *)
(* TODO:
-[] formally create a coq project in this folder
-[] maybe set up a CI on git
-[] think of useful predicates and how to implement them
*)

(* NOTE: The biggest difference for informal logic to formal logic is that
informal logic is context based, and everything needs to be given an intrepretation
manually,so its hard to formalize. This project is for entertainment only. *)

(* NOTE(draft): Architecture for each joke should be like:
Module joke_n.
  (* predicates appeared in the joke *)
  Module Predicates.
  End Predicates.

  (* each proposition in this module should start with `says` *)
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

(* Initial way to analyze the sentences *)
Inductive expr :=
(* Someone is asking a question. Parameter : 
- the person to speak with
- the content of the sentence *)
| Ask : String.string -> expr -> expr

(* Someone is replying. Parameter : 
- the person to reply with
- the content of the sentence *)
| Answer : string -> expr -> expr

| And : expr -> expr -> expr
| Or : expr -> expr -> expr

(* 
Adjective. Parameter :
- the adjective
- the thing to describe with
*)
| Adj : expr -> expr -> expr

(* Another sentence follows after this one. Similar to cons for lists.
  Should I just change into normal cons instead?
*)
| Follow : expr -> expr -> expr

| Plain : string -> expr
.

(* TODO: set up notations for:
- Ask as _ ?
- Answer as _ !
- Follow as _ ; _
- Plain as [| _ |]
*)

(* I'm thinking of generalizing the following predicate to a series of "actions" that people can act *)
(* Predicate. Just to label that someone is saying a full sentence. Should be formed as the actual dialogue in the joke 
parameters:
- name of the person
- the expression that he says
*)
Parameter says : string -> expr -> expr.
(* TODO: make a new type for `says` and write a destructor for the type *)

(* Predicate. A and B confilcts, therefore this story is a joke. *)
Definition is_joke (A : Prop) : A -> ~A -> Prop. Admitted.

(* Predicate. If there's a joke in the dialogue, the whole dialogue should be a joke 
  TODO: redesign the parameters in the future
*)
Definition is_joke_dialogue (A : Prop) (dialogue : expr)
  (* (s1 s2 : A) (joke : is_joke s1 s2)  *)
  : Prop. Admitted.

(* Predicate. Example: A under intrepretation A' means a' and A'' means a''. 
They have different meaning resulted into a joke 
parameters:
- original sentence or slice (undefined, not a clue)
- the context to make the interpretation
*)
Definition means (A : Set) : A -> A -> expr. Admitted.

(* Predicate. Some sentence makes an ambiguity under different interpretation.
Parameter:
- A: the sentence to be interpreted
- B, C: different contexts to interpret the sentence
NOTE: did i define this predicate wrong?
*)
(* Definition ambiguity_meanings (T : Set) (A : T) (B C : T) : 
  is_joke expr (means T A B) (means T A C). Admitted. *)

(* Predicate. For ambiguity on a single word 
- A: the sentence to be interpreted
- B, C: different contexts to interpret the sentence
*)
Definition ambiguity_word : Set. Admitted.

(* ********Misc******** *)

(* Predicate. Example: "ab" consists of "a" and "b" *)
Definition consists_of : Set. Admitted.

(* A predicate to show someone has said something in the sentence. Parameters:
- the expression to contain
- the whole expression *)
Definition contains : expr -> expr -> Prop. Admitted.

(* TODO: theorem: If 
- we have predicate P(A), and
- some sentence contains A
- then we should conclude a more general claim on that sentence from A
*)

Parameter is : expr -> expr -> expr.

Parameter has : expr -> Prop.

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
    Definition normal : string -> Prop. Admitted.
  End Predicates.

  Module Dialogue.
    (* NOTE: This looks like the easiest joke to fomalize! The joke here is about the poor finance situation for devils
    -- Would you choose a capitalist hell or a communist one?
    -- Of course, communist: they either don't have fuel, don't have enough pots for everyone or all devils are drunk.
    *)
    (* TODO: a completed sentence should be defined with a definition *)
    Definition d_1 := says "A" (Ask "B"
        (Or
          (Adj (Plain "capitalist") (Plain "hell"))
          (Adj (Plain "communist") (Plain "hell")))).

    (* TODO: unfold the reasons *)
    Definition d_2 := says "B" 
      (Follow
        (Answer "A" (Adj (Plain "communist") (Plain "hell")))
        (is (Adj (Plain "communist") (Plain "hell")) 
            (Or (Plain "don't have fuel")
              (Or (Plain "don't have enough pots for everyone")
                  (Plain "all devils are drunk"))))).
  End Dialogue.

  Module Assumptions.
    (* "don't have fuel, don't have enough pots for everyone or all devils are drunk" means poor 
    *)
    Definition a_1 :=
      (is (Plain "poor")
          (Or (Plain "don't have fuel")
            (Or (Plain "don't have enough pots for everyone")
                (Plain "all devils are drunk")))).
    
    (* If people make a choice for d_1's question, this person isn't normal 
    TODO: redesign the `exprerssion` parameter
    *)
    Definition a_2 : Prop := forall (person : string) (expression : expr), 
      ((contains (Answer "A" (Adj (Plain "capitalist") (Plain "hell"))) expression) \/
      (contains (Answer "A" (Adj (Plain "communist") (Plain "hell"))) expression)) -> 
      ~(Predicates.normal person).

    (* Everyone should be normal person *)
    Definition a_3 : Prop := forall (person : string), Predicates.normal person.
    
  End Assumptions.

  (* 
  1. [assumption] we first assume that the description in sentence 2 means poor
  2. [sentence 2, 1] 2nd sentence shows that comm hell is poor
  3. [sentence 1] 1st sentence is asking for a choice (how to formalize this?)
  4. [sentence 2, sentence 1] 2nd sentence is making a choice to answer sentence 1
  5. [sentence 1, assumption on common sense] normally ppl won't think of a reason to make the choice
  6. [5] if a person makes the choice, he isn't normal
  7. [4] person 2 made a choice, so he isn't normal
  8. [assumption on common sense] we usually assume that any ppl is normal
  9. [6, 7] there exists a person in the chat being not normal. (actually, he's mad)
  10. [9] 9 is the joke
  *)
  Module Joke_proof.
    (* TODO: what should the proposition be like? *)
    (* TODO: write small tests below *)
  End Joke_proof.
End Joke_1.

(* 
Two judges meet in a court and one is laughing hysterically.
The other: what's so funny?
The first one: i've just heard the most ridiculous anecdote of my life.
The other: Care to share?
The first: Can't, just gave a guy 15 years for it.
General idea:
- (A rules that)if someone tells a joke, he will be sent to prison
- if A tells a joke, A will be sent to prison
- A cannot tell the joke
*)

(* 
In the museum of Vasily Chapayev the guide shows the visitors a skeleton:
"And here you can see the skeleton of Vasily Chapayev."
"And what is this small skeleton next to him?"
"That's Vasily Chapayev in his childhood."
General idea:
- one person could have only one skeleton
- for exhibition and bluffing purpose, Vasily got 2x in the museum
- Vasily isn't a "normal" person, hence the joke

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
TODO: give an exact explanation to this joke
*)

(* 
Russian and American go to hell. Satan approaches them, says:
– Choose which hell you go to. There is Russian hell and American hell.
– What is the difference? Both ask.
– In American hell, you need to eat a bucket of shit once a day, and in Russian – 2 buckets of shit, – Satan answers.
– Why do I have another bucket of shit? – says the American, chooses the American hell.
– Well, I lived in Russia, into the Russian hell and I will go, what is it, – says the Russian, chooses the Russian hell.
They meet somehow after a while. Russian asks an American: – Well, how are you in hell? – Yes, good. I ate one bucket and walk all day. And you? – Yes, as usual: there are not enough buckets for all, then they will bring little shit.
*)
