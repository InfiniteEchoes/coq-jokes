(* TODO:
- formally create a coq project in this folder
- maybe set up a CI on git
- think of useful predicates and how to implement them
*)

(* NOTE: the biggest diff for informal logic to formal logic is that
informal logic is context based so its hard to formalize or even have
multiple meaning. The attempt to formalize jokes is for entertainment solely. *)

(* ******************************** *)
(* Initial draft for predicates *)
(* ******************************** *)

(* Example: "ab" consists of "a" and "b" *)
Parameter consists_of : Set.

(* Example: A and B confilcts, therefore this story is a joke
  Should take a proposition that resulted in false, and return true *)
Parameter is_joke : Set.

(* Example: A under intrepretation A' means a' and A'' means a''. 
  They have different meaning resulted into a joke 
  1st parameter : original sentence or slice
  2nd parameter : the contexts to make the interpretation
  *)
Parameter means : Set -> Set -> Set.

(* Theorem: idea being described above. B and C should be different context to make the ambiguity *)
Parameter ambiguity_on_meanings (A : Set) (B C : Set): means A B -> means A C -> is_joke A.

(* TODO: think of an mechanic to destruct any words including predicates into list of characters *)

(* Wrapper for a single sentence. Words within it should be already formalized as an AST-like thing *)
Parameter chat : [Set] -> Set.

(* If there's a joke in the story, the whole story should be a joke *)
Parameter is_joke_story (A : Set) (story : A) (proof : is_joke A) : is_joke story.

(* For ambiguity on a single word *)
Parameter ambiguity : Set.

(* Something just to label that a sentence is totally unrelated to the joke. Could be useful? *)
Parameter unrelated : Set.

(* DRAFT: some initial way to analyze the sentences *)
Inductive expr :=
(* Someone is asking a question *)
| Ask : Set (* TODO: from person x to person y *)-> expr -> expr
| Answer : Set -> expr -> expr
| And : expr -> expr
| Or : expr -> expr
| Plain : Set (* Should be string? *)-> expr
.

(* Draft: the architecture for each joke should be like:
Module joke_1.
  Module context.
  End context.

  Module sentences.
  End sentences.

  Module joke_proof.
  End joke_proof.
End joke_1.
*)


(* ******************************** *)
(* Draft for jokes that might be easy 
   to formalize *)
(* ******************************** *)

(* 
https://www.reddit.com/r/AskARussian/comments/n4qj1m/any_good_soviet_jokes/ 
https://www.johndclare.net/Russ12_Jokes.htm
https://en.wikipedia.org/wiki/Russian_political_jokes
*)

(* NOTE: this looks like the easiest joke to fomalize! The joke here is about the poor finance situation for devils
-- Would you choose a capitalist hell or a communist one?
-- Of course, communist: they either don't have fuel, don't have enough pots for everyone or all devils are drunk.
*)
(* NOTE: the reasonings is formed as follows:
1. [assumption] we first assume that the description in sentence 2 means poor
2. [sentence 2, 1] 2nd sentence shows that comm hell is poor
3. [sentence 1] 1st sentence is asking for a choice (how to formalize this?)
4. [sentence 2, sentence 1] 2nd sentence is making a choice to answer sentence 1
5. [sentence 1, assumption on common sense] normally ppl won't think of a reason to make the choice
6. [5] if a person makes the choice, he isn't normal
7. [4] person 2 made a choice, so he isn't normal
8. [assumption on common sense] we usually assume that any ppl is normal
9. [6, 7] there exists a person in the chat being not normal. (actually he's mad)
10. [9] 9 is the joke
*)
Module joke_1.
End joke_1.

(* 
Two judges meet in a court and one is laughing hysterically.
The other: what's so funny?
The first one: i've just heard the most ridiculous anecdote of my life.
The other: Care to share?
The first: Can't, just gave a guy 15 years for it.
TODO: I cannot even get the joke! ask gpt...
*)

(* 
In the museum of Vasily Chapayev the guide shows the visitors a skeleton:
"And here you can see the skeleton of Vasily Chapayev."
"And what is this small skeleton next to him?"
"That's Vasily Chapayev in his childhood."
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