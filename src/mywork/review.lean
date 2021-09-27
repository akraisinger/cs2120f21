/-axiom is a way of saying to assume a truth.
A type judgement? can do more than one via axioms-/
namespace implies
axioms (P Q : Prop)

def if_P_is_true_then_so_is_Q : Prop := P → Q
/-binding if_P_is to be a proposition 

arrow shows conditional in logic.

"if P then Q"

to show p implies q, show in context of p,
q must be true.

-/

axiom p : P
-- assume P is true
-- assume we have a prrof of P (p)

axiom pq : P → Q
-- assume that we have a proof of pq, that if p then q
-- P → Q is a proposition


-- intro rule for implies: assume premise, show conclusion
-- elimination rule for implies: apply proof of p → q to proof of p

#check pq
#check p
#check (pq p)

/- suppose P and Q are propostions and you
know that P → Q and that P are both true.
Show that Q is true.

Proof: Apply the truth of P → Q to the
truth of P to derrive the truth of Q.

Also,
Proof: By the elimination rule for → with
pq applied to p.add_key_equivalence

Also,
Proof: By "modus ponens". QED
-/

-- think of proof P→Q as a function!
-- takes in a proof of P
-- returns a proof of Q
end implies
/-
FOR ALL (∀)
-/

namespace all
axioms
  (T : Type)
  (P: T → Prop)
  --predicate (P) of a type that assumes a proposition
  (t : T) 
  (a : ∀ (x : T), P x)
  -- for any object of type T that object has property of P
  -- does t have property P?
  -- yes! bc t is of type T where any object of that type it has that property

example : P t := a t -- applying axiom a to t proves that t has property P
#check a t
end all

/-
AND & →
-/


/- 
P ∧ Q 
if have proof of p and proof of q then can proof of p ∧ q
two smaller proofs into one bigger proof
-/

/-

given proposition of P, can also make proposition ¬P

way to prove ¬P is to show P has no proof.
if ¬P is true, then assuming P is true will able to deduce proof of false.
say ¬P by saying P is true is impossible, and because impossible, no proof of P.

if P→false is true, then there is not proof of P, so ¬P.
(remember, no proofs of false)

-/

/-
-- INTRO AND ELIM RULES!! --

EQUALS (=)
intro: (1 rule)
elim: (1 rule)

AND (∧)
intro: (and.intro)
elim: (and.elim_left, and.elim_right)

OR (∨)
intro: (or.intro_left, or.intro_right)
elim: (or.elim)

FOR ALL (∀)
intro: if you can assume an arbitrary version and prove it,
then you can for all
elim: apply the for all func

IMPLIES (→)
intro: assume the antecedent, if you can prove the consequent,
then you can prove implies.
elim: apply the implies func

NOT (¬)
intro (none??)
elim??

IF AND ONLY IFF (↔)
intro: (iff.intro)
elim?

TRUE
intro: (true.intro)
elim: no real elimination rule for true

FALSE
intro: no real intro rule for false
elim: (false.elim) 

-/
