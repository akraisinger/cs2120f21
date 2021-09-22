-- Anna Kraisinger alk6tx

-- due wednesday
/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro

example : false := _    -- trick question? why?
/-
No proof for false, because then false would be true, and then everything
would be true. False is not true, so cannot have proof that it is.
-/

-- 1
example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _, -- iff intro rule you must prove → both ways
  -- forward
    assume porp,
    apply or.elim porp,
    -- left disjunct
    assume p,
    exact p,
    -- right disjunct
    assume p,
    exact p,
  -- backwards
    assume p,
    exact or.intro_left P p, -- can also use or.intro_right
end

-- 2
example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  -- forward
    assume pandp,
    exact and.elim_left pandp,
  -- backward
    assume p,
    exact and.intro p p,
end

-- 3
example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  -- forward
    assume porq,
    apply or.elim porq,
    assume P,
    apply or.intro_right,
    exact P,
    assume Q,
    apply or.intro_left,
    exact Q,
  -- backward
    assume qorp,
    apply or.elim qorp,
    assume Q,
    apply or.intro_right,
    exact Q,
    assume P,
    apply or.intro_left,
    exact P,
end

-- 4
example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  -- forward
    assume pandq,
    exact and.intro(and.elim_right pandq)(and.elim_left pandq),
  -- backward
    assume qandp,
    exact and.intro(and.elim_right qandp)(and.elim_left qandp),
end

-- 5
example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
  -- forward
    assume e,
    have p := and.elim_left e,
    have qr := and.elim_right e,
    cases qr,
    apply or.intro_left,
    exact and.intro p qr,
    apply or.intro_right,
    exact and.intro p qr,
  -- backward
    assume e,
    apply and.intro,
    cases e,
    have p := and.elim_left e,
    exact p,
    have p := and.elim_left e,
    exact p,
    cases e,
    apply or.intro_left,
    have q := and.elim_right e,
    exact q,
    apply or.intro_right,
    have r := and.elim_right e,
    exact r,
end

-- 6
example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  assume P Q R,
  apply iff.intro,
  -- forward
    assume e,
    apply and.intro,
    cases e,
    apply or.intro_left,
    exact e,
    apply or.intro_right,
    exact (and.elim_left e),
    cases e,
    apply or.intro_left,
    exact e,
    apply or.intro_right,
    exact (and.elim_right e),
  -- backward
    assume e,
    have pq := and.elim_left e,
    cases pq,
    apply or.intro_left,
    exact pq,
    have pr := and.elim_right e,
    cases pr,
    apply or.intro_left,
    exact pr,
    apply or.intro_right,
    exact and.intro pq pr,
end

-- 7
example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro,
  -- forward
    assume e,
    have p := and.elim_left e,
    exact p,
  -- backward
    assume e,
    apply and.intro,
    exact e,
    apply or.intro_left,
    exact e,
end

-- 8
example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro,
  -- forward
    assume e,
    cases e,
    exact e,
    have p := and.elim_left e,
    exact p,
  -- backward
    assume e,
    apply or.intro_left,
    exact e,
end

-- 9
example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,
  apply iff.intro,
  -- forward
    assume e,
    cases e,
    apply true.intro,
    exact e,
  -- backward
    assume e,
    apply or.intro_right,
    exact e,
end

-- 10
example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume P,
  apply iff.intro,
  -- forward
    assume e,
    cases e,
    exact e,
    apply false.elim,
    exact e,
  -- backward
    assume e,
    apply or.intro_left,
    exact e,
end

-- 11
example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
  assume P,
  apply iff.intro,
  -- forward
    assume e,
    apply and.elim_left e,
  -- backward
    assume e,
    apply and.intro,
    exact e,
    apply true.intro,
end

-- 12
example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro,
  -- forward
    assume e,
    apply and.elim_right e,
  -- backward
    assume e,
    apply and.intro,
    apply false.elim,
    exact e,
    exact e,
end

