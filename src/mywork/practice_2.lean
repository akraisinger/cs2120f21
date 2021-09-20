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

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
  -- forward
    assume h,
    have p := and.elim_left h,
    have qr := and.elim_right h,
    cases qr,
    apply or.intro_left,
    exact and.intro p qr,
    apply or.intro_right,
    exact and.intro p qr,
  -- backward
    assume h,
    apply and.intro,
    cases h,
    have p := and.elim_left h,
    exact p,
    have p := and.elim_left h,
    exact p,
    cases h,
    apply or.intro_left,
    have q := and.elim_right h,
    exact q,
    apply or.intro_right,
    have r := and.elim_right h,
    exact r,
end

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
end

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
end

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
end

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
end

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
end

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
end

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
end


