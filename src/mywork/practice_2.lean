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

-- 6
example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  assume P Q R,
  apply iff.intro,
  -- forward
    assume h,
    apply and.intro,
    cases h,
    apply or.intro_left,
    exact h,
    apply or.intro_right,
    exact (and.elim_left h),
    cases h,
    apply or.intro_left,
    exact h,
    apply or.intro_right,
    exact (and.elim_right h),
  -- backward
    assume h,
    have pq := and.elim_left h,
    cases pq,
    apply or.intro_left,
    exact pq,
    have pr := and.elim_right h,
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
    assume h,
    have p := and.elim_left h,
    exact p,
  -- backward
    assume h,
    apply and.intro,
    exact h,
    apply or.intro_left,
    exact h,
end

-- 8
example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro,
  -- forward
    assume h,
    cases h,
    exact h,
    have p := and.elim_left h,
    exact p,
  -- backward
    assume h,
    apply or.intro_left,
    exact h,
end

-- 9
example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,
  apply iff.intro,
  -- forward
    assume h,
    cases h,
    apply true.intro,
    exact h,
  -- backward
    assume h,
    apply or.intro_right,
    exact h,
end

-- 10
example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume P,
  apply iff.intro,
  -- forward
    assume h,
    cases h,
    exact h,
    apply false.elim,
    exact h,
  -- backward
    assume h,
    apply or.intro_left,
    exact h,
end

-- 11
example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
  assume P,
  apply iff.intro,
  -- forward
    assume h,
    apply and.elim_left h,
  -- backward
    assume h,
    apply and.intro,
    exact h,
    apply true.intro,
end

-- 12
example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro,
  -- forward
    assume h,
    apply and.elim_right h,
  -- backward
    assume h,
    apply and.intro,
    apply false.elim,
    exact h,
    exact h,
end

