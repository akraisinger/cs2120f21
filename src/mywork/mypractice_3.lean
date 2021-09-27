-- 1
example : 0 ≠ 1 :=
begin
  assume h,
  cases h,
end

-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  apply false.elim,
  apply h,
  apply eq.refl,
end
-- alternative answer
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  have f : false := h (eq.refl 0),
  exact false.elim (f)
end

-- 3
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P p,
  assume h, -- ¬¬P is the same as ¬P → false is the same as (P → false) → false 
  have ph := h p,
  exact ph, -- can also use cases f or exact false.elim f
end
-- alternative answer:
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P p,
  assume h, -- ¬¬P is the same as ¬P → false is the same as (P → false) → false 
  contradiction,
end

-- We might need classical (vs constructive) reasoning
#check classical.em
open classical
#check em


/-
axiom em : ∀ (p : Prop), p ∧ ¬p

This is the famous and historically controversial
"law" (now axiom) of the excluded middle. It's is
a key to proving many intuitive theorems in logic
and mathematics. But it also leads to giving up on
having evidence *why* something is either true or
not tru, in that you no longer need a proof of
either P or of ¬P to have a proof of P ∨ ¬P.
-/


-- 4
theorem neg_elim : ∀ (P: Prop), ¬¬P → P :=
begin
  assume P,
  assume h, 
  -- the elimination rule of negation allows eliminate double negations?
  -- cannot assume ¬¬P is true under PL? add law of excluded to follow 
  -- classical logic that it is true? some stuff only CLASSICALLY true
  have pornp := classical.em P,
  cases pornp,
  exact pornp,
  apply false.elim,
  have hpornp := h pornp,
  exact hpornp, -- could also use contradiction
end

-- 5
theorem demorgan_1 : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬P :=
begin
end

-- 6
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → ¬P :=
begin
end 