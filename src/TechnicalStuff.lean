import tactic
import data.real.basic
import measure_theory.measure.lebesgue

/- 
  If some statement holds for almost all x and it always implies another statement
  then the other statement also holds almost everywhere  
 -/
lemma ae_of_implies_and_ae {p : ℝ → Prop} {q : ℝ → Prop} : 
  (∀ x, p x → q x) → (∀ᵐ x : ℝ, p x) → (∀ᵐ x : ℝ, q x) :=
begin
  intros hpq hpae,
  have h : {x | ¬ q x} ⊆ {x | ¬ p x} := begin
    simp,
    intro x,
    specialize hpq x,
    intro hnq,
    intro hp,
    apply hnq,
    apply hpq,
    assumption
  end,
  apply measure_theory.outer_measure.mono_null _ h (measure_theory.ae_iff.1 hpae),
end