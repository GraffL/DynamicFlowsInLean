import tactic
import data.real.basic
import measure_theory.function.locally_integrable
import measure_theory.measure.lebesgue
import measure_theory.integral.interval_integral

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

lemma interval_integrable_of_locally_integrable (f: ℝ → ℝ) (a : ℝ) (b : ℝ) {μ : measure_theory.measure ℝ}:
  measure_theory.locally_integrable f μ → interval_integrable f μ a b :=
begin
  sorry,
end

lemma lebesgue_measure_translation_invariant {μ : measure_theory.outer_measure ℝ} (p : ℝ → Prop) {x : ℝ} :
  μ {y : ℝ | p y} = μ {y : ℝ | p (y - x)} :=
begin
  sorry,
end