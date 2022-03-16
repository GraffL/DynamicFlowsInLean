import tactic
import data.real.basic
import measure_theory.function.locally_integrable
import measure_theory.measure.lebesgue

structure edgeflow := 
  (fp : ℝ → ℝ)
  (h_fp_locint : measure_theory.locally_integrable fp stieltjes_function.id.measure)
  (fm : ℝ → ℝ)
  (h_fm_locint : measure_theory.locally_integrable fm stieltjes_function.id.measure)

namespace edgeflow
  variables (f : edgeflow)

  noncomputable def Fp : ℝ → ℝ := λ θ, ∫ z in (set.interval 0 θ), f.fp z
  noncomputable def Fm : ℝ → ℝ := λ θ, ∫ z in (set.interval 0 θ), f.fm z

  noncomputable def q (τ : ℝ) : ℝ → ℝ := λ θ, (f.Fp θ) - (f.Fm (θ + τ))

  def weak_flowconservation (τ : ℝ) : Prop := ∀ θ ≥ 0, f.Fm (θ + τ) ≤ f.Fp θ

  def flow_respects_capacity (τ : ℝ) (ν : ℝ) : Prop := ∀ θ ≥ 0, f.fm (θ + τ) ≤ ν
    -- TODO: Must only hold for almost all θ

  def queue_operates_at_capacity (τ : ℝ) (ν : ℝ) : Prop := 
    -- TODO: Must only hold for almost all θ
    ∀ θ ≥ 0, if f.q τ θ > 0 then f.fm (θ + τ) = ν else f.fm (θ + τ) = min (f.fp θ) ν

  lemma weak_flowconservation_iff_queue_nonnegative (τ : ℝ) :
    weak_flowconservation f τ ↔ ∀ θ ≥ 0, f.q τ θ ≥ 0 :=
  begin
    split,
    {
      -- Show that weak flow conservation implies that the queue is nonnegative
      intros hweak_fc θ hθpos,
      specialize hweak_fc θ hθpos,
      have h : (f.Fp θ) - (f.Fm (θ + τ)) ≥ 0 := begin
        linarith,
      end,
      assumption,
    },
    {
      -- Show that a nonnegative queue implies weak flow conservation
      intros hqnonneg θ hθpos,
      specialize hqnonneg θ hθpos,
      calc f.Fm (θ + τ) = f.Fp θ - (f.Fp θ - f.Fm (θ + τ)) : by ring
                ...     = f.Fp θ - (f.q τ θ) : by refl
                ...     ≤  f.Fp θ : by linarith,
    }
  end 

  lemma respects_cap_of_queue_op_at_cap_im (ν : ℝ) (τ : ℝ): 
    queue_operates_at_capacity f τ ν → flow_respects_capacity f τ ν :=
  begin
    intros h θ hθpos,
    specialize h θ hθpos,
    split_ifs at h,
    {
      -- Case of non-empty queue
      linarith,
    },
    {
      -- Case of empty queue
      rw h,
      apply min_le_right,
    }
  end

end edgeflow
