import tactic
import data.real.basic
import measure_theory.function.locally_integrable
import measure_theory.measure.lebesgue
import measure_theory.integral.interval_integral
import TechnicalStuff

noncomputable def μ := real.measure_space.volume

structure edgeflow := 
  (fp : ℝ →ₘ[μ] ℝ)
  (h_fp_locint : measure_theory.locally_integrable fp μ)
  (h_fp_0_before_0 : ∀ᵐ θ, θ < 0 → fp θ = 0)
  (fm : ℝ →ₘ[μ] ℝ)
  (h_fm_locint : measure_theory.locally_integrable fm μ)
  (h_fm_0_before_0 : ∀ᵐ θ, θ < 0 → fm θ = 0)

namespace edgeflow
  variables (f : edgeflow)

  noncomputable def Fp : ℝ → ℝ := λ θ, ∫ z in 0..θ, f.fp z ∂μ
  noncomputable def Fm : ℝ → ℝ := λ θ, ∫ z in 0..θ, f.fm z ∂μ

  noncomputable def q (τ : ℝ) : ℝ → ℝ := λ θ, (f.Fp θ) - (f.Fm (θ + τ))

  noncomputable def c (τ : ℝ) (ν : ℝ) : ℝ → ℝ := λ θ, τ + (f.q τ θ) / ν

  def weak_flowconservation (τ : ℝ) : Prop := ∀ θ ≥ 0, f.Fm (θ + τ) ≤ f.Fp θ

  def flow_respects_capacity (τ : ℝ) (ν : ℝ) : Prop := 
    ∀ᵐ θ : ℝ, f.fm (θ + τ) ≤ ν

  def queue_operates_at_capacity (τ : ℝ) (ν : ℝ) : Prop := 
    ∀ᵐ θ : ℝ, if f.q τ θ > 0 then f.fm (θ + τ) = ν else f.fm (θ + τ) = min (f.fp θ) ν

  def queue_operates_at_capacity_cum (τ : ℝ) (ν : ℝ) : Prop :=
    ∀ θ : ℝ, f.Fm (θ + f.c τ ν θ) = f.Fp θ

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

  lemma respects_cap_of_queue_op_at_cap (τ : ℝ) (ν : ℝ): 
    queue_operates_at_capacity f τ ν → flow_respects_capacity f τ ν :=
  begin
    apply ae_of_implies_and_ae,
    intros x hqatcap,
    split_ifs at hqatcap,
    {
      apply le_of_eq,
      assumption,
    },
    rw hqatcap,
    exact min_le_right _ _,
  end

  lemma queue_op_at_cap_cum_of_queue_op_at_cap (τ : ℝ) (ν : ℝ):
    queue_operates_at_capacity f τ ν → queue_operates_at_capacity_cum f τ ν :=
  begin
    intros h θ,
    have hq_depletes_slow : ∀ θ', θ ≤ θ' ∧ θ' < θ + (f.q τ θ)/ν → f.q τ θ' > 0 :=
    begin
      sorry
    end,
    have h : ∀ᵐ z : ℝ ∂μ, z ∈ set.interval_oc (θ + τ) (θ + (f.q τ θ)/ν + τ) → f.fm z = (λ θ, ν) z 
      := sorry,
    have hνpos : ν ≠ 0 
      := sorry,
    show ∫ z in 0..θ + f.c τ ν θ, f.fm z ∂μ = f.Fp θ,
    rw ← interval_integral.integral_add_adjacent_intervals 
            (interval_integrable_of_locally_integrable f.fm 0 (θ + τ) f.h_fm_locint)
            (interval_integrable_of_locally_integrable f.fm (θ + τ) (θ + f.c τ ν θ) f.h_fm_locint),
    show f.Fm (θ + τ) + ∫ z in θ + τ..θ + f.c τ ν θ, f.fm z ∂μ = f.Fp θ,
    show f.Fm (θ + τ) + ∫ z in θ + τ..θ + (τ + (f.q τ θ) / ν), f.fm z ∂μ = f.Fp θ,
    rw add_comm τ _,
    rw ← add_assoc,
    rw interval_integral.integral_congr_ae h,
    simp,
    show f.Fm (θ + τ) + ∫ (x : ℝ) in θ + τ..θ + f.q τ θ / ν + τ, ν = f.Fp θ,
    rw interval_integral.integral_const,
    calc f.Fm (θ + τ) + (θ + f.q τ θ / ν + τ - (θ + τ)) • ν 
                    = f.Fm (θ + τ) + (f.q τ θ / ν) • ν : by ring_nf
                ... = f.Fm (θ + τ) + f.q τ θ : by finish
                ... = f.Fm (θ + τ) + (f.Fp θ - f.Fm (θ + τ)) : by refl
                ... = f.Fp θ : by ring_nf,
  end

end edgeflow

