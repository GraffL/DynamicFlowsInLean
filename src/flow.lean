import tactic
import data.real.basic
import measure_theory.function.locally_integrable
import measure_theory.measure.lebesgue
import measure_theory.integral.interval_integral
import measure_theory.group.measure
import TechnicalStuff

noncomputable def μ := real.measure_space.volume

structure edgeflow (τ : ℝ) (ν : ℝ):= 
  (τnn : τ ≥ 0)
  (νpos : ν > 0)
  (fp : ℝ →ₘ[μ] ℝ)
  (h_fp_locint : measure_theory.locally_integrable fp μ)
  (h_fp_0_before_0 : ∀ᵐ θ, θ < 0 → fp θ = 0)
  (fm : ℝ →ₘ[μ] ℝ)
  (h_fm_locint : measure_theory.locally_integrable fm μ)
  (h_fm_0_before_0 : ∀ᵐ θ, θ < 0 → fm θ = 0)

namespace edgeflow
  variables {τ : ℝ} {ν : ℝ} (f : edgeflow τ ν)

  noncomputable def Fp : ℝ → ℝ := λ θ, ∫ z in 0..θ, f.fp z ∂μ
  noncomputable def Fm : ℝ → ℝ := λ θ, ∫ z in 0..θ, f.fm z ∂μ

  noncomputable def q : ℝ → ℝ := λ θ, (f.Fp θ) - (f.Fm (θ + τ))

  noncomputable def c : ℝ → ℝ := λ θ, τ + (f.q θ) / ν

  def weak_flowconservation : Prop := ∀ θ : ℝ, f.Fm (θ + τ) ≤ f.Fp θ

  def flow_respects_capacity : Prop := 
    ∀ᵐ θ : ℝ, f.fm (θ + τ) ≤ ν

  def queue_operates_at_capacity_at (θ : ℝ) : Prop := 
    if f.q θ > 0 then f.fm (θ + τ) = ν else f.fm (θ + τ) = min (f.fp θ) ν

  def queue_operates_at_capacity : Prop := 
    ∀ᵐ θ : ℝ, f.queue_operates_at_capacity_at θ

  def queue_operates_at_capacity_cum : Prop :=
    ∀ θ : ℝ, f.Fm (θ + f.c θ) = f.Fp θ

  lemma weak_flowconservation_iff_queue_nonnegative :
    weak_flowconservation f ↔ ∀ θ : ℝ, f.q θ ≥ 0 :=
  begin
    split,
    {
      -- Show that weak flow conservation implies that the queue is nonnegative
      intros hweak_fc θ,
      specialize hweak_fc θ,
      have h : (f.Fp θ) - (f.Fm (θ + τ)) ≥ 0 := begin
        linarith,
      end,
      assumption,
    },
    {
      -- Show that a nonnegative queue implies weak flow conservation
      intros hqnonneg θ,
      specialize hqnonneg θ,
      calc f.Fm (θ + τ) = f.Fp θ - (f.Fp θ - f.Fm (θ + τ)) : by ring
                ...     = f.Fp θ - (f.q θ) : by refl
                ...     ≤  f.Fp θ : by linarith,
    }
  end 

  lemma respects_cap_of_queue_op_at_cap: 
    queue_operates_at_capacity f → flow_respects_capacity f :=
  begin
    apply ae_of_implies_and_ae,
    intros θ hqatcap,
    unfold queue_operates_at_capacity_at at hqatcap,
    split_ifs at hqatcap,
    {
      apply le_of_eq,
      assumption,
    },
    rw hqatcap,
    exact min_le_right _ _,
  end

  lemma weak_flowconservation_of_queue_op_at_cap:
    queue_operates_at_capacity f → weak_flowconservation f :=
  begin
    sorry,
  end

  lemma queue_depletes_fast_of_respects_capacity {θ : ℝ}:
    flow_respects_capacity f → ∀ θ', θ ≤ θ' ∧ θ' < θ + (f.q θ)/ν → f.q θ' > 0 :=
  begin
    sorry,
  end

  lemma queue_op_at_cap_cum_of_queue_op_at_cap:
    queue_operates_at_capacity f → queue_operates_at_capacity_cum f :=
  begin
    intros hatcap θ,
    have hq_depletes_slow : ∀ θ', θ ≤ θ' ∧ θ' < θ + (f.q θ)/ν → f.q θ' > 0 :=
    begin
      apply queue_depletes_fast_of_respects_capacity,
      apply respects_cap_of_queue_op_at_cap,
      assumption,
    end,
    have hmaxoutflow : ∀ᵐ z : ℝ ∂μ, z ∈ set.interval_oc (θ + τ) (θ + f.c θ) → f.fm z = (λ θ, ν) z := 
    begin
      have h' : μ ({z : ℝ | ¬f.queue_operates_at_capacity_at (z - τ)} ∪ {θ + f.c θ}) = 0 :=
      begin
        apply measure_theory.outer_measure.union_null,
        {
          rw ← lebesgue_measure_translation_invariant (λ a, ¬f.queue_operates_at_capacity_at a),
          simp,
          unfold queue_operates_at_capacity at hatcap,
          rw measure_theory.ae_iff at hatcap,
          exact hatcap,
        },
        exact real.volume_singleton,
      end,
      apply measure_theory.ae_iff.2,
      simp,
      have h'' : {a : ℝ | a ∈ set.interval_oc (θ + τ) (θ + f.c θ) ∧ ¬f.fm a = ν} ⊆ {z : ℝ | ¬f.queue_operates_at_capacity_at (z - τ)} ∪ {θ + f.c θ} :=
      begin
        intros x hx,
        by_cases x = θ + f.c θ,
        {
          right,
          rw h,
          simp,
        },
        left,
        cases hx with hx1 hx2,
        have g : θ + τ ≤ θ + f.c θ := 
        begin
          unfold c, 
          have k : f.q θ ≥ 0 := 
          begin
            apply (weak_flowconservation_iff_queue_nonnegative f).1 _ θ,
            apply weak_flowconservation_of_queue_op_at_cap f,
            exact hatcap
          end,
          rw ge_iff_le at k,
          rw ← div_le_div_right f.νpos at k,
          simp at k,
          linarith,
        end,
        rw set.interval_oc_of_le g at hx1,
        rw set.mem_Ioc at hx1,
        have g1 : θ ≤ x - τ := 
        begin
          linarith
        end,
        have g2 : x - τ < θ + f.q θ / ν := 
        begin
          unfold c at hx1,
          unfold c at h,
          rw sub_lt_iff_lt_add,
          rw add_assoc,
          rw add_comm _ τ,
          apply lt_of_le_of_ne,
          exact hx1.2,
          exact h,
        end,
        specialize hq_depletes_slow (x - τ) ⟨g1, g2⟩,
        intro g'',
        unfold queue_operates_at_capacity_at at g'',
        split_ifs at g'',
        rw sub_add_cancel at g'',
        exact hx2 g'',
      end,
      exact measure_theory.outer_measure.mono_null _ h'' h',
    end,
    have hνpos : ν ≠ 0 :=
    begin
      have h' : ν > 0 := f.νpos,
      linarith,
    end,

    calc f.Fm (θ + f.c θ) = ∫ z in 0..θ + f.c θ, f.fm z ∂μ : by refl
            ... = ∫ z in 0..θ + τ, f.fm z ∂μ + ∫ z in θ + τ..θ + f.c θ, f.fm z ∂μ : 
                    by rw ← interval_integral.integral_add_adjacent_intervals 
                      (interval_integrable_of_locally_integrable f.fm 0 (θ + τ) f.h_fm_locint)
                      (interval_integrable_of_locally_integrable f.fm (θ + τ) (θ + f.c θ) f.h_fm_locint)
            ... = f.Fm (θ + τ) + ∫ z in θ + τ..θ + f.c θ, f.fm z ∂μ : by refl
            ... = f.Fm (θ + τ) + ∫ z in θ + τ..θ + f.c θ, (λ z', (λ θ, ν) z') z ∂μ : 
                    by rw interval_integral.integral_congr_ae hmaxoutflow
            ... = f.Fm (θ + τ) + ∫ z in θ + τ..θ + f.c θ, ν : by refl
            ... = f.Fm (θ + τ) + (θ + f.c θ - (θ + τ)) • ν : 
                    by rw interval_integral.integral_const
            ... = f.Fm (θ + τ) + (θ + (τ + f.q θ / ν) - (θ + τ)) • ν : by refl
            ... = f.Fm (θ + τ) + (f.q θ / ν) • ν : by ring_nf
            ... = f.Fm (θ + τ) + f.q θ : by finish
            ... = f.Fm (θ + τ) + (f.Fp θ - f.Fm (θ + τ)) : by refl
            ... = f.Fp θ : by ring_nf,
  end
end edgeflow