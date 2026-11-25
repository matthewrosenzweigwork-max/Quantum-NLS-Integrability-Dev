import Mathlib
import QuantumNLS.RootPoissonInversion

/-!
# Poisson inversion, assembly: `M = ρ dt` from locally uniform Poisson convergence

New module (R-7E0532E7, `eq:root-explicit-density`).  Imports `RootPoissonInversion` (Poisson integral limit).  Pure measure theory.

**`measure_eq_withDensity`**: for a finite measure `M` on `ℝ`, a continuous `ρ ≥ 0`, if `poisson η M / π → ρ` uniformly on every
compact set as `η ↓ 0`, then `M = volume.withDensity (ofReal ∘ ρ)`.  Used with `ρ = (πκ)⁻¹ arcosh(|Δ|/2)` (`RootDensity.rootDensity`)
for the canonical quantum measure.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal Real

namespace QuantumNLS.RootPoissonDensity

open QuantumNLS.CauchyUniqueness (pk poisson pk_nonneg continuous_pk integrable_pk integral_pk)
open QuantumNLS.RootPoissonInversion

/-- Fubini: `∫ φ(t) poisson η M t dt = ∫ Φ_η dM`. -/
theorem fubini (M : Measure ℝ) [IsFiniteMeasure M] {φ : ℝ → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    {η : ℝ} (hη : 0 < η) :
    ∫ t, φ t * poisson η M t = ∫ x, Phi φ η x ∂M := by
  have h1 : Integrable φ := hφ.integrable_of_hasCompactSupport hc
  have hint : Integrable (Function.uncurry fun t x => φ t * pk η (t - x)) ((volume : Measure ℝ).prod M) := by
    have hb := (h1.norm.mul_prod (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) M)).const_mul η⁻¹
    refine hb.mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact ((hφ.comp continuous_fst).mul
        ((continuous_pk hη).comp (continuous_fst.sub continuous_snd))).aestronglyMeasurable
    · simp only [Function.uncurry]
      rw [norm_mul, Real.norm_eq_abs (pk η _), abs_of_nonneg (pk_nonneg hη _)]
      calc ‖φ p.1‖ * pk η (p.1 - p.2) ≤ ‖φ p.1‖ * η⁻¹ := mul_le_mul_of_nonneg_left (pk_le hη _) (norm_nonneg _)
        _ = η⁻¹ * (‖φ p.1‖ * 1) := by ring
  unfold poisson Phi
  simp_rw [← integral_const_mul]
  exact integral_integral_swap hint

theorem continuous_phi {φ : ℝ → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) {η : ℝ} (hη : 0 < η) :
    Continuous (Phi φ η) := by
  have h1 : Integrable φ := hφ.integrable_of_hasCompactSupport hc
  unfold Phi
  refine continuous_of_dominated (bound := fun t => η⁻¹ * |φ t|) (fun x => ?_) (fun x => ?_) (h1.abs.const_mul _) ?_
  · exact (integrable_phi_pk hφ hc hη x).aestronglyMeasurable
  · refine Eventually.of_forall fun t => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pk_nonneg hη _), mul_comm]
    exact mul_le_mul_of_nonneg_right (pk_le hη _) (abs_nonneg _)
  · exact Eventually.of_forall fun t => continuous_const.mul ((continuous_pk hη).comp (continuous_const.sub continuous_id))

theorem integral_phi_tendsto (M : Measure ℝ) [IsFiniteMeasure M] {φ : ℝ → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    {C : ℝ} (hC : ∀ t, |φ t| ≤ C) :
    Tendsto (fun η => ∫ x, Phi φ η x / π ∂M) (𝓝[>] 0) (𝓝 (∫ x, φ x ∂M)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => C) ?_ ?_ (integrable_const _) ?_
  · filter_upwards [self_mem_nhdsWithin] with η hη
    exact ((continuous_phi hφ hc hη).div_const _).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with η hη
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_div, abs_of_pos Real.pi_pos, div_le_iff₀ Real.pi_pos]
    exact phi_bound hC hφ hc hη x
  · exact Eventually.of_forall fun x => phi_tendsto hφ hC x

/-- **Poisson inversion.** -/
theorem measure_eq_withDensity (M : Measure ℝ) [IsFiniteMeasure M] (ρ : ℝ → ℝ) (hρc : Continuous ρ)
    (hρ0 : ∀ t, 0 ≤ ρ t)
    (hlim : ∀ K : Set ℝ, IsCompact K →
      TendstoUniformlyOn (fun η x => poisson η M x / π) ρ (𝓝[>] 0) K) :
    M = volume.withDensity (fun t => ENNReal.ofReal (ρ t)) := by
  have : IsLocallyFiniteMeasure (volume.withDensity (fun t => ENNReal.ofReal (ρ t))) :=
    IsLocallyFiniteMeasure.withDensity_ofReal hρc
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have hφc : Continuous (f : ℝ → ℝ) := f.continuous
  have hcs : HasCompactSupport (f : ℝ → ℝ) := f.hasCompactSupport
  obtain ⟨C, hC⟩ := hφc.bounded_above_of_compact_support hcs
  have hC' : ∀ t, |(f : ℝ → ℝ) t| ≤ C := fun t => by simpa [Real.norm_eq_abs] using hC t
  have hA := integral_phi_tendsto M hφc hcs hC'
  -- rewrite the approximants
  have hA' : Tendsto (fun η => ∫ t, (f : ℝ → ℝ) t * (poisson η M t / π)) (𝓝[>] 0) (𝓝 (∫ x, (f : ℝ → ℝ) x ∂M)) := by
    refine hA.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with η hη
    have := fubini M hφc hcs hη
    calc ∫ x, Phi f η x / π ∂M = (∫ x, Phi f η x ∂M) / π := integral_div _ _
      _ = (∫ t, (f : ℝ → ℝ) t * poisson η M t) / π := by rw [this]
      _ = ∫ t, (f : ℝ → ℝ) t * (poisson η M t / π) := by
          rw [← integral_div]
          exact integral_congr_ae (Eventually.of_forall fun t => by simp only; ring)
  -- the other limit
  have hK : IsCompact (tsupport (f : ℝ → ℝ)) := hcs
  obtain ⟨B0, hB0⟩ := hK.exists_bound_of_continuousOn hρc.continuousOn
  have hB : Tendsto (fun η => ∫ t, (f : ℝ → ℝ) t * (poisson η M t / π)) (𝓝[>] 0)
      (𝓝 (∫ t, (f : ℝ → ℝ) t * ρ t)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun t => |(f : ℝ → ℝ) t| * (|B0| + 1)) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with η hη
      exact (hφc.mul ((continuous_poisson M hη).div_const _)).aestronglyMeasurable
    · have hu := (Metric.tendstoUniformlyOn_iff.1 (hlim _ hK)) 1 one_pos
      filter_upwards [hu] with η hη
      refine Eventually.of_forall fun t => ?_
      by_cases ht : t ∈ tsupport (f : ℝ → ℝ)
      · have h1 := hη t ht
        rw [Real.dist_eq] at h1
        have h2 := hB0 t ht
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have : |poisson η M t / π| ≤ |ρ t| + 1 := by
          have := abs_sub_abs_le_abs_sub (poisson η M t / π) (ρ t)
          rw [abs_sub_comm] at this
          linarith
        rw [Real.norm_eq_abs] at h2
        linarith [abs_nonneg B0, le_abs_self B0]
      · rw [image_eq_zero_of_notMem_tsupport ht]
        simp
    · exact ((hφc.integrable_of_hasCompactSupport hcs).abs.mul_const _)
    · refine Eventually.of_forall fun t => ?_
      by_cases ht : t ∈ tsupport (f : ℝ → ℝ)
      · exact ((hlim _ hK).tendsto_at ht).const_mul _
      · rw [image_eq_zero_of_notMem_tsupport ht]
        simp
  have heq := tendsto_nhds_unique hA' hB
  rw [heq]
  have hnu : ∫ x, (f : ℝ → ℝ) x ∂(volume.withDensity (fun t => ENNReal.ofReal (ρ t))) =
      ∫ t, ρ t * (f : ℝ → ℝ) t := by
    rw [integral_withDensity_eq_integral_toReal_smul (f := fun t => ENNReal.ofReal (ρ t))
      (show Measurable (fun t => ENNReal.ofReal (ρ t)) from ENNReal.measurable_ofReal.comp hρc.measurable)
      (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp [ENNReal.toReal_ofReal (hρ0 t)]
  rw [hnu]
  exact integral_congr_ae (Eventually.of_forall fun t => by simp only; ring)

end QuantumNLS.RootPoissonDensity

#print axioms QuantumNLS.RootPoissonDensity.measure_eq_withDensity
