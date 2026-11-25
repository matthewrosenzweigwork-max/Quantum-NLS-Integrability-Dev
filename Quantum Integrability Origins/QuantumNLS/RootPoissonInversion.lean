import Mathlib
import QuantumNLS.CauchyUniqueness

/-!
# Poisson inversion: a finite measure whose Poisson smoothings converge locally uniformly to a continuous density has that density

New module (R-7E0532E7, `eq:root-explicit-density`, the Poisson/Fubini boundary-value step).  Proved directly from mathlib; no EXT-025.

For a finite measure `M` on `ℝ` with Poisson smoothing `poisson η M t = ∫ P_η(t - s) dM(s)` (`CauchyUniqueness.poisson`,
`P_η(y) = η/(η²+y²)`), a continuous `ρ ≥ 0` and the hypothesis
`hlim : ∀ compact K, poisson η M / π → ρ uniformly on K as η ↓ 0`,
**`measure_eq_withDensity`**: `M = volume.withDensity (ofReal ∘ ρ)`.

Steps: (i) Fubini, `∫ φ(t) poisson η M t dt = ∫ Φ_η(x) dM(x)` with `Φ_η(x) = ∫ φ(t) P_η(t - x) dt`; (ii) the Poisson integral
`Φ_η(x)/π → φ(x)` (substitution `t = x + ηs`, dominated convergence, `∫ (1+s²)⁻¹ = π`) and dominated convergence in `M`;
(iii) the uniform hypothesis gives `∫ φ · poisson η M / π → ∫ φ ρ`; (iv) `∫ φ dM = ∫ φ ρ` for every `φ ∈ C_c(ℝ)` and
`Measure.ext_of_integral_eq_on_compactlySupported`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal Real

namespace QuantumNLS.RootPoissonInversion

open QuantumNLS.CauchyUniqueness (pk poisson pk_nonneg continuous_pk integrable_pk integral_pk)

theorem pk_le {η : ℝ} (hη : 0 < η) (y : ℝ) : pk η y ≤ η⁻¹ := by
  unfold pk
  rw [div_le_iff₀ (by positivity)]
  have : η * η⁻¹ = 1 := mul_inv_cancel₀ hη.ne'
  nlinarith [sq_nonneg y, inv_pos.2 hη]

theorem continuous_poisson (M : Measure ℝ) [IsFiniteMeasure M] {η : ℝ} (hη : 0 < η) :
    Continuous (poisson η M) := by
  unfold poisson
  refine continuous_of_dominated (bound := fun _ => η⁻¹) (fun t => ?_) (fun t => ?_) (integrable_const _) ?_
  · exact ((continuous_pk hη).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · refine Eventually.of_forall fun s => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (pk_nonneg hη _)]
    exact pk_le hη _
  · exact Eventually.of_forall fun s => (continuous_pk hη).comp (continuous_id.sub continuous_const)

theorem poisson_nonneg (M : Measure ℝ) {η : ℝ} (hη : 0 < η) (t : ℝ) : 0 ≤ poisson η M t :=
  integral_nonneg (fun s => pk_nonneg hη _)

/-- The Poisson integral of a test function. -/
def Phi (φ : ℝ → ℝ) (η x : ℝ) : ℝ := ∫ t, φ t * pk η (t - x)

theorem integrable_phi_pk {φ : ℝ → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) {η : ℝ} (hη : 0 < η) (x : ℝ) :
    Integrable (fun t => φ t * pk η (t - x)) := by
  have h1 : Integrable φ := hφ.integrable_of_hasCompactSupport hc
  have hb : Continuous (fun t => pk η (t - x)) := (continuous_pk hη).comp (continuous_id.sub continuous_const)
  refine h1.mul_bdd (c := η⁻¹) hb.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (pk_nonneg hη _)]
  exact pk_le hη _

theorem phi_bound {φ : ℝ → ℝ} {C : ℝ} (hC : ∀ t, |φ t| ≤ C) (hφ : Continuous φ) (hc : HasCompactSupport φ)
    {η : ℝ} (hη : 0 < η) (x : ℝ) : |Phi φ η x| ≤ C * π := by
  unfold Phi
  have hi := integrable_phi_pk hφ hc hη x
  have hpk : Integrable (fun t => pk η (t - x)) := (integrable_pk hη).comp_sub_right x
  have hint : ∫ t, pk η (t - x) = π := by
    rw [integral_sub_right_eq_self (fun t => pk η t) x]; exact integral_pk hη
  calc |∫ t, φ t * pk η (t - x)| ≤ ∫ t, |φ t * pk η (t - x)| := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun t => φ t * pk η (t - x))
    _ ≤ ∫ t, C * pk η (t - x) := by
        refine integral_mono hi.abs (hpk.const_mul C) (fun t => ?_)
        rw [abs_mul, abs_of_nonneg (pk_nonneg hη _)]
        exact mul_le_mul_of_nonneg_right (hC t) (pk_nonneg hη _)
    _ = C * π := by rw [integral_const_mul, hint]

/-- The Poisson integral of a bounded continuous function equals its scaled average against `(1+s²)⁻¹`. -/
theorem phi_eq {φ : ℝ → ℝ} {η : ℝ} (hη : 0 < η) (x : ℝ) :
    Phi φ η x = ∫ s : ℝ, φ (η * s + x) * (1 + s ^ 2)⁻¹ := by
  unfold Phi
  have h1 : ∫ t, φ t * pk η (t - x) = ∫ u, φ (u + x) * pk η u := by
    have := integral_add_right_eq_self (μ := volume) (fun t => φ t * pk η (t - x)) x
    simpa using this.symm
  rw [h1]
  have h2 := Measure.integral_comp_mul_left (fun u => φ (u + x) * pk η u) η
  rw [abs_of_pos (inv_pos.2 hη)] at h2
  have h3 : ∫ u, φ (u + x) * pk η u = η * ∫ s, φ (η * s + x) * pk η (η * s) := by
    rw [h2]; simp only [smul_eq_mul]; field_simp
  rw [h3, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [pk]
  field_simp

theorem phi_tendsto {φ : ℝ → ℝ} (hφ : Continuous φ) {C : ℝ} (hC : ∀ t, |φ t| ≤ C) (x : ℝ) :
    Tendsto (fun η => Phi φ η x / π) (𝓝[>] 0) (𝓝 (φ x)) := by
  have hbound : Integrable (fun s : ℝ => C * (1 + s ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul C
  have key : Tendsto (fun η : ℝ => ∫ s : ℝ, φ (η * s + x) * (1 + s ^ 2)⁻¹) (𝓝[>] 0)
      (𝓝 (∫ s : ℝ, φ x * (1 + s ^ 2)⁻¹)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun s => C * (1 + s ^ 2)⁻¹) ?_ ?_ hbound ?_
    · exact Eventually.of_forall fun η =>
        ((hφ.comp ((continuous_const.mul continuous_id).add continuous_const)).mul
          ((continuous_const.add (continuous_pow 2)).inv₀ (fun s => (by positivity : (0:ℝ) < 1 + s ^ 2).ne') : Continuous fun s : ℝ => (1 + s ^ 2)⁻¹)).aestronglyMeasurable
    · exact Eventually.of_forall fun η => Eventually.of_forall fun s => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (by positivity : (0:ℝ) < 1 + s ^ 2))]
        exact mul_le_mul_of_nonneg_right (hC _) (inv_pos.2 (by positivity : (0:ℝ) < 1 + s ^ 2)).le
    · refine Eventually.of_forall fun s => ?_
      have : Tendsto (fun η : ℝ => φ (η * s + x) * (1 + s ^ 2)⁻¹) (𝓝[>] 0) (𝓝 (φ x * (1 + s ^ 2)⁻¹)) := by
        have h0 : Tendsto (fun η : ℝ => η * s + x) (𝓝[>] 0) (𝓝 x) := by
          have : Tendsto (fun η : ℝ => η * s + x) (𝓝 0) (𝓝 (0 * s + x)) :=
            ((continuous_id.mul continuous_const).add continuous_const).tendsto 0
          simpa using this.mono_left nhdsWithin_le_nhds
        exact ((hφ.tendsto x).comp h0).mul_const _
      exact this
  have hval : ∫ s : ℝ, φ x * (1 + s ^ 2)⁻¹ = φ x * π := by
    rw [integral_const_mul, integral_univ_inv_one_add_sq]
  rw [hval] at key
  have key2 : Tendsto (fun η => Phi φ η x) (𝓝[>] 0) (𝓝 (φ x * π)) := by
    refine key.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact (phi_eq hη x).symm
  have := key2.div_const π
  simpa [mul_div_assoc, div_self Real.pi_pos.ne'] using this

end QuantumNLS.RootPoissonInversion

#print axioms QuantumNLS.RootPoissonInversion.phi_tendsto
