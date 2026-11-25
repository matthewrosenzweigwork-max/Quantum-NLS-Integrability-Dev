                                                                                     
                                                               
import Mathlib
import NlsGge.ThirdConsultation.I.I043BL

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

namespace NlsGge.ThirdConsultation.I.I044Aux

theorem boundedLipschitzDistance_nonneg
    {alpha : Type*} [PseudoMetricSpace alpha] [MeasurableSpace alpha]
    [BorelSpace alpha] (mu nu : Measure alpha)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    0 ≤ I.boundedLipschitzDistance mu nu := by
  obtain ⟨hz, hb⟩ := I043BLAux.testValues_bounds mu nu
  exact le_csSup hb hz

theorem boundedLipschitzDistance_triangle
    {alpha : Type*} [PseudoMetricSpace alpha] [MeasurableSpace alpha]
    [BorelSpace alpha] (mu nu eta : Measure alpha)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] [IsProbabilityMeasure eta] :
    I.boundedLipschitzDistance mu eta ≤
      I.boundedLipschitzDistance mu nu + I.boundedLipschitzDistance nu eta := by
  obtain ⟨hz, _⟩ := I043BLAux.testValues_bounds mu eta
  apply csSup_le ⟨0, hz⟩
  rintro a ⟨f, hf, hlip, rfl⟩
  have hleft : |(∫ x, f x ∂mu) - ∫ x, f x ∂nu| ≤
      I.boundedLipschitzDistance mu nu :=
    le_csSup (I043BLAux.testValues_bounds mu nu).2 ⟨f, hf, hlip, rfl⟩
  have hright : |(∫ x, f x ∂nu) - ∫ x, f x ∂eta| ≤
      I.boundedLipschitzDistance nu eta :=
    le_csSup (I043BLAux.testValues_bounds nu eta).2 ⟨f, hf, hlip, rfl⟩
  exact (abs_sub_le (∫ x, f x ∂mu) (∫ x, f x ∂nu)
    (∫ x, f x ∂eta)).trans (add_le_add hleft hright)

/-- The reverse implication for the literal supremum used by I-043. -/
theorem integral_tendsto_of_boundedLipschitzDistance_tendsto_zero
    {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha]
    [BorelSpace alpha] (mu : ℕ → Measure alpha) (nu : Measure alpha)
    (hmu : ∀ n : ℕ, IsProbabilityMeasure (mu n)) (hnu : IsProbabilityMeasure nu)
    (hBL : Tendsto (fun n : ℕ => I.boundedLipschitzDistance (mu n) nu)
      atTop (𝓝 0)) (F : alpha →ᵇ ℝ) :
    Tendsto (fun n : ℕ => ∫ x, F x ∂mu n) atTop (𝓝 (∫ x, F x ∂nu)) := by
  letI : ∀ n : ℕ, IsProbabilityMeasure (mu n) := hmu
  letI : IsProbabilityMeasure nu := hnu
  have htest (f : alpha →ᵇ ℝ) (L : NNReal) (hf : LipschitzWith L f) :
      Tendsto (fun n : ℕ => ∫ x, f x ∂mu n) atTop (𝓝 (∫ x, f x ∂nu)) := by
    let C : ℝ := max ‖f‖ (L : ℝ) + 1
    have hmax : 0 ≤ max ‖f‖ (L : ℝ) :=
      (norm_nonneg f).trans (le_max_left _ _)
    have hC : 0 < C := by dsimp [C]; linarith only [hmax]
    have hfnorm : ‖f‖ ≤ C := (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)
    have hL : (L : ℝ) ≤ C := (le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one)
    let g : alpha →ᵇ ℝ := C⁻¹ • f
    have hgnorm : ‖g‖ ≤ 1 := by
      change ‖C⁻¹ • f‖ ≤ 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hC)]
      calc
        C⁻¹ * ‖f‖ ≤ C⁻¹ * C :=
          mul_le_mul_of_nonneg_left hfnorm (inv_nonneg.mpr hC.le)
        _ = 1 := inv_mul_cancel₀ hC.ne'
    have hglip : LipschitzWith 1 g := by
      apply LipschitzWith.mk_one
      intro x y
      change dist (C⁻¹ * f x) (C⁻¹ * f y) ≤ dist x y
      rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hC)]
      calc
        C⁻¹ * |f x - f y| ≤ C⁻¹ * ((L : ℝ) * dist x y) :=
          mul_le_mul_of_nonneg_left (hf.dist_le_mul x y) (inv_nonneg.mpr hC.le)
        _ ≤ C⁻¹ * (C * dist x y) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hL dist_nonneg) (inv_nonneg.mpr hC.le)
        _ = dist x y := by rw [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul]
    have hsmall : Tendsto
        (fun n : ℕ => |(∫ x, g x ∂mu n) - ∫ x, g x ∂nu|) atTop (𝓝 0) := by
      apply squeeze_zero (fun n => abs_nonneg _) (fun n => ?_) hBL
      exact le_csSup (I043BLAux.testValues_bounds (mu n) nu).2
        ⟨g, hgnorm, hglip, rfl⟩
    have hgweak : Tendsto (fun n : ℕ => ∫ x, g x ∂mu n)
        atTop (𝓝 (∫ x, g x ∂nu)) := by
      apply tendsto_iff_dist_tendsto_zero.mpr
      exact hsmall
    have hfint : ∀ n : ℕ, Integrable f (mu n) := fun n => f.integrable (mu n)
    have hfnu : Integrable f nu := f.integrable nu
    have hgint : ∀ n : ℕ, Integrable g (mu n) := fun n => g.integrable (mu n)
    have hgnu : Integrable g nu := g.integrable nu
    have hfg (x : alpha) : f x = C * g x := by
      change f x = C * (C⁻¹ * f x)
      rw [← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul]
    have hmu_eq (n : ℕ) :
        (∫ x, f x ∂mu n) = C * (∫ x, g x ∂mu n) := by
      calc
        (∫ x, f x ∂mu n) = ∫ x, C * g x ∂mu n :=
          integral_congr_ae (Eventually.of_forall hfg)
        _ = C * (∫ x, g x ∂mu n) := integral_const_mul C _
    have hnu_eq : (∫ x, f x ∂nu) = C * (∫ x, g x ∂nu) := by
      calc
        (∫ x, f x ∂nu) = ∫ x, C * g x ∂nu :=
          integral_congr_ae (Eventually.of_forall hfg)
        _ = C * (∫ x, g x ∂nu) := integral_const_mul C _
    rw [hnu_eq]
    exact (hgweak.const_mul C).congr (fun n => (hmu_eq n).symm)
  let p : ℕ → ProbabilityMeasure alpha := fun n => ⟨mu n, hmu n⟩
  let q : ProbabilityMeasure alpha := ⟨nu, hnu⟩
  have hp : Tendsto p atTop (𝓝 q) := by
    apply MeasureTheory.tendsto_iff_forall_lipschitz_integral_tendsto.mpr
    intro f hfbounded hflip
    obtain ⟨L, hL⟩ := hflip
    let f' : alpha →ᵇ ℝ :=
      { toFun := f
        continuous_toFun := hL.continuous
        map_bounded' := hfbounded }
    exact htest f' L hL
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hp F

end NlsGge.ThirdConsultation.I.I044Aux

end
