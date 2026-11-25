import NlsGge.Hierarchy.FullEnergySpectralIdentification38
import NlsGge.Hierarchy.FullEnergyExistenceW01_38
import NlsGge.Spectral.ActualTraceFormulaQ024E02_38
import Mathlib.Tactic

/-! W-F06a: the moment inequality `F:eq:moment` on the finite plane.
`Q_{2j} ≥ H^j / M^{j-1} ≥ H^{(j+1)/2}`, `H ≥ ∫|u|⁴ ≥ M²`, with `M = Q₀`, `H = Q₂`. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open NlsGge.Pilot NlsGge.SpectralFoundations MeasureTheory
open scoped ContDiff BigOperators

/-- Target 1: local formula for `Q₂` on the plane. -/
theorem planeQ2_local38 (N : ℕ) (z : FourierPlane N) :
    localCharge38 (planeReal N z) 1 =
      ∫ x in (0:ℝ)..1, (‖planeReal N (derivativePlane N z) x‖ ^ 2 + ‖planeReal N z x‖ ^ 4) := by
  unfold localCharge38
  rw [complexQ2_local_formula_Q024 _ (planeReal_smooth38 N z) (planeReal_periodic N z),
    deriv_planeReal]

theorem planeQ0_local38 (N : ℕ) (z : FourierPlane N) :
    localCharge38 (planeReal N z) 0 = ∫ x in (0:ℝ)..1, ‖planeReal N z x‖ ^ 2 := by
  unfold localCharge38
  exact complexQ0_local_formula_Q024 _

theorem continuous_planeReal38 (N : ℕ) (z : FourierPlane N) : Continuous (planeReal N z) :=
  (planeReal_smooth38 N z).continuous

/-- Target 2: `M² ≤ ∫₀¹ |u|⁴` (Cauchy–Schwarz on the unit interval). -/
theorem planeMass_sq_le_quartic38 (N : ℕ) (z : FourierPlane N) :
    (localCharge38 (planeReal N z) 0) ^ 2 ≤ ∫ x in (0:ℝ)..1, ‖planeReal N z x‖ ^ 4 := by
  rw [planeQ0_local38]
  set m := ∫ x in (0:ℝ)..1, ‖planeReal N z x‖ ^ 2 with hm
  have hc : Continuous (planeReal N z) := continuous_planeReal38 N z
  have h2 : IntervalIntegrable (fun x => ‖planeReal N z x‖ ^ 2) MeasureTheory.volume 0 1 :=
    (hc.norm.pow 2).intervalIntegrable _ _
  have h4 : IntervalIntegrable (fun x => ‖planeReal N z x‖ ^ 4) MeasureTheory.volume 0 1 :=
    (hc.norm.pow 4).intervalIntegrable _ _
  have hlow : IntervalIntegrable (fun x => 2 * m * ‖planeReal N z x‖ ^ 2 - m ^ 2)
      MeasureTheory.volume 0 1 :=
    (h2.const_mul _).sub intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on (zero_le_one' ℝ) hlow h4 (fun x _ => by
    nlinarith [sq_nonneg (‖planeReal N z x‖ ^ 2 - m)])
  rw [intervalIntegral.integral_sub (h2.const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul] at hmono
  simp at hmono
  nlinarith [hmono]

/-- Target 3: `M² ≤ H`. -/
theorem planeQ2_ge_mass_sq38 (N : ℕ) (z : FourierPlane N) :
    (localCharge38 (planeReal N z) 0) ^ 2 ≤ localCharge38 (planeReal N z) 1 := by
  refine (planeMass_sq_le_quartic38 N z).trans ?_
  rw [planeQ2_local38]
  have hc : Continuous (planeReal N z) := continuous_planeReal38 N z
  have hd : Continuous (planeReal N (derivativePlane N z)) :=
    continuous_planeReal38 N (derivativePlane N z)
  refine intervalIntegral.integral_mono_on (zero_le_one' ℝ)
    ((hc.norm.pow 4).intervalIntegrable _ _)
    (((hd.norm.pow 2).add (hc.norm.pow 4)).intervalIntegrable _ _) (fun x _ => ?_)
  have := sq_nonneg ‖planeReal N (derivativePlane N z) x‖
  linarith

/-- Tangent-line (Bernoulli) Jensen inequality for a nonnegative weight. -/
theorem jensen_moment38 (f w : ℝ → ℝ) (j : ℕ) (hj : 1 ≤ j) (hf : ∀ t, 0 ≤ f t)
    (hw : ∀ t, 0 ≤ w t) (iw : Integrable w) (ifw : Integrable (fun t => f t * w t))
    (ijw : Integrable (fun t => f t ^ j * w t)) :
    (∫ t, f t * w t) ^ j ≤ (∫ t, w t) ^ (j - 1) * ∫ t, f t ^ j * w t := by
  set m := ∫ t, w t with hm
  set A := ∫ t, f t * w t with hA
  set B := ∫ t, f t ^ j * w t with hB
  have hm0 : 0 ≤ m := integral_nonneg hw
  have hA0 : 0 ≤ A := integral_nonneg fun t => mul_nonneg (hf t) (hw t)
  have hB0 : 0 ≤ B := integral_nonneg fun t => mul_nonneg (pow_nonneg (hf t) _) (hw t)
  rcases hm0.eq_or_lt with hm0' | hmpos
  · -- m = 0 : w = 0 a.e.
    have hz : w =ᵐ[volume] 0 := (integral_eq_zero_iff_of_nonneg hw iw).1 hm0'.symm
    have hA' : A = 0 := by
      rw [hA]
      have : (fun t => f t * w t) =ᵐ[volume] 0 := hz.mono fun t ht => by simp [ht]
      rw [integral_congr_ae this]; simp
    rw [hA']
    rw [zero_pow (by omega)]
    exact mul_nonneg (pow_nonneg hm0 _) hB0
  · rcases hA0.eq_or_lt with hA0' | hApos
    · rw [← hA0', zero_pow (by omega)]
      exact mul_nonneg (pow_nonneg hm0 _) hB0
    · set a := A / m with ha
      have hapos : 0 < a := div_pos hApos hmpos
      clear_value a
      have hpt : ∀ t, (a ^ j * (1 - j)) * w t + (j * a ^ j / a) * (f t * w t) ≤
          f t ^ j * w t := by
        intro t
        have hb := one_add_mul_le_pow (a := f t / a - 1) (by
          have : 0 ≤ f t / a := div_nonneg (hf t) hapos.le
          linarith) j
        have hfa : f t ^ j = a ^ j * (f t / a) ^ j := by
          rw [div_pow]; field_simp
        have : a ^ j * (1 + j * (f t / a - 1)) ≤ f t ^ j := by
          rw [hfa]
          exact mul_le_mul_of_nonneg_left (by simpa using hb) (pow_pos hapos _).le
        have := mul_le_mul_of_nonneg_right this (hw t)
        calc (a ^ j * (1 - j)) * w t + (j * a ^ j / a) * (f t * w t)
            = (a ^ j * (1 + j * (f t / a - 1))) * w t := by field_simp; ring
          _ ≤ _ := this
      have hint := integral_mono (((iw.const_mul (a ^ j * (1 - j))).add
        (ifw.const_mul (j * a ^ j / a)))) ijw hpt
      simp only [Pi.add_apply] at hint
      rw [integral_add (iw.const_mul _) (ifw.const_mul _), integral_const_mul,
        integral_const_mul] at hint
      have hAm : A = a * m := by rw [ha]; field_simp
      have key : a ^ j * m ≤ B := by
        have : (a ^ j * (1 - j)) * m + (j * a ^ j / a) * A = a ^ j * m := by
          rw [hAm]; field_simp; ring
        linarith
      calc A ^ j = (a * m) ^ j := by rw [hAm]
        _ = a ^ j * m * m ^ (j - 1) := by
          obtain ⟨k, hk⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
          subst hk
          simp only [Nat.add_sub_cancel]
          ring
        _ ≤ B * m ^ (j - 1) := mul_le_mul_of_nonneg_right key (pow_nonneg hm0 _)
        _ = _ := by ring

/-- Target 4: `H^j ≤ M^{j-1} Q_{2j}` for `j ≥ 1` (the cleared form of `Q_{2j} ≥ H^j/M^{j-1}`). -/
theorem planeMoment38 (N : ℕ) (z : FourierPlane N) (j : ℕ) (hj : 1 ≤ j) :
    (localCharge38 (planeReal N z) 1) ^ j ≤
      (localCharge38 (planeReal N z) 0) ^ (j - 1) * localCharge38 (planeReal N z) (j) := by
  obtain ⟨i0, h0⟩ := plane_trace38 N z 0
  obtain ⟨i1, h1⟩ := plane_trace38 N z 1
  obtain ⟨ij, hjj⟩ := plane_trace38 N z j
  set v := actualGapHeightE02_38 (planeL2 N z) with hv
  have hv0 : ∀ t, 0 ≤ v t := fun t => actualGapHeightE02_38_nonneg _ _
  have e0 : (fun t : ℝ => (2*t)^(2*0) * v t) = v := by funext t; simp
  rw [e0] at i0 h0
  have key := jensen_moment38 (fun t => (2*t)^2) v j hj (fun t => by positivity) hv0 i0
    (by simpa using i1) (by
      refine ij.congr (Filter.Eventually.of_forall fun t => ?_)
      simp only [← pow_mul])
  have eA : ∫ t, (2*t)^2 * v t = ∫ t, (2*t)^(2*1) * v t := by simp
  have eB : ∫ t, ((2*t)^2) ^ j * v t = ∫ t, (2*t)^(2*j) * v t := by
    congr 1; funext t; rw [← pow_mul]
  rw [eA, eB] at key
  rw [h1, h0, hjj]
  have hc : (0:ℝ) ≤ 2 / Real.pi := by positivity
  set A := ∫ t, (2*t)^(2*1) * v t
  set m := ∫ t, v t
  set B := ∫ t, (2*t)^(2*j) * v t
  have hmpos : 0 ≤ m := integral_nonneg hv0
  -- (c A)^j ≤ (c m)^(j-1) (c B) = c^j m^(j-1) B
  have hj' : j = (j - 1) + 1 := by omega
  calc (2 / Real.pi * A) ^ j = (2 / Real.pi) ^ j * A ^ j := mul_pow _ _ _
    _ ≤ (2 / Real.pi) ^ j * (m ^ (j - 1) * B) := mul_le_mul_of_nonneg_left key (pow_nonneg hc _)
    _ = (2 / Real.pi * m) ^ (j - 1) * (2 / Real.pi * B) := by
        obtain ⟨k, hk⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
        subst hk
        simp only [Nat.add_sub_cancel]
        ring

/-- Target 5: `H^{(j+1)/2} ≤ Q_{2j}` in square-root form: `(√H)^{j+1} ≤ Q_{2j}`. -/
theorem planeMoment_sqrt38 (N : ℕ) (z : FourierPlane N) (j : ℕ) (hj : 1 ≤ j) :
    (Real.sqrt (localCharge38 (planeReal N z) 1)) ^ (j + 1) ≤ localCharge38 (planeReal N z) j := by
  set M := localCharge38 (planeReal N z) 0 with hM
  set H := localCharge38 (planeReal N z) 1 with hH
  have hM0 : 0 ≤ M := localCharge38_plane_nonneg N z 0
  have hH0 : 0 ≤ H := localCharge38_plane_nonneg N z 1
  have hQ0 : 0 ≤ localCharge38 (planeReal N z) j := localCharge38_plane_nonneg N z j
  have hmom := planeMoment38 N z j hj
  have hMs : M ≤ Real.sqrt H := Real.le_sqrt_of_sq_le (planeQ2_ge_mass_sq38 N z)
  set s := Real.sqrt H with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hHs : H = s ^ 2 := (Real.sq_sqrt hH0).symm
  rcases hs0.eq_or_lt with h | hspos
  · rw [← h, zero_pow (by omega)]; exact hQ0
  · have h1 : s ^ (2 * j) ≤ s ^ (j - 1) * localCharge38 (planeReal N z) j := by
      calc s ^ (2 * j) = H ^ j := by rw [hHs, pow_mul]
        _ ≤ M ^ (j - 1) * _ := hmom
        _ ≤ s ^ (j - 1) * _ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hM0 hMs _) hQ0
    have h2 : s ^ (j - 1) * s ^ (j + 1) = s ^ (2 * j) := by
      rw [← pow_add]; congr 1; omega
    rw [← h2] at h1
    exact le_of_mul_le_mul_left h1 (pow_pos hspos _)

/-- Corollary: `Q_{2j} ≥ M^{j+1}`. -/
theorem planeMoment_mass38 (N : ℕ) (z : FourierPlane N) (j : ℕ) (hj : 1 ≤ j) :
    (localCharge38 (planeReal N z) 0) ^ (j + 1) ≤ localCharge38 (planeReal N z) j := by
  refine le_trans ?_ (planeMoment_sqrt38 N z j hj)
  have hM0 : 0 ≤ localCharge38 (planeReal N z) 0 := localCharge38_plane_nonneg N z 0
  exact pow_le_pow_left₀ hM0 (Real.le_sqrt_of_sq_le (planeQ2_ge_mass_sq38 N z)) _

end NlsGge.HierarchyRiccati.Core
