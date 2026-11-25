import QuantumNLS.TerraMultiRound43RatioBall
import QuantumNLS.TerraMultiRound43FixedBridge

/-! Identification of every positive signed Fourier-ball fixed point with the
independently constructed small L∞ ratio, for nonzero physical fields. -/
set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Filter
namespace QuantumNLS.TerraMultiRound43SolutionAgreement
open QuantumNLS.PhysicalTensor QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.ComplexifiedSobolevField QuantumNLS.TerraMultiRound39PhysicalBall
open QuantumNLS.RootH1RatioOperator QuantumNLS.RootH1RatioNonlinear
open QuantumNLS.RootH1RatioBounds QuantumNLS.TerraMultiRound43RatioBall
open QuantumNLS.TerraMultiRound43FixedBridge

theorem positive_solution_agreement_eventually (L : ℝ) [hLf : Fact (0 < L)] {a : ℝ}
    (ha : 1 / 2 < a) (κ : ℝ) (hκ : 0 < κ) (u : Ell2)
    (hu : fieldMap L a (by linarith : (0 : ℝ) ≤ a) u ≠ 0) :
    ∃ B : ℝ, 0 < B ∧ ∀ Y : ℝ, B ≤ Y → ∀ r : Ell2,
      ‖r‖ ≤ 2 * ‖u‖ / Y →
      ∀ (hY : 0 < Y), physicalT hLf.out ha (abs_pos.mpr hY.ne') κ u r = r →
      ∃ (hlog : Real.log 3 ≤ Y * L)
        (hsmall : 16 * κ * ‖fieldMap L a (by linarith : (0 : ℝ) ≤ a) u‖ ^ 2 ≤ Y),
        fieldMap L a (by linarith : (0 : ℝ) ≤ a) r =
          ratioL2 hY hlog hκ.le (fieldMap L a (by linarith : (0 : ℝ) ≤ a) u) hsmall := by
  let U := fieldMap L a (by linarith : (0 : ℝ) ≤ a) u
  obtain ⟨B₀, hB₀, hball⟩ := fourier_ball_in_ratio_ball L ha u hu
  refine ⟨max B₀ (max (Real.log 3 / L) (16 * κ * ‖U‖ ^ 2)),
    lt_of_lt_of_le hB₀ (le_max_left _ _), ?_⟩
  intro Y hYB r hrn hY hr
  have hlog : Real.log 3 ≤ Y * L := by
    have h := (le_max_left (Real.log 3 / L) (16 * κ * ‖U‖ ^ 2)).trans
      ((le_max_right _ _).trans hYB)
    have h' := (div_le_iff₀ hLf.out).mp h
    simpa [mul_comm] using h'
  have hsmall : 16 * κ * ‖U‖ ^ 2 ≤ Y :=
    (le_max_right (Real.log 3 / L) (16 * κ * ‖U‖ ^ 2)).trans
      ((le_max_right _ _).trans hYB)
  obtain ⟨s, hs, hsn⟩ := hball Y ((le_max_left _ _).trans hYB) r hrn
  have hmap := fieldMap_physicalT L ha hY κ u r s hs
  rw [hr] at hmap
  have hfix : ratioMap hY hlog κ U s = s := by
    apply Lp.ext
    have hae := coe_infinityResolvent hY hlog (forcing κ U s)
    filter_upwards [hae, hs] with z hz hz'
    change infinityResolvent hY hlog (forcing κ U s) z = s z
    rw [hz, ← hmap, ← hz']
  have heq : s = ratio hY hlog hκ.le U hsmall := ratio_unique hY hlog hκ.le U hsmall hsn hfix
  refine ⟨hlog, hsmall, ?_⟩
  apply Lp.ext
  have hratiol2 := ratioL2_ae hY hlog hκ.le U hsmall
  filter_upwards [hs, hratiol2] with z hz hz'
  rw [← hz, heq, hz']

#print axioms positive_solution_agreement_eventually
end QuantumNLS.TerraMultiRound43SolutionAgreement
