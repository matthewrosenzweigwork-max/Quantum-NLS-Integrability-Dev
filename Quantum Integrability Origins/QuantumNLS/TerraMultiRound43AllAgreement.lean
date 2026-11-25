import QuantumNLS.TerraMultiRound43SolutionAgreement
import QuantumNLS.TerraMultiRound42ZeroField

/-! Positive solution agreement, including the zero physical field. -/
set_option autoImplicit false
noncomputable section
open Complex MeasureTheory
namespace QuantumNLS.TerraMultiRound43AllAgreement
open QuantumNLS.PhysicalTensor QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE2b
open QuantumNLS.ComplexifiedSobolevField QuantumNLS.TerraMultiRound39PhysicalBall
open QuantumNLS.RootH1RatioBounds QuantumNLS.TerraMultiRound42ZeroField
open QuantumNLS.TerraMultiRound43SolutionAgreement

lemma fieldMap_eq_zero_iff (L : ℝ) [Fact (0 < L)] {a : ℝ} (ha : 0 ≤ a) (u : Ell2) :
    fieldMap L a ha u = 0 ↔ u = 0 := by
  constructor
  · intro hu
    apply lp.ext
    funext k
    have hh := coeff_fieldMap L a ha u k
    rw [hu] at hh
    have hc0 : QuantumNLS.Fourier.coeff L (0 : L2T L) k = 0 := by
      rw [← QuantumNLS.Fourier.fourierL2_apply]
      simp
    have hzero : toField L a u k = 0 := by simpa only [hc0] using hh.symm
    change u k / ((pw L a k : ℝ) : ℂ) = 0 at hzero
    have hh' := congrArg (fun z : ℂ => z * ((pw L a k : ℝ) : ℂ)) hzero
    simpa [div_mul_cancel₀ _ (pw_ne_zero L a k)] using hh'
  · rintro rfl
    exact map_zero _

theorem positive_solution_agreement_all (L : ℝ) [hLf : Fact (0 < L)] {a : ℝ}
    (ha : 1 / 2 < a) (κ : ℝ) (hκ : 0 < κ) (u : Ell2) :
    ∃ B : ℝ, 0 < B ∧ ∀ Y : ℝ, B ≤ Y → ∀ r : Ell2,
      ‖r‖ ≤ 2 * ‖u‖ / Y →
      ∀ (hY : 0 < Y), physicalT hLf.out ha (abs_pos.mpr hY.ne') κ u r = r →
      ∃ (hlog : Real.log 3 ≤ Y * L)
        (hsmall : 16 * κ * ‖fieldMap L a (by linarith : (0 : ℝ) ≤ a) u‖ ^ 2 ≤ Y),
        fieldMap L a (by linarith : (0 : ℝ) ≤ a) r =
          ratioL2 hY hlog hκ.le (fieldMap L a (by linarith : (0 : ℝ) ≤ a) u) hsmall := by
  by_cases hu : fieldMap L a (by linarith : (0 : ℝ) ≤ a) u = 0
  · have hu0 : u = 0 := (fieldMap_eq_zero_iff L (by linarith) u).mp hu
    subst u
    refine ⟨max 1 (Real.log 3 / L), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
    intro Y hYB r hrn hY _
    have hlog : Real.log 3 ≤ Y * L := by
      have h := (le_max_right 1 (Real.log 3 / L)).trans hYB
      have h' := (div_le_iff₀ hLf.out).mp h
      simpa [mul_comm] using h'
    have hsmall : 16 * κ * ‖(0 : L2T L)‖ ^ 2 ≤ Y := by simpa using hY.le
    have hr : r = 0 := norm_eq_zero.mp (by simpa using hrn)
    subst r
    refine ⟨hlog, ?_, ?_⟩
    · simpa using hsmall
    · simpa using (ratioL2_zero hY hlog hκ.le hsmall).symm
  · exact positive_solution_agreement_eventually L ha κ hκ u hu

#print axioms fieldMap_eq_zero_iff
#print axioms positive_solution_agreement_all
end QuantumNLS.TerraMultiRound43AllAgreement
