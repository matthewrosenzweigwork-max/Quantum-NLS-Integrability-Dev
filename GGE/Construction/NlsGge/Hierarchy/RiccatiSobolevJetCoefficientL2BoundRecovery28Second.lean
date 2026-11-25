import NlsGge.Hierarchy.RiccatiPhysicalH1EnergyCandidateAfterFourierCoefficientPrerequisite
import NlsGge.Sobolev.SourceEmbeddings
import NlsGge.Sobolev.WeightedHilbert
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open NlsGge.Pilot

/-- The physical order-`k` Fourier coefficient candidate on the concrete
weighted Sobolev carrier. This definition alone does not identify it with a
classical derivative. -/
def riccatiSobolevJetCoefficientL2Recovery28Second
    (m k : ℕ) (x : SobolevHilbert (m : ℝ)) : ℤ → ℂ :=
  fun n => fourierMultiplier n ^ k *
    (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n

theorem riccatiSobolevJetCoefficient_norm_sqL2Recovery28Second
    (m k : ℕ) (x : SobolevHilbert (m : ℝ)) (n : ℤ) :
    ‖riccatiSobolevJetCoefficientL2Recovery28Second m k x n‖ ^ 2 =
      (2 * Real.pi) ^ (2 * k) * |(n : ℝ)| ^ (2 * k) *
        ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n‖ ^ 2 := by
  rw [riccatiSobolevJetCoefficientL2Recovery28Second,
    norm_mul, norm_pow, norm_fourierMultiplier]
  rw [mul_pow, ← pow_mul, show k * 2 = 2 * k by omega, mul_pow]

theorem riccatiSobolevJetCoefficient_square_leL2Recovery28Second
    (m k : ℕ) (hkm : k ≤ m) (x : SobolevHilbert (m : ℝ)) (n : ℤ) :
    ‖riccatiSobolevJetCoefficientL2Recovery28Second m k x n‖ ^ 2 ≤
      (2 * Real.pi) ^ (2 * k) *
        (sobolevModeWeight (m : ℝ) n *
          ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n‖ ^ 2) := by
  have hn : |(n : ℝ)| ≤ japaneseBracket n := by
    unfold japaneseBracket
    apply Real.le_sqrt_of_sq_le
    rw [sq_abs]
    linarith
  have hpowN : |(n : ℝ)| ^ (2 * k) ≤ japaneseBracket n ^ (2 * k) :=
    pow_le_pow_left₀ (abs_nonneg _) hn _
  have hpowB : japaneseBracket n ^ (2 * k) ≤ japaneseBracket n ^ (2 * m) :=
    pow_le_pow_right₀ (japaneseBracket_one_le n) (by omega)
  have hweight : sobolevModeWeight (m : ℝ) n = japaneseBracket n ^ (2 * m) := by
    unfold sobolevModeWeight
    have he : 2 * (m : ℝ) = ((2 * m : ℕ) : ℝ) := by push_cast; ring
    rw [he]
    exact Real.rpow_natCast _ _
  rw [riccatiSobolevJetCoefficient_norm_sqL2Recovery28Second, hweight]
  calc
    (2 * Real.pi) ^ (2 * k) * |(n : ℝ)| ^ (2 * k) *
        ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n‖ ^ 2 ≤
      (2 * Real.pi) ^ (2 * k) * japaneseBracket n ^ (2 * k) *
        ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n‖ ^ 2 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpowN (by positivity)) (sq_nonneg _)
    _ ≤ (2 * Real.pi) ^ (2 * k) * japaneseBracket n ^ (2 * m) *
        ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n‖ ^ 2 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpowB (by positivity)) (sq_nonneg _)
    _ = (2 * Real.pi) ^ (2 * k) *
        (japaneseBracket n ^ (2 * m) *
          ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n‖ ^ 2) := by ring

theorem riccatiSobolevJetCoefficients_l2SummableRecovery28
    (m k : ℕ) (hkm : k ≤ m) (x : SobolevHilbert (m : ℝ)) :
    Summable (fun n : ℤ =>
      ‖riccatiSobolevJetCoefficientL2Recovery28Second m k x n‖ ^ 2) := by
  let C : ℝ := (2 * Real.pi) ^ (2 * k)
  have hx : Summable (fun n : ℤ => sobolevModeWeight (m : ℝ) n *
      ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n‖ ^ 2) :=
    (weightedHilbert_hasSum (sobolevModeWeight (m : ℝ))
      (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x)).summable
  refine Summable.of_nonneg_of_le ?_ ?_ (hx.mul_left C)
  · intro n
    exact sq_nonneg _
  · intro n
    simpa only [C] using
      riccatiSobolevJetCoefficient_square_leL2Recovery28Second m k hkm x n

end NlsGge.HierarchyRiccati.Core

end
