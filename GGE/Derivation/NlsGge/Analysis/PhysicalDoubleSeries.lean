import NlsGge.Analysis.PhysicalH1Bounds
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

set_option autoImplicit false
noncomputable section

namespace NlsGge.Analysis

open NlsGge.Pilot

theorem physicalH1_weighted_summable (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    Summable (fun p : ℤ => (1 + (p : ℝ) ^ 2) * ‖physicalFourier u p‖ ^ 2) := by
  simpa only [SobolevSquareSummable, japaneseBracket_h1_weight] using hu

theorem physicalH1_convolution_summable (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (n : ℤ) :
    Summable (fun p : ℤ => ‖physicalFourier u p‖ ^ 2 * inverseSquareConvolution (p - n)) :=
  summable_weighted_convolution _ (fun p => sq_nonneg _) (physicalH1_weighted_summable u hu) n

theorem physicalH1_double_convolution_summable (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (n : ℤ) :
    Summable (fun pr : ℤ × ℤ => ‖physicalFourier u pr.1‖ ^ 2 *
      convolutionTerm (pr.1 - n) pr.2) := by
  have hfiber : ∀ p : ℤ, Summable (fun r : ℤ =>
      ‖physicalFourier u p‖ ^ 2 * convolutionTerm (p - n) r) := by
    intro p
    exact (summable_convolutionTerm (p - n)).mul_left (‖physicalFourier u p‖ ^ 2)
  have houter : Summable (fun p : ℤ => ∑' r : ℤ,
      ‖physicalFourier u p‖ ^ 2 * convolutionTerm (p - n) r) := by
    simpa only [tsum_mul_left, inverseSquareConvolution] using
      physicalH1_convolution_summable u hu n
  exact (summable_prod_of_nonneg
    (f := fun pr : ℤ × ℤ => ‖physicalFourier u pr.1‖ ^ 2 * convolutionTerm (pr.1 - n) pr.2)
    (fun pr => mul_nonneg (sq_nonneg _) (convolutionTerm_nonneg _ _))).2 ⟨hfiber, houter⟩

theorem physicalH1_double_convolution_tsum_eq (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (n : ℤ) :
    (∑' pr : ℤ × ℤ, ‖physicalFourier u pr.1‖ ^ 2 * convolutionTerm (pr.1 - n) pr.2) =
      ∑' p : ℤ, ‖physicalFourier u p‖ ^ 2 * inverseSquareConvolution (p - n) := by
  rw [(physicalH1_double_convolution_summable u hu n).tsum_prod]
  simp only [tsum_mul_left, inverseSquareConvolution]

/-- Exact source indexing p=n+r+s; it preserves every signed mode and its zero terms. -/
def sourceConvolutionIndex (n : ℤ) : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun rs := (n + rs.1 + rs.2, rs.1)
  invFun pr := (pr.2, pr.1 - n - pr.2)
  left_inv rs := by ext <;> dsimp <;> omega
  right_inv pr := by ext <;> dsimp <;> omega

theorem sourceConvolutionIndex_term (u : PhysicalL2) (n : ℤ) (rs : ℤ × ℤ) :
    ‖physicalFourier u ((sourceConvolutionIndex n rs).1)‖ ^ 2 *
        convolutionTerm ((sourceConvolutionIndex n rs).1 - n) ((sourceConvolutionIndex n rs).2) =
      ‖physicalFourier u (n + rs.1 + rs.2)‖ ^ 2 * inverseSquare rs.1 * inverseSquare rs.2 := by
  simp only [sourceConvolutionIndex, Equiv.coe_fn_mk, convolutionTerm]
  have hi : n + rs.1 + rs.2 - n - rs.1 = rs.2 := by omega
  rw [hi, mul_assoc]

theorem physicalH1_source_double_summable (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (n : ℤ) :
    Summable (fun rs : ℤ × ℤ => ‖physicalFourier u (n + rs.1 + rs.2)‖ ^ 2 *
      inverseSquare rs.1 * inverseSquare rs.2) := by
  have hs := (physicalH1_double_convolution_summable u hu n).comp_injective
    (sourceConvolutionIndex n).injective
  exact hs.congr (fun rs => sourceConvolutionIndex_term u n rs)

theorem physicalH1_source_double_tsum_eq (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (n : ℤ) :
    (∑' rs : ℤ × ℤ, ‖physicalFourier u (n + rs.1 + rs.2)‖ ^ 2 *
      inverseSquare rs.1 * inverseSquare rs.2) =
      ∑' p : ℤ, ‖physicalFourier u p‖ ^ 2 * inverseSquareConvolution (p - n) := by
  calc
    _ = ∑' pr : ℤ × ℤ, ‖physicalFourier u pr.1‖ ^ 2 * convolutionTerm (pr.1 - n) pr.2 := by
      calc
        _ = ∑' rs : ℤ × ℤ, ‖physicalFourier u ((sourceConvolutionIndex n rs).1)‖ ^ 2 *
            convolutionTerm ((sourceConvolutionIndex n rs).1 - n) ((sourceConvolutionIndex n rs).2) :=
          tsum_congr (fun rs => (sourceConvolutionIndex_term u n rs).symm)
        _ = _ := (sourceConvolutionIndex n).tsum_eq
          (fun pr : ℤ × ℤ => ‖physicalFourier u pr.1‖ ^ 2 * convolutionTerm (pr.1 - n) pr.2)
    _ = _ := physicalH1_double_convolution_tsum_eq u hu n

theorem physicalH1_source_double_tsum_bound (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (n : ℤ) :
    (∑' rs : ℤ × ℤ, ‖physicalFourier u (n + rs.1 + rs.2)‖ ^ 2 *
      inverseSquare rs.1 * inverseSquare rs.2) ≤
      (2 * uniformConvolutionConstant / (1 + (n : ℝ) ^ 2)) *
        ‖physicalSobolevL2 1 u hu‖ ^ 2 := by
  have hs := physicalH1_source_double_summable u hu n
  rw [physicalH1_source_double_tsum_eq u hu n]
  exact physicalH1_convolution_tsum_bound u hu n

end NlsGge.Analysis
