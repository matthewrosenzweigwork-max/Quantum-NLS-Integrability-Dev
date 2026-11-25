import NlsGge.Analysis.PhysicalReflectedSeries

set_option autoImplicit false
noncomputable section
namespace NlsGge.Analysis
open NlsGge.Pilot

/-- Literal source exclusions r≠0,s≠0, independent of the physical coefficient mode. -/
def sourceNonresonantPairs : Set (ℤ × ℤ) := {rs | rs.1 ≠ 0 ∧ rs.2 ≠ 0}

theorem source_double_kernel_support (a : ℤ → ℝ) (n : ℤ) :
    Function.support (fun rs : ℤ × ℤ => a (n + rs.1 + rs.2) *
      inverseSquare rs.1 * inverseSquare rs.2) ⊆ sourceNonresonantPairs := by
  intro rs hrs
  change a (n + rs.1 + rs.2) * inverseSquare rs.1 * inverseSquare rs.2 ≠ 0 at hrs
  constructor
  · intro h
    exact hrs (by simp [h])
  · intro h
    exact hrs (by simp [h])

theorem physicalH1_source_nonres_double_summable (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (n : ℤ) :
    Summable (fun rs : sourceNonresonantPairs =>
      ‖physicalFourier u (n + rs.val.1 + rs.val.2)‖ ^ 2 *
        inverseSquare rs.val.1 * inverseSquare rs.val.2) :=
  (physicalH1_source_double_summable u hu n).subtype sourceNonresonantPairs

theorem physicalH1_source_nonres_double_tsum_eq (u : PhysicalL2) (n : ℤ) :
    (∑' rs : sourceNonresonantPairs, ‖physicalFourier u (n + rs.val.1 + rs.val.2)‖ ^ 2 *
      inverseSquare rs.val.1 * inverseSquare rs.val.2) =
      ∑' rs : ℤ × ℤ, ‖physicalFourier u (n + rs.1 + rs.2)‖ ^ 2 *
        inverseSquare rs.1 * inverseSquare rs.2 :=
  tsum_subtype_eq_of_support_subset (source_double_kernel_support
    (fun p => ‖physicalFourier u p‖ ^ 2) n)

theorem physicalH1_source_nonres_double_tsum_bound (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (n : ℤ) :
    (∑' rs : sourceNonresonantPairs, ‖physicalFourier u (n + rs.val.1 + rs.val.2)‖ ^ 2 *
      inverseSquare rs.val.1 * inverseSquare rs.val.2) ≤
      (2 * uniformConvolutionConstant / (1 + (n : ℝ) ^ 2)) *
        ‖physicalSobolevL2 1 u hu‖ ^ 2 := by
  have hs := physicalH1_source_nonres_double_summable u hu n
  rw [physicalH1_source_nonres_double_tsum_eq]
  exact physicalH1_source_double_tsum_bound u hu n

theorem reflected_double_kernel_support (a : ℤ → ℝ) (n : ℤ) :
    Function.support (fun rs : ℤ × ℤ => a (-(n + rs.1 + rs.2)) *
      inverseSquare rs.1 * inverseSquare rs.2) ⊆ sourceNonresonantPairs :=
  source_double_kernel_support (fun p => a (-p)) n

theorem physicalH1_reflected_nonres_double_summable (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (n : ℤ) :
    Summable (fun rs : sourceNonresonantPairs =>
      ‖physicalFourier u (-(n + rs.val.1 + rs.val.2))‖ ^ 2 *
        inverseSquare rs.val.1 * inverseSquare rs.val.2) :=
  (physicalH1_reflected_double_summable u hu n).subtype sourceNonresonantPairs

theorem physicalH1_reflected_nonres_double_tsum_eq (u : PhysicalL2) (n : ℤ) :
    (∑' rs : sourceNonresonantPairs, ‖physicalFourier u (-(n + rs.val.1 + rs.val.2))‖ ^ 2 *
      inverseSquare rs.val.1 * inverseSquare rs.val.2) =
      ∑' rs : ℤ × ℤ, ‖physicalFourier u (-(n + rs.1 + rs.2))‖ ^ 2 *
        inverseSquare rs.1 * inverseSquare rs.2 :=
  tsum_subtype_eq_of_support_subset (reflected_double_kernel_support
    (fun p => ‖physicalFourier u p‖ ^ 2) n)

theorem physicalH1_reflected_nonres_double_tsum_bound (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (n : ℤ) :
    (∑' rs : sourceNonresonantPairs, ‖physicalFourier u (-(n + rs.val.1 + rs.val.2))‖ ^ 2 *
      inverseSquare rs.val.1 * inverseSquare rs.val.2) ≤
      (2 * uniformConvolutionConstant / (1 + (n : ℝ) ^ 2)) *
        ‖physicalSobolevL2 1 u hu‖ ^ 2 := by
  have hs := physicalH1_reflected_nonres_double_summable u hu n
  rw [physicalH1_reflected_nonres_double_tsum_eq]
  exact physicalH1_reflected_double_tsum_bound u hu n

end NlsGge.Analysis
