import Mathlib
import NlsGge.Composition.Convolution

                                                                                                                                                                                                                                                                                                                                                              
set_option autoImplicit false
open scoped BigOperators

namespace NlsGge.ThirdConsultation.R
noncomputable section

def wNormL2 (w A : ℤ → ℝ) : ℝ :=
  Real.sqrt (∑' n : ℤ, (w n * A n) ^ 2)

def wConvNorm (w A B : ℤ → ℝ) : ℝ :=
  Real.sqrt (∑' n : ℤ,
    (w n * (∑' k : ℤ, A k * B (n - k))) ^ 2)


open NlsGge.ThirdConsultation.R in
theorem r084_weighted_conv_real (w r A B : ℤ → ℝ)
    (hr : NlsGge.Composition.RatioMajorant w r)
    (hA0 : ∀ n : ℤ, 0 ≤ A n) (hB0 : ∀ n : ℤ, 0 ≤ B n)
    (hA : Summable (fun n : ℤ => (w n * A n) ^ 2))
    (hB : Summable (fun n : ℤ => (w n * B n) ^ 2)) :
    (∀ n : ℤ, Summable (fun k : ℤ => A k * B (n - k))) ∧
    Summable (fun n : ℤ => (w n * (∑' k : ℤ, A k * B (n - k))) ^ 2) ∧
    wConvNorm w A B ≤
      2 * Real.sqrt (NlsGge.Composition.ratioNormSq r) * wNormL2 w A * wNormL2 w B := by
  obtain ⟨h1, h2, h3⟩ := NlsGge.Composition.weighted_conv_real hr hA0 hB0 hA hB
  refine ⟨h1, h2, ?_⟩
  have hR : 0 ≤ NlsGge.Composition.ratioNormSq r := by
    unfold NlsGge.Composition.ratioNormSq
    exact tsum_nonneg fun n => sq_nonneg _
  have hSA : 0 ≤ ∑' n : ℤ, (w n * A n) ^ 2 := tsum_nonneg fun n => sq_nonneg _
  have hSB : 0 ≤ ∑' n : ℤ, (w n * B n) ^ 2 := tsum_nonneg fun n => sq_nonneg _
  unfold wConvNorm wNormL2
  have hrhs : 2 * Real.sqrt (NlsGge.Composition.ratioNormSq r) *
      Real.sqrt (∑' n : ℤ, (w n * A n) ^ 2) * Real.sqrt (∑' n : ℤ, (w n * B n) ^ 2) =
      Real.sqrt (4 * NlsGge.Composition.ratioNormSq r * (∑' n : ℤ, (w n * A n) ^ 2) *
        (∑' n : ℤ, (w n * B n) ^ 2)) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hrhs]
  exact Real.sqrt_le_sqrt h3
