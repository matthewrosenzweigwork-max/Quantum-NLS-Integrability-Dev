import NlsGge.GK38.GradFundamentalCubic

/-! # K1: pointwise cubic gradient residual bounds.
GK Chapter I, Lemma4.3. Two scalar squared masses are bounded before finite
spectral windows or any real tsum are used.
-/
set_option autoImplicit false
open Set
open scoped Matrix.Norms.Elementwise
namespace NlsGge.GK38
noncomputable section

def k1CyclicVec38 (M B : PairMat38) : PairVec38 :=
  ![-(M * B * M.adjugate) 1 0, (M * B * M.adjugate) 0 1]

theorem scaled_gradDiscrim38_cyclic (φ : PotPair) (z : ℂ) (t : Icc (0 : ℝ) 1) :
    Complex.I • gradDiscrim38 φ z t = k1CyclicVec38 (fundPair φ z t) (monodromyPair φ z) := by
  rw [gradDiscrim38_cyclic, k1FundContEndpoint38]
  ext k
  fin_cases k <;> simp [k1CyclicVec38, Complex.I_sq, ← mul_assoc]

theorem scaled_gradAntiDiscrim38_cyclic (φ : PotPair) (z : ℂ) (t : Icc (0 : ℝ) 1) :
    Complex.I • gradAntiDiscrim38 φ z t =
      k1CyclicVec38 (fundPair φ z t) (k1SwapMat38 * monodromyPair φ z) := by
  rw [gradAntiDiscrim38_cyclic, k1FundContEndpoint38]
  ext k
  fin_cases k <;> simp [k1CyclicVec38, Complex.I_sq, ← mul_assoc]

theorem k1CyclicVec38_mass_error (M B m b : PairMat38) (H : ℝ) (hH : 0 ≤ H)
    (hM : ‖M‖ ≤ H) (hB : ‖B‖ ≤ H) (hm : ‖m‖ ≤ H) (hb : ‖b‖ ≤ H) :
    ‖(k1CyclicVec38 M B - k1CyclicVec38 m b) 0‖ ^ 2 +
      ‖(k1CyclicVec38 M B - k1CyclicVec38 m b) 1‖ ^ 2 ≤
        256 * H ^ 4 * (‖M - m‖ ^ 2 + ‖B - b‖ ^ 2) := by
  have ha : ‖M.adjugate - m.adjugate‖ ≤ ‖M - m‖ := by
    rw [← k1AdjugateSub38]
    exact k1AdjugateNorm38 _
  have ht := k1MatrixTripleError38 M B M.adjugate m b m.adjugate H hH hB
    ((k1AdjugateNorm38 M).trans hM) hm hb
  have ht' : ‖M * B * M.adjugate - m * b * m.adjugate‖ ≤
      4 * H ^ 2 * (2 * ‖M - m‖ + ‖B - b‖) := by
    refine ht.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  have hc (k : Fin 2) : ‖(k1CyclicVec38 M B - k1CyclicVec38 m b) k‖ ≤
      4 * H ^ 2 * (2 * ‖M - m‖ + ‖B - b‖) := by
    fin_cases k
    · have he := (Matrix.norm_entry_le_entrywise_sup_norm
        (M * B * M.adjugate - m * b * m.adjugate) (i := 1) (j := 0)).trans ht'
      change ‖-(M * B * M.adjugate) 1 0 - -(m * b * m.adjugate) 1 0‖ ≤ _
      rw [neg_sub_neg, norm_sub_rev]
      exact he
    · exact (Matrix.norm_entry_le_entrywise_sup_norm
        (M * B * M.adjugate - m * b * m.adjugate) (i := 0) (j := 1)).trans ht'
  have h0 := pow_le_pow_left₀ (norm_nonneg _) (hc 0) 2
  have h1 := pow_le_pow_left₀ (norm_nonneg _) (hc 1) 2
  have hsq : (2 * ‖M - m‖ + ‖B - b‖) ^ 2 ≤
      8 * (‖M - m‖ ^ 2 + ‖B - b‖ ^ 2) := by
    nlinarith [sq_nonneg (2 * ‖M - m‖ - ‖B - b‖), sq_nonneg ‖B - b‖]
  calc
    _ ≤ 2 * (4 * H ^ 2 * (2 * ‖M - m‖ + ‖B - b‖)) ^ 2 := by linarith
    _ = (32 * H ^ 4) * (2 * ‖M - m‖ + ‖B - b‖) ^ 2 := by ring
    _ ≤ (32 * H ^ 4) * (8 * (‖M - m‖ ^ 2 + ‖B - b‖ ^ 2)) := by gcongr
    _ = _ := by ring

end
end NlsGge.GK38
