import NlsGge.GK38.GradFundamentalODE

/-! # K1: adjugate variation calculus for the traceless ZS coefficient. -/
set_option autoImplicit false
open Filter Topology MeasureTheory Set
namespace NlsGge.GK38
noncomputable section

/-- Pointwise AC negation, with the coherent complex metric instance. -/
theorem k1ACPointwiseNeg38 {f : ℝ → ℂ} (hf : AbsolutelyContinuousOnInterval f 0 1) :
    AbsolutelyContinuousOnInterval (fun s => -f s) 0 1 := by
  convert! hf.neg using 1 <;> rfl

/-- Pointwise AC sum of products, checked before the adjugate application. -/
theorem k1ACPointwiseAddMul38 {a b c d : ℝ → ℂ}
    (ha : AbsolutelyContinuousOnInterval a 0 1) (hb : AbsolutelyContinuousOnInterval b 0 1)
    (hc : AbsolutelyContinuousOnInterval c 0 1) (hd : AbsolutelyContinuousOnInterval d 0 1) :
    AbsolutelyContinuousOnInterval (fun s => a s * b s + c s * d s) 0 1 := by
  convert! (ha.smul hb).add (hc.smul hd) using 1 <;> rfl

theorem ac_adjugateEntry38 {M : ℝ → PairMat38}
    (hM : ∀ i j, AbsolutelyContinuousOnInterval (fun s => M s i j) 0 1) (i j : Fin 2) :
    AbsolutelyContinuousOnInterval (fun s => (M s).adjugate i j) 0 1 := by
  fin_cases i <;> fin_cases j
  · simpa [Matrix.adjugate_fin_two] using hM 1 1
  · simpa [Matrix.adjugate_fin_two] using k1ACPointwiseNeg38 (hM 0 1)
  · simpa [Matrix.adjugate_fin_two] using k1ACPointwiseNeg38 (hM 1 0)
  · simpa [Matrix.adjugate_fin_two] using hM 0 0

theorem hasDerivAt_adjugateEntry38 {M : ℝ → PairMat38} {M' : PairMat38} {s : ℝ}
    (hM : ∀ i j, HasDerivAt (fun r => M r i j) (M' i j) s) (i j : Fin 2) :
    HasDerivAt (fun r => (M r).adjugate i j) (M'.adjugate i j) s := by
  fin_cases i <;> fin_cases j
  · simpa [Matrix.adjugate_fin_two] using hM 1 1
  · simpa [Matrix.adjugate_fin_two] using (hM 0 1).fun_neg
  · simpa [Matrix.adjugate_fin_two] using (hM 1 0).fun_neg
  · simpa [Matrix.adjugate_fin_two] using hM 0 0

/-- Tracelessness identifies the derivative of the adjugate in dimension two. -/
theorem adjugate_zs_mul38 (φ : PotPair) (z : ℂ) (s : ℝ) (M : PairMat38) :
    (zsCoeffPot38 φ z s * M).adjugate = -(M.adjugate * zsCoeffPot38 φ z s) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_two, zsCoeffPot38, zsCoeffPair, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two] <;> ring

theorem ac_adjugate_mulEntry38 {M W : ℝ → PairMat38}
    (hM : ∀ i j, AbsolutelyContinuousOnInterval (fun s => M s i j) 0 1)
    (hW : ∀ i j, AbsolutelyContinuousOnInterval (fun s => W s i j) 0 1) (i j : Fin 2) :
    AbsolutelyContinuousOnInterval (fun s => ((M s).adjugate * W s) i j) 0 1 := by
  simpa only [Matrix.mul_apply, Fin.sum_univ_two] using
    k1ACPointwiseAddMul38 (ac_adjugateEntry38 hM i 0) (hW 0 j)
      (ac_adjugateEntry38 hM i 1) (hW 1 j)

theorem hasDerivAt_adjugate_mulEntry38 {M W : ℝ → PairMat38}
    {M' W' : PairMat38} {s : ℝ}
    (hM : ∀ i j, HasDerivAt (fun r => M r i j) (M' i j) s)
    (hW : ∀ i j, HasDerivAt (fun r => W r i j) (W' i j) s) (i j : Fin 2) :
    HasDerivAt (fun r => ((M r).adjugate * W r) i j)
      ((M'.adjugate * W s + (M s).adjugate * W') i j) s := by
  have h0 := (hasDerivAt_adjugateEntry38 hM i 0).mul (hW 0 j)
  have h1 := (hasDerivAt_adjugateEntry38 hM i 1).mul (hW 1 j)
  convert h0.fun_add h1 using 1
  · funext r
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Pi.mul_apply]
  · simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]
    ring

/-- Algebraic cancellation in the independently defined variation primitive. -/
theorem adjugate_variation_cancel38 (φ : PotPair) (z : ℂ) (s : ℝ) (M W B : PairMat38) :
    (zsCoeffPot38 φ z s * M).adjugate * W +
      M.adjugate * (zsCoeffPot38 φ z s * W + B) = M.adjugate * B := by
  rw [adjugate_zs_mul38, neg_mul, Matrix.mul_add, mul_assoc]
  abel

end
end NlsGge.GK38
