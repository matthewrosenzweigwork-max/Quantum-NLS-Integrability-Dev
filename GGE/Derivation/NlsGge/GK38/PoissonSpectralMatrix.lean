import NlsGge.GK38.PoissonSpectralModel

/-! Finite matrix calculus before the actual rough-potential application. -/
set_option autoImplicit false
open Set Filter Topology MeasureTheory NlsGge.GK38
namespace NlsGge.GK38.PoissonSpectral38
noncomputable section

theorem ac_mulEntry38 {M W : ℝ → PairMat38}
    (hM : ∀ i j, AbsolutelyContinuousOnInterval (fun s => M s i j) 0 1)
    (hW : ∀ i j, AbsolutelyContinuousOnInterval (fun s => W s i j) 0 1) (i j : Fin 2) :
    AbsolutelyContinuousOnInterval (fun s => (M s * W s) i j) 0 1 := by
  simpa only [Matrix.mul_apply, Fin.sum_univ_two] using
    k1ACPointwiseAddMul38 (hM i 0) (hW 0 j) (hM i 1) (hW 1 j)

theorem hasDerivAt_mulEntry38 {M W : ℝ → PairMat38}
    {M' W' : PairMat38} {s : ℝ}
    (hM : ∀ i j, HasDerivAt (fun r => M r i j) (M' i j) s)
    (hW : ∀ i j, HasDerivAt (fun r => W r i j) (W' i j) s) (i j : Fin 2) :
    HasDerivAt (fun r => (M r * W r) i j)
      ((M' * W s + M s * W') i j) s := by
  have h0 := (hM i 0).mul (hW 0 j)
  have h1 := (hM i 1).mul (hW 1 j)
  convert h0.fun_add h1 using 1
  · funext r
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Pi.mul_apply]
  · simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]
    ring

theorem ac_cyclicEntry38 {M : ℝ → PairMat38} (C : PairMat38)
    (hM : ∀ i j, AbsolutelyContinuousOnInterval (fun s => M s i j) 0 1)
    (i j : Fin 2) :
    AbsolutelyContinuousOnInterval (fun s => (M s * C * (M s).adjugate) i j) 0 1 := by
  have hC (a b : Fin 2) : AbsolutelyContinuousOnInterval (fun _ : ℝ => C a b) 0 1 :=
    absolutelyContinuousOnInterval_const38 (C a b) 0 1
  exact ac_mulEntry38 (ac_mulEntry38 hM hC) (ac_adjugateEntry38 hM) i j

theorem hasDerivAt_cyclicEntry38 (φ : PotPair) (z : ℂ)
    {M : ℝ → PairMat38} (C : PairMat38) {s : ℝ}
    (hM : ∀ i j, HasDerivAt (fun r => M r i j)
      ((zsCoeffPot38 φ z s * M s) i j) s) (i j : Fin 2) :
    HasDerivAt (fun r => (M r * C * (M r).adjugate) i j)
      ((zsCoeffPot38 φ z s * (M s * C * (M s).adjugate) -
        (M s * C * (M s).adjugate) * zsCoeffPot38 φ z s) i j) s := by
  have hC (a b : Fin 2) : HasDerivAt (fun _ : ℝ => C a b) ((0 : PairMat38) a b) s :=
    hasDerivAt_const s (C a b)
  have hMC (a b : Fin 2) : HasDerivAt (fun r => (M r * C) a b)
      ((zsCoeffPot38 φ z s * M s * C) a b) s := by
    simpa only [mul_zero, add_zero] using hasDerivAt_mulEntry38 hM hC a b
  have hd := hasDerivAt_mulEntry38 hMC (hasDerivAt_adjugateEntry38 hM) i j
  apply hd.congr_deriv
  have heq : zsCoeffPot38 φ z s * M s * C * (M s).adjugate +
      M s * C * (zsCoeffPot38 φ z s * M s).adjugate =
      zsCoeffPot38 φ z s * (M s * C * (M s).adjugate) -
        (M s * C * (M s).adjugate) * zsCoeffPot38 φ z s := by
    simp only [adjugate_zs_mul38, mul_neg, mul_assoc, sub_eq_add_neg]
  exact congrArg (fun A : PairMat38 => A i j) heq

/-- The trace commutator identity isolates the spectral difference exactly. -/
theorem trace_commutator_spectral38 (φ : PotPair) (z w : ℂ) (s : ℝ)
    (A B : PairMat38) :
    traceProduct38 (zsCoeffPot38 φ z s * A - A * zsCoeffPot38 φ z s) B +
      traceProduct38 A (zsCoeffPot38 φ w s * B - B * zsCoeffPot38 φ w s) =
      2 * Complex.I * (z - w) * (A 1 0 * B 0 1 - A 0 1 * B 1 0) := by
  simp [traceProduct38, zsCoeffPot38, zsCoeffPair, Matrix.mul_apply,
    Matrix.vecMul, dotProduct, Matrix.sub_apply, Fin.sum_univ_two]
  ring

end
end NlsGge.GK38.PoissonSpectral38
