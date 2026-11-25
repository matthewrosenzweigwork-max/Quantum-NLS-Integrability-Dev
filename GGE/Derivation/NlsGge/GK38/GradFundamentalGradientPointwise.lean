import NlsGge.GK38.GradFundamentalGradientBound

/-! # K1: concrete uniform-ball pointwise gradient residual estimates.
GK Chapter I, Lemma4.3. Free reference phases use the actual complex frequency.
-/
set_option autoImplicit false
open Set
open scoped Matrix.Norms.Elementwise
namespace NlsGge.GK38
noncomputable section

theorem k1FundMatrixBallBound38 (r d : ℝ) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (φ : PotPair) (z : ℂ) (hφ : ‖φ‖ ≤ r) (hz : |z.im| ≤ d) (t : Icc (0 : ℝ) 1) :
    ‖fundPair φ z t‖ ≤ Real.exp (d + 2 * r) := by
  apply (Matrix.norm_le_iff (Real.exp_nonneg _)).mpr
  intro i j
  refine (norm_fundPair_entry_le φ z t i j).trans (Real.exp_le_exp.mpr ?_)
  have hpot : potPrim38 φ t ≤ 2 * r :=
    (potPrim38_le_one φ t.2).trans ((potL1Norm38_le_two_mul φ).trans
      (mul_le_mul_of_nonneg_left hφ (by norm_num)))
  have him : |z.im| * (t : ℝ) ≤ d :=
    (mul_le_mul_of_nonneg_right hz t.2.1).trans (mul_le_of_le_one_right hd t.2.2)
  linarith

def k1GradDiscrimMass38 (φ : PotPair) (z : ℂ) (t : Icc (0 : ℝ) 1) : ℝ :=
  ‖(Complex.I • gradDiscrim38 φ z t) 0‖ ^ 2 + ‖(Complex.I • gradDiscrim38 φ z t) 1‖ ^ 2

def k1GradAntiResidual38 (φ : PotPair) (z : ℂ) (t : Icc (0 : ℝ) 1) : PairVec38 :=
  Complex.I • gradAntiDiscrim38 φ z t -
    ![-Complex.exp (-Complex.I * z * (1 - 2 * (t : ℝ))),
      Complex.exp (Complex.I * z * (1 - 2 * (t : ℝ)))]

def k1GradAntiMass38 (φ : PotPair) (z : ℂ) (t : Icc (0 : ℝ) 1) : ℝ :=
  ‖k1GradAntiResidual38 φ z t 0‖ ^ 2 + ‖k1GradAntiResidual38 φ z t 1‖ ^ 2

theorem k1GradientMassPointwise38 (r d : ℝ) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (φ : PotPair) (z : ℂ) (hφ : ‖φ‖ ≤ r) (hz : |z.im| ≤ d) (t : Icc (0 : ℝ) 1) :
    k1GradDiscrimMass38 φ z t ≤ 256 * (Real.exp (d + 2 * r)) ^ 4 *
      (‖fundPair φ z t - freeFund z t‖ ^ 2 +
        ‖fundPair φ z ⟨1, zero_le_one, le_rfl⟩ - freeFund z ⟨1, zero_le_one, le_rfl⟩‖ ^ 2) ∧
    k1GradAntiMass38 φ z t ≤ 256 * (Real.exp (d + 2 * r)) ^ 4 *
      (‖fundPair φ z t - freeFund z t‖ ^ 2 +
        ‖fundPair φ z ⟨1, zero_le_one, le_rfl⟩ - freeFund z ⟨1, zero_le_one, le_rfl⟩‖ ^ 2) := by
  let H := Real.exp (d + 2 * r)
  let τ : Icc (0 : ℝ) 1 := ⟨1, zero_le_one, le_rfl⟩
  have hM := k1FundMatrixBallBound38 r d hr hd φ z hφ hz t
  have hm := k1FundMatrixBallBound38 r d hr hd 0 z (by simpa using hr) hz t
  have hB : ‖monodromyPair φ z‖ ≤ H := by
    rw [monodromyPair_eq_fundPair]
    exact k1FundMatrixBallBound38 r d hr hd φ z hφ hz τ
  have hb : ‖monodromyPair 0 z‖ ≤ H := by
    rw [monodromyPair_eq_fundPair]
    exact k1FundMatrixBallBound38 r d hr hd 0 z (by simpa using hr) hz τ
  have htrace := k1CyclicVec38_mass_error (fundPair φ z t) (monodromyPair φ z)
    (fundPair 0 z t) (monodromyPair 0 z) H (Real.exp_nonneg _) hM hB hm hb
  rw [← scaled_gradDiscrim38_cyclic, ← scaled_gradDiscrim38_cyclic,
    scaled_gradDiscrim38_zero, sub_zero, monodromyPair_eq_fundPair,
    monodromyPair_eq_fundPair, fundPair_zero_potential, fundPair_zero_potential] at htrace
  have hanti := k1CyclicVec38_mass_error (fundPair φ z t) (k1SwapMat38 * monodromyPair φ z)
    (fundPair 0 z t) (k1SwapMat38 * monodromyPair 0 z) H (Real.exp_nonneg _) hM
      ((k1SwapNorm38 _).trans hB) hm ((k1SwapNorm38 _).trans hb)
  have hdiff : ‖k1SwapMat38 * monodromyPair φ z - k1SwapMat38 * monodromyPair 0 z‖ ≤
      ‖monodromyPair φ z - monodromyPair 0 z‖ := by
    rw [← mul_sub]
    exact k1SwapNorm38 _
  have hanti' : ‖(k1CyclicVec38 (fundPair φ z t) (k1SwapMat38 * monodromyPair φ z) -
      k1CyclicVec38 (fundPair 0 z t) (k1SwapMat38 * monodromyPair 0 z)) 0‖ ^ 2 +
      ‖(k1CyclicVec38 (fundPair φ z t) (k1SwapMat38 * monodromyPair φ z) -
      k1CyclicVec38 (fundPair 0 z t) (k1SwapMat38 * monodromyPair 0 z)) 1‖ ^ 2 ≤
      256 * H ^ 4 * (‖fundPair φ z t - fundPair 0 z t‖ ^ 2 +
        ‖monodromyPair φ z - monodromyPair 0 z‖ ^ 2) := by
    refine hanti.trans ?_
    gcongr
  rw [← scaled_gradAntiDiscrim38_cyclic, ← scaled_gradAntiDiscrim38_cyclic,
    scaled_gradAntiDiscrim38_zero, monodromyPair_eq_fundPair, monodromyPair_eq_fundPair,
    fundPair_zero_potential, fundPair_zero_potential] at hanti'
  exact ⟨htrace, hanti'⟩

end
end NlsGge.GK38
