import QuantumNLS.Reg010LowBasic

/-! The all-L² Riccati identity and the uniform linear large-height bound.
The small ratio and its selected Cauchy identity are accepted inputs. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
namespace QuantumNLS.Reg010LowRiccati
open QuantumNLS.PhysicalTensor QuantumNLS.FreeLimit QuantumNLS.Reg010LowBasic
open QuantumNLS.RootH1RatioBounds QuantumNLS.RootH1RatioOperator
open QuantumNLS.RootH1RatioConvergence QuantumNLS.RootH1RatioStrong
open QuantumNLS.RootMassSpectralR27 QuantumNLS.RootMassFourierR27

variable {L : ℝ} [Fact (0 < L)]

/-- The accepted selected Cauchy identity, including the zero field. -/
theorem all_L2_cauchy {Y κ : ℝ} (hY : 0 < Y) (hlog : Real.log 3 ≤ Y * L)
    (hκ : 0 < κ) (u : L2T L) (hsmall : 16 * κ * ‖u‖ ^ 2 ≤ Y) :
    CauchyUniqueness.cauchyTransform (PhysicalQuantumMeasure.measure hκ u)
      ((Y : ℂ) * Complex.I) = -Complex.I * inner ℂ u (ratioL2 hY hlog hκ.le u hsmall) := by
  rw [PhysicalL2Normalization.measure_eq_Mmeas]
  by_cases hu : u = 0
  · subst u
    simp [QuantumNLS.FullMass.Mmeas_zero, CauchyUniqueness.cauchyTransform]
  · exact QuantumNLS.RootH1RatioCauchy.ratio_cauchy hY hlog hκ u hu hsmall

theorem physical_regularization {Y κ : ℝ} (hY : 0 < Y) (hlog : Real.log 3 ≤ Y * L)
    (hκ : 0 < κ) (u : L2T L) (hsmall : 16 * κ * ‖u‖ ^ 2 ≤ Y) :
    (∫ t, RootH1PositiveSpectral.kernel Y t ∂(PhysicalQuantumMeasure.measure hκ u)) =
      Y ^ 2 * (‖u‖ ^ 2 - (inner ℂ u ((Y : ℂ) • ratioL2 hY hlog hκ.le u hsmall)).re) := by
  rw [PhysicalL2Normalization.measure_eq_Mmeas, RootH1PositiveSpectral.physical_identity hY]
  have hc := all_L2_cauchy hY hlog hκ u hsmall
  rw [PhysicalL2Normalization.measure_eq_Mmeas] at hc
  rw [hc, inner_smul_right]
  simp only [neg_mul, Complex.neg_im, Complex.I_mul_im, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem free_regularization {Y : ℝ} (hY : 0 < Y) (u : L2T L) :
    (∫ t, RootH1PositiveSpectral.kernel Y t ∂(freeMeasure L u)) =
      Y ^ 2 * (‖u‖ ^ 2 - (inner ℂ u (rescaled Y u)).re) := by
  haveI := free_finite u
  have hi : Integrable (fun t : ℝ => t ^ (2 * 0)) (freeMeasure L u) := by
    simpa using (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) (freeMeasure L u))
  have hs := QuantumNLS.Reg014Moments.free_kernel_sum hY u 0 hi
  rw [← fourier_deficit hY u, ← tsum_mul_left]
  calc
    _ = ∑' n : ℤ, Y ^ 2 * (QuantumNLS.RootWeightedCellsR26.momentum L n) ^ 2 /
        (Y ^ 2 + (QuantumNLS.RootWeightedCellsR26.momentum L n) ^ 2) *
        ‖QuantumNLS.Fourier.coeff L u n‖ ^ 2 := by
      simpa only [QuantumNLS.TerraMultiRound60Kernel.kernel,
        RootH1PositiveSpectral.kernel, Nat.reduceAdd, Nat.reduceMul] using hs
    _ = _ := by
      apply tsum_congr
      intro n
      rw [QuantumNLS.Fourier.fourierL2_apply]
      unfold deficit
      ring

/-- The exact low-order error as a pairing with the nonlinear resolvent error. -/
theorem correction_pairing {Y κ : ℝ} (hY : 0 < Y) (hlog : Real.log 3 ≤ Y * L)
    (hκ : 0 < κ) (u : L2T L) (hsmall : 16 * κ * ‖u‖ ^ 2 ≤ Y) :
    correction κ hκ u Y = -(Y ^ 2) *
      (inner ℂ u ((Y : ℂ) •
        (ratioL2 hY hlog hκ.le u hsmall - resolvent Y u))).re := by
  rw [correction, physical_regularization hY hlog hκ u hsmall, free_regularization hY u]
  simp only [smul_sub, inner_sub_right, Complex.sub_re, rescaled, smul_apply]
  ring

/-- The all-L² bound has the printed coefficient 4κ‖u‖⁴. -/
theorem large_bound (κ : ℝ) (hκ : 0 < κ) (u : L2T L) {Y : ℝ}
    (hYB : threshold κ u ≤ Y) : |correction κ hκ u Y| ≤ 4 * κ * ‖u‖ ^ 4 * Y := by
  obtain ⟨hY, hlog, hsmall⟩ := height_spec u hYB
  rw [correction_pairing hY hlog hκ u hsmall, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg Y)]
  have hn := nonlinear_error hY hlog hκ.le u hsmall
  have hp : |(inner ℂ u ((Y : ℂ) •
      (ratioL2 hY hlog hκ.le u hsmall - resolvent Y u))).re| ≤ ‖u‖ * (4 * κ * ‖u‖ ^ 3 / Y) :=
    (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left hn (norm_nonneg _)))
  calc
    _ ≤ Y ^ 2 * (‖u‖ * (4 * κ * ‖u‖ ^ 3 / Y)) :=
      mul_le_mul_of_nonneg_left hp (sq_nonneg Y)
    _ = _ := by field_simp

/-- One threshold and one linear coefficient suffice on every L²-bounded set. -/
theorem large_bound_uniform (κ : ℝ) (hκ : 0 < κ) (B : Set (L2T L))
    (hB : Bornology.IsBounded B) :
    ∃ C Y₀ : ℝ, 0 ≤ C ∧ 1 ≤ Y₀ ∧ ∀ u ∈ B, ∀ Y : ℝ, Y₀ ≤ Y →
      |correction κ hκ u Y| ≤ C * Y := by
  obtain ⟨U, hU⟩ := isBounded_iff_forall_norm_le.mp hB
  let V := max U 0
  refine ⟨4 * κ * V ^ 4, max 1 (max (Real.log 3 / L) (16 * κ * V ^ 2)),
    by positivity, le_max_left _ _, ?_⟩
  intro u hu Y hY
  have hn : ‖u‖ ≤ V := (hU u hu).trans (le_max_left _ _)
  have ht : threshold κ u ≤ Y := by
    apply le_trans _ hY
    unfold threshold
    gcongr
  have hY0 : 0 ≤ Y := by linarith [le_max_left 1 (max (Real.log 3 / L) (16 * κ * V ^ 2))]
  exact (large_bound κ hκ u ht).trans (by gcongr)

/-- A single quadratic/linear envelope, suitable for the fractional integral. -/
theorem correction_bounds (κ : ℝ) (hκ : 0 < κ) (B : Set (L2T L))
    (hB : Bornology.IsBounded B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ B, ∀ Y > 0,
      |correction κ hκ u Y| ≤ C * (if Y ≤ 1 then Y ^ 2 else Y) := by
  obtain ⟨U, hU⟩ := isBounded_iff_forall_norm_le.mp hB
  obtain ⟨D, Y₀, hD, hY₀, hl⟩ := large_bound_uniform κ hκ B hB
  let A := (max U 0) ^ 2
  have hA : 0 ≤ A := sq_nonneg _
  have hs : ∀ u ∈ B, ∀ Y > 0, |correction κ hκ u Y| ≤ A * Y ^ 2 := by
    intro u hu Y hY
    calc
      _ ≤ Y ^ 2 * ‖u‖ ^ 2 := small_bound κ hκ u hY
      _ ≤ A * Y ^ 2 := by
        have hn := pow_le_pow_left₀ (norm_nonneg u)
          ((hU u hu).trans (le_max_left U 0)) 2
        dsimp [A]
        nlinarith [mul_le_mul_of_nonneg_left hn (sq_nonneg Y)]
  let C := max A (max D (A * Y₀))
  refine ⟨C, hA.trans (le_max_left _ _), ?_⟩
  intro u hu Y hY
  by_cases h1 : Y ≤ 1
  · simp only [ite_eq_left h1]
    exact (hs u hu Y hY).trans (by gcongr; exact le_max_left _ _)
  · simp only [ite_eq_right h1]
    by_cases h0 : Y₀ ≤ Y
    · exact (hl u hu Y h0).trans (by gcongr; exact (le_max_left _ _).trans (le_max_right _ _))
    · calc
        _ ≤ A * Y ^ 2 := hs u hu Y hY
        _ ≤ (A * Y₀) * Y := by nlinarith [mul_nonneg hA (show 0 ≤ Y₀ - Y by linarith)]
        _ ≤ C * Y := by gcongr; exact (le_max_right _ _).trans (le_max_right _ _)

#print axioms all_L2_cauchy
#print axioms physical_regularization
#print axioms free_regularization
#print axioms correction_pairing
#print axioms large_bound
#print axioms large_bound_uniform
#print axioms correction_bounds
end QuantumNLS.Reg010LowRiccati

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Reg010LowRiccati." ||
        n.toString.startsWith "_private.QuantumNLS.Reg010LowRiccati." then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Round45 aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
