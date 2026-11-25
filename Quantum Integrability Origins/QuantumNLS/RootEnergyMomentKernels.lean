import QuantumNLS.FullMass
import QuantumNLS.SmoothScalarMomentsMain
import QuantumNLS.ProductEnergyPreparation

/-! R-484B3F6D support only: exact positive spectral regularization and its
monotone limit, plus the H¹ Fourier kinetic limit. No energy moment, Riccati
asymptotic, uniform integrability, or actual-law L¹ limit is assumed or asserted.
The measure below is the already constructed FullMass.Mmeas. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped ENNReal Topology
open MeasureTheory Filter QuantumNLS.PhysicalTensor QuantumNLS.FullMass
  QuantumNLS.ProductEnergyPreparation QuantumNLS.ChargeEnergy QuantumNLS.Fourier
  QuantumNLS.SmoothScalarMomentsPositive QuantumNLS.SmoothScalarMomentsCauchy
namespace QuantumNLS.RootEnergyMomentKernels
variable {L : ℝ} [Fact (0 < L)]

lemma kernel1_integrable (κ : ℝ) (u : L2T L) (n : ℕ) :
    Integrable (kernel 1 n) (Mmeas κ u) := by
  refine (integrable_const (((n : ℝ)+1)^2)).mono'
    (kernel_continuous 1 n).aestronglyMeasurable (ae_of_all _ fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg _ _ _)]
  simpa only [Nat.mul_zero, pow_zero, mul_one] using kernel_step_bound 0 n t

lemma kernel0_integrable (κ : ℝ) (u : L2T L) (n : ℕ) :
    Integrable (kernel 0 n) (Mmeas κ u) := by
  refine (integrable_const (1 : ℝ)).mono'
    (kernel_continuous 0 n).aestronglyMeasurable (ae_of_all _ fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg _ _ _)]
  exact kernel_zero_le_one n t

/-- Exact Cauchy-transform identity for the actual full-mass quantum measure.
Its right side is bounded regularization; no second moment is presumed finite. -/
lemma spectral_regularized_identity (κ : ℝ) (u : L2T L) (n : ℕ) :
    (∫ t, kernel 1 n t ∂(Mmeas κ u)) =
      ((n : ℝ)+1)^2 * (‖u‖^2 + ((n : ℝ)+1) *
        (QuantumNLS.EmpiricalRapidity.cauchyTransform (Mmeas κ u) (height n)).im) := by
  have h0 := QuantumNLS.SmoothScalarMomentsMain.kernel_integral_eq_remainder_re
    (Mmeas κ u) (fun _ => (0 : ℝ)) n
  have hre : (height n).re = 0 := by simp [height]
  change (∫ t, kernel 0 n t ∂(Mmeas κ u)) =
    (height n * (∫ t : ℝ, (height n-t)⁻¹ ∂(Mmeas κ u))).re at h0
  rw [Complex.mul_re, hre, height_im, zero_mul, zero_sub] at h0
  have hm : (Mmeas κ u).real Set.univ = ‖u‖^2 := by
    rw [measureReal_def, Mmeas_univ, ENNReal.toReal_ofReal (sq_nonneg _)]
  simp_rw [show kernel 1 n = fun t => ((n : ℝ)+1)^2 * (1-kernel 0 n t) from
    funext fun t => by simpa only [Nat.mul_zero, pow_zero] using kernel_step 0 n t]
  rw [integral_const_mul, integral_sub (integrable_const _) (kernel0_integrable κ u n),
    integral_const, smul_eq_mul, mul_one, hm, h0]
  simp only [QuantumNLS.EmpiricalRapidity.cauchyTransform]
  ring

/-- Monotone convergence to the possibly infinite second moment. This does
not replace the missing proof that its value equals the physical energy. -/
lemma spectral_monotone_limit (κ : ℝ) (u : L2T L) :
    Tendsto (fun n => ENNReal.ofReal (∫ t, kernel 1 n t ∂(Mmeas κ u))) atTop
      (nhds (∫⁻ t, ENNReal.ofReal (t^2) ∂(Mmeas κ u))) := by
  have hm := lintegral_tendsto_of_tendsto_of_monotone
    (fun n => (kernel1_integrable κ u n).aemeasurable.ennreal_ofReal)
    (ae_of_all (Mmeas κ u) fun t n k hnk => ENNReal.ofReal_le_ofReal (kernel_mono 1 t hnk))
    (ae_of_all (Mmeas κ u) fun t =>
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp (kernel_tendsto 1 t))
  simpa only [show 2*1=2 by decide,
    ← ofReal_integral_eq_lintegral_ofReal (kernel1_integrable κ u _)
      (ae_of_all (Mmeas κ u) (kernel_nonneg 1 _))] using hm

lemma kernel1_le_square (n : ℕ) (t : ℝ) : kernel 1 n t ≤ t^2 := by
  unfold kernel
  norm_num only [Nat.mul_one]
  exact div_le_self (sq_nonneg t) (le_add_of_nonneg_right (by positivity))

/-- The linear resolvent's regularized real energy has exactly the H¹
kinetic limit, proved by weighted Fourier dominated convergence. -/
lemma fourier_kinetic_limit (u : L2T L) (hH : OneH1 u) :
    Tendsto (fun n : ℕ => ∑' k : ℤ,
      kernel 1 n (freq L k) * ‖fourierL2 L u k‖^2) atTop
      (nhds (kinetic (u : AddCircle L → ℂ))) := by
  have hs := (hasSum_kin_a hH).summable
  have ht := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (G := ℝ)
    (f := fun (n : ℕ) k => kernel 1 n (freq L k) * ‖fourierL2 L u k‖^2)
    (g := fun k => freq L k^2 * ‖fourierL2 L u k‖^2)
    (bound := fun k => freq L k^2 * ‖fourierL2 L u k‖^2) hs
    (fun k => by simpa only [show 2*1=2 by decide] using
      (kernel_tendsto 1 (freq L k)).mul_const (‖fourierL2 L u k‖^2))
    (Eventually.of_forall fun n k => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (kernel_nonneg _ _ _) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right (kernel1_le_square n _) (sq_nonneg _))
  rwa [← kinetic_eq] at ht

#print axioms spectral_regularized_identity
#print axioms spectral_monotone_limit
#print axioms fourier_kinetic_limit
end QuantumNLS.RootEnergyMomentKernels

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootEnergyMomentKernels." ||
        n.toString.startsWith "_private.QuantumNLS.RootEnergyMomentKernels." then
      pending := pending.push n
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
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
