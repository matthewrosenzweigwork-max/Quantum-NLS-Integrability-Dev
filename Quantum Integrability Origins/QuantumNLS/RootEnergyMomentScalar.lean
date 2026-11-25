import QuantumNLS.RootEnergyMomentPhysical

/-! Exact H¹ scalar energy moment of the quantum-derived full-mass measure.
The finite Born-law assertions of R-484B3F6D are separate obligations. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE1
open QuantumNLS.ComplexifiedSobolevField QuantumNLS.RiccatiExpansions
open QuantumNLS.RiccatiPicardBall QuantumNLS.RiccatiModeAnalytic
open QuantumNLS.RootEnergyMomentResolvent QuantumNLS.RootEnergyMomentBranch
open QuantumNLS.RootEnergyMomentPhysical QuantumNLS.RootEnergyMomentKernels
open QuantumNLS.SmoothScalarMomentsPositive QuantumNLS.PhysicalTensor
open QuantumNLS.ProductEnergyPreparation QuantumNLS.ChargeEnergy
namespace QuantumNLS.RootEnergyMomentScalar
variable {L : ℝ} [hLf : Fact (0 < L)]

omit hLf in
lemma scaledR_field (n : ℕ) (u : Ell2) (k : ℤ) :
    toField L 1 (scaledR L n u) k =
      toField L 1 u k / (1 + Complex.I * (freq L k : ℂ) / (y n : ℂ)) := by
  unfold toField
  rw [scaledR_apply]
  ring

lemma multiplier_real (n : ℕ) (p : ℝ) (c : ℂ) :
    (conj c * (c / (1 + Complex.I * (p : ℂ) / (y n : ℂ)))).re =
      kernel 0 n p * ‖c‖^2 := by
  let d : ℂ := 1 + Complex.I * (p : ℂ) / (y n : ℂ)
  have hdre : d.re = 1 := by simp [d, Complex.mul_re]
  have hdim : d.im = p / y n := by simp [d, Complex.mul_im]
  change (conj c * (c / d)).re = _
  rw [← mul_div_assoc, Complex.conj_mul', ← Complex.ofReal_pow, Complex.div_re]
  simp only [Complex.normSq_apply, hdre, hdim, Complex.ofReal_re, Complex.ofReal_im,
    mul_one, zero_mul, zero_div, add_zero]
  rw [← pow_two, div_pow]
  unfold kernel y
  norm_num only [Nat.mul_zero, pow_zero]
  ring

lemma linear_regularization (u : L2T L) (hH : OneH1 u) (n : ℕ) :
    y n^2 * (‖u‖^2 - (floquetJ L 1 (base u hH)
      (scaledR L n (base u hH))).re) =
      ∑' k : ℤ, kernel 1 n (QuantumNLS.Fourier.freq L k) *
        ‖QuantumNLS.Fourier.fourierL2 L u k‖^2 := by
  let b := base u hH
  have hs := QuantumNLS.Energy.summable_sq (QuantumNLS.Fourier.fourierL2 L u)
  have hnorm : ‖u‖^2 = ∑' k, ‖QuantumNLS.Fourier.fourierL2 L u k‖^2 := by
    rw [← QuantumNLS.Fourier.norm_fourierL2 L u]
    exact QuantumNLS.Energy.norm_sq_eq_tsum _
  have hp : Summable (fun k => conj (toField L 1 b k) *
      toField L 1 (scaledR L n b) k) := by
    have h := lp.summable_inner (𝕜 := ℂ) (divEll L 1 (by norm_num) b)
      (divEll L 1 (by norm_num) (scaledR L n b))
    simpa only [RCLike.inner_apply', divEll_apply, toField, mul_comm] using h
  have he : (floquetJ L 1 b (scaledR L n b)).re =
      ∑' k, kernel 0 n (freq L k) * ‖toField L 1 b k‖^2 := by
    rw [floquetJ_fourier (by norm_num), Complex.re_tsum hp]
    apply tsum_congr
    intro k
    rw [scaledR_field, multiplier_real]
  have hk : Summable (fun k => kernel 0 n (freq L k) * ‖toField L 1 b k‖^2) := by
    have hh := (Complex.hasSum_re hp.hasSum).summable
    convert hh using 1
    funext k
    rw [scaledR_field, multiplier_real]
  rw [he, hnorm, ← hs.tsum_sub (by simpa only [b, toField_base] using hk), ← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [show toField L 1 b k = QuantumNLS.Fourier.fourierL2 L u k from congrFun (toField_base u hH) k]
  have hstep := kernel_step 0 n (freq L k)
  simp only [Nat.mul_zero, pow_zero, zero_add] at hstep
  change y n^2 * (‖QuantumNLS.Fourier.fourierL2 L u k‖^2 -
    kernel 0 n (freq L k) * ‖QuantumNLS.Fourier.fourierL2 L u k‖^2) =
      kernel 1 n (freq L k) * ‖QuantumNLS.Fourier.fourierL2 L u k‖^2
  rw [hstep]
  unfold y
  ring

lemma fixed_scaled_identity (κ : ℝ) (u : Ell2) (n : ℕ)
    (hr : riccatiT hLf.out (by norm_num : (1/2 : ℝ) < 1) (z_pos n)
      (κ/L) u (jEll u) (branch hLf.out (by norm_num : (1/2 : ℝ) < 1) κ u n) =
      branch hLf.out (by norm_num : (1/2 : ℝ) < 1) κ u n) :
    let r := branch hLf.out (by norm_num : (1/2 : ℝ) < 1) κ u n
    (y n : ℂ) • r = scaledR L n u -
      (((κ/L)/(y n)^2 : ℝ) : ℂ) • scaledR L n
        (mulBil hLf.out (by norm_num : (1/2 : ℝ) < 1) (jEll u)
          (mulBil hLf.out (by norm_num : (1/2 : ℝ) < 1)
            ((y n : ℂ) • r) ((y n : ℂ) • r))) := by
  dsimp only
  let r := branch hLf.out (by norm_num : (1/2 : ℝ) < 1) κ u n
  have hh : r = ropCLM L (z n) (z_pos n) u -
      (((κ/L : ℝ) : ℂ)) • ropCLM L (z n) (z_pos n)
        (mulBil hLf.out (by norm_num : (1/2 : ℝ) < 1) (jEll u)
          (mulBil hLf.out (by norm_num : (1/2 : ℝ) < 1) r r)) := hr.symm
  have hw : mulBil hLf.out (by norm_num : (1/2 : ℝ) < 1) (jEll u)
      (mulBil hLf.out (by norm_num : (1/2 : ℝ) < 1) ((y n : ℂ) • r) ((y n : ℂ) • r)) =
      ((y n : ℂ) * (y n : ℂ)) • mulBil hLf.out (by norm_num : (1/2 : ℝ) < 1)
        (jEll u) (mulBil hLf.out (by norm_num : (1/2 : ℝ) < 1) r r) := by
    simp only [map_smul, smul_apply, smul_smul]
  change (y n : ℂ) • r = _
  calc
    _ = (y n : ℂ) • (ropCLM L (z n) (z_pos n) u -
        (((κ/L : ℝ) : ℂ)) • ropCLM L (z n) (z_pos n)
          (mulBil hLf.out (by norm_num : (1/2 : ℝ) < 1) (jEll u)
            (mulBil hLf.out (by norm_num : (1/2 : ℝ) < 1) r r))) :=
      congrArg (fun v : Ell2 => (y n : ℂ) • v) hh
    _ = _ := by
      rw [hw]
      simp only [scaledR, smul_apply, map_smul, smul_sub, smul_smul]
      congr 2
      have hy : (y n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (y_pos n).ne'
      push_cast
      field_simp

/-- Scalar part of the printed theorem, for EVERY actual H¹ input and every
positive physical coupling, including the zero input. Finiteness is proved by
positive monotone recovery, not assumed. -/
theorem scalar_energy_moment {κ : ℝ} (hκ : 0 < κ) (u : L2T L) (hH : OneH1 u) :
    Integrable (fun t : ℝ => t^2) (QuantumNLS.FullMass.Mmeas κ u) ∧
      (∫ t : ℝ, t^2 ∂(QuantumNLS.FullMass.Mmeas κ u)) =
        energyH1 κ (u : AddCircle L → ℂ) := by
  let b := base u hH
  let ha : (1/2 : ℝ) < 1 := by norm_num
  let w := fun n => scaledR L n
    (mulBil hLf.out ha (jEll b)
      (mulBil hLf.out ha ((y n : ℂ) • branch hLf.out ha κ b n)
        ((y n : ℂ) • branch hLf.out ha κ b n)))
  have hw : Tendsto (fun n => (floquetJ L 1 b (w n)).re) atTop
      (nhds (L * quartic (u : AddCircle L → ℂ))) := by
    have ht := Complex.continuous_re.continuousAt.tendsto.comp
      (nonlinear_pairing_limit (L := L) ha κ b)
    rw [nonlinear_quartic ha, fieldMap_base] at ht
    exact ht
  have hlim := (fourier_kinetic_limit u hH).add (hw.const_mul (κ/L))
  have he : kinetic (u : AddCircle L → ℂ) + (κ/L) * (L * quartic (u : AddCircle L → ℂ)) =
      energyH1 κ (u : AddCircle L → ℂ) := by
    unfold energyH1
    rw [← mul_assoc, div_mul_cancel₀ _ hLf.out.ne']
  rw [he] at hlim
  have hreg : ∀ᶠ n in atTop,
      (∫ t, kernel 1 n t ∂(QuantumNLS.FullMass.Mmeas κ u)) =
        (∑' k : ℤ, kernel 1 n (QuantumNLS.Fourier.freq L k) *
          ‖QuantumNLS.Fourier.fourierL2 L u k‖^2) +
          (κ/L) * (floquetJ L 1 b (w n)).re := by
    filter_upwards [branch_cauchy (L := L) ha hκ b, branch_eventually hLf.out ha κ b] with n hc hn
    rw [fieldMap_base] at hc
    have hc' : (QuantumNLS.EmpiricalRapidity.cauchyTransform
        (QuantumNLS.FullMass.Mmeas κ u) (QuantumNLS.SmoothScalarMomentsCauchy.height n)).im =
        -(floquetJ L 1 b (branch hLf.out ha κ b n)).re := by
      have hh := congrArg Complex.re hc
      simp only [Complex.I_mul_re] at hh
      have hzheight : QuantumNLS.SmoothScalarMomentsCauchy.height n = z n := by
        simp [QuantumNLS.SmoothScalarMomentsCauchy.height, z, y]
      rw [hzheight]
      change (QuantumNLS.CauchyUniqueness.cauchyTransform
        (QuantumNLS.FullMass.Mmeas κ u) (z n)).im = _
      linarith only [hh]
    rw [spectral_regularized_identity, hc']
    have hf := fixed_scaled_identity κ b n hn.2.1
    let F := modeCoefCLM hLf.out ha (jEll b)
    have hF := congrArg F hf
    change F ((y n : ℂ) • branch hLf.out ha κ b n) =
      F (scaledR L n b - (((κ/L)/(y n)^2 : ℝ) : ℂ) • w n) at hF
    rw [map_smul, map_sub, map_smul] at hF
    have hmC : (y n : ℂ) * floquetJ L 1 b (branch hLf.out ha κ b n) =
        floquetJ L 1 b (scaledR L n b) -
          (((κ/L)/(y n)^2 : ℝ) : ℂ) * floquetJ L 1 b (w n) := by
      simpa only [F, modeCoefCLM_apply, ← floquetJ_eq_mode, smul_eq_mul] using hF
    have hm := congrArg Complex.re hmC
    simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] at hm
    rw [← linear_regularization u hH n]
    change y n^2 * (‖u‖^2 + y n * -(floquetJ L 1 b (branch hLf.out ha κ b n)).re) =
      y n^2 * (‖u‖^2 - (floquetJ L 1 b (scaledR L n b)).re) +
        (κ/L) * (floquetJ L 1 b (w n)).re
    have hy := (y_pos n).ne'
    field_simp [hy, hLf.out.ne'] at hm ⊢
    nlinarith only [hm]

  have hc := hlim.congr' (hreg.mono fun _ h => h.symm)
  exact recover_nonnegative (kernel1_integrable κ u) (kernel_nonneg 1)
    (kernel_mono 1) (by simpa only [show 2*1=2 by decide] using kernel_tendsto 1)
    (continuous_id.pow 2).aestronglyMeasurable hc

#print axioms scalar_energy_moment
end QuantumNLS.RootEnergyMomentScalar

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootEnergyMomentScalar." ||
        n.toString.startsWith "_private.QuantumNLS.RootEnergyMomentScalar." then
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
