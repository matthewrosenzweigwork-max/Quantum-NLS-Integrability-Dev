import QuantumNLS.RootEnergyMomentResolvent
import QuantumNLS.SmoothScalarMomentsBinding
import QuantumNLS.RiccatiModeAnalytic
import QuantumNLS.RiccatiChargeIdent

/-! The actual Picard branch determines the Cauchy transform of the existing
quantum measure. All strip, smallness and norm conditions are proved eventually.
No scalar energy moment or asymptotic identity is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Filter Topology
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE1
open QuantumNLS.ComplexifiedSobolevField QuantumNLS.RiccatiPointwiseDisc
open QuantumNLS.RiccatiExpansions QuantumNLS.RiccatiPicardBall
open QuantumNLS.RootEnergyMomentResolvent QuantumNLS.RiccatiModeAnalytic
open QuantumNLS.SmoothScalarMomentsBinding QuantumNLS.RiccatiChargeLevels
namespace QuantumNLS.RootEnergyMomentBranch
variable {L : ℝ} [hLf : Fact (0 < L)] {a : ℝ}

lemma y_atTop : Tendsto y atTop atTop := by
  exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop

/-- The proved branch is physically bound to the quantum-derived full-mass
measure; the finite prefix has no bearing on this eventual equality. -/
theorem branch_cauchy (ha : 1/2 < a) {κ : ℝ} (hκ : 0 < κ) (u : Ell2) :
    ∀ᶠ n in atTop, floquetJ L a u (branch hLf.out ha κ u n) =
      Complex.I * QuantumNLS.CauchyUniqueness.cauchyTransform
        (QuantumNLS.FullMass.Mmeas κ (fieldMap L a (by linarith) u)) (z n) := by
  let U := fieldMap L a (by linarith : 0 ≤ a) u
  let B : ℝ := 1 + ‖U‖^2 + 2 * L * physK L a^2 * beta u^2
  have hb0 : 0 ≤ 2 * L * physK L a^2 * beta u^2 := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hLf.out.le)
      (sq_nonneg _)) (sq_nonneg _)
  have hB : 0 < B := by dsimp [B]; positivity
  have hm : ‖U‖^2 ≤ B := by dsimp [B]; linarith
  have hb : 2 * L * physK L a^2 * beta u^2 ≤ B := by
    dsimp [B]; nlinarith [sq_nonneg ‖U‖]
  have he1 := y_atTop.eventually_ge_atTop (4 * (κ * B))
  have he2 := y_atTop.eventually_ge_atTop (Real.log 16 / L)
  filter_upwards [branch_eventually hLf.out ha κ u, he1, he2] with n hn h1 h2
  have hz := z_pos n
  have hhigh : QuantumNLS.RootMeasureComplex.HighHalf L (κ * B) (z n) := by
    constructor
    · simpa only [z_im] using h1
    · rw [div_le_iff₀ hLf.out] at h2
      simpa only [z_im, mul_comm] using h2
  have htrace := QuantumNLS.RootTraceSymbolFinal.traceSymbol_all (L := L) hκ.le U (z n)
  rw [l2_discriminant_monodromy L ha hz hκ u _ hn.2.1,
    psi_floquet κ hLf.out ha] at htrace
  have ht : Complex.exp (Complex.I * z n * (L : ℂ) / 2) *
      (Complex.exp (-(Complex.I * z n * (L : ℂ) / 2) + (κ : ℂ) *
        floquetJ L a u (branch hLf.out ha κ u n)) +
      (Complex.exp (-(Complex.I * z n * (L : ℂ) / 2) + (κ : ℂ) *
        floquetJ L a u (branch hLf.out ha κ u n)))⁻¹) =
      QuantumNLS.NormalizedTransfer.productSymbol L κ U (z n) := by
    rw [← htrace, ← mul_assoc, ← Complex.exp_add]
    simp
  have hp : 0 ≤ physK L a := physK_nonneg (by linarith)
  have hu : ‖u‖ ≤ beta u := by unfold beta; linarith
  have hJ : ‖floquetJ L a u (branch hLf.out ha κ u n)‖ ≤ B / (z n).im := by
    have h := QuantumNLS.RiccatiJBound.norm_J_le hLf.out.le
      (mul_nonneg hp (beta_pos u).le)
      (fun t _ => (physRep_norm_le hLf.out ha u t).trans
        (mul_le_mul_of_nonneg_left hu hp))
      (fun t _ => (physRep_norm_le hLf.out ha _ t).trans
        (mul_le_mul_of_nonneg_left hn.1 hp))
    change ‖floquetJ L a u (branch hLf.out ha κ u n)‖ ≤ _ at h
    calc
      _ ≤ L * (physK L a * beta u * (physK L a * (2 * beta u / y n))) := h
      _ = (2 * L * physK L a^2 * beta u^2) / (z n).im := by rw [z_im]; ring
      _ ≤ B / (z n).im := div_le_div_of_nonneg_right hb hz.le
  exact cauchy_eq_floquet hκ hB U hm hhigh hz hJ ht

omit hLf in
lemma floquetJ_eq_mode (u r : Ell2) :
    floquetJ L a u r = modeCoef L a (jEll u) r := by
  unfold floquetJ modeCoef
  simp_rw [physRep_jEll]

/-- The actual nonlinear contribution converges after integration. Continuity
of this integral is proved by the existing bounded bilinear map. -/
theorem nonlinear_pairing_limit (ha : 1/2 < a) (κ : ℝ) (u : Ell2) :
    Tendsto (fun n => floquetJ L a u (scaledR L n
      (mulBil hLf.out ha (jEll u)
        (mulBil hLf.out ha ((y n : ℂ) • branch hLf.out ha κ u n)
          ((y n : ℂ) • branch hLf.out ha κ u n))))) atTop
      (nhds (floquetJ L a u (mulBil hLf.out ha (jEll u) (mulBil hLf.out ha u u)))) := by
  simpa only [floquetJ_eq_mode, Function.comp_def, modeCoefCLM_apply] using
    ((modeCoefCLM hLf.out ha (jEll u)).continuous.continuousAt.tendsto.comp
      (nonlinear_scaled_limit hLf.out ha κ u))

#print axioms branch_cauchy
#print axioms nonlinear_pairing_limit
end QuantumNLS.RootEnergyMomentBranch

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootEnergyMomentBranch." ||
        n.toString.startsWith "_private.QuantumNLS.RootEnergyMomentBranch." then
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
