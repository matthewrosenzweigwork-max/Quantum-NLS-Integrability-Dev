import QuantumNLS.RootEnergyMomentBranch
import QuantumNLS.RootEnergyMomentKernels

/-! Physical H¹ normalization and pairing. Actual objects, with no added
regularity or moment premise. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE1 QuantumNLS.RiccatiSobolevE2b
open QuantumNLS.ComplexifiedSobolevField QuantumNLS.RiccatiPointwiseDisc
open QuantumNLS.RiccatiPointwiseRep QuantumNLS.RiccatiExpansions
open QuantumNLS.RiccatiChargeLevels QuantumNLS.RiccatiChargeIdent
open QuantumNLS.PhysicalTensor QuantumNLS.ProductEnergyPreparation QuantumNLS.Fourier
namespace QuantumNLS.RootEnergyMomentPhysical
variable {L : ℝ} [hLf : Fact (0 < L)]

lemma weighted_summable (u : L2T L) (hH : OneH1 u) :
    Summable (fun k => wt L 1 k * ‖fourierL2 L u k‖^2) := by
  apply Summable.of_nonneg_of_le (fun k => mul_nonneg (wt_nonneg _ _ _) (sq_nonneg _))
    (fun k => ?_) (hH.mul_left 2)
  have he : wt L 1 k = (1 + |QuantumNLS.Fourier.freq L k|)^2 := by
    unfold wt
    norm_num [QuantumNLS.RiccatiSobolevE1.freq, QuantumNLS.Fourier.freq]
  rw [he, f04Weight_one]
  have hq : (1 + |QuantumNLS.Fourier.freq L k|)^2 ≤ 2 * (1 + QuantumNLS.Fourier.freq L k^2) := by
    nlinarith [sq_nonneg (|QuantumNLS.Fourier.freq L k|-1), sq_abs (QuantumNLS.Fourier.freq L k)]
  nlinarith [mul_le_mul_of_nonneg_right hq (sq_nonneg ‖fourierL2 L u k‖)]

/-- Every actual H¹ input has a base in the complete Riccati space. -/
def base (u : L2T L) (hH : OneH1 u) : Ell2 :=
  ⟨fun k => (pw L 1 k : ℂ) * fourierL2 L u k,
    memℓp_of_summable (weighted_summable u hH)⟩

lemma toField_base (u : L2T L) (hH : OneH1 u) :
    toField L 1 (base u hH) = fun k => fourierL2 L u k := by
  funext k
  exact mul_div_cancel_left₀ _ (pw_ne_zero L 1 k)

lemma fieldMap_base (u : L2T L) (hH : OneH1 u) :
    fieldMap L 1 (by norm_num) (base u hH) = u := by
  apply (fourierL2 L).injective
  apply lp.ext
  funext k
  rw [fourierL2_apply, coeff_fieldMap]
  exact congrFun (toField_base u hH) k

lemma floquetJ_inner {a : ℝ} (ha : 1/2 < a) (u r : Ell2) :
    floquetJ L a u r = ⟪fieldMap L a (by linarith) u,
      fieldMap L a (by linarith) r⟫_ℂ := by
  obtain ⟨f, _, hf, hfp, _⟩ := fieldMap_rep L ha u
  obtain ⟨g, _, hg, hgp, _⟩ := fieldMap_rep L ha r
  have hi : ⟪fieldMap L a (by linarith) u, fieldMap L a (by linarith) r⟫_ℂ =
      ∫ t : AddCircle L, conj (f t) * g t := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf, hg] with t ht hs
    rw [ht, hs, RCLike.inner_apply']
  rw [hi, ← AddCircle.intervalIntegral_preimage L 0]
  simp only [zero_add]
  unfold floquetJ
  apply intervalIntegral.integral_congr
  intro t _
  simp only [physRep, hfp, hgp]

lemma floquetJ_fourier {a : ℝ} (ha : 1/2 < a) (u r : Ell2) :
    floquetJ L a u r = ∑' k, conj (toField L a u k) * toField L a r k := by
  rw [floquetJ_inner ha, ← (fourierL2 L).inner_map_map, lp.inner_eq_tsum]
  apply tsum_congr
  intro k
  rw [RCLike.inner_apply', fourierL2_apply, fourierL2_apply, coeff_fieldMap, coeff_fieldMap]

/-- The two convolution products contribute exactly L; this cancels the
model coupling κ/L. The physical measure is mass L on the torus. -/
lemma nonlinear_quartic {a : ℝ} (ha : 1/2 < a) (u : Ell2) :
    floquetJ L a u (mulBil hLf.out ha (jEll u) (mulBil hLf.out ha u u)) =
      ((L * QuantumNLS.ChargeEnergy.quartic
        (fieldMap L a (by linarith) u : AddCircle L → ℂ) : ℝ) : ℂ) := by
  obtain ⟨f, _, hf, hfp, _⟩ := fieldMap_rep L ha u
  have hq : QuantumNLS.ChargeEnergy.quartic
      (fieldMap L a (by linarith) u : AddCircle L → ℂ) =
      ∫ t : AddCircle L, ‖f t‖^4 := by
    unfold QuantumNLS.ChargeEnergy.quartic
    apply integral_congr_ae
    filter_upwards [hf] with t ht
    rw [ht]
  have hs : (Real.sqrt L : ℂ)^2 = (L : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hLf.out.le]
  have he (t : ℝ) : conj (physRep L a u t) *
      physRep L a (mulBil hLf.out ha (jEll u) (mulBil hLf.out ha u u)) t =
      (L : ℂ) * (‖f (t : AddCircle L)‖^4 : ℝ) := by
    change conj (physRep L a u t) *
      physRep L a (mulEll hLf.out ha (jEll u) (mulEll hLf.out ha u u)) t = _
    have hfpt : physRep L a u t = f (t : AddCircle L) := (hfp t).symm
    rw [physRep_mulEll, physRep_mulEll, physRep_jEll, hfpt]
    have hn' : f (t : AddCircle L) * conj (f (t : AddCircle L)) =
        (‖f (t : AddCircle L)‖^2 : ℝ) := by
      rw [Complex.mul_conj, Complex.sq_norm]
    calc
      _ = (Real.sqrt L : ℂ)^2 * (f (t : AddCircle L) * conj (f (t : AddCircle L)))^2 := by ring
      _ = _ := by rw [hs, hn']; push_cast; ring
  unfold floquetJ
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  have hhC := AddCircle.intervalIntegral_preimage L 0
    (fun t : AddCircle L => ((‖f t‖^4 : ℝ) : ℂ))
  simp only [zero_add] at hhC
  rw [hhC, integral_complex_ofReal, ← hq, Complex.ofReal_mul]

#print axioms fieldMap_base
#print axioms floquetJ_inner
#print axioms floquetJ_fourier
#print axioms nonlinear_quartic
end QuantumNLS.RootEnergyMomentPhysical

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootEnergyMomentPhysical." ||
        n.toString.startsWith "_private.QuantumNLS.RootEnergyMomentPhysical." then
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
