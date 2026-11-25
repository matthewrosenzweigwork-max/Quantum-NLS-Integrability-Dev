import QuantumNLS.R52CFCompact
import QuantumNLS.Q07SobolevModelR24
import QuantumNLS.SmoothScalarMomentsPhysical

/-! Normalized smooth Fourier approximations of the actual DEF-002 ball.
This is used at fixed particle number after the gauge has been selected. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace QuantumNLS.RetargetRoughR48b
open PhysicalTensor Sobolev ClassicalCharges
open RiccatiPointwiseDisc RiccatiExpansions Q07SobolevModelR24
variable {L : ℝ} [Fact (0 < L)]

def unitBall (R : ℝ) : Set (L2T L) :=
  {u | ‖u‖ = 1 ∧ ∃ v : H02 L 1, v.val = u ∧ ‖v‖ ≤ R}

/-- Genuine normalized smooth approximants in any strictly larger radius. -/
theorem mem_smooth_closure (R R' : ℝ) (hR : R < R') {u : L2T L}
    (hu : u ∈ unitBall (L := L) R) : u ∈ closure (R52CFCompact.profileClass L R') := by
  obtain ⟨hu, v, hv, hvR⟩ := hu
  let e := coordinates (L := L) (S := 1) zero_le_one
  let i := H02.toL2 (L := L) (s := 1) zero_le_one
  let x := e v
  let xJ := approx x
  let p (J : Finset ℤ) := i (e.symm (xJ J))
  have hp : Tendsto p atTop (𝓝 u) := by
    have h := (i.continuous.comp e.symm.continuous).continuousAt.tendsto.comp (approx_tendsto x)
    simpa only [Function.comp_def, x, LinearIsometryEquiv.symm_apply_apply, show i v = u from hv] using h
  have hpn : Tendsto (fun J => ‖p J‖) atTop (𝓝 (1 : ℝ)) := by
    simpa only [hu] using hp.norm
  let c (J : Finset ℤ) : ℂ := ((‖p J‖⁻¹ : ℝ) : ℂ)
  have hc : Tendsto c atTop (𝓝 (1 : ℂ)) := by
    simpa only [c, inv_one, Complex.ofReal_one, Function.comp_def] using
      (Complex.continuous_ofReal.continuousAt.tendsto.comp (hpn.inv₀ one_ne_zero))
  let y (J : Finset ℤ) := e.symm (c J • xJ J)
  have hy : Tendsto y atTop (𝓝 v) := by
    have hy' := e.symm.continuous.continuousAt.tendsto.comp (hc.smul (approx_tendsto x))
    simpa only [Function.comp_def, one_smul, x, LinearIsometryEquiv.symm_apply_apply] using hy'
  have hui : Tendsto (fun J => i (y J)) atTop (𝓝 u) := by
    have h := i.continuous.continuousAt.tendsto.comp hy
    simpa only [Function.comp_def, show i v = u from hv] using h
  apply mem_closure_of_tendsto hui
  filter_upwards [hpn.eventually (lt_mem_nhds one_pos),
    hy.norm.eventually (gt_mem_nhds (hvR.trans_lt hR))] with J hpJ hyJ
  have hnorm : ‖i (y J)‖ = 1 := by
    change ‖i (e.symm (c J • xJ J))‖ = 1
    rw [map_smul, map_smul, norm_smul]
    change ‖((‖p J‖⁻¹ : ℝ) : ℂ)‖ * ‖p J‖ = 1
    rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hpJ.le)]
    exact inv_mul_cancel₀ hpJ.ne'
  have hsm : SmoothPeriodic L (physRep L 1 (c J • xJ J)) := by
    rw [physRep_smul]
    have hs := approx_smooth (L := L) (S := 1) x J
    refine ⟨?_, ?_⟩
    · exact contDiff_const.mul hs.smooth
    · intro t
      exact congrArg (fun z : ℂ => c J * z) (hs.periodic t)
  have hrep : i (y J) = PhysicalProductPreparation.smoothClass hsm := by
    change (model (L := L) (S := 1) zero_le_one (c J • xJ J)).val = _
    rw [model_val]
    exact SmoothScalarMomentsPhysical.fieldMap_eq_smooth (by norm_num : (1:ℝ)/2 < 1)
      hsm (c J • xJ J) rfl
  refine ⟨⟨_, hsm, hrep⟩, hnorm, ?_⟩
  change Fourier.hsLpNormSq L 1 (y J).val ≤ R' ^ 2
  rw [← H02.norm_sq_eq]
  exact pow_le_pow_left₀ (norm_nonneg _) hyJ.le 2

end QuantumNLS.RetargetRoughR48b

#print axioms QuantumNLS.RetargetRoughR48b.mem_smooth_closure

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "QuantumNLS.RetargetRoughR48b." ||
        name.toString.startsWith "_private.QuantumNLS.RetargetRoughR48b." then
      pending := pending.push name
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    unless seen.contains name do
      seen := seen.insert name
      if (name.toString.splitOn "HeldGP14Tonelli").length > 1 then
        throwError "Rejected dependency: {name}"
      if let some info := env.find? name then
        match info with
        | .axiomInfo _ =>
          unless name == ``propext || name == ``Classical.choice || name == ``Quot.sound do
            throwError "Nonstandard dependency: {name}"
        | _ => pure ()
        pending := pending ++ info.type.getUsedConstants
        if let some value := info.value? (allowOpaque := true) then
          pending := pending ++ value.getUsedConstants
      else
        throwError "Missing dependency: {name}"
  Lean.logInfo m!"R48b aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only."
