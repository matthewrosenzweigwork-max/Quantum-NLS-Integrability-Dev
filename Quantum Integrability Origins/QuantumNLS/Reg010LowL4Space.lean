import QuantumNLS.Reg010LowCorrection

/-! The native L⁴ carrier and its continuous inclusion into physical L². -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace QuantumNLS.Reg010LowL4Space
open QuantumNLS.PhysicalTensor
variable {L : ℝ} [Fact (0 < L)]

instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

abbrev L4T (L : ℝ) [Fact (0 < L)] : Type := Lp ℂ 4 (volume : Measure (AddCircle L))

def toL2 (u : L4T L) : L2T L :=
  ((Lp.memLp u).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)).toLp u

theorem toL2_ae (u : L4T L) : toL2 u =ᵐ[volume] u := MemLp.coeFn_toLp _

def inclusionConstant (L : ℝ) [Fact (0 < L)] : ℝ :=
  ((volume : Measure (AddCircle L)) univ).toReal ^ (1 / 4 : ℝ)

theorem toL2_norm (u : L4T L) : ‖toL2 u‖ ≤ inclusionConstant L * ‖u‖ := by
  rw [toL2, Lp.norm_toLp]
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (by norm_num : (2 : ℝ≥0∞) ≤ 4) (Lp.aestronglyMeasurable u)
  calc
    _ ≤ (eLpNorm u 4 volume * (volume univ) ^ (1 / (2 : ℝ≥0∞).toReal - 1 / (4 : ℝ≥0∞).toReal)).toReal :=
      ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top u)
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _))) h
    _ = _ := by
      rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
      norm_num [inclusionConstant, Lp.norm_def]
      ring

def toL2Linear : L4T L →ₗ[ℂ] L2T L where
  toFun := toL2
  map_add' u v := by
    apply Lp.ext
    filter_upwards [toL2_ae (u + v), toL2_ae u, toL2_ae v, Lp.coeFn_add u v,
      Lp.coeFn_add (toL2 u) (toL2 v)] with x h1 h2 h3 h4 h5
    rw [h1, h5, Pi.add_apply, h4, Pi.add_apply, h2, h3]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [toL2_ae (c • u), toL2_ae u, Lp.coeFn_smul c u,
      Lp.coeFn_smul c (toL2 u)] with x h1 h2 h3 h4
    change toL2 (c • u) x = (c • toL2 u) x
    rw [h1, h4, Pi.smul_apply, h3, Pi.smul_apply, h2]

def toL2CLM : L4T L →L[ℂ] L2T L :=
  toL2Linear.mkContinuous (inclusionConstant L) toL2_norm

theorem toL2_continuous : Continuous (toL2 (L := L)) := toL2CLM.continuous

theorem fourth_integrable (u : L4T L) : Integrable (fun x => ‖u x‖ ^ 4) volume := by
  have h := ((Lp.memLp u).norm_rpow (by norm_num) (by norm_num)).integrable (by norm_num)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat] using h

theorem fourth_integral (u : L4T L) : (∫ x, ‖u x‖ ^ 4) = ‖u‖ ^ 4 := by
  have hn : ‖u‖ = (∫ x, ‖u x‖ ^ 4) ^ (1 / 4 : ℝ) := by
    rw [Lp.norm_def, MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) (Lp.memLp u),
      ENNReal.toReal_ofReal (by positivity)]
    norm_num only [ENNReal.toReal_ofNat, Real.rpow_ofNat, invOf_eq_inv, one_div]
  rw [hn, ← Real.rpow_natCast, ← Real.rpow_mul (integral_nonneg (fun x => by positivity))]
  norm_num

theorem toL2_fourth_integrable (u : L4T L) :
    Integrable (fun x => ‖toL2 u x‖ ^ 4) volume :=
  (fourth_integrable u).congr ((toL2_ae u).fun_comp (fun z : ℂ => ‖z‖ ^ 4)).symm

theorem toL2_fourth_integral (u : L4T L) : (∫ x, ‖toL2 u x‖ ^ 4) = ‖u‖ ^ 4 := by
  rw [← fourth_integral u]
  exact integral_congr_ae ((toL2_ae u).fun_comp (fun z : ℂ => ‖z‖ ^ 4))

#print axioms toL2_ae
#print axioms toL2_norm
#print axioms toL2_continuous
#print axioms fourth_integrable
#print axioms fourth_integral
#print axioms toL2_fourth_integrable
#print axioms toL2_fourth_integral
end QuantumNLS.Reg010LowL4Space

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Reg010LowL4Space." ||
        n.toString.startsWith "_private.QuantumNLS.Reg010LowL4Space." then
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
