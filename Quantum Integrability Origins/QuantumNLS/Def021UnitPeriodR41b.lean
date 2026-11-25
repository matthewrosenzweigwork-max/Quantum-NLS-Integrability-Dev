import QuantumNLS.Def021CouplingR41b

/-! The literal DEF-021 rescaling predicate at period one, on actual L2
classes, and the displayed normalization identity for the actual chart. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
namespace QuantumNLS.Def021UnitPeriodR41b
open MeasureTheory PhysicalTensor Def021ChartR41b HierarchyScaling

theorem dilation_one (x : AddCircle (1 : ℝ)) : dilation 1 x = x := by
  induction x using QuotientAddGroup.induction_on with
  | H x => simp [dilation]

theorem rescaling_one_iff (κ : ℝ) (u v : L2T 1) :
    IsRescaling 1 κ u v ↔ v = (Real.sqrt κ : ℂ) • u := by
  constructor
  · intro h
    apply Lp.ext
    filter_upwards [h, Lp.coeFn_smul (Real.sqrt κ : ℂ) u] with x hx hs
    rw [hs]
    simpa only [one_mul, dilation_one, smul_eq_mul, Pi.smul_apply] using hx
  · intro h
    subst v
    filter_upwards [Lp.coeFn_smul (Real.sqrt κ : ℂ) u] with x hx
    simpa only [one_mul, dilation_one, smul_eq_mul, Pi.smul_apply] using hx

/-- Every term of the source formula, including the ae physical rescaling,
is verified at unit period. General period conversion remains separate. -/
theorem normalization_one {κ : ℝ} (hκ : 0 < κ) (u v : L2T 1)
    (hv : IsRescaling 1 κ u v) :
    Phi 1 κ u = ((scalingFactor 1 κ : ℝ) : ℂ) • Phi 1 1 v := by
  have he : Real.sqrt κ • u = v := by
    rw [(rescaling_one_iff κ u v).1 hv, Complex.coe_smul]
    rfl
  simpa only [scalingFactor, mul_one, he] using
    Def021CouplingR41b.unit_coupling_rpow (L := 1) hκ u

end QuantumNLS.Def021UnitPeriodR41b

#print axioms QuantumNLS.Def021UnitPeriodR41b.dilation_one
#print axioms QuantumNLS.Def021UnitPeriodR41b.rescaling_one_iff
#print axioms QuantumNLS.Def021UnitPeriodR41b.normalization_one

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Def021UnitPeriodR41b." ||
        n.toString.startsWith "_private.QuantumNLS.Def021UnitPeriodR41b." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 then
        throwError "Rejected dependency: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"R41b aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only."
