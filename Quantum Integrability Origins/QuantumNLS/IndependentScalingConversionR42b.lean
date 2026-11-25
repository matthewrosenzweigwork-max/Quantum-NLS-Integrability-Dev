import QuantumNLS.PeriodChartR42b

/-! R-71F7DDC8, scaling_and_phase_freedom.tex:3–47. Both equalities
hold for the selected R41b chart family. The DEF-021 corollary uses its
original ae predicate and literal negative-half-power coefficient. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open MeasureTheory
namespace QuantumNLS.IndependentScalingConversionR42b
open PhysicalTensor (L2T)
open PeriodFieldR42b Def021ChartR41b HierarchyScaling
variable (L κ : ℝ) [Fact (0 < L)]

/-- The standard unit-coupling spectral potential L sqrt(kappa) u(L dot). -/
def unitPotential (u : L2T L) : L2T 1 := Real.sqrt (κ*L) • period L u

theorem sqrt_conversion (hκ : 0 < κ) : Real.sqrt (κ*L)*Real.sqrt L = L*Real.sqrt κ := by
  rw [Real.sqrt_mul hκ.le]
  calc
    Real.sqrt κ * Real.sqrt L * Real.sqrt L = Real.sqrt κ * (Real.sqrt L)^2 := by ring
    _ = L*Real.sqrt κ := by rw [Real.sq_sqrt (Fact.out : 0 < L).le]; ring

theorem unitPotential_ae (hκ : 0 < κ) (u : L2T L) :
    (unitPotential L κ u : AddCircle (1:ℝ) → ℂ) =ᵐ[volume]
      fun x => ((L*Real.sqrt κ:ℝ):ℂ)*u (dilation L x) := by
  filter_upwards [Lp.coeFn_smul (Real.sqrt (κ*L)) (period L u), period_ae L u] with x hx hp
  rw [show (unitPotential L κ u : AddCircle (1:ℝ) → ℂ) x =
    (Real.sqrt (κ*L):ℂ)*(period L u : AddCircle (1:ℝ) → ℂ) x by
      simpa only [unitPotential, Pi.smul_apply, Complex.real_smul] using hx, hp, ← mul_assoc]
  congr 1
  exact_mod_cast sqrt_conversion L κ hκ

theorem rescaling_iff (hκ : 0 < κ) (u : L2T L) (v : L2T 1) :
    IsRescaling L κ u v ↔ v = unitPotential L κ u := by
  constructor
  · intro hv
    apply Lp.ext
    filter_upwards [hv, unitPotential_ae L κ hκ u] with x hx hp
    exact hx.trans hp.symm
  · intro hv
    subst v
    exact unitPotential_ae L κ hκ u

/-- **Independent scaling conversion (R-71F7DDC8).** The first and last
members of the printed chain are equal for every physical input. -/
theorem independent_scaling_conversion (hκ : 0 < κ) (u : L2T L) :
    Phi L κ u = Phi 1 (κ*L) (period L u) ∧
    Phi L κ u = (Real.sqrt (κ*L))⁻¹ • Phi 1 1 (unitPotential L κ u) := by
  refine ⟨PeriodChartR42b.period_conversion hκ u, ?_⟩
  rw [PeriodChartR42b.period_conversion hκ u]
  exact Def021CouplingR41b.unit_coupling (mul_pos hκ (Fact.out : 0 < L)) (period L u)

/-- DEF-021's full displayed arbitrary-period formula for the R41b objects. -/
theorem def021_arbitrary_period_formula : PeriodCouplingNormalization Phi := by
  intro L _ κ hκ u v hv
  have hκL : 0 < κ*L := mul_pos hκ (Fact.out : 0 < L)
  have he := (rescaling_iff L κ hκ u v).1 hv
  rw [PeriodChartR42b.period_conversion hκ u, he]
  change Phi 1 (κ*L) (period L u) =
    ((scalingFactor L κ:ℝ):ℂ) • Phi 1 1 (Real.sqrt (κ*L) • period L u)
  exact Def021CouplingR41b.unit_coupling_rpow hκL (period L u)

end QuantumNLS.IndependentScalingConversionR42b

#print axioms QuantumNLS.IndependentScalingConversionR42b.sqrt_conversion
#print axioms QuantumNLS.IndependentScalingConversionR42b.unitPotential_ae
#print axioms QuantumNLS.IndependentScalingConversionR42b.rescaling_iff
#print axioms QuantumNLS.IndependentScalingConversionR42b.independent_scaling_conversion
#print axioms QuantumNLS.IndependentScalingConversionR42b.def021_arbitrary_period_formula

#check @QuantumNLS.IndependentScalingConversionR42b.independent_scaling_conversion
#check @QuantumNLS.IndependentScalingConversionR42b.def021_arbitrary_period_formula

-- R42b final aggregate audit
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.IndependentScalingConversionR42b." ||
        n.toString.startsWith "_private.QuantumNLS.IndependentScalingConversionR42b." then
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
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"R42b aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only."

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.IndependentScalingConversionR42b.independent_scaling_conversion,
    ``QuantumNLS.IndependentScalingConversionR42b.def021_arbitrary_period_formula]
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing headline dependency: {n}"
  for n in #[``QuantumNLS.Def021ChartR41b.Phi,
      ``QuantumNLS.GlobalCompatR47a.global_compatibility,
      ``QuantumNLS.PeriodMeasureR42b.masses_scale,
      ``QuantumNLS.PeriodSpatialR42b.discriminant_scale] do
    unless seen.contains n do
      throwError "Missing required source binding: {n}"
  Lean.logInfo m!"R42b headline source bindings PASS: selected R41b Phi; named global_compatibility; actual indexed masses; literal L2 discriminant. {seen.size} dependencies."
