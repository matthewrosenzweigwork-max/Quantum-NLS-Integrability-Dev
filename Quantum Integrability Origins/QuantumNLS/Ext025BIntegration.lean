import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Analytic.Basic

/-! GP-16 support: the vector integral and weak scalar covector average.
The compact-image/simple-function construction is descriptive prose for the
standard Bochner integral. No operator-norm measurability of a strongly
continuous operator family is used below. The full analytic-coefficient clause
is separately recorded as OPEN in the receipt until its exact series is proved. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Topology
namespace QuantumNLS.Ext025BIntegration
variable {X E F : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {μ : Measure X}

/-- The interval case under precisely strong measurability and integrable norm. -/
theorem «FIN-EXT025-GP-16-integrable» (f : X → E)
    (hm : AEStronglyMeasurable f μ) (hn : Integrable (fun x => ‖f x‖) μ) :
    Integrable f μ ∧ ‖∫ x, f x ∂μ‖ ≤ ∫ x, ‖f x‖ ∂μ ∧
      ∀ T : E →L[ℝ] F, (∫ x, T (f x) ∂μ) = T (∫ x, f x ∂μ) := by
  have hf : Integrable f μ := (integrable_norm_iff hm).mp hn
  exact ⟨hf, norm_integral_le_integral_norm f, fun T => T.integral_comp_comm hf⟩

/-- Compact-Haar vector case; the measure only needs to be finite. -/
theorem «FIN-EXT025-GP-16-compact» [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [BorelSpace X] [IsFiniteMeasure μ]
    (f : X → E) (hf : Continuous f) :
    Integrable f μ ∧ ‖∫ x, f x ∂μ‖ ≤ ∫ x, ‖f x‖ ∂μ ∧
      ∀ T : E →L[ℝ] F, (∫ x, T (f x) ∂μ) = T (∫ x, f x ∂μ) := by
  have hi : Integrable f μ := by
    simpa using (hf.continuousOn.integrableOn_compact (μ := μ) isCompact_univ)
  exact ⟨hi, norm_integral_le_integral_norm f, fun T => T.integral_comp_comm hi⟩

omit [CompleteSpace E] in
/-- Weakly measurable uniformly bounded linear scalar evaluations have an
integrable scalar evaluation, without measurability into the normed dual. -/
theorem scalar_integrable [IsProbabilityMeasure μ] (a : X → E →ₗ[ℝ] ℝ)
    (C : ℝ) (_hC : 0 ≤ C) (hm : ∀ v, Measurable (fun x => a x v))
    (hb : ∀ x v, ‖a x v‖ ≤ C * ‖v‖) (v : E) :
    Integrable (fun x => a x v) μ :=
  Integrable.of_bound (hm v).aestronglyMeasurable (C * ‖v‖)
    (Filter.Eventually.of_forall (fun x => hb x v))

/-- The covector average is constructed only from scalar evaluations. -/
def averageCovector [IsProbabilityMeasure μ] (a : X → E →ₗ[ℝ] ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hm : ∀ v, Measurable (fun x => a x v))
    (hb : ∀ x v, ‖a x v‖ ≤ C * ‖v‖) : E →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun v => ∫ x, a x v ∂μ
      map_add' := fun v w => by
        simp_rw [map_add]
        exact integral_add (scalar_integrable a C hC hm hb v)
          (scalar_integrable a C hC hm hb w)
      map_smul' := fun c v => by simp [integral_const_mul] }
    C (fun v => by
      simpa using norm_integral_le_of_norm_le_const
        (μ := μ) (C := C * ‖v‖) (Filter.Eventually.of_forall (fun x => hb x v)))

omit [CompleteSpace E] in
/-- GP-16 scalar-average conclusion; full analytic clause is still open. -/
theorem «FIN-EXT025-GP-16-covector» [IsProbabilityMeasure μ]
    (a : X → E →ₗ[ℝ] ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hm : ∀ v, Measurable (fun x => a x v)) (hb : ∀ x v, ‖a x v‖ ≤ C * ‖v‖) :
    ∃ A : E →L[ℝ] ℝ, (∀ v, A v = ∫ x, a x v ∂μ) ∧ ‖A‖ ≤ C := by
  refine ⟨averageCovector a C hC hm hb, fun _ => rfl, ?_⟩
  exact LinearMap.mkContinuous_norm_le _ hC _

omit [CompleteSpace E] [CompleteSpace F] in
/-- Integrability is checked on each vector, with no operator-space
measurability assumption. -/
theorem operator_integrable [IsProbabilityMeasure μ] (a : X → E →ₗ[ℝ] F)
    (C : ℝ) (hm : ∀ v, AEStronglyMeasurable (fun x => a x v) μ)
    (hb : ∀ x v, ‖a x v‖ ≤ C * ‖v‖) (v : E) :
    Integrable (fun x => a x v) μ :=
  Integrable.of_bound (hm v) (C * ‖v‖)
    (Filter.Eventually.of_forall (fun x => hb x v))

/-- Vectorwise strong operator integral. -/
def operatorAverage [IsProbabilityMeasure μ] (a : X → E →ₗ[ℝ] F)
    (C : ℝ) (hm : ∀ v, AEStronglyMeasurable (fun x => a x v) μ)
    (hb : ∀ x v, ‖a x v‖ ≤ C * ‖v‖) : E →L[ℝ] F :=
  LinearMap.mkContinuous
    { toFun := fun v => ∫ x, a x v ∂μ
      map_add' := fun v w => by
        simp_rw [map_add]
        exact integral_add (operator_integrable a C hm hb v)
          (operator_integrable a C hm hb w)
      map_smul' := fun c v => by simp [integral_smul] }
    C (fun v => by
      simpa using norm_integral_le_of_norm_le_const
        (μ := μ) (C := C * ‖v‖) (Filter.Eventually.of_forall (fun x => hb x v)))

omit [CompleteSpace E] in
/-- GP-16 operator wrapper, including all scalar pairings used to identify an
adjoint. Only vectorwise measurability is required. -/
theorem «FIN-EXT025-GP-16-strong-operator-average» [IsProbabilityMeasure μ]
    (a : X → E →ₗ[ℝ] F) (C : ℝ) (hC : 0 ≤ C)
    (hm : ∀ v, AEStronglyMeasurable (fun x => a x v) μ)
    (hb : ∀ x v, ‖a x v‖ ≤ C * ‖v‖) :
    ∃ A : E →L[ℝ] F, (∀ v, A v = ∫ x, a x v ∂μ) ∧ ‖A‖ ≤ C ∧
      ∀ (ℓ : F →L[ℝ] ℝ) v, ℓ (A v) = ∫ x, ℓ (a x v) ∂μ := by
  refine ⟨operatorAverage a C hm hb, fun _ => rfl,
    LinearMap.mkContinuous_norm_le _ hC _, ?_⟩
  intro ℓ v
  exact (ℓ.integral_comp_comm (operator_integrable a C hm hb v)).symm

end QuantumNLS.Ext025BIntegration

#print axioms QuantumNLS.Ext025BIntegration.«FIN-EXT025-GP-16-integrable»
#print axioms QuantumNLS.Ext025BIntegration.«FIN-EXT025-GP-16-compact»
#print axioms QuantumNLS.Ext025BIntegration.scalar_integrable
#print axioms QuantumNLS.Ext025BIntegration.averageCovector
#print axioms QuantumNLS.Ext025BIntegration.«FIN-EXT025-GP-16-covector»

#print axioms QuantumNLS.Ext025BIntegration.operator_integrable
#print axioms QuantumNLS.Ext025BIntegration.operatorAverage
#print axioms QuantumNLS.Ext025BIntegration.«FIN-EXT025-GP-16-strong-operator-average»

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants do
    if n.toString.startsWith "QuantumNLS.Ext025BIntegration." then
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
  Lean.logInfo m!"Ext025BIntegration audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
