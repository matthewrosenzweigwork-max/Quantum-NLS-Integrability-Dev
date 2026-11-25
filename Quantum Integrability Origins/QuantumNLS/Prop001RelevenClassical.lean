import QuantumNLS.Prop001RtenHierarchy

/-! PROP-001, thm:A2-bounded-propagation, first printed clause only.
Rank n+1 is the source rank r. The zero extension and first-slot
contraction appear explicitly in the equation. This is an assembly of the
frozen classical proof; it adds no hierarchy or propagation conclusion.
The next source-proof clause is stopped at FIN-EXT025-GP-09, whose general
mixed-state partial trace with trace-norm contraction is not supplied here. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators InnerProductSpace
namespace QuantumNLS.Prop001
open TensorCarrier TensorPlacements Ext025A8
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H

/-- The first sentence and equation A2-hartree, under the two printed rank
summability assumptions. Uniqueness is among global unit-sphere C1 solutions.
The actual vector field is displayed rather than assumed as a flow. -/
theorem thm_A2_bounded_propagation_classical
    (A : Interactions H) (hA : ∀ n, IsSelfAdjoint (A n))
    {a : ℝ} (ha : 0 < a)
    (hcubic : Summable (fun n => ((n + 1 : ℕ) : ℝ) ^ 3 * ‖A n‖))
    (hexp : Summable (fun n => (n + 1 : ℕ) * ‖A n‖ * Real.exp (a * n)))
    {u₀ : H} (hu₀ : ‖u₀‖ = 1) :
    ∃! u : ℝ → H, u 0 = u₀ ∧ ContDiff ℝ 1 u ∧
      (∀ t, ‖u t‖ = 1 ∧ HasDerivAt u
        ((-Complex.I) • ∑' n : ℕ,
          ((n + 1 : ℕ) : ℂ) • hartreeContraction (extendSymKernel (A n)) (u t) (u t)) t) := by
  obtain ⟨u, hzero, hC1, hode, huniq⟩ := classical A hA ha hcubic hexp hu₀
  refine ⟨u, ⟨hzero, hC1, ?_⟩, ?_⟩
  · simpa only [sourceHartreeField, hartreeField, hartreeTerm] using hode
  · intro v hv
    apply huniq v hv.1
    simpa only [sourceHartreeField, hartreeField, hartreeTerm] using hv.2.2

end QuantumNLS.Prop001

#print axioms QuantumNLS.Prop001.thm_A2_bounded_propagation_classical

run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.Prop001.thm_A2_bounded_propagation_classical]
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
            throwError "PROP001Releven nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some value := ci.value? (allowOpaque := true) then
          pending := pending ++ value.getUsedConstants
      else
        throwError "PROP001Releven missing dependency: {n}"
  Lean.logInfo m!"PROP001Releven aggregate audit PASS: {seen.size} transitive constants; 1 explicit roots; only standard dependencies. Author verification only."
