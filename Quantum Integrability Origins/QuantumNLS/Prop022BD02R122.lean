import QuantumNLS.Ext006BD02R44a

/-! The reviewed source-Weyl BD-02 theorem replaces the former reserved input.
This bridge is at the original S. The quadratic propagator's covariance and
the actual classical flow's HS estimate are separate obligations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.Prop022BD02R122
open Ext006KernelHilbertSchmidt Ext006OriginalVacuumR42a Ext006SourceWeylR44a
open Ext006NumberPhase Ext006PhysQuasifree Ext006PhysFockCoord
variable {L : ℝ} [Fact (0 < L)]
attribute [local instance] InnerProductSpace.complexToReal

/-- Proved replacement for the old unproved BD-02 reservation. The reviewed
headline supplies a forward source-Weyl implementer and its correctly oriented
vacuum, and fixes the number expectation of every such implementer. -/
theorem PROP022_BD02_forward_implementer_and_vacuum_R122
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    ∃ U : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L,
      SourceWeylImplementer S U ∧ U vac = originalVacuum S hS hβ ∧
      ‖U vac‖ = 1 ∧
      ∀ V : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L,
        SourceWeylImplementer S V →
        (∃ z : ℂ, ‖z‖ = 1 ∧ ∀ x, V x = z • U x) ∧
        numberExpectation (fun n => (n : ℝ≥0∞)) (V vac) =
          TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ∧
        numberExpectation (fun n => (n : ℝ≥0∞)) (V vac) ≠ ⊤ := by
  have h := Ext006BD02R44a.«FIN-CORE-BD-02» S hS hβ
  dsimp only at h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, U, hU, hvac, _, _, hall⟩ := h
  refine ⟨U, hU, hvac, ?_, ?_⟩
  · rw [hvac]
    exact originalVacuum_norm S hS hβ
  · intro V hV
    have hh := hall V hV
    exact ⟨hh.1, hh.2.2.2.2.1, hh.2.2.2.2.2.1⟩

end QuantumNLS.Prop022BD02R122
#print axioms QuantumNLS.Prop022BD02R122.PROP022_BD02_forward_implementer_and_vacuum_R122

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022BD02R122." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022BD02R122." then
      pending := pending.push n
  let roots := pending.size
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
  Lean.logInfo m!"R122 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
