import QuantumNLS.Def024CubicSmoothEquation
import QuantumNLS.Def024CubicClassical

/-! DEF-024 r=2 D3 Flow: actual global Sobolev solution reconstruction. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open Filter MeasureTheory QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.LocalWellPosedness QuantumNLS.LocalWellPosednessFull QuantumNLS.F04Regularity
open QuantumNLS.ClassicalCharges QuantumNLS.ChargeEnergy QuantumNLS.HierarchyFlow
open QuantumNLS.Def024CubicSmoothData QuantumNLS.Def024CubicSmoothEmbedding
open QuantumNLS.Def024CubicSmoothNonlinearity QuantumNLS.Def024CubicSmoothTime
open QuantumNLS.Def024CubicSmoothEvaluation QuantumNLS.Def024CubicGradient
open QuantumNLS.Def024CubicSmoothJoint QuantumNLS.Def024CubicSmoothEquation
namespace QuantumNLS.Def024CubicSmoothFlow
variable {L : ℝ} [Fact (0 < L)]

/-- A total map on profiles, with the classical flow on every smooth periodic input. -/
def Φ (κ t : ℝ) (u : ℝ → ℂ) : ℝ → ℂ := by
  classical
  exact if hu : SmoothPeriodic L u then profile hu κ t else u

lemma Φ_of_smooth {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (κ t : ℝ) :
    Φ (L := L) κ t u = profile hu κ t := by simp [Φ, hu]

theorem Φ_zero (κ : ℝ) (hκ : 0 ≤ κ) (u : ℝ → ℂ) : Φ (L := L) κ 0 u = u := by
  classical
  by_cases hu : SmoothPeriodic L u
  · rw [Φ_of_smooth hu]
    exact profile_zero hu hκ
  · simp only [Φ, dite_eq_right hu]

/-- The requested r=2 Hamiltonian flow exists, constructed from persist_global's umax. -/
theorem isHamFlow (κ : ℝ) (hκ : 0 ≤ κ) :
    IsHamFlow L (hamiltonian L κ 2) (Φ (L := L) κ) := by
  apply (QuantumNLS.Def024CubicClassical.isHamFlow_two_iff Fact.out κ (Φ (L := L) κ)).mpr
  intro u hu
  simp only [Φ_of_smooth hu]
  exact ⟨profile_zero hu hκ, joint_smooth hu hκ,
    fun t => ⟨smoothPeriodic_profile hu hκ t, profile_equation hu hκ t⟩⟩


#print axioms Φ_zero
#print axioms Φ_of_smooth
#print axioms isHamFlow
end QuantumNLS.Def024CubicSmoothFlow

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Def024CubicSmoothFlow." ||
        n.toString.startsWith "_private.QuantumNLS.Def024CubicSmoothFlow." then
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
