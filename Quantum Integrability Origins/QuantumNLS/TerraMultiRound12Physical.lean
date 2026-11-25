import QuantumNLS.TerraMultiRound12Definitions
import QuantumNLS.UnconditionalBetheBasis
import QuantumNLS.PhysicalQuantumMeasure

/-! Bind the round-12 definitions to the existing physical mean-field basis,
product Born weights, scalar transfer, and full-mass measure. These definitions
assert no asymptotic limit and no existence of the classical hierarchy. -/
set_option autoImplicit false
noncomputable section
open Filter MeasureTheory Topology
open scoped ENNReal InnerProductSpace
namespace QuantumNLS.TerraMultiRound12Physical
open QuantumNLS.BetheCoefficientTransform QuantumNLS.BetheSpectralCharges
  QuantumNLS.BetheLabels QuantumNLS.TerraMultiRound12Definitions

variable {L : ℝ} [Fact (0 < L)]

/-- The quantum joint hierarchy flow in the physical mean-field Bethe basis. -/
def quantumFlow (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 1 ≤ N)
    (R : Finset ℕ) (t : ℕ → ℝ) : HN L N ≃ₗᵢ[ℂ] HN L N :=
  QuantumNLS.HierarchyFlow.quantumFlow
    (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ) κ R t

/-- The physical flow has the joint charge-eigenvalue phase of DEF-024. -/
theorem quantumFlow_coord (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 1 ≤ N)
    (R : Finset ℕ) (t : ℕ → ℝ) (ψ : HN L N) (m : MArr N) :
    ⟪QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ m,
      quantumFlow κ hκ N hN R t ψ⟫_ℂ =
      Complex.exp (-((∑ r ∈ R, t r * eigenvalue L N (κ / N) r m : ℝ) : ℂ) * Complex.I) *
        ⟪QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ m, ψ⟫_ℂ :=
  QuantumNLS.HierarchyFlow.quantumFlow_coord _ κ R t ψ m

/-- DEF-033 convergence under the original physical product Born law. Positive
particle numbers are indexed as N+1; the missing-sector value is explicit. -/
def PhysicalBornDifferenceConverges (κ : ℝ) (hκ : 0 < κ)
    (u : QuantumNLS.PhysicalTensor.L2T L) (r : ℕ) (a b : ℤ) (ω : ℤ → ℝ)
    (missing : ∀ N, MArr (N + 1) → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun N : ℕ =>
    ∑' m : MArr (N + 1),
      if ε < |extendedDifference L κ (N + 1) r a b (missing N) m - frequencyTarget ω a b|
      then ENNReal.ofReal (bornLaw
        (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L (N + 1) (by omega) hκ) u m)
      else 0) atTop (𝓝 0)

/-- The DEF-044 action-dependence clause, instantiated with the existing
product scalar transfer and the physical full-mass measure. This is a
predicate, not a claim that the clause has been established. -/
def PhysicalActionDetermination {κ : ℝ} (hκ : 0 < κ)
    (D : QuantumNLS.IndexedMassProperness.IndexedMassData L κ) : Prop :=
  ActionDeterminesScalarAndMeasure D
    (QuantumNLS.NormalizedTransfer.productSymbol L κ)
    (QuantumNLS.PhysicalQuantumMeasure.measure hκ)

#print axioms quantumFlow_coord

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.TerraMultiRound12Physical." then
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
  Lean.logInfo m!"TerraMultiRound12Physical audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
end QuantumNLS.TerraMultiRound12Physical
