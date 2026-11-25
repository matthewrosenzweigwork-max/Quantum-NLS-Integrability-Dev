import QuantumNLS.Ext006FiniteTraceR40a

/-! The all-degree physical norm recurrence now contains the ACTUAL trace
powers of K* K. The completed physical terms retain -a*(K)/2 and factorials. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open scoped InnerProductSpace ENNReal
open Filter Topology
namespace QuantumNLS.Ext006ActualNormTraceR40a
open TraceClass Ext006CompressionR32a Ext006FiniteTraceR40a
open Ext006PhysicalApproximationR38a Ext006PhysicalExponentialTerms
open Ext006PhysicalNormBridge.PairTensor Ext006PhysicalSeriesR39a
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The literal finite compression trace converges to the actual operator trace. -/
theorem compression_trace_tendsto (b : HilbertBasis ℤ ℂ H) (K : H →L[ℂ] H)
    (hHS : hsSq b K ≠ ⊤) (n : ℕ) :
    Tendsto (fun S : Finset ℤ =>
      (((Ext006CoreNorm.Tm S (coordinates b K))^(n+1)).trace).re) atTop
      (𝓝 ((traceNorm ((K.adjoint ∘L K)^(n+1))).toReal)) := by
  simpa only [finite_density_trace_power] using
    Ext006TracePowersR40a.adjoint_density_trace_power_limit b K hHS n

variable {L : ℝ} [Fact (0 < L)]

/-- The finite physical CCR recurrence passes to actual completed physical
terms and actual infinite-dimensional trace powers, in every degree. -/
theorem actual_physical_trace_recurrence
    (K : PhysicalTensor.L2T L →L[ℂ] PhysicalTensor.L2T L)
    (hSym : ∀ i j, coordinates (Ext006KernelHilbertSchmidt.physicalBasis L) K i j =
      coordinates (Ext006KernelHilbertSchmidt.physicalBasis L) K j i)
    (hHS : hsSq (Ext006KernelHilbertSchmidt.physicalBasis L) K ≠ ⊤) (n : ℕ) :
    2 * (n : ℝ) * ‖term (physicalPair (Ext006KernelHilbertSchmidt.physicalBasis L) K hHS hSym) n‖^2 =
      ∑ j ∈ Finset.range n,
        ‖term (physicalPair (Ext006KernelHilbertSchmidt.physicalBasis L) K hHS hSym) (n-1-j)‖^2 *
        (traceNorm ((K.adjoint ∘L K)^(j+1))).toReal := by
  let b := Ext006KernelHilbertSchmidt.physicalBasis L
  have ht : ∀ m : ℕ, Tendsto (fun S : Finset ℤ => ‖term (finitePair b K S) m‖^2) atTop
      (𝓝 (‖term (physicalPair b K hHS hSym) m‖^2)) :=
    fun m => (finitePair_term_tendsto b K hHS hSym m).norm.pow 2
  have hl := (ht n).const_mul (2*(n:ℝ))
  have hr := tendsto_finsetSum (Finset.range n) (fun j _ =>
    (ht (n-1-j)).mul (compression_trace_tendsto b K hHS j))
  apply tendsto_nhds_unique hl
  apply hr.congr'
  filter_upwards [] with S
  exact (finite_physical_trace_recurrence K hSym S n).symm

end QuantumNLS.Ext006ActualNormTraceR40a
#print axioms QuantumNLS.Ext006ActualNormTraceR40a.compression_trace_tendsto
#print axioms QuantumNLS.Ext006ActualNormTraceR40a.actual_physical_trace_recurrence

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006ActualNormTraceR40a." then
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
  Lean.logInfo m!"Round40a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
