import QuantumNLS.Local014KernelFieldR29m
import QuantumNLS.Local014Interval
import QuantumNLS.IndexedUnitRayR30b

/-!
LOCAL-016 is the scoped consumer of LOCAL-014. Its actual invocation in
`IndexedUnitRayR30b.actual_unit_ray` takes the indexed mass as `F`, the Hermitian
contour Hamiltonians as `HN`, and the solution of that same indexed-mass field
as the trajectory. Here the interval form of accepted LOCAL-014 is specialized
to those data, with continuity of the exact state derivative as a conclusion.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace QuantumNLS.Local014ActualUseR29m

open Filter Topology
open PhysicalTensor (L2T)
open SymplecticBracket RootMassInvolutionR8 IndexedGlobalR27b
open IndexedHermitianR30b IndexedPrincipalBindingR30b IndexedProductStatesR30b
open Local014RealSymbol (hReal)
open TensorCarrier KernelDefinition Ext025A12Trace TraceClass
open Local014Heisenberg Local014OneBody Local014Main

attribute [local instance] InnerProductSpace.complexToReal

variable {L κ : ℝ} [Fact (0 < L)]

/-- The analytic kernel representative for the very contour Hamiltonians
used in LOCAL-016 also has a continuous state derivative on its open ball. -/
theorem continuousOn_contour_field_derivative (hκ : 0 < κ)
    (hs : κ * L ≤ 1 / 1000000000000) (n : ℤ) :
    ContinuousOn (fderiv ℝ (hamField (hReal (hamiltonianLimit (L := L) κ n))))
      (Metric.ball (0 : L2T L) (Real.sqrt 8)) :=
  Local014KernelFieldR29m.continuousOn_kernel_field_derivative (hamiltonian_converges hκ hs n)

/-- The derivative takes values in bounded real linear maps on the full
physical space. The Hamiltonian is the very `F` at the LOCAL-016 call site. -/
theorem continuous_actual_field_derivative (hκ : 0 < κ) (n : ℤ) :
    Continuous (fderiv ℝ (hamField (mass (L := L) hκ n))) :=
  continuous_iff_continuousAt.mpr fun u =>
    (IndexedFieldR27b.analytic_field hκ n u).fderiv.continuousAt

/-- The registered LOCAL-016 use of LOCAL-014, with the same Hamiltonians,
mass, trajectory and product states, on every interval containing zero. -/
theorem actual_egorov_on (hκ : 0 < κ) (hs : κ * L ≤ 1 / 1000000000000)
    (n : ℤ) (u : L2T L) (hu : ‖u‖ = 1) {I : Set ℝ} (hI : I.OrdConnected) (hI0 : 0 ∈ I) :
    Continuous (fderiv ℝ (hamField (mass (L := L) hκ n))) ∧
    (∀ t ∈ I, ∀ (q : ℕ) (B : BoundedSymmetricKernel (L2T L) q),
      Tendsto (fun N => if h : q ≤ N then
          tr (productDensity u N *
            (opExp ((Complex.I * (t : ℂ) * (N : ℂ)) • hamiltonian (L := L) κ n N) *
              RadiusBound.Q N q h B *
              opExp (-((Complex.I * (t : ℂ) * (N : ℂ)) • hamiltonian (L := L) κ n N))))
          else 0)
        atTop (𝓝 (kernelProductSymbol B (flow hκ n t u)))) ∧
    (∀ t ∈ I, Tendsto (fun N => traceNorm
      (oneBody N (evolve N (hamiltonian (L := L) κ n N) (productDensity u N) t) -
        InnerProductSpace.rankOne ℂ (flow hκ n t u) (flow hκ n t u))) atTop (𝓝 0)) := by
  have egorov := Local014Interval.local014_analytic_egorov_interval
    (H := L2T L) (hamiltonian (L := L) κ n)
    (hamiltonian_selfAdjoint (L := L) κ n) (hamiltonian_expansion (L := L) κ n)
    (hamiltonian_converges hκ hs n)
    (mass hκ n)
    (fun v _ => (DEF014MassAnalytic.analyticAt_physical_coordinate hκ n v).differentiableAt)
    (fun v hv => (principal_symbol_actual_mass hκ hs n v hv).symm)
    hu hI hI0 (phi := fun t => flow hκ n t u) (flow_initial hκ n u)
    (fun t _ => (flow_derivative hκ n u t).hasDerivWithinAt)
    (fun t _ => (flow_norm hκ n u t).trans hu)
    (productDensity u) (product_normal hu) (product_condensation hu)
  exact ⟨continuous_actual_field_derivative hκ n, egorov.2⟩

end QuantumNLS.Local014ActualUseR29m

#print axioms QuantumNLS.Local014ActualUseR29m.continuousOn_contour_field_derivative
#print axioms QuantumNLS.Local014ActualUseR29m.continuous_actual_field_derivative
#print axioms QuantumNLS.Local014ActualUseR29m.actual_egorov_on

set_option maxHeartbeats 24000000 in
run_cmd do
  let env ← Lean.getEnv
  let prefixes := #["QuantumNLS.Local014KernelFieldR29m.", "QuantumNLS.Local014ActualUseR29m."]
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if prefixes.any (fun p => n.toString.startsWith p || n.toString.startsWith ("_private." ++ p)) then
      pending := pending.push n
  unless pending.size ≥ 10 do
    throwError "Incomplete declaration audit root set"
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if ["HeldGP14Tonelli", "RegularCut"].any (fun s => (n.toString.splitOn s).length > 1) then
        throwError "Rejected dependency: {n}"
      let some ci := env.find? n | throwError "Missing dependency: {n}"
      match ci with
      | .axiomInfo _ =>
        unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
          throwError "Nonstandard axiom: {n}"
      | _ => pure ()
      pending := pending ++ ci.type.getUsedConstants
      if let some value := ci.value? (allowOpaque := true) then
        pending := pending ++ value.getUsedConstants
  Lean.logInfo m!"R29m aggregate audit PASS: {roots} own constants, {seen.size} reachable constants."
