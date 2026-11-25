import QuantumNLS.MarginalSandwichNorm
import QuantumNLS.PhysicalCutoffEvolutionBounds
import QuantumNLS.PlacementGrouping

/-! Literal arbitrary-placement interpretation of the source error on every
actual normalized energy-cutoff orbit. No placement compatibility is supplied. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set Filter Topology
open scoped InnerProductSpace ComplexConjugate
namespace QuantumNLS.PhysicalPlacementError
open TensorCarrier PhysicalTensor TensorPlacements KernelDefinition PlacementFusion PlacementGrouping
open LinearTailGenerator LinearTailKineticError PhysicalCutoffEvolutionBounds
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Equality-transport of a tensor operator has its literal vector-norm interpretation. -/
theorem cast_norm_apply {m n : ℕ} (h : m = n)
    (T : HilbertTensorPower ℂ H m →L[ℂ] HilbertTensorPower ℂ H m)
    (ψ : HilbertTensorPower ℂ H n) :
    ‖castTensorOperator h T ψ‖ = ‖T (castHTP h.symm ψ)‖ := by
  cases h
  rfl

/-- Every actual full N-particle subset placement has exactly the canonical marginal error. -/
theorem rawPlacement_norm (N r : ℕ) (hr : r ≤ N)
    (A : BoundedSymmetricKernel H r) (S : PlacementSubset r (N - r))
    (ψ : HilbertTensorPower ℂ H N) (hψ : ψ ∈ SymSector ℂ H N) :
    ‖rawSubsetPlacement N r hr S A ψ‖ =
      quadraticError (extendSymKernel A) (reducedDensityN N r hr ψ) := by
  unfold rawSubsetPlacement
  rw [cast_norm_apply, MarginalSandwichNorm.subsetPlacement_norm A _
    (castHTP_mem_symSector _ hψ)]
  rfl

variable (L : ℝ) [Fact (0 < L)]

/-- Every literal finite-tail rank kernel is selfadjoint, for real weights. -/
theorem finiteT_selfadjoint (r : ℕ) (a : Finset ℤ) (t : ℤ → ℝ) :
    IsSelfAdjoint (finiteT L r a t) := by
  change (finiteT L r a t).adjoint = finiteT L r a t
  simp only [finiteT, map_sum, map_smulₛₗ, BethePhysicalTransfer.physicalKernel_adjoint,
    LinearTailSelfadjoint.adjointPhase_gridPt, LinearTailSelfadjoint.conj_gridPt,
    Complex.conj_ofReal, one_smul]

/-- The constructed sourceError bounds every actual raw placement applied to a cutoff orbit.
The bound is independent of the number of particles and the placement slots. -/
theorem cutoff_placement_error (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 1 ≤ N)
    (E : ℝ) (hE : 0 ≤ E) (a : Finset ℤ) (t : ℤ → ℝ) :
    ∃ P : ContactOperator.SymL2 L N →L[ℂ] ContactOperator.SymL2 L N,
      IsEnergyCutoff L κ N hκ hN E P ∧
      ∀ ψ : ContactOperator.SymL2 L N, P ψ = ψ → ‖ψ‖ = 1 → ∀ s : ℝ,
      ∀ (n : ℕ) (hn : n + 1 ≤ N) (R : ℕ) (b : Finset ℤ) (v : ℤ → ℝ),
      (∀ m ∈ b, |v m| ≤ 1) → (∀ m ∈ b, (R : ℤ) < |m|) →
      ∀ S : PlacementSubset (n + 1) (N - (n + 1)),
      ‖rawSubsetPlacement N (n + 1) hn S (finiteT L (n + 1) b v)
        (tensorOrbit L κ N a t s ψ)‖ ≤ sourceError L n E R := by
  obtain ⟨P, hdiag, hbound⟩ := cutoff_marginal_quadratic_error L κ hκ N hN E hE a t
  refine ⟨P, hdiag, fun ψ hψ hnorm s n hn R b v hv hb S => ?_⟩
  have hsec : tensorOrbit L κ N a t s ψ ∈ SymSector ℂ (L2T L) N :=
    ((BethePhysicalTransfer.symmetricPosition L N).symm
      (LinearTailPhysicalEvolution.physicalEvolution L κ N a t s ψ)).property
  rw [rawPlacement_norm N (n + 1) hn _ S _ hsec]
  exact hbound ψ hψ hnorm s n hn R b v hv hb

end QuantumNLS.PhysicalPlacementError

#print axioms QuantumNLS.PhysicalPlacementError.cast_norm_apply
#print axioms QuantumNLS.PhysicalPlacementError.rawPlacement_norm
#print axioms QuantumNLS.PhysicalPlacementError.finiteT_selfadjoint
#print axioms QuantumNLS.PhysicalPlacementError.cutoff_placement_error

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.PhysicalPlacementError." then
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
