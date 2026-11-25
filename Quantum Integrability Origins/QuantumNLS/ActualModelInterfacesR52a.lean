import QuantumNLS.ActualModelSpectralR52a
import QuantumNLS.ActualModelPeriodsR52a
import QuantumNLS.ActualModelDifferentialsR52a
import QuantumNLS.ActualModelHierarchyR52a

/-! R-E679E41D: physical interface assembly. This is an INTERMEDIATE
interface theorem, not the final named propagation corollary. The exact
pending hierarchy theorem remains ONE explicit named input. PROP-025,
the physical window theorem and DEF-044/DEF033 final bindings are not
silently assumed or promoted here. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open Set Filter Topology MeasureTheory
namespace QuantumNLS.ActualModelInterfacesR52a
open PhysicalTensor Def044D1SpectralR51a Def044InterfacesR51a Def044ChartR51a
open ActualModelScalarR52a ActualModelSpectralR52a
variable {L κ : ℝ} [Fact (0 < L)]

/-- Every clause of the fixed-profile scalar interface is now supplied by
an accepted physical theorem and the exact D1 realization, with no
analytical hypothesis and no altered normalization. -/
theorem scalar_requirements (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1) :
    Nonempty (ScalarRequirements hκ (physical u) hu) := by
  obtain ⟨C,hC,hms⟩ := cauchy_mean_square hκ (physical u) hu
  refine ⟨{
    indexed := indexed hκ (physical u) hu
    physical_measure := rfl
    absolute_moments := fun p => ((smooth_moments hκ u).2 p).1
    R0 := Prop017Quantum.eta0 L κ
    R0_positive := Prop017Quantum.eta0_pos hκ
    positive_tail := ?_
    eta0 := Prop017Quantum.eta0 L κ
    eta0_positive := Prop017Quantum.eta0_pos hκ
    cauchy_bound := ?_
    height := Prop017Quantum.eta0 L κ+1
    height_gt_eta0 := by linarith
    high_geometry := high_geometry hκ u hu (by linarith [Prop017Quantum.eta0_pos (L := L) hκ])
  }⟩
  · intro p hp
    obtain ⟨A,D,hA,hD,ht⟩ := positive_tails hκ u hu p
    refine ⟨A,D,hA,hD,?_⟩
    intro N R hR
    have hb := ht (N+1) (by omega) R hR
    have heq : (∫ m, Def044D1SpectralR51a.tailFraction (L := L) (κ := κ) N R m
        ∂originalLaw hκ (physical u) hu N) =
        (∫ m, RootEvent.tailFraction (Prop017Quantum.qAct L κ (N+1)) R m
          ∂EmpiricalRapidity.bornMeasure (BulkResponseActual.physBasis L hκ (N+1)) (physical u) hu) := by
      rw [originalLaw_eq]
      exact integral_congr_ae (ae_of_all _ (fun m => tail_eq hκ N R m))
    exact heq.le.trans (by simpa only [Nat.cast_add,Nat.cast_one] using hb)
  · refine ⟨C,hC,?_⟩
    intro N x y hy
    have hb := hms (N+1) (by omega) x y hy
    have heq : (∫ m, ‖empiricalG (L := L) (κ := κ) N m (x+y*Complex.I) -
          scalarG (PhysicalQuantumMeasure.measure hκ (physical u)) (x+y*Complex.I)‖^2
          ∂originalLaw hκ (physical u) hu N) =
        (∫ m, ‖Extrapolation.Gfull (PhysicalQuantumMeasure.measure hκ (physical u)) (x+y*Complex.I) -
          Extrapolation.GN (Prop017Quantum.qAct L κ (N+1) m) (x+y*Complex.I)‖^2
          ∂EmpiricalRapidity.bornMeasure (BulkResponseActual.physBasis L hκ (N+1)) (physical u) hu) := by
      rw [originalLaw_eq]
      apply integral_congr_ae
      apply ae_of_all
      intro m
      dsimp only
      rw [empiricalG_eq hκ N m,RootSpectralInputsDischarge.Gfull_eq]
      exact congrArg (fun a : ℝ => a^2) (norm_sub_rev _ _)
    exact heq.le.trans (by simpa only [Nat.cast_add,Nat.cast_one] using hb)

#print axioms QuantumNLS.ActualModelInterfacesR52a.scalar_requirements

/-- Actual common Bethe resolution, exact coefficients/kernel bound, all
scalar estimates and high-cut geometry. No interface is an assumption. -/
theorem spectral_interface (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1) :
    Nonempty (SpectralInterface hκ (physical u) hu) :=
  ⟨⟨ActualModelQuantumR52a.quantum_requirements hκ,
    Classical.choice (scalar_requirements hκ u hu)⟩⟩

/-- The actual accepted global chart, with all real nonnegative Sobolev
restrictions, full-mass scalar dependence and full-open logarithmic periods. -/
def chart_interface (hκ : 0 < κ) : ChartInterface (L := L) hκ where
  chart := Def021ChartR41b.chart L κ hκ
  sobolev := ActualModelChartR52a.sobolev_restrictions hκ (Def021ChartR41b.chart L κ hκ)
  action_determination := ActualModelChartR52a.action_determination hκ
  full_open_periods := ActualModelPeriodsR52a.full_open_periods hκ

/-- INTERMEDIATE: static interfaces and exact common-dual estimate are
unconditional; only the exact R-7B122087 statement is a named input to the
smooth-hierarchy component. This theorem asserts no mixed propagation. -/
theorem actual_interfaces_intermediate (hκ : 0 < κ)
    (HierarchyInput : ActualModelHierarchyR52a.HierarchyInput (L := L) hκ (chart_interface (L := L) hκ).chart) :
    (∀ (u : Smooth L) (hu : ‖physical u‖ = 1), Nonempty (SpectralInterface hκ (physical u) hu)) ∧
    WindowDifferentials (L := L) hκ ∧
    ActualModelHierarchyR52a.HierarchyConclusion (L := L) hκ (chart_interface (L := L) hκ).chart :=
  ⟨spectral_interface (L := L) hκ,ActualModelDifferentialsR52a.window_differentials (L := L) hκ,
    ActualModelHierarchyR52a.hierarchy_intermediate (L := L) hκ
      (chart_interface (L := L) hκ).chart HierarchyInput⟩

end QuantumNLS.ActualModelInterfacesR52a
#print axioms QuantumNLS.ActualModelInterfacesR52a.spectral_interface
#print axioms QuantumNLS.ActualModelInterfacesR52a.chart_interface
#print axioms QuantumNLS.ActualModelInterfacesR52a.actual_interfaces_intermediate
#print QuantumNLS.ActualModelInterfacesR52a.actual_interfaces_intermediate

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.ActualModelInterfacesR52a." ||
        n.toString.startsWith "_private.QuantumNLS.ActualModelInterfacesR52a." then
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
  Lean.logInfo m!"Round52 aggregate audit PASS: {own} own constants; {seen.size} transitive constants; standard only."
