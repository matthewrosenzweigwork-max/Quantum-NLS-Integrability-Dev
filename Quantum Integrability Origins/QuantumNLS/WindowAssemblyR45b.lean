import QuantumNLS.WindowScalarsR45b
import QuantumNLS.WindowComparisonR45b
import QuantumNLS.WindowHierarchyInputR45b
import QuantumNLS.WindowActualTrajectoryR45b
import QuantumNLS.WindowSymplecticR45b

/-! Actual scalar-rotation assembly for R-E59628C9. The full physical
hierarchy is obtained from the ONE exact formal HierarchyInput. The rate
below compares the actual scalar-derived rotations through the accepted
physical inverse. Identification of these full scalar rotations with that
physical hierarchy is deliberately not hidden in a hypothesis or claimed. -/
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set
open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.WindowScalarsR45b QuantumNLS.WindowActualEstimatesR44b
open QuantumNLS.WindowComparisonR45b QuantumNLS.WindowRateEstimateR44b
open QuantumNLS.WindowPhaseR44b QuantumNLS.Reg015Setting QuantumNLS.PROP017UniformN
namespace QuantumNLS.WindowAssemblyR45b
variable {L κ : ℝ} [Fact (0 < L)]

/-- Actual full-charge scalar rotations, returned to physical L². -/
def fullPhysical (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (d : ℕ) (t : Fin (d+1) → ℝ) (z : h02 L (sequenceOrder d)) : PhysicalTensor.L2T L :=
  C.Ψ (toBase (sequenceOrder d) (sequenceOrder d).2
    (rotate (angle Finset.univ (fun r : Fin (d+1) => full hκ C d r.val (by omega)) t z) z))

/-- Actual contour scalar rotations at cutoff `cutSeq L l`. -/
def windowPhysical (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (d : ℕ) (h : ℝ) (l : ℕ) (t : Fin (d+1) → ℝ)
    (z : h02 L (sequenceOrder d)) : PhysicalTensor.L2T L :=
  C.Ψ (toBase (sequenceOrder d) (sequenceOrder d).2
    (rotate (angle Finset.univ (fun r : Fin (d+1) => window hκ C d r.val h l) t z) z))

/-- The quarter-power estimate for actual scalar-derived rotations. Every
scalar differential bound, its invariance, the torus union and the physical
inverse bound are discharged; the constants are selected before the cutoff. -/
theorem actual_scalar_rate (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (d : ℕ) {h : ℝ} (hh : 0 < h)
    {K : Set (h02 L (sequenceOrder d))} (hK : IsCompact K)
    (T : Fin (d+1) → ℝ) (_hT : ∀ r, 0 ≤ T r) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ l0 : ℕ, ∀ l : ℕ, l0 ≤ l → ∀ z ∈ K,
      ∀ t : Fin (d+1) → ℝ, (∀ r, |t r| ≤ T r) →
      ‖windowPhysical hκ C d h l t z-fullPhysical hκ C d t z‖ ≤
        A*(cutSeq L l)^(-(1/4 : ℝ)) := by
  classical
  let W := def002 L (sequenceOrder d)
  have hW : ∀ j, 1 ≤ W.w j := one_le_def002 L (sequenceOrder d).2
  let f : WSeq WindowInterpolationR44b.unitWeight → PhysicalTensor.L2T L :=
    fun z => C.Ψ (toL2 WindowInterpolationR44b.unitWeight z)
  have hf : ContDiff ℝ 1 f := actual_inverse_contDiff hκ C
  obtain ⟨M,hM,hbound⟩ := uniform_comparison (ι := Fin (d+1)) W hW hK f hf
  have hdata : ∀ r : Fin (d+1), ∃ A : ℝ, 0 ≤ A ∧ ∃ l0 : ℕ,
      ∀ l : ℕ, l0 ≤ l → ∀ z ∈ K,
        DifferentiableAt ℝ (window hκ C d r.val h l) z ∧
        ‖fderiv ℝ (full hκ C d r.val (by omega)) z-
          fderiv ℝ (window hκ C d r.val h l) z‖ ≤ A*(cutSeq L l)^(-(1/2 : ℝ)) :=
    fun r => scalar_data hκ C d r.val (by omega) hh hK
  choose A hA l₀ hdata using hdata
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn (continuous_id.continuousOn : ContinuousOn (fun z : WSeq W => z) K)
  let B₀ := max B 0
  let l0 := max 1 (Finset.univ.sup l₀)
  refine ⟨M*Real.sqrt ((∑ r, T r*A r)*(2*B₀)),by positivity,l0,?_⟩
  intro l hl z hz t ht
  have hll : ∀ r, l₀ r ≤ l := fun r =>
    (Finset.le_sup (f := l₀) (Finset.mem_univ r)).trans ((le_max_right _ _).trans hl)
  have ha : 0 < cutSeq L l := by
    unfold cutSeq
    positivity [(Fact.out : 0 < L)]
  have hb := hbound Finset.univ (fun r : Fin (d+1) => full hκ C d r.val (by omega))
    (fun r : Fin (d+1) => window hκ C d r.val h l) T A B₀
    (fun r z _ => ((full_contDiff hκ C d r.val (by omega)).differentiable (by norm_num)) z)
    (fun r z hz => (hdata r l (hll r) z hz).1)
    (fun r => full_rotation hκ C d r.val (by omega))
    (fun r => window_rotation hκ C d r.val h l)
    (fun r _ => hA r) (fun z hz => (hB z hz).trans (le_max_left B 0))
    (cutSeq L l) ha (fun r _ z hz => (hdata r l (hll r) z hz).2)
    z hz t (fun r _ => ht r)
  change ‖C.Ψ (toL2 _ (lower W hW _))-C.Ψ (toL2 _ (lower W hW _))‖ ≤ _ at hb
  rw [unit_base (sequenceOrder d) (sequenceOrder d).2 _ hW,
    unit_base (sequenceOrder d) (sequenceOrder d).2 _ hW] at hb
  change ‖fullPhysical hκ C d t z-windowPhysical hκ C d h l t z‖ ≤ _ at hb
  rw [norm_sub_rev] at hb
  exact hb

/-- PRE-START intermediate assembly with the exact shared predecessor as a
formal hypothesis. This conclusion records both proved components without
asserting the outstanding equality between their trajectories. -/
theorem window_scalar_intermediate (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (hw : REF88PrintedChart.PrintedChart hκ C.Φ)
    (HierarchyInput : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (d : ℕ) {h : ℝ} (hh : 0 < h)
    {K : Set (h02 L (sequenceOrder d))} (hK : IsCompact K)
    (T : Fin (d+1) → ℝ) (hT : ∀ r, 0 ≤ T r) :
    HierarchyInputR25m.HierarchyConclusion (κ := κ) C.Φ
      (fun u n => (RootIndexedMasses.masses hκ u).1 n) ∧
    ∃ A : ℝ, 0 ≤ A ∧ ∃ l0 : ℕ, ∀ l : ℕ, l0 ≤ l → ∀ z ∈ K,
      ∀ t : Fin (d+1) → ℝ, (∀ r, |t r| ≤ T r) →
      ‖windowPhysical hκ C d h l t z-fullPhysical hκ C d t z‖ ≤
        A*(cutSeq L l)^(-(1/4 : ℝ)) :=
  ⟨WindowHierarchyInputR45b.hierarchy_intermediate hκ C.Φ hw HierarchyInput,
    actual_scalar_rate hκ C d hh hK T hT⟩

end QuantumNLS.WindowAssemblyR45b
#print QuantumNLS.WindowAssemblyR45b.window_scalar_intermediate
#print axioms QuantumNLS.WindowAssemblyR45b.actual_scalar_rate
#print axioms QuantumNLS.WindowAssemblyR45b.window_scalar_intermediate

-- Recursive type/value audit of every own declaration, including generated declarations.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.WindowAssemblyR45b." ||
        n.toString.startsWith "_private.QuantumNLS.WindowAssemblyR45b." then
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
  Lean.logInfo m!"R45b aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only."
