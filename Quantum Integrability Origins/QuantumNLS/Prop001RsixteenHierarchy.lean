import QuantumNLS.Prop001RsixteenReduction
import QuantumNLS.Prop001RsixteenHigher
import QuantumNLS.Prop001RsixteenSeries

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
open Filter Topology
open scoped InnerProductSpace BigOperators ENNReal
namespace QuantumNLS.Prop001RsixteenHierarchy
open TraceClass TraceIdeal TensorCarrier TensorPlacements PlacementFusion PlacementGrouping
  PhysicalTensor PhysicalEnergyTrace RootOverlapCommutator Ext025A12Trace Ext025A12Normal
  Ext025A12PartialTrace Ext025A12Collision Prop001 Prop001RthirteenSeries
  Prop001RfourteenRegrouping Prop001RfourteenTraceRegrouping
  Prop001RfifteenTransport Prop001RfifteenDerivative Prop001RfifteenRemainder
  Prop001RsixteenCounting Prop001RsixteenAssembly Prop001RsixteenOne
  Prop001RsixteenHigher Prop001RsixteenSeries
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem sum_range_two (n : ℕ) {M : Type*} [AddCommMonoid M] (F : ℕ → M) :
    (∑ ell ∈ Finset.range (n+2),F ell)=F 0+F 1+∑ s ∈ Finset.range n,F (s+2) := by
  have h2 : (∑ ell ∈ Finset.range 2,F ell)=F 0+F 1 := by
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  have h := Finset.sum_range_add F 2 n
  rw [h2] at h
  simpa only [Nat.add_comm 2] using h

/-- Original finite Hamiltonian: zero, one and multiple overlaps, on the
actual evolved symmetric density. -/
theorem raw_trace_one_multiple (D : ClassicalData H) (k m : ℕ)
    (ψ : SymSector ℂ H ((k+1)+m)) (t : ℝ) :
    let N := (k+1)+m
    let z := quantumVector D.A N ψ t
    let P := InnerProductSpace.rankOne ℂ z z
    splitTrace (k+1) m (rawGenerator D.A N*P-P*rawGenerator D.A N)
      (commutator_finite _ P (rankOne_finite _ _)) =
      (∑ n : Fin N, (((((n.val+1).factorial : ℝ)*N/(N : ℝ)^(n.val+1)) : ℝ) : ℂ) •
        (splitMap (k+1) m (overlapIdeal N (k+1) (n.val+1) 1 (by omega)
          (Nat.succ_le_of_lt n.isLt) (D.A n.val) ⟨P,rankOne_finite _ _⟩)).val)+
      multipleRemainder D (k+1) m (firstPositions (p := k+1) (q := m)) P (rankOne_finite _ _) := by
  classical
  dsimp only
  rw [rawGenerator_trace_regroup D.A (k+1) m
    (InnerProductSpace.rankOne ℂ (quantumVector D.A ((k+1)+m) ψ t)
      (quantumVector D.A ((k+1)+m) ψ t)) (rankOne_finite _ _)]
  rw [← higher_overlap_eq_multipleRemainder D (k+1) m
    (InnerProductSpace.rankOne ℂ (quantumVector D.A ((k+1)+m) ψ t)
      (quantumVector D.A ((k+1)+m) ψ t)) (rankOne_finite _ _)]
  simp only [Nat.cast_add,Nat.cast_one]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [sum_range_two,smul_add]
  congr 1
  have hz := overlap_trace_zero (k+1) m (n.val+1) (Nat.succ_le_of_lt n.isLt)
    (D.A n.val) (quantumEvolution D.A ((k+1)+m) t ψ)
  dsimp only at hz
  rw [show (splitMap (k+1) m (overlapIdeal ((k+1)+m) (k+1) (n.val+1) 0 (by omega)
      (Nat.succ_le_of_lt n.isLt) (D.A n.val)
      ⟨InnerProductSpace.rankOne ℂ (quantumVector D.A ((k+1)+m) ψ t)
        (quantumVector D.A ((k+1)+m) ψ t),rankOne_finite _ _⟩)).val=0 from hz,zero_add]

/-- Total natural-rank version of the literal weighted one-overlap term. -/
def oneTerm (D : ClassicalData H) (k m : ℕ)
    (ψ : SymSector ℂ H ((k+1)+m)) (t : ℝ) (n : ℕ) : RankOperator H (k+1) := by
  classical
  let N := (k+1)+m
  let z := quantumVector D.A N ψ t
  let P := InnerProductSpace.rankOne ℂ z z
  exact if hn : n<N then (((((n+1).factorial : ℝ)*N/(N : ℝ)^(n+1)) : ℝ) : ℂ) •
    (splitMap (k+1) m (overlapIdeal N (k+1) (n+1) 1 (by omega)
      (Nat.succ_le_of_lt hn) (D.A n) ⟨P,rankOne_finite _ _⟩)).val else 0

theorem oneTerm_above (D : ClassicalData H) (k m n : ℕ) (hn : m < n)
    (ψ : SymSector ℂ H ((k+1)+m)) (t : ℝ) : oneTerm D k m ψ t n=0 := by
  classical
  unfold oneTerm
  dsimp only
  split_ifs with hN
  · have hc := card_overlap_subsets ((k+1)+m) (k+1) (n+1) 1 (by omega)
      (Nat.succ_le_of_lt hN) (by omega)
    have hm : (k+1)+m-(k+1)=m := by omega
    rw [hm,Nat.add_sub_cancel,Nat.choose_eq_zero_of_lt hn,mul_zero] at hc
    have he := Finset.card_eq_zero.mp hc
    simp only [overlapIdeal,he,Finset.sum_empty,map_zero,Submodule.coe_zero,smul_zero]
  · rfl

theorem oneTerm_admissible (D : ClassicalData H) (k m n : ℕ) (hn : n ≤ m)
    (ψ : SymSector ℂ H ((k+1)+m)) (hψ : ‖ψ‖=1) (t : ℝ) :
    oneTerm D k m ψ t n = (alpha ((k+1)+m) (k+1) n : ℂ) •
      sourceRankCollision k n (D.A n) (extendedMarginal D.A ((k+1)+m) ((k+1)+n) t ψ)
        (extendedMarginal_isTraceClass D.A D.selfAdjoint ((k+1)+m) t ψ hψ _) := by
  classical
  obtain ⟨q,hq⟩ := Nat.exists_eq_add_of_le hn
  subst m
  unfold oneTerm
  dsimp only
  rw [dite_eq_left (show n < (k+1)+(n+q) by omega)]
  simpa only [extendedMarginal_of_le D.A _ _
    (show (k+1)+n ≤ (k+1)+(n+q) by omega),marginal,quantumVector,Nat.cast_add,Nat.cast_one] using
    oneOverlap_weighted_identification k n q (D.A n)
      (quantumEvolution D.A ((k+1)+(n+q)) t ψ)

theorem oneTerm_sum (D : ClassicalData H) (k m : ℕ)
    (ψ : SymSector ℂ H ((k+1)+m)) (hψ : ‖ψ‖=1) (t : ℝ) :
    (∑ n : Fin ((k+1)+m),oneTerm D k m ψ t n.val) =
      ∑ n ∈ Finset.range (m+1), (alpha ((k+1)+m) (k+1) n : ℂ) •
        sourceRankCollision k n (D.A n) (extendedMarginal D.A ((k+1)+m) ((k+1)+n) t ψ)
          (extendedMarginal_isTraceClass D.A D.selfAdjoint ((k+1)+m) t ψ hψ _) := by
  classical
  rw [Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ n ∈ Finset.range (m+1),oneTerm D k m ψ t n := by
      symm
      apply Finset.sum_subset (Finset.range_mono (show m+1 ≤ (k+1)+m by omega))
      intro n _ hn
      exact oneTerm_above D k m n (by
        have hh : m+1 ≤ n := Nat.le_of_not_gt (fun h => hn (Finset.mem_range.mpr h))
        omega) ψ t
    _ = _ := Finset.sum_congr rfl (fun n hn =>
      oneTerm_admissible D k m n (by have hh := Finset.mem_range.mp hn; omega) ψ hψ t)

/-- The concrete correction is exactly the error in the actual finite
marginal commutator equation, including N=1. -/
theorem finite_hierarchy_identity (D : ClassicalData H) (k m : ℕ)
    (ψ : SymSector ℂ H ((k+1)+m)) (hψ : ‖ψ‖=1) (t : ℝ) :
    let N := (k+1)+m
    let z := quantumVector D.A N ψ t
    let P := InnerProductSpace.rankOne ℂ z z
    splitTrace (k+1) m (rawGenerator D.A N*P-P*rawGenerator D.A N)
      (commutator_finite _ P (rankOne_finite _ _)) =
      collisionSeries D.A (fun j => extendedMarginal D.A N j t ψ)
        (extendedMarginal_isTraceClass D.A D.selfAdjoint N t ψ hψ) k+
      finiteCorrection D k m ψ hψ t := by
  classical
  dsimp only
  rw [raw_trace_one_multiple D k m ψ t]
  have ho : (∑ n : Fin ((k+1)+m),
      (((((n.val+1).factorial : ℝ)*((k+1)+m)/((k+1)+m : ℝ)^(n.val+1)) : ℝ) : ℂ) •
        (splitMap (k+1) m (overlapIdeal ((k+1)+m) (k+1) (n.val+1) 1 (by omega)
          (Nat.succ_le_of_lt n.isLt) (D.A n.val)
          ⟨InnerProductSpace.rankOne ℂ (quantumVector D.A ((k+1)+m) ψ t)
            (quantumVector D.A ((k+1)+m) ψ t),rankOne_finite _ _⟩)).val) =
      ∑ n : Fin ((k+1)+m),oneTerm D k m ψ t n.val := by
    apply Finset.sum_congr rfl
    intro n _
    simp only [oneTerm,dite_eq_left n.isLt,Nat.cast_add,Nat.cast_one]
  simp only [Nat.cast_add,Nat.cast_one] at ho ⊢
  rw [ho,oneTerm_sum D k m ψ hψ t,finiteCorrection,
    finite_collision_eq_sum D ((k+1)+m) k ψ hψ t,oneOverlapCorrection]
  have hm : (k+1)+m-(k+1)+1=m+1 := by omega
  rw [hm,← add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  push_cast
  module

/-- The actual finite hierarchy and the actual C0 remainder bound. -/
theorem PROP001_finite_hierarchy (D : ClassicalData H) (k m : ℕ)
    (ψ : SymSector ℂ H ((k+1)+m)) (hψ : ‖ψ‖=1) (t : ℝ) :
    Tendsto (fun s => traceNorm
      (slope (fun r => marginal D.A ((k+1)+m) (k+1) (by omega) r ψ) t s-
        (-Complex.I) • (collisionSeries D.A
          (fun j => extendedMarginal D.A ((k+1)+m) j t ψ)
          (extendedMarginal_isTraceClass D.A D.selfAdjoint ((k+1)+m) t ψ hψ) k+
          finiteCorrection D k m ψ hψ t))) (𝓝[≠] t) (𝓝 0) ∧
    traceNorm (finiteCorrection D k m ψ hψ t) ≤
      ENNReal.ofReal (errorSum D.A*((k+1 : ℕ) : ℝ)^2/((k+1)+m)) := by
  refine ⟨?_,finiteCorrection_bound_positive D k m ψ hψ t⟩
  have h := marginal_trace_derivative D.A D.selfAdjoint (k+1) m ψ t
  dsimp only at h
  rw [finite_hierarchy_identity D k m ψ hψ t] at h
  exact h

end QuantumNLS.Prop001RsixteenHierarchy

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001RsixteenHierarchy" then
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
  Lean.logInfo m!"Prop001RsixteenHierarchy audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."



#print axioms QuantumNLS.Prop001RsixteenHierarchy.sum_range_two
#print axioms QuantumNLS.Prop001RsixteenHierarchy.raw_trace_one_multiple
#print axioms QuantumNLS.Prop001RsixteenHierarchy.oneTerm
#print axioms QuantumNLS.Prop001RsixteenHierarchy.oneTerm_above
#print axioms QuantumNLS.Prop001RsixteenHierarchy.oneTerm_admissible
#print axioms QuantumNLS.Prop001RsixteenHierarchy.oneTerm_sum
#print axioms QuantumNLS.Prop001RsixteenHierarchy.finite_hierarchy_identity
#print axioms QuantumNLS.Prop001RsixteenHierarchy.PROP001_finite_hierarchy
