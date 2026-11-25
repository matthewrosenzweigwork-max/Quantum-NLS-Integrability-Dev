import QuantumNLS.Prop001RthirteenSeries
import QuantumNLS.PlacementGrouping

/-! Finite overlap partition of the literal full-tensor Hamiltonian. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped InnerProductSpace BigOperators
namespace QuantumNLS.Prop001RfourteenRegrouping
open TensorCarrier TensorPlacements PlacementFusion PlacementGrouping Prop001
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The same subset averages as the source Hamiltonian, before restriction. -/
def rawGenerator (A : Interactions H) (N : ℕ) : RankOperator H N :=
  (N : ℂ) • ∑ n : Fin N, (theta N (n.val+1) : ℂ) •
    rawSubsetAverage N (n.val+1) (Nat.succ_le_of_lt n.isLt) (A n.val)

/-- The raw Hamiltonian restricts to the actual source generator. -/
theorem rawGenerator_restrict (A : Interactions H) (N : ℕ) (x : SymSector ℂ H N) :
    rawGenerator A N x = (generator A N x : HilbertTensorPower ℂ H N) := by
  simp only [rawGenerator,generator,smul_apply,sum_apply,
    Submodule.coe_smul_of_tower,Submodule.coe_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  rw [genericU_eq_rawSubsetAverageOnSector]
  rfl

/-- Count the selected output coordinates in the actual subset. -/
def overlap (N k r : ℕ) (hk : k ≤ N) (hr : r ≤ N)
    (S : PlacementSubset r (N-r)) : ℕ :=
  ((S.val.map (finCongr (Nat.add_sub_of_le hr)).toEmbedding) ∩
    ((firstPositions (p := k) (q := N-k)).map (finCongr (Nat.add_sub_of_le hk)).toEmbedding)).card

theorem overlap_le (N k r : ℕ) (hk : k ≤ N) (hr : r ≤ N)
    (S : PlacementSubset r (N-r)) : overlap N k r hk hr S ≤ r := by
  unfold overlap
  calc
    _ ≤ (S.val.map (finCongr (Nat.add_sub_of_le hr)).toEmbedding).card := Finset.card_le_card Finset.inter_subset_left
    _ = r := by rw [Finset.card_map,S.property]

/-- The actual finite subset commutators partitioned by overlap count. -/
def overlapCommutator (N k r ell : ℕ) (hk : k ≤ N) (hr : r ≤ N)
    (A : SymSector ℂ H r →L[ℂ] SymSector ℂ H r) (T : RankOperator H N) : RankOperator H N := by
  classical
  exact ∑ S ∈ (Finset.univ : Finset (PlacementSubset r (N-r))).filter
    (fun S => overlap N k r hk hr S=ell),
    (rawSubsetPlacement N r hr S A*T-T*rawSubsetPlacement N r hr S A)

theorem subset_commutators_regroup (N k r : ℕ) (hk : k ≤ N) (hr : r ≤ N)
    (A : SymSector ℂ H r →L[ℂ] SymSector ℂ H r) (T : RankOperator H N) :
    (rawSubsetPlacementSum N r hr A*T-T*rawSubsetPlacementSum N r hr A) =
      ∑ ell ∈ Finset.range (r+1),overlapCommutator N k r ell hk hr A T := by
  classical
  unfold overlapCommutator rawSubsetPlacementSum
  simp only [Finset.sum_mul,Finset.mul_sum,← Finset.sum_sub_distrib]
  exact (Finset.sum_fiberwise_of_maps_to
    (fun S _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (overlap_le N k r hk hr S))) _).symm

/-- The source factorial coefficient, now on the actual raw placements. -/
theorem rawGenerator_subset_expansion (A : Interactions H) (N : ℕ) :
    rawGenerator A N = ∑ n : Fin N,
      (((((n.val+1).factorial : ℝ)*N/(N : ℝ)^(n.val+1)) : ℝ) : ℂ) •
        rawSubsetPlacementSum N (n.val+1) (Nat.succ_le_of_lt n.isLt) (A n.val) := by
  unfold rawGenerator
  simp only [rawSubsetAverage_eq_rawSubsetPlacementSum,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  have hc := generator_subset_coefficient N (n.val+1) (Nat.succ_le_of_lt n.isLt)
  have he := congrArg (fun x : ℝ => (x : ℂ)) hc
  push_cast at he ⊢
  simpa only [div_eq_mul_inv,mul_assoc] using he

/-- Exact operator regrouping of the finite Hamiltonian by rank and overlap. -/
theorem rawGenerator_commutator_regroup (A : Interactions H) (N k : ℕ)
    (hk : k ≤ N) (T : RankOperator H N) :
    rawGenerator A N*T-T*rawGenerator A N =
      ∑ n : Fin N, (((((n.val+1).factorial : ℝ)*N/(N : ℝ)^(n.val+1)) : ℝ) : ℂ) •
        ∑ ell ∈ Finset.range (n.val+2),
          overlapCommutator N k (n.val+1) ell hk (Nat.succ_le_of_lt n.isLt) (A n.val) T := by
  rw [rawGenerator_subset_expansion]
  simp only [Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm,
    ← Finset.sum_sub_distrib,← smul_sub]
  exact Finset.sum_congr rfl (fun n _ => congrArg _
    (subset_commutators_regroup N k (n.val+1) hk (Nat.succ_le_of_lt n.isLt) (A n.val) T))

end QuantumNLS.Prop001RfourteenRegrouping

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001RfourteenRegrouping" then
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
  Lean.logInfo m!"Prop001RfourteenRegrouping audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."


#print axioms QuantumNLS.Prop001RfourteenRegrouping.rawGenerator

#print axioms QuantumNLS.Prop001RfourteenRegrouping.rawGenerator_restrict

#print axioms QuantumNLS.Prop001RfourteenRegrouping.overlap

#print axioms QuantumNLS.Prop001RfourteenRegrouping.overlap_le

#print axioms QuantumNLS.Prop001RfourteenRegrouping.overlapCommutator

#print axioms QuantumNLS.Prop001RfourteenRegrouping.subset_commutators_regroup

#print axioms QuantumNLS.Prop001RfourteenRegrouping.rawGenerator_subset_expansion

#print axioms QuantumNLS.Prop001RfourteenRegrouping.rawGenerator_commutator_regroup
