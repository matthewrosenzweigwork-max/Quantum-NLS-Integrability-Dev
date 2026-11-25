import QuantumNLS.Prop001RfourteenRegrouping

/-! Exact finite regrouping after the constructed general partial trace.
The lower-rank marginal identifications are separate obligations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped InnerProductSpace BigOperators ENNReal
namespace QuantumNLS.Prop001RfourteenTraceRegrouping
open TraceClass TraceIdeal TensorCarrier TensorPlacements PlacementGrouping PhysicalEnergyTrace
  Ext025A12Trace Ext025A12Normal Ext025A12PartialTrace Ext025A12Collision Prop001
  Prop001RfourteenRegrouping
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Pullback on the actual trace ideal, with finiteness proved by unitary invariance. -/
def pullTraceMap {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (e : X ≃ₗᵢ[ℂ] Y) : traceIdeal Y →ₗ[ℂ] traceIdeal X where
  toFun T := ⟨pull e T.val,by
    change IsTraceClass (pull e T.val)
    rw [IsTraceClass,traceNorm_pull]
    exact T.property⟩
  map_add' S T := by
    apply Subtype.ext
    ext x
    simp only [Submodule.coe_add,pull_apply,add_apply,map_add]
  map_smul' a T := by
    apply Subtype.ext
    ext x
    simp only [Submodule.coe_smul_of_tower,pull_apply,smul_apply,map_smul,RingHom.id_apply]

def splitMap (k m : ℕ) : traceIdeal (HilbertTensorPower ℂ H (k+m)) →ₗ[ℂ]
    traceIdeal (HilbertTensorPower ℂ H k) :=
  partialTraceLinear.comp (pullTraceMap (splitIsometry k m).symm)

theorem splitMap_val (k m : ℕ) (T : traceIdeal (HilbertTensorPower ℂ H (k+m))) :
    (splitMap k m T).val = splitTrace k m T.val T.property := rfl

def commutatorIdeal {N : ℕ} (B : RankOperator H N)
    (T : traceIdeal (HilbertTensorPower ℂ H N)) : traceIdeal (HilbertTensorPower ℂ H N) :=
  ⟨B*T.val-T.val*B,commutator_finite B T.val T.property⟩

def overlapIdeal (N k r ell : ℕ) (hk : k ≤ N) (hr : r ≤ N)
    (A : SymSector ℂ H r →L[ℂ] SymSector ℂ H r)
    (T : traceIdeal (HilbertTensorPower ℂ H N)) : traceIdeal (HilbertTensorPower ℂ H N) := by
  classical
  exact ∑ S ∈ (Finset.univ : Finset (PlacementSubset r (N-r))).filter
    (fun S => overlap N k r hk hr S=ell),
    commutatorIdeal (rawSubsetPlacement N r hr S A) T

theorem overlapIdeal_val (N k r ell : ℕ) (hk : k ≤ N) (hr : r ≤ N)
    (A : SymSector ℂ H r →L[ℂ] SymSector ℂ H r)
    (T : traceIdeal (HilbertTensorPower ℂ H N)) :
    (overlapIdeal N k r ell hk hr A T).val = overlapCommutator N k r ell hk hr A T.val := by
  classical
  simp only [overlapIdeal,overlapCommutator,Submodule.coe_sum,commutatorIdeal]

theorem rawGenerator_ideal_regroup (A : Interactions H) (N k : ℕ) (hk : k ≤ N)
    (T : traceIdeal (HilbertTensorPower ℂ H N)) :
    commutatorIdeal (rawGenerator A N) T =
      ∑ n : Fin N, (((((n.val+1).factorial : ℝ)*N/(N : ℝ)^(n.val+1)) : ℝ) : ℂ) •
        ∑ ell ∈ Finset.range (n.val+2),
          overlapIdeal N k (n.val+1) ell hk (Nat.succ_le_of_lt n.isLt) (A n.val) T := by
  apply Subtype.ext
  simpa only [commutatorIdeal,Submodule.coe_sum,Submodule.coe_smul_of_tower,overlapIdeal_val] using
    rawGenerator_commutator_regroup A N k hk T.val

/-- Exact partial-trace grouping on every trace-class input, using the actual
finite Hamiltonian and the actual overlap subsets. -/
theorem rawGenerator_trace_regroup (A : Interactions H) (k m : ℕ)
    (T : RankOperator H (k+m)) (hT : IsTraceClass T) :
    splitTrace k m (rawGenerator A (k+m)*T-T*rawGenerator A (k+m))
      (commutator_finite _ T hT) =
      ∑ n : Fin (k+m), (((((n.val+1).factorial : ℝ)*(k+m)/(k+m : ℝ)^(n.val+1)) : ℝ) : ℂ) •
        ∑ ell ∈ Finset.range (n.val+2),
          (splitMap k m (overlapIdeal (k+m) k (n.val+1) ell (by omega)
            (Nat.succ_le_of_lt n.isLt) (A n.val) ⟨T,hT⟩)).val := by
  have h := congrArg (splitMap (H := H) k m)
    (rawGenerator_ideal_regroup A (k+m) k (by omega) ⟨T,hT⟩)
  simp only [map_sum,map_smul] at h
  have hv := congrArg Subtype.val h
  simpa only [splitMap_val,commutatorIdeal,Submodule.coe_sum,Submodule.coe_smul_of_tower,
    Nat.cast_add] using hv

end QuantumNLS.Prop001RfourteenTraceRegrouping

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001RfourteenTraceRegrouping" then
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
  Lean.logInfo m!"Prop001RfourteenTraceRegrouping audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."


#print axioms QuantumNLS.Prop001RfourteenTraceRegrouping.pullTraceMap

#print axioms QuantumNLS.Prop001RfourteenTraceRegrouping.splitMap

#print axioms QuantumNLS.Prop001RfourteenTraceRegrouping.splitMap_val

#print axioms QuantumNLS.Prop001RfourteenTraceRegrouping.commutatorIdeal

#print axioms QuantumNLS.Prop001RfourteenTraceRegrouping.overlapIdeal

#print axioms QuantumNLS.Prop001RfourteenTraceRegrouping.overlapIdeal_val

#print axioms QuantumNLS.Prop001RfourteenTraceRegrouping.rawGenerator_ideal_regroup

#print axioms QuantumNLS.Prop001RfourteenTraceRegrouping.rawGenerator_trace_regroup
