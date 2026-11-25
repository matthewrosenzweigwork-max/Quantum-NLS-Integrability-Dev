import QuantumNLS.Ext025A12PartialTrace
import QuantumNLS.Prop001RtenHierarchy
import QuantumNLS.PhysicalEnergyTrace

/-! PROP-001: trace-class collision terms on the actual tensor powers. The
commutator is reduced by the constructed general partial trace. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
open scoped InnerProductSpace BigOperators ENNReal
namespace QuantumNLS.Ext025A12Collision
open TraceClass TraceIdeal TensorCarrier TensorPlacements PlacementFusion PhysicalEnergyTrace
  Ext025A12Trace Ext025A12Normal Ext025A12PartialTrace Prop001
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem commutator_finite {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (B T : E →L[ℂ] E) (ht : IsTraceClass T) : IsTraceClass (B*T-T*B) :=
  finite_sub (lt_top_iff_ne_top.mpr (Ext025B11TracePairing.finite_left B T ht.ne))
    (finite_right B T ht)

/-- General partial trace transported across the repository's completed split. -/
def splitTrace (k m : ℕ) (T : RankOperator H (k+m)) (ht : IsTraceClass T) : RankOperator H k :=
  partialTrace (pull (splitIsometry k m).symm T)
    (by simpa only [IsTraceClass,traceNorm_pull] using ht)

theorem splitTrace_bound (k m : ℕ) (T : RankOperator H (k+m)) (ht : IsTraceClass T) :
    traceNorm (splitTrace k m T ht) ≤ traceNorm T := by
  unfold splitTrace
  exact (traceNorm_partialTrace_le _ _).trans_eq (traceNorm_pull _ T)

theorem collision_commutator_bound (k m : ℕ) (B T : RankOperator H (k+m))
    (ht : IsTraceClass T) :
    traceNorm (splitTrace k m (B*T-T*B) (commutator_finite B T ht)) ≤
      2*ENNReal.ofReal ‖B‖*traceNorm T :=
  (splitTrace_bound k m _ _).trans (Prop001.traceNorm_commutator_le B T)

/-- A rank n+1 interaction in any permuted placement. The universal bound
below therefore applies in particular to the source's one-overlap placements. -/
def placedInteraction (k n : ℕ) (σ : Equiv.Perm (Fin (n+1+k)))
    (A : SymSector ℂ H (n+1) →L[ℂ] SymSector ℂ H (n+1)) : RankOperator H ((k+1)+n) :=
  castTensorOperator (by omega : n+1+k=(k+1)+n) (permutedPlacement (q := k) σ A)

theorem placedInteraction_norm (k n : ℕ) (σ : Equiv.Perm (Fin (n+1+k)))
    (A : SymSector ℂ H (n+1) →L[ℂ] SymSector ℂ H (n+1)) :
    ‖placedInteraction k n σ A‖ ≤ ‖A‖ := by
  rw [placedInteraction,norm_castTensorOperator]
  exact norm_permutedPlacement_le σ A

/-- The rank-r collision sum at positive output rank k+1; r=n+1.
No hierarchy identity or differential equation is supplied as a premise. -/
def rankCollision (k n : ℕ) (σ : Fin (k+1) → Equiv.Perm (Fin (n+1+k)))
    (A : SymSector ℂ H (n+1) →L[ℂ] SymSector ℂ H (n+1))
    (T : RankOperator H ((k+1)+n)) (ht : IsTraceClass T) : RankOperator H (k+1) :=
  ((n+1 : ℕ) : ℂ) • ∑ j : Fin (k+1), splitTrace (k+1) n
    (placedInteraction k n (σ j) A*T-T*placedInteraction k n (σ j) A)
    (commutator_finite _ T ht)

/-- The printed rank-r bound 2 r k ||A_r||, for every choice of its
permuted placements, on arbitrary trace-class hierarchy errors. -/
theorem rankCollision_bound (k n : ℕ) (σ : Fin (k+1) → Equiv.Perm (Fin (n+1+k)))
    (A : SymSector ℂ H (n+1) →L[ℂ] SymSector ℂ H (n+1))
    (T : RankOperator H ((k+1)+n)) (ht : IsTraceClass T) :
    traceNorm (rankCollision k n σ A T ht) ≤
      ENNReal.ofReal (2*((n+1 : ℕ) : ℝ)*((k+1 : ℕ) : ℝ)*‖A‖)*traceNorm T := by
  unfold rankCollision
  rw [traceNorm_smul]
  have hb := Fidelity.traceNorm_sum_le (Finset.univ : Finset (Fin (k+1)))
    (fun j => splitTrace (k+1) n
      (placedInteraction k n (σ j) A*T-T*placedInteraction k n (σ j) A)
      (commutator_finite _ T ht))
  calc
    _ ≤ ENNReal.ofReal ‖((n+1 : ℕ) : ℂ)‖ * ∑ j : Fin (k+1), traceNorm
        (splitTrace (k+1) n (placedInteraction k n (σ j) A*T-T*placedInteraction k n (σ j) A)
          (commutator_finite _ T ht)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ ENNReal.ofReal ‖((n+1 : ℕ) : ℂ)‖ * ∑ _j : Fin (k+1),
        (2*ENNReal.ofReal ‖A‖*traceNorm T) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro j _
      exact (collision_commutator_bound (k+1) n _ T ht).trans (by
        gcongr
        exact placedInteraction_norm k n (σ j) A)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      rw [Complex.norm_natCast,ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (by positivity)]
      simp only [ENNReal.ofReal_natCast,ENNReal.ofReal_ofNat]
      ring

/-- The source's active coordinates: one of the first k+1 slots and all
n spectator slots, transported only by the displayed arithmetic equality. -/
def oneOverlapSubset (k n : ℕ) (j : Fin (k+1)) : PlacementSubset (n+1) k := by
  classical
  let tail : Finset (Fin ((k+1)+n)) := Finset.univ.map (Fin.natAddEmb (k+1))
  have hj : Fin.castAdd n j ∉ tail := by
    intro h
    obtain ⟨i,_,he⟩ := Finset.mem_map.mp h
    change Fin.natAdd (k+1) i = Fin.castAdd n j at he
    have hv : k+1+i.val=j.val := congrArg Fin.val he
    omega
  exact ⟨(insert (Fin.castAdd n j) tail).map
    (finCongr (by omega : (k+1)+n=n+1+k)).toEmbedding,by
      rw [Finset.card_map,Finset.card_insert_of_notMem hj]
      simp only [tail,Finset.card_map,Finset.card_univ,Fintype.card_fin]⟩

/-- The actual one-overlap collision in eq:A2-infinite-collision. -/
def sourceRankCollision (k n : ℕ)
    (A : SymSector ℂ H (n+1) →L[ℂ] SymSector ℂ H (n+1))
    (T : RankOperator H ((k+1)+n)) (ht : IsTraceClass T) : RankOperator H (k+1) :=
  rankCollision k n (fun j => subsetRepresentative (oneOverlapSubset k n j)) A T ht

theorem sourceRankCollision_bound (k n : ℕ)
    (A : SymSector ℂ H (n+1) →L[ℂ] SymSector ℂ H (n+1))
    (T : RankOperator H ((k+1)+n)) (ht : IsTraceClass T) :
    traceNorm (sourceRankCollision k n A T ht) ≤
      ENNReal.ofReal (2*((n+1 : ℕ) : ℝ)*((k+1 : ℕ) : ℝ)*‖A‖)*traceNorm T :=
  rankCollision_bound k n _ A T ht

/-- The ell=0 terms of the finite hierarchy vanish after partial trace,
for arbitrary mixed trace-class inputs and arbitrary bounded spectators. -/
theorem spectator_commutator_zero {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (C : Y →L[ℂ] Y) (T : HilbertTensor ℂ X Y →L[ℂ] HilbertTensor ℂ X Y)
    (ht : IsTraceClass T) :
    partialTrace (htmap (ContinuousLinearMap.id ℂ X) C*T-T*htmap (ContinuousLinearMap.id ℂ X) C)
      (commutator_finite _ T ht) = (0 : X →L[ℂ] X) := by
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [inner_partialTrace,zero_apply,inner_zero_right]
  let K := ampliate ℂ X Y (InnerProductSpace.rankOne ℂ y x)
  let B := htmap (ContinuousLinearMap.id ℂ X) C
  have hc : Commute K B := disjoint_htmap_commute _ C
  have hf : IsTraceClass (K*T) := lt_top_iff_ne_top.mpr (Ext025B11TracePairing.finite_left K T ht.ne)
  have he : K*(B*T-T*B) = B*(K*T)-(K*T)*B := by
    rw [mul_sub,← mul_assoc,hc.eq,mul_assoc,mul_assoc]
  change tr (K*(B*T-T*B)) = 0
  rw [he,tr,Ext025B11TracePairing.trace_sub _ _ _
    (Ext025B11TracePairing.finite_left B _ hf.ne) (finite_right B _ hf).ne,
    trace_cycle _ B (K*T) hf,sub_self]

end QuantumNLS.Ext025A12Collision

#print axioms QuantumNLS.Ext025A12Collision.splitTrace
#print axioms QuantumNLS.Ext025A12Collision.splitTrace_bound
#print axioms QuantumNLS.Ext025A12Collision.collision_commutator_bound
#print axioms QuantumNLS.Ext025A12Collision.rankCollision_bound
set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025A12Collision" then
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
  Lean.logInfo m!"Ext025A12Collision audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
