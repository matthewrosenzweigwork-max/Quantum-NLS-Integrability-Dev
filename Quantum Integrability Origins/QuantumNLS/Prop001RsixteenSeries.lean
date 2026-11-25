import QuantumNLS.Prop001RfifteenFinite

/-! Exact finite support of the actual marginal collision series. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
open Filter Topology
open scoped InnerProductSpace BigOperators ENNReal
namespace QuantumNLS.Prop001RsixteenSeries
open TraceClass TraceIdeal TensorCarrier TensorPlacements PlacementFusion PhysicalEnergyTrace
  Ext025A12Trace Ext025A12Normal Ext025A12PartialTrace Ext025A12Collision
  Prop001 Prop001RfourteenTraceRegrouping Prop001RthirteenSeries
  Prop001RfifteenTransport Prop001RfifteenRemainder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H
local instance (j : ℕ) : NormedSpace ℝ (RankOperator H j) :=
  NormedSpace.restrictScalars ℝ ℂ (RankOperator H j)

/-- Zero input has zero constructed partial trace. -/
theorem splitTrace_zero (k m : ℕ) (h : IsTraceClass (0 : RankOperator H (k+m))) :
    splitTrace k m (0 : RankOperator H (k+m)) h = 0 := by
  change (splitMap k m (⟨0,h⟩ : traceIdeal (HilbertTensorPower ℂ H (k+m)))).val=0
  have hz : (⟨0,h⟩ : traceIdeal (HilbertTensorPower ℂ H (k+m)))=0 := Subtype.ext rfl
  rw [hz,map_zero]
  rfl

/-- Collision terms vanish exactly at zero input, including every actual
placement and every constructed partial trace. -/
theorem sourceRankCollision_zero (k n : ℕ)
    (A : SymSector ℂ H (n+1) →L[ℂ] SymSector ℂ H (n+1))
    (h : IsTraceClass (0 : RankOperator H ((k+1)+n))) :
    sourceRankCollision k n A 0 h = 0 := by
  unfold sourceRankCollision rankCollision
  simp only [mul_zero,zero_mul,sub_self,splitTrace_zero,Finset.sum_const_zero,smul_zero]

/-- Above N, the actual extended marginal is identically zero. -/
theorem extendedMarginal_above (A : Interactions H) (N j : ℕ) (hj : N < j)
    (ψ : SymSector ℂ H N) (t : ℝ) : extendedMarginal A N j t ψ = 0 := by
  rw [extendedMarginal,dite_eq_right (by omega)]

/-- No infinite tail remains in the finite marginal's collision series.
This is an exact operator identity on the literal actual marginals. -/
theorem finite_collision_eq_sum (D : ClassicalData H) (N k : ℕ)
    (ψ : SymSector ℂ H N) (hψ : ‖ψ‖=1) (t : ℝ) :
    collisionSeries D.A (fun j => extendedMarginal D.A N j t ψ)
      (extendedMarginal_isTraceClass D.A D.selfAdjoint N t ψ hψ) k =
    ∑ n ∈ Finset.range (N-(k+1)+1), sourceRankCollision k n (D.A n)
      (extendedMarginal D.A N ((k+1)+n) t ψ)
      (extendedMarginal_isTraceClass D.A D.selfAdjoint N t ψ hψ _) := by
  unfold collisionSeries
  apply tsum_eq_sum
  intro n hn
  have hnj : N < (k+1)+n := by
    have hnn : N-(k+1)+1 ≤ n := Nat.le_of_not_gt (fun h => hn (Finset.mem_range.mpr h))
    omega
  simp only [extendedMarginal_above D.A N _ hnj,sourceRankCollision_zero]

/-- The collision component itself vanishes above the largest finite rank. -/
theorem finite_collision_above (D : ClassicalData H) (N k : ℕ) (hk : N < k+1)
    (ψ : SymSector ℂ H N) (hψ : ‖ψ‖=1) (t : ℝ) :
    collisionSeries D.A (fun j => extendedMarginal D.A N j t ψ)
      (extendedMarginal_isTraceClass D.A D.selfAdjoint N t ψ hψ) k = 0 := by
  unfold collisionSeries
  have hz (n : ℕ) : sourceRankCollision k n (D.A n)
      (extendedMarginal D.A N ((k+1)+n) t ψ)
      (extendedMarginal_isTraceClass D.A D.selfAdjoint N t ψ hψ _) = 0 := by
    simp only [extendedMarginal_above D.A N _ (show N < (k+1)+n by omega),sourceRankCollision_zero]
  simp_rw [hz]
  exact tsum_zero

/-- The exact finite hierarchy equation above N holds with zero remainder.
Neither a derivative nor a hierarchy equation is supplied as a premise. -/
theorem above_rank_hierarchy (D : ClassicalData H) (N k : ℕ) (hk : N < k+1)
    (ψ : SymSector ℂ H N) (hψ : ‖ψ‖=1) (t : ℝ) :
    Tendsto (fun s => traceNorm
      (slope (fun r => extendedMarginal D.A N (k+1) r ψ) t s-
        (-Complex.I) • collisionSeries D.A (fun j => extendedMarginal D.A N j t ψ)
          (extendedMarginal_isTraceClass D.A D.selfAdjoint N t ψ hψ) k))
      (𝓝[≠] t) (𝓝 0) := by
  let _ : SMulZeroClass ℝ (RankOperator H (k+1)) :=
    { (NormedSpace.restrictScalars ℝ ℂ (RankOperator H (k+1))).toModule.toDistribMulAction with }
  simp only [extendedMarginal_above D.A N _ hk,finite_collision_above D N k hk ψ hψ t,
    smul_zero,slope_def_module,sub_self,Fidelity.traceNorm_zero]
  exact tendsto_const_nhds

/-- A visible block of size at most one cannot meet an active subset twice. -/
theorem multipleOverlapEvent_small {N : ℕ} (P : Finset (Fin N)) (hP : P.card ≤ 1)
    (r : ℕ) : multipleOverlapEvent P r=∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro Q hQ
  have h := (Finset.mem_filter.mp hQ).2
  have hh := Finset.card_le_card (Finset.inter_subset_left (s₁ := P) (s₂ := Q))
  omega

/-- The literal two-overlap remainder is zero at one-particle output rank. -/
theorem multipleRemainder_one (D : ClassicalData H) (m : ℕ)
    (P : Finset (Fin (1+m))) (hP : P.card ≤ 1)
    (T : RankOperator H (1+m)) (hT : IsTraceClass T) :
    multipleRemainder D 1 m P T hT=0 := by
  classical
  unfold multipleRemainder multipleRank
  simp only [multipleOverlapEvent_small P hP,Finset.sum_empty,smul_zero,Finset.sum_const_zero]

/-- At N=1 the concrete correction is exactly zero, including its literal
multiple-overlap placement sum. -/
theorem finiteCorrection_None (D : ClassicalData H)
    (ψ : SymSector ℂ H ((0+1)+0)) (hψ : ‖ψ‖=1) (t : ℝ) :
    finiteCorrection D 0 0 ψ hψ t=0 := by
  classical
  unfold finiteCorrection
  rw [multipleRemainder_one D 0 _ (card_firstPositions 1 0).le]
  simp only [add_zero,oneOverlapCorrection]
  norm_num [alpha_zero]

/-- The concrete C0 k²/N budget includes the previously missing N=1
boundary. Its identification with the complete hierarchy remains separate. -/
theorem finiteCorrection_bound_positive (D : ClassicalData H) (k m : ℕ)
    (ψ : SymSector ℂ H ((k+1)+m)) (hψ : ‖ψ‖=1) (t : ℝ) :
    traceNorm (finiteCorrection D k m ψ hψ t) ≤
      ENNReal.ofReal (errorSum D.A*((k+1 : ℕ) : ℝ)^2/((k+1)+m)) := by
  by_cases hN : 2 ≤ (k+1)+m
  · exact finiteCorrection_bound D k m hN ψ hψ t
  · have hk : k=0 := by omega
    have hm : m=0 := by omega
    subst k
    subst m
    rw [finiteCorrection_None,Fidelity.traceNorm_zero]
    exact bot_le

end QuantumNLS.Prop001RsixteenSeries

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001RsixteenSeries" then
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
  Lean.logInfo m!"Prop001RsixteenSeries audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."



#print axioms QuantumNLS.Prop001RsixteenSeries.splitTrace_zero
#print axioms QuantumNLS.Prop001RsixteenSeries.sourceRankCollision_zero
#print axioms QuantumNLS.Prop001RsixteenSeries.extendedMarginal_above
#print axioms QuantumNLS.Prop001RsixteenSeries.finite_collision_eq_sum
#print axioms QuantumNLS.Prop001RsixteenSeries.finite_collision_above
#print axioms QuantumNLS.Prop001RsixteenSeries.above_rank_hierarchy
#print axioms QuantumNLS.Prop001RsixteenSeries.multipleOverlapEvent_small
#print axioms QuantumNLS.Prop001RsixteenSeries.multipleRemainder_one
#print axioms QuantumNLS.Prop001RsixteenSeries.finiteCorrection_None
#print axioms QuantumNLS.Prop001RsixteenSeries.finiteCorrection_bound_positive
