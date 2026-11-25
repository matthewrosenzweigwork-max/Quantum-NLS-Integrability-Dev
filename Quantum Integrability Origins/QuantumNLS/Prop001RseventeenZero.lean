import QuantumNLS.Prop001RsixteenDuhamel
import QuantumNLS.Prop001RfourteenIdentification

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 200000
open Filter Topology
open scoped InnerProductSpace BigOperators ENNReal
namespace QuantumNLS.Prop001RseventeenZero
open TraceClass TraceIdeal TensorCarrier PhysicalTensor Prop001
  Ext025A12Trace Ext025B11TracePairing Ext025B11TraceBasis Prop001RthirteenSeries
  Prop001RfifteenRemainder Prop001RsixteenHierarchy Prop001RsixteenSeries
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance (j : ℕ) : NormedSpace ℝ (RankOperator H j) :=
  NormedSpace.restrictScalars ℝ ℂ (RankOperator H j)

/-- The normalized vacuum vector spans the actual completed zero tensor power. -/
theorem zero_tensor_span (v : H) (x : HilbertTensorPower ℂ H 0) :
    x = (zeroSectorIso x) • (htpow 0 v : HilbertTensorPower ℂ H 0) := by
  apply zeroSectorIso.injective
  simp [zeroSectorIso_htpow]

/-- A positive trace-one operator on a Hilbert line is its unit density.
The generic carrier keeps the completed tensor's inner-product instance fixed. -/
theorem unit_density_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (e : E ≃ₗᵢ[ℂ] ℂ) (z : E) (hz : e z=1)
    (T : E →L[ℂ] E) (hT : T.IsPositive)
    (ht : traceIn (((OrthonormalBasis.singleton Unit ℂ).map e.symm).toHilbertBasis) T = 1) :
    T = InnerProductSpace.rankOne ℂ z z := by
  let b := ((OrthonormalBasis.singleton Unit ℂ).map e.symm).toHilbertBasis
  have hb (i : Unit) : b i=z := by
    apply e.injective
    simp [b,OrthonormalBasis.coe_toHilbertBasis,hz]
  have htr : trace b T = 1 := by
    rw [trace_positive b T hT,posTrace_eq b hT,ht]
    simp
  have hdiag : ⟪z,T z⟫_ℂ = 1 := by simpa [trace,hb] using htr
  have hin (x : E) : ⟪z,x⟫_ℂ=e x := by
    have hi := e.inner_map_map z x
    rw [hz] at hi
    simpa using hi.symm
  have hTz : T z=z := by
    apply e.injective
    rw [← hin (T z),hdiag,hz]
  have hspan (x : E) : x=(e x) • z := by
    apply e.injective
    simp [hz]
  ext x
  calc
    T x = (e x) • z := by conv_lhs => rw [hspan x,map_smul,hTz]
    _ = InnerProductSpace.rankOne ℂ z z x := by rw [InnerProductSpace.rankOne_apply,hin]

/-- The actual rank-zero marginal is identically the scalar vacuum density. -/
theorem marginal_zero (D : ClassicalData H) (N : ℕ)
    (ψ : SymSector ℂ H N) (hψ : ‖ψ‖=1) (v : H) (t : ℝ) :
    extendedMarginal D.A N 0 t ψ = coherentProjector 0 v := by
  rw [extendedMarginal_of_le D.A N 0 (Nat.zero_le N)]
  exact unit_density_eq (zeroSectorIso (𝕜 := ℂ) (E := H)) (htpow 0 v)
    (zeroSectorIso_htpow v) _ (marginal_positive D.A N 0 (Nat.zero_le N) t ψ)
    (marginal_trace_one D.A D.selfAdjoint N 0 (Nat.zero_le N) t ψ hψ _)

/-- The source collision operator includes its empty output-rank sum. -/
def allCollision (A : Interactions H) (Γ : Hierarchy H)
    (hΓ : ∀ k,IsTraceClass (Γ k)) : ∀ k,RankOperator H k
  | 0 => 0
  | k+1 => collisionSeries A Γ hΓ k

/-- Every natural output rank, including zero, has the actual finite hierarchy
and the source C0 bound. The remainder is constructed by rank cases. -/
theorem finite_hierarchy_at_rank (D : ClassicalData H) (N j : ℕ)
    (ψ : SymSector ℂ H N) (hψ : ‖ψ‖=1) :
    ∃ R : ℝ → RankOperator H j, ∀ t : ℝ,
      Tendsto (fun s => traceNorm
        (slope (fun r => extendedMarginal D.A N j r ψ) t s-
          (-Complex.I) • (allCollision D.A
            (fun k => extendedMarginal D.A N k t ψ)
            (extendedMarginal_isTraceClass D.A D.selfAdjoint N t ψ hψ) j+R t)))
        (𝓝[≠] t) (𝓝 0) ∧
      traceNorm (R t) ≤ ENNReal.ofReal (errorSum D.A*(j : ℝ)^2/N) := by
  cases j with
  | zero =>
    let : NormedSpace ℝ (RankOperator H 0) := NormedSpace.restrictScalars ℝ ℂ (RankOperator H 0)
    refine ⟨fun _ => 0,fun t => ⟨?_,?_⟩⟩
    · have he : (fun r => extendedMarginal D.A N 0 r ψ) =
          (fun _ : ℝ => coherentProjector 0 (0 : H)) :=
        funext (marginal_zero D N ψ hψ 0)
      simp only [he,allCollision,add_zero,smul_zero,slope_def_module,
        sub_self,Fidelity.traceNorm_zero]
      exact tendsto_const_nhds
    · simp [Fidelity.traceNorm_zero]
  | succ k =>
    by_cases hk : k+1 ≤ N
    · obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hk
      refine ⟨finiteCorrection D k m ψ hψ,fun t => ?_⟩
      simpa only [allCollision,extendedMarginal_of_le D.A ((k+1)+m) (k+1) (by omega),
        Nat.cast_add,Nat.cast_one]
        using PROP001_finite_hierarchy D k m ψ hψ t
    · refine ⟨fun _ => 0,fun t => ⟨?_,?_⟩⟩
      · simpa only [allCollision,add_zero] using above_rank_hierarchy D N k (by omega) ψ hψ t
      · simp only [Fidelity.traceNorm_zero];exact bot_le

/-- A single hierarchy of constructed remainders gives the equation and bound
simultaneously at every natural rank. No equation or bound is an input. -/
theorem PROP001_finite_hierarchy_all (D : ClassicalData H) (N : ℕ)
    (ψ : SymSector ℂ H N) (hψ : ‖ψ‖=1) :
    ∃ R : ∀ j : ℕ,ℝ → RankOperator H j, ∀ (j : ℕ) (t : ℝ),
      Tendsto (fun s => traceNorm
        (slope (fun r => extendedMarginal D.A N j r ψ) t s-
          (-Complex.I) • (allCollision D.A
            (fun k => extendedMarginal D.A N k t ψ)
            (extendedMarginal_isTraceClass D.A D.selfAdjoint N t ψ hψ) j+R j t)))
        (𝓝[≠] t) (𝓝 0) ∧
      traceNorm (R j t) ≤ ENNReal.ofReal (errorSum D.A*(j : ℝ)^2/N) := by
  classical
  exact ⟨fun j => (finite_hierarchy_at_rank D N j ψ hψ).choose,
    fun j => (finite_hierarchy_at_rank D N j ψ hψ).choose_spec⟩

end QuantumNLS.Prop001RseventeenZero

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001RseventeenZero" then
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
  Lean.logInfo m!"Prop001RseventeenZero audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."




#print axioms QuantumNLS.Prop001RseventeenZero.zero_tensor_span
#print axioms QuantumNLS.Prop001RseventeenZero.unit_density_eq
#print axioms QuantumNLS.Prop001RseventeenZero.marginal_zero
#print axioms QuantumNLS.Prop001RseventeenZero.allCollision

#print axioms QuantumNLS.Prop001RseventeenZero.finite_hierarchy_at_rank
#print axioms QuantumNLS.Prop001RseventeenZero.PROP001_finite_hierarchy_all
