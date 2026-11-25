import QuantumNLS.Prop001RfourteenContraction
import QuantumNLS.Prop001RthirteenDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
open Filter Topology
open scoped InnerProductSpace BigOperators ENNReal
namespace QuantumNLS.Prop001RfourteenIdentification
open TensorCarrier TensorPlacements PhysicalEnergyTrace Ext025A12Collision
  Prop001RthirteenProduct Ext025A8 Prop001 Prop001RfourteenContraction
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H

def velocityMap (k : ℕ) (u : H) : H →L[ℂ] HilbertTensorPower ℂ H k :=
  (tensorMultilinear k).linearDeriv (fun _ => u) ∘L
    ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℂ H)

theorem velocityMap_apply (k : ℕ) (u v : H) : velocityMap k u v = tensorVelocity k u v := rfl

theorem rankContraction_product (k n : ℕ)
    (A : SymSector ℂ H (n+1) →L[ℂ] SymSector ℂ H (n+1)) (u : H) :
    rankContraction k n A u (htpow (k+1) u) =
      velocityMap (k+1) u (((n+1 : ℕ) : ℂ) • hartreeContraction (extendSymKernel A) u u) := by
  unfold rankContraction
  simp only [smul_apply,sum_apply,splitContraction_product]
  rw [← tensorVelocity_eq_sum]
  exact ((velocityMap (k+1) u).map_smul _ _).symm

theorem hartreeTerms_summable (A : Interactions H)
    (hcubic : Summable (fun n => ((n+1 : ℕ) : ℝ)^3*‖A n‖))
    (u : H) (hu : ‖u‖ = 1) :
    Summable (fun n => hartreeTerm (fun m => extendSymKernel (A m)) n u) := by
  apply Summable.of_norm_bounded (Prop001RthirteenSeries.weighted_rank_summable A hcubic)
  intro n
  have hn := hartreeTerm_norm (fun m => extendSymKernel (A m)) n u
  simp only [hu,one_pow,mul_one] at hn
  exact hn.trans (by gcongr; exact norm_extendSymKernel_le _)

theorem summedContraction_product (A : Interactions H)
    (hcubic : Summable (fun n => ((n+1 : ℕ) : ℝ)^3*‖A n‖))
    (k : ℕ) (u : H) (hu : ‖u‖ = 1) :
    (∑' n,rankContraction k n (A n) u) (htpow (k+1) u) =
      velocityMap (k+1) u (∑' n,hartreeTerm (fun m => extendSymKernel (A m)) n u) := by
  rw [tsum_apply (rankContraction_summable A hcubic k u hu)]
  simp_rw [rankContraction_product]
  exact ((velocityMap (k+1) u).map_tsum (hartreeTerms_summable A hcubic u hu)).symm

theorem hartree_tensor_velocity (A : Interactions H)
    (hcubic : Summable (fun n => ((n+1 : ℕ) : ℝ)^3*‖A n‖))
    (k : ℕ) (u : H) (hu : ‖u‖ = 1) :
    tensorVelocity (k+1) u (sourceHartreeField A u) =
      (-Complex.I) • (∑' n,rankContraction k n (A n) u) (htpow (k+1) u) := by
  change velocityMap (k+1) u ((-Complex.I) • ∑' n,hartreeTerm (fun m => extendSymKernel (A m)) n u) = _
  rw [map_smul,← summedContraction_product A hcubic k u hu]

theorem perm_adjoint (m : ℕ) (σ : Equiv.Perm (Fin m)) :
    (permRep ℂ H m σ : HilbertTensorPower ℂ H m →L[ℂ] _).adjoint =
      (permRep ℂ H m σ⁻¹ : HilbertTensorPower ℂ H m →L[ℂ] _) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  exact (Prop001RfourteenContraction.inner_perm m σ x y).symm

theorem placedInteraction_adjoint (k n : ℕ) (σ : Equiv.Perm (Fin (n+1+k)))
    (A : SymSector ℂ H (n+1) →L[ℂ] SymSector ℂ H (n+1)) :
    (placedInteraction k n σ A).adjoint = placedInteraction k n σ A.adjoint := by
  have hp : (permutedPlacement (q := k) σ A).adjoint =
      permutedPlacement σ A.adjoint := by
    simp only [permutedPlacement,ContinuousLinearMap.adjoint_comp,perm_adjoint,
      GenericUAdjoint.adjoint_firstPlacement,inv_inv,ContinuousLinearMap.comp_assoc]
  have hc {m l : ℕ} (h : m=l) (T : RankOperator H m) :
      (PlacementFusion.castTensorOperator h T).adjoint =
        PlacementFusion.castTensorOperator h T.adjoint := by cases h; rfl
  unfold placedInteraction
  rw [hc,hp]

theorem pull_adjoint {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (e : X ≃ₗᵢ[ℂ] Y) (T : Y →L[ℂ] Y) : (pull e T).adjoint = pull e T.adjoint := by
  change ((e.symm.toLinearIsometry.toContinuousLinearMap ∘L T) ∘L
      e.toLinearIsometry.toContinuousLinearMap).adjoint =
    e.symm.toLinearIsometry.toContinuousLinearMap ∘L T.adjoint ∘L
      e.toLinearIsometry.toContinuousLinearMap
  simp only [ContinuousLinearMap.adjoint_comp,GenericUAdjoint.adjoint_iso,
    LinearIsometryEquiv.symm_symm,ContinuousLinearMap.comp_assoc]

theorem rankContraction_selfAdjoint (k n : ℕ)
    (A : SymSector ℂ H (n+1) →L[ℂ] SymSector ℂ H (n+1))
    (hA : IsSelfAdjoint A) (u : H) : IsSelfAdjoint (rankContraction k n A u) := by
  have hs (j : Fin (k+1)) : IsSelfAdjoint (splitContraction (k+1) n
      (placedInteraction k n (subsetRepresentative (oneOverlapSubset k n j)) A) u) := by
    apply contraction_selfAdjoint
    change (pull _ _).adjoint = pull _ _
    rw [pull_adjoint,placedInteraction_adjoint,show A.adjoint=A from hA]
  change star (rankContraction k n A u) = rankContraction k n A u
  unfold rankContraction
  rw [star_smul,star_sum]
  simp only [star_natCast]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => hs j)

theorem summedContraction_selfAdjoint (A : Interactions H)
    (hA : ∀ n, IsSelfAdjoint (A n)) (k : ℕ) (u : H) :
    IsSelfAdjoint (∑' n,rankContraction k n (A n) u) := by
  change star (∑' n,rankContraction k n (A n) u) = _
  rw [tsum_star]
  exact tsum_congr (fun n => rankContraction_selfAdjoint k n (A n) (hA n) u)

theorem projector_commutator {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (B : E →L[ℂ] E) (hB : IsSelfAdjoint B) (z : E) :
    InnerProductSpace.rankOne ℂ ((-Complex.I) • B z) z +
      InnerProductSpace.rankOne ℂ z ((-Complex.I) • B z) =
      (-Complex.I) • (B*InnerProductSpace.rankOne ℂ z z-InnerProductSpace.rankOne ℂ z z*B) := by
  ext x
  simp only [add_apply,smul_apply,sub_apply,mul_apply_eq_comp,
    InnerProductSpace.rankOne_apply,inner_smul_left,map_smul]
  rw [← ContinuousLinearMap.adjoint_inner_left B,show B.adjoint = B from hB]
  simp only [map_neg,Complex.conj_I,neg_neg]
  module

/-- The source collision series equals the trace-norm product derivative,
with the actual placements and the constructed Hartree field. -/
theorem product_collision_identification (A : Interactions H)
    (hA : ∀ n, IsSelfAdjoint (A n))
    (hcubic : Summable (fun n => ((n+1 : ℕ) : ℝ)^3*‖A n‖))
    (k : ℕ) (u : H) (hu : ‖u‖ = 1) :
    let z := (htpow (k+1) u : HilbertTensorPower ℂ H (k+1))
    let w := tensorVelocity (k+1) u (sourceHartreeField A u)
    InnerProductSpace.rankOne ℂ w z+InnerProductSpace.rankOne ℂ z w =
      (-Complex.I) • Prop001RthirteenSeries.collisionSeries A (fun m => coherentProjector m u)
        (Prop001RthirteenSeries.coherent_isTraceClass u hu) k := by
  dsimp only
  rw [hartree_tensor_velocity A hcubic k u hu,
    collisionSeries_product_commutator A hcubic k u hu]
  exact projector_commutator _ (summedContraction_selfAdjoint A hA k u) _

/-- Literal trace-norm hierarchy equation along the global Hartree flow. -/
theorem trajectory_collision_derivative (D : ClassicalData H) (u : Sphere H)
    (k : ℕ) (t : ℝ) :
    Tendsto (fun s => TraceClass.traceNorm
      (slope (fun r => coherentProjector (k+1) (trajectory D u r)) t s -
        (-Complex.I) • Prop001RthirteenSeries.collisionSeries D.A
          (fun m => coherentProjector m (trajectory D u t))
          (Prop001RthirteenSeries.coherent_isTraceClass (trajectory D u t)
            (((trajectory_spec D u).2.2.1 t).1)) k)) (𝓝[≠] t) (𝓝 0) := by
  rw [← product_collision_identification D.A D.selfAdjoint D.cubic k
    (trajectory D u t) (((trajectory_spec D u).2.2.1 t).1)]
  exact Prop001RthirteenDerivative.trajectory_trace_derivative D u (k+1) t

/-- Printed source hypotheses imply the global Hartree solution and its
actual product-hierarchy collision equation. This theorem does not assert
the still-open finite-marginal propagation rate. -/
theorem PROP001_hartree_collision
    (A : Interactions H) (hA : ∀ n, IsSelfAdjoint (A n))
    {a : ℝ} (ha : 0 < a)
    (hcubic : Summable (fun n => ((n+1 : ℕ) : ℝ)^3*‖A n‖))
    (hexp : Summable (fun n => (n+1 : ℕ)*‖A n‖*Real.exp (a*n)))
    {u₀ : H} (hu₀ : ‖u₀‖ = 1) :
    ∃ (α : ℝ → H) (hunit : ∀ t, ‖α t‖ = 1),
      α 0 = u₀ ∧ ContDiff ℝ 1 α ∧
      (∀ t, HasDerivAt α (sourceHartreeField A (α t)) t) ∧
      (∀ (k : ℕ) (t : ℝ),
        Tendsto (fun s => TraceClass.traceNorm
          (slope (fun r => coherentProjector (k+1) (α r)) t s -
            (-Complex.I) • Prop001RthirteenSeries.collisionSeries A
              (fun m => coherentProjector m (α t))
              (Prop001RthirteenSeries.coherent_isTraceClass (α t) (hunit t)) k))
          (𝓝[≠] t) (𝓝 0)) ∧
      (∀ β : ℝ → H, β 0 = u₀ →
        (∀ t, ‖β t‖ = 1 ∧ HasDerivAt β (sourceHartreeField A (β t)) t) → β = α) := by
  let D : ClassicalData H := ⟨A,hA,a,ha,hcubic,hexp⟩
  let u : Sphere H := ⟨u₀,hu₀⟩
  have hs := trajectory_spec D u
  refine ⟨trajectory D u,fun t => (hs.2.2.1 t).1,hs.1,hs.2.1,
    fun t => (hs.2.2.1 t).2,?_,hs.2.2.2⟩
  intro k t
  exact trajectory_collision_derivative D u k t

end QuantumNLS.Prop001RfourteenIdentification

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001RfourteenIdentification" then
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
  Lean.logInfo m!"Prop001RfourteenIdentification audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."


#print axioms QuantumNLS.Prop001RfourteenIdentification.velocityMap

#print axioms QuantumNLS.Prop001RfourteenIdentification.velocityMap_apply

#print axioms QuantumNLS.Prop001RfourteenIdentification.rankContraction_product

#print axioms QuantumNLS.Prop001RfourteenIdentification.hartreeTerms_summable

#print axioms QuantumNLS.Prop001RfourteenIdentification.summedContraction_product

#print axioms QuantumNLS.Prop001RfourteenIdentification.hartree_tensor_velocity

#print axioms QuantumNLS.Prop001RfourteenIdentification.perm_adjoint

#print axioms QuantumNLS.Prop001RfourteenIdentification.placedInteraction_adjoint

#print axioms QuantumNLS.Prop001RfourteenIdentification.pull_adjoint

#print axioms QuantumNLS.Prop001RfourteenIdentification.rankContraction_selfAdjoint

#print axioms QuantumNLS.Prop001RfourteenIdentification.summedContraction_selfAdjoint

#print axioms QuantumNLS.Prop001RfourteenIdentification.projector_commutator

#print axioms QuantumNLS.Prop001RfourteenIdentification.product_collision_identification

#print axioms QuantumNLS.Prop001RfourteenIdentification.trajectory_collision_derivative

#print axioms QuantumNLS.Prop001RfourteenIdentification.PROP001_hartree_collision

set_option pp.proofs false in
#print QuantumNLS.Prop001RfourteenIdentification.PROP001_hartree_collision
