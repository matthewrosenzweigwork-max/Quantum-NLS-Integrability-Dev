import QuantumNLS.Prop001RthirteenSeries

/-! Product-state contraction identity for the constructed mixed-state
partial trace. This is an operator identity, without an assumed equation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped InnerProductSpace ENNReal BigOperators
namespace QuantumNLS.Prop001RthirteenProduct
open TraceClass TraceIdeal TensorCarrier Ext025A12Trace Ext025A12Normal
  Ext025A12PartialTrace Ext025A12Collision
variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

/-- Insertion of a fixed spectator vector in the second tensor factor. -/
def insertRight (v : Y) : X →L[ℂ] HilbertTensor ℂ X Y :=
  LinearMap.mkContinuous
    { toFun := fun x => htmul x v
      map_add' := fun x y => htmul_add_left x y v
      map_smul' := fun c x => htmul_smul_left c x v } ‖v‖ (by
      intro x
      simp only [LinearMap.coe_mk, AddHom.coe_mk, norm_htmul]
      exact (mul_comm _ _).le)

def contraction (v : Y) (B : HilbertTensor ℂ X Y →L[ℂ] HilbertTensor ℂ X Y) :
    X →L[ℂ] X := (insertRight v).adjoint ∘L B ∘L insertRight v

omit [CompleteSpace Y] in
theorem inner_contraction (v : Y) (B : HilbertTensor ℂ X Y →L[ℂ] HilbertTensor ℂ X Y)
    (x y : X) :
    ⟪x, contraction v B y⟫_ℂ = ⟪htmul x v, B (htmul y v)⟫_ℂ := by
  exact ContinuousLinearMap.adjoint_inner_right (insertRight v) x (B (htmul y v))

omit [CompleteSpace X] [CompleteSpace Y] in
theorem insertRight_norm (v : Y) : ‖insertRight (X := X) v‖ ≤ ‖v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖htmul x v‖ ≤ _
  rw [norm_htmul,mul_comm]

omit [CompleteSpace Y] in
theorem contraction_norm (v : Y)
    (B : HilbertTensor ℂ X Y →L[ℂ] HilbertTensor ℂ X Y) :
    ‖contraction v B‖ ≤ ‖v‖ * (‖B‖ * ‖v‖) := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  refine (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)).trans ?_
  rw [ContinuousLinearMap.adjoint.norm_map]
  gcongr <;> exact insertRight_norm v

omit [CompleteSpace Y] in
theorem contraction_selfAdjoint (v : Y)
    (B : HilbertTensor ℂ X Y →L[ℂ] HilbertTensor ℂ X Y) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (contraction v B) := by
  change (contraction v B).adjoint = contraction v B
  simp only [contraction,ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint]
  rw [show B.adjoint = B from hB,ContinuousLinearMap.comp_assoc]

/-- Partial trace of a bounded commutator on a product state is exactly
the commutator of its partial contraction and the first-factor projector.
Neither factor is required to be normalized. -/
theorem partialTrace_product_commutator (v : Y) (u : X)
    (B : HilbertTensor ℂ X Y →L[ℂ] HilbertTensor ℂ X Y) :
    let ψ := (htmul u v : HilbertTensor ℂ X Y)
    let P := InnerProductSpace.rankOne ℂ ψ ψ
    let ht : IsTraceClass P := (Fidelity.traceNorm_rankOne_le ψ ψ).trans_lt ENNReal.ofReal_lt_top
    partialTrace (B*P-P*B) (commutator_finite B P ht) =
      contraction v B * InnerProductSpace.rankOne ℂ u u -
        InnerProductSpace.rankOne ℂ u u * contraction v B := by
  dsimp only
  let ψ := (htmul u v : HilbertTensor ℂ X Y)
  let P := InnerProductSpace.rankOne ℂ ψ ψ
  have ht : IsTraceClass P := (Fidelity.traceNorm_rankOne_le ψ ψ).trans_lt ENNReal.ofReal_lt_top
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [inner_partialTrace]
  let K := ampliate ℂ X Y (InnerProductSpace.rankOne ℂ y x)
  have hbp : IsTraceClass (B*P) := lt_top_iff_ne_top.mpr (Ext025B11TracePairing.finite_left B P ht.ne)
  have hpb : IsTraceClass (P*B) := finite_right B P ht
  have h1 : tr (K*(B*P)) = ⟪ψ,K (B ψ)⟫_ℂ := by
    rw [← mul_assoc,tr,trace_rankOne_left]
    rfl
  have h2 : tr (K*(P*B)) = ⟪ψ,B (K ψ)⟫_ℂ := by
    rw [← mul_assoc]
    change tr ((K*InnerProductSpace.rankOne ℂ ψ ψ)*B) = _
    have hKP : K*InnerProductSpace.rankOne ℂ ψ ψ = InnerProductSpace.rankOne ℂ (K ψ) ψ := by
      rw [ContinuousLinearMap.mul_def,InnerProductSpace.comp_rankOne]
    rw [hKP,tr,trace_rankOne_right]
  have hK : K ψ = ⟪x,u⟫_ℂ • htmul y v := by
    change htmap (InnerProductSpace.rankOne ℂ y x) (ContinuousLinearMap.id ℂ Y) (htmul u v) = _
    rw [htmap_htmul,InnerProductSpace.rankOne_apply,ContinuousLinearMap.id_apply,htmul_smul_left]
  have hKa : K.adjoint ψ = ⟪y,u⟫_ℂ • htmul x v := by
    change (htmap (InnerProductSpace.rankOne ℂ y x) (ContinuousLinearMap.id ℂ Y)).adjoint (htmul u v) = _
    rw [adjoint_htmap,InnerProductSpace.adjoint_rankOne,ContinuousLinearMap.adjoint_id,
      htmap_htmul,InnerProductSpace.rankOne_apply,ContinuousLinearMap.id_apply,htmul_smul_left]
  change tr (K*(B*P-P*B)) = _
  rw [mul_sub,tr,Ext025B11TracePairing.trace_sub _ _ _
    (Ext025B11TracePairing.finite_left K _ hbp.ne)
    (Ext025B11TracePairing.finite_left K _ hpb.ne)]
  change tr (K*(B*P))-tr (K*(P*B)) = _
  rw [h1,h2,← ContinuousLinearMap.adjoint_inner_left K,hKa,hK,map_smul,
    inner_smul_left,inner_smul_right]
  simp only [sub_apply,mul_apply_eq_comp,InnerProductSpace.rankOne_apply,map_smul,
    inner_sub_right,inner_smul_right]
  rw [inner_contraction,inner_contraction,inner_conj_symm]
  ring

open Prop001 PhysicalEnergyTrace PhysicalTensor

theorem pull_rankOne {F G : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (e : G ≃ₗᵢ[ℂ] F) (a b : F) :
    pull e (InnerProductSpace.rankOne ℂ a b) =
      InnerProductSpace.rankOne ℂ (e.symm a) (e.symm b) := by
  ext x
  simp only [pull_apply,InnerProductSpace.rankOne_apply,map_smul]
  rw [PhysicalEnergyTrace.inner_symm_left]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The concrete interaction after contracting the actual spectator factors
in the completed split; it is not supplied as a hypothesis. -/
def splitContraction (k n : ℕ) (B : RankOperator H (k+n)) (v : H) : RankOperator H k :=
  contraction (htpow n v : HilbertTensorPower ℂ H n) (pull (splitIsometry k n).symm B)

theorem splitTrace_product_commutator (k n : ℕ) (B : RankOperator H (k+n))
    (v : H) (hv : ‖v‖ = 1) :
    splitTrace k n (B*coherentProjector (k+n) v-coherentProjector (k+n) v*B)
      (commutator_finite B _ (Prop001RthirteenSeries.coherent_isTraceClass v hv (k+n))) =
      splitContraction k n B v*coherentProjector k v-
        coherentProjector k v*splitContraction k n B v := by
  unfold splitTrace
  simp only [pull_sub,pull_mul,coherentProjector,pull_rankOne,
    LinearIsometryEquiv.symm_symm,splitIsometry_htpow]
  exact partialTrace_product_commutator (htpow n v : HilbertTensorPower ℂ H n)
    (htpow k v : HilbertTensorPower ℂ H k) (pull (splitIsometry k n).symm B)

/-- Exact product evaluation of every rank of the source collision sum.
The remaining slot-contraction identification with the Hartree derivative
is deliberately a separate obligation. -/
theorem sourceRankCollision_product (k n : ℕ)
    (A : SymSector ℂ H (n+1) →L[ℂ] SymSector ℂ H (n+1)) (v : H) (hv : ‖v‖ = 1) :
    sourceRankCollision k n A (coherentProjector ((k+1)+n) v)
      (Prop001RthirteenSeries.coherent_isTraceClass v hv _) =
      (((n+1 : ℕ) : ℂ) • ∑ j : Fin (k+1),
        splitContraction (k+1) n
          (placedInteraction k n (TensorPlacements.subsetRepresentative (oneOverlapSubset k n j)) A) v) *
        coherentProjector (k+1) v - coherentProjector (k+1) v *
      (((n+1 : ℕ) : ℂ) • ∑ j : Fin (k+1),
        splitContraction (k+1) n
          (placedInteraction k n (TensorPlacements.subsetRepresentative (oneOverlapSubset k n j)) A) v) := by
  unfold sourceRankCollision rankCollision
  simp_rw [splitTrace_product_commutator _ _ _ v hv]
  simp only [Finset.sum_sub_distrib,Finset.sum_mul,Finset.mul_sum,smul_sub,
    smul_mul_assoc,mul_smul_comm]

def rankContraction (k n : ℕ)
    (A : SymSector ℂ H (n+1) →L[ℂ] SymSector ℂ H (n+1)) (v : H) : RankOperator H (k+1) :=
  ((n+1 : ℕ) : ℂ) • ∑ j : Fin (k+1), splitContraction (k+1) n
    (placedInteraction k n (TensorPlacements.subsetRepresentative (oneOverlapSubset k n j)) A) v

theorem splitContraction_norm_le (k n : ℕ) (B : RankOperator H (k+n))
    (v : H) (hv : ‖v‖ = 1) : ‖splitContraction k n B v‖ ≤ ‖B‖ := by
  have h := contraction_norm (htpow n v : HilbertTensorPower ℂ H n)
    (pull (splitIsometry k n).symm B)
  simp only [norm_htpow,hv,one_pow,one_mul,mul_one] at h
  exact h.trans (norm_pull_le _ _)

theorem rankContraction_norm_le (k n : ℕ)
    (A : SymSector ℂ H (n+1) →L[ℂ] SymSector ℂ H (n+1)) (v : H) (hv : ‖v‖ = 1) :
    ‖rankContraction k n A v‖ ≤ ((k+1 : ℕ) : ℝ) * (((n+1 : ℕ) : ℝ)*‖A‖) := by
  unfold rankContraction
  rw [norm_smul,Complex.norm_natCast]
  calc
    _ ≤ ((n+1 : ℕ) : ℝ) * ∑ j : Fin (k+1), ‖splitContraction (k+1) n
        (placedInteraction k n (TensorPlacements.subsetRepresentative (oneOverlapSubset k n j)) A) v‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ ((n+1 : ℕ) : ℝ) * ∑ _j : Fin (k+1), ‖A‖ := by
      gcongr with j
      exact (splitContraction_norm_le _ _ _ v hv).trans (placedInteraction_norm k n _ A)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

theorem rankContraction_summable (A : Interactions H)
    (hcubic : Summable (fun n => ((n+1 : ℕ) : ℝ)^3*‖A n‖))
    (k : ℕ) (v : H) (hv : ‖v‖ = 1) : Summable (fun n => rankContraction k n (A n) v) := by
  exact Summable.of_norm_bounded ((Prop001RthirteenSeries.weighted_rank_summable A hcubic).mul_left
    ((k+1 : ℕ) : ℝ)) (fun n => rankContraction_norm_le k n (A n) v hv)

/-- Exact infinite product collision identity with the actual summed
spectator contractions. Identifying its action with the Hartree tensor
velocity is the next source obligation, not a premise of this theorem. -/
theorem collisionSeries_product_commutator (A : Interactions H)
    (hcubic : Summable (fun n => ((n+1 : ℕ) : ℝ)^3*‖A n‖))
    (k : ℕ) (v : H) (hv : ‖v‖ = 1) :
    Prop001RthirteenSeries.collisionSeries A (fun m => coherentProjector m v)
      (Prop001RthirteenSeries.coherent_isTraceClass v hv) k =
      (∑' n, rankContraction k n (A n) v)*coherentProjector (k+1) v -
        coherentProjector (k+1) v*(∑' n, rankContraction k n (A n) v) := by
  have hs := rankContraction_summable A hcubic k v hv
  unfold Prop001RthirteenSeries.collisionSeries
  simp_rw [sourceRankCollision_product k _ _ v hv]
  change (∑' n, (rankContraction k n (A n) v*coherentProjector (k+1) v -
    coherentProjector (k+1) v*rankContraction k n (A n) v)) = _
  rw [(hs.mul_right _).tsum_sub (hs.mul_left _),hs.tsum_mul_right,hs.tsum_mul_left]

end QuantumNLS.Prop001RthirteenProduct

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001RthirteenProduct" then
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
  Lean.logInfo m!"Prop001RthirteenProduct audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."

#print axioms QuantumNLS.Prop001RthirteenProduct.insertRight
#print axioms QuantumNLS.Prop001RthirteenProduct.contraction
#print axioms QuantumNLS.Prop001RthirteenProduct.inner_contraction
#print axioms QuantumNLS.Prop001RthirteenProduct.contraction_selfAdjoint
#print axioms QuantumNLS.Prop001RthirteenProduct.partialTrace_product_commutator

#print axioms QuantumNLS.Prop001RthirteenProduct.pull_rankOne

#print axioms QuantumNLS.Prop001RthirteenProduct.splitContraction

#print axioms QuantumNLS.Prop001RthirteenProduct.splitTrace_product_commutator

#print axioms QuantumNLS.Prop001RthirteenProduct.sourceRankCollision_product

#print axioms QuantumNLS.Prop001RthirteenProduct.insertRight_norm

#print axioms QuantumNLS.Prop001RthirteenProduct.contraction_norm

#print axioms QuantumNLS.Prop001RthirteenProduct.rankContraction

#print axioms QuantumNLS.Prop001RthirteenProduct.splitContraction_norm_le

#print axioms QuantumNLS.Prop001RthirteenProduct.rankContraction_norm_le

#print axioms QuantumNLS.Prop001RthirteenProduct.rankContraction_summable

#print axioms QuantumNLS.Prop001RthirteenProduct.collisionSeries_product_commutator
