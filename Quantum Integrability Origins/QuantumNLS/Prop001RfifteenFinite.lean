import QuantumNLS.Prop001RfifteenTransport

set_option linter.unusedSectionVars false

/-! Compatibility of successive partial traces and actual prefix commutators. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped InnerProductSpace BigOperators ENNReal
namespace QuantumNLS.Prop001RfifteenNestedTrace
open TraceClass TraceIdeal TensorCarrier PhysicalTensor PhysicalEnergyTrace RootOverlapCommutator
  Ext025B11TracePairing Ext025A12Trace Ext025A12Normal Ext025A12Tensor
  Ext025A12PartialTrace Ext025A12Collision Prop001 Prop001RfifteenTransport
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Lift a bounded observable on the first k tensor slots. -/
def prefixLift (k m : ℕ) (B : RankOperator H k) : RankOperator H (k+m) :=
  pull (splitIsometry k m) (ampliate ℂ _ _ B)

theorem splitTrace_finite (k m : ℕ) (T : RankOperator H (k+m)) (hT : IsTraceClass T) :
    IsTraceClass (splitTrace k m T hT) := (splitTrace_bound k m T hT).trans_lt hT

theorem reducedDensity_finite (N k : ℕ) (hk : k ≤ N) (z : HilbertTensorPower ℂ H N) :
    IsTraceClass (reducedDensityN N k hk z) := by
  rw [IsTraceClass,traceNorm_reducedDensityN]
  exact ENNReal.ofReal_lt_top

/-- Duality on the repository's completed tensor powers. -/
theorem splitTrace_duality (k m : ℕ) (T : RankOperator H (k+m))
    (hT : IsTraceClass T) (B : RankOperator H k) :
    tr (splitTrace k m T hT*B) = tr (T*prefixLift k m B) := by
  unfold splitTrace
  rw [partialTrace_duality]
  have hf : IsTraceClass (pull (splitIsometry k m).symm T) := by
    simpa only [IsTraceClass,traceNorm_pull] using hT
  rw [← tr_pull (splitIsometry k m) _ (finite_right _ _ hf),pull_mul,pull_pull_symm]
  rfl

/-- Two successive completed splits have the same elementary tensors. -/
theorem split_assoc_ptC {k m t : ℕ}
    (x : HilbertTensorPower ℂ H k) (b : Fin m → H) (c : Fin t → H) :
    (cIso (Nat.add_assoc k m t)
      ((splitIsometry (k + m) t).symm
        (htmul ((splitIsometry k m).symm (htmul x (ptC b))) (ptC c))) :
          HilbertTensorPower ℂ H (k + (m + t))) =
      (splitIsometry k (m + t)).symm
        (htmul x (ptC (Fin.append b c))) := by
  let F : HilbertTensorPower ℂ H k →L[ℂ]
      HilbertTensorPower ℂ H (k + (m + t)) :=
    (cIso (Nat.add_assoc k m t)).toLinearIsometry.toContinuousLinearMap.comp
      ((splitIsometry (k + m) t).symm.toLinearIsometry.toContinuousLinearMap.comp
        ((htL (ptC c)).comp
          ((splitIsometry k m).symm.toLinearIsometry.toContinuousLinearMap.comp
            (htL (ptC b)))))
  let G : HilbertTensorPower ℂ H k →L[ℂ]
      HilbertTensorPower ℂ H (k + (m + t)) :=
    (splitIsometry k (m + t)).symm.toLinearIsometry.toContinuousLinearMap.comp
      (htL (ptC (Fin.append b c)))
  have hFG := eq_of_eq_on_ptC F G (fun a => by
    simp only [F, G, ContinuousLinearMap.comp_apply, htL_apply,
      LinearIsometryEquiv.coe_toLinearIsometry,
      LinearIsometry.coe_toContinuousLinearMap]
    rw [split_symm_ptC, split_symm_ptC, split_symm_ptC, cIso_ptC]
    congr 1
    have hidx :
        (fun i : Fin (k + (m + t)) =>
          (Fin.append (Fin.append a b) c) (Fin.cast (Nat.add_assoc k m t).symm i)) =
          Fin.append a (Fin.append b c) := by
      funext i
      refine Fin.addCases (fun j : Fin k => ?_) (fun j : Fin (m + t) => ?_) i
      · have hi : Fin.cast (Nat.add_assoc k m t).symm (Fin.castAdd (m + t) j) =
            Fin.castAdd t (Fin.castAdd m j) := by
          apply Fin.ext
          simp
        rw [hi]
        simp [Fin.append]
      · refine Fin.addCases (fun j : Fin m => ?_) (fun j : Fin t => ?_) j
        · have hi : Fin.cast (Nat.add_assoc k m t).symm
              (Fin.natAdd k (Fin.castAdd t j)) = Fin.castAdd t (Fin.natAdd k j) := by
            apply Fin.ext
            simp
          rw [hi]
          simp [Fin.append]
        · have hi : Fin.cast (Nat.add_assoc k m t).symm
              (Fin.natAdd k (Fin.natAdd m j)) = Fin.natAdd (k + m) j := by
            apply Fin.ext
            simp
            omega
          rw [hi]
          simp [Fin.append]
    exact hidx)
  have h := congrArg (fun T : HilbertTensorPower ℂ H k →L[ℂ]
      HilbertTensorPower ℂ H (k + (m + t)) => T x) hFG
  simpa [F, G, ContinuousLinearMap.comp_apply, htL_apply, htR_apply] using h


/-- Lifting a prefix observable twice equals its direct lift. -/
theorem prefixLift_assoc (k m t : ℕ) (B : RankOperator H k) :
    pull (cIso (Nat.add_assoc k m t)) (prefixLift k (m+t) B) =
      prefixLift (k+m) t (prefixLift k m B) := by
  apply eq_of_eq_on_ptC
  intro f
  let a : Fin k → H := fun i => f (Fin.castAdd t (Fin.castAdd m i))
  let b : Fin m → H := fun i => f (Fin.castAdd t (Fin.natAdd k i))
  let c : Fin t → H := fun i => f (Fin.natAdd (k+m) i)
  have hf : f=Fin.append (Fin.append a b) c := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp [a,b]
    · simp [c]
  rw [hf]
  have hi : (fun i : Fin (k+(m+t)) =>
      Fin.append (Fin.append a b) c (Fin.cast (Nat.add_assoc k m t).symm i)) =
      Fin.append a (Fin.append b c) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have hj : Fin.cast (Nat.add_assoc k m t).symm (Fin.castAdd (m+t) j) =
          Fin.castAdd t (Fin.castAdd m j) := by apply Fin.ext; simp
      rw [hj]; simp
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · have hj : Fin.cast (Nat.add_assoc k m t).symm
            (Fin.natAdd k (Fin.castAdd t j)) = Fin.castAdd t (Fin.natAdd k j) := by
          apply Fin.ext; simp
        rw [hj]; simp
      · have hj : Fin.cast (Nat.add_assoc k m t).symm
            (Fin.natAdd k (Fin.natAdd m j)) = Fin.natAdd (k+m) j := by
          apply Fin.ext; simp; omega
        rw [hj]; simp
  simp only [prefixLift,pull_apply]
  rw [cIso_ptC,hi,splitIsometry_ptprod_append,splitIsometry_ptprod_append,
    ampliate_apply,htmap_htmul,ContinuousLinearMap.id_apply]
  simp only [ampliate_apply,htmap_htmul,ContinuousLinearMap.id_apply,pull_apply,
    splitIsometry_ptprod_append]
  apply (cIso (Nat.add_assoc k m t)).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact (split_assoc_ptC (B (ptC a)) b c).symm

/-- Transitivity of the constructed general partial trace. -/
theorem splitTrace_trans (k m t : ℕ) (T : RankOperator H ((k+m)+t))
    (hT : IsTraceClass T) :
    splitTrace k m (splitTrace (k+m) t T hT)
      (splitTrace_finite (k+m) t T hT) =
    splitTrace k (m+t) (pull (cIso (Nat.add_assoc k m t)).symm T)
      (by simpa only [IsTraceClass,traceNorm_pull] using hT) := by
  apply tr_separates
  intro B
  rw [splitTrace_duality,splitTrace_duality,splitTrace_duality]
  have hf : IsTraceClass (pull (cIso (Nat.add_assoc k m t)).symm T) := by
    simpa only [IsTraceClass,traceNorm_pull] using hT
  rw [← tr_pull (cIso (Nat.add_assoc k m t)) _ (finite_right _ _ hf),
    pull_mul,pull_pull_symm,prefixLift_assoc]

/-- Prefix commutators reduce to commutators on the actual reduced state. -/
theorem splitTrace_prefix_commutator (k m : ℕ) (B : RankOperator H k)
    (T : RankOperator H (k+m)) (hT : IsTraceClass T) :
    splitTrace k m (prefixLift k m B*T-T*prefixLift k m B)
      (commutator_finite _ T hT) =
        B*splitTrace k m T hT-splitTrace k m T hT*B := by
  unfold splitTrace
  simp only [pull_sub,pull_mul,prefixLift,pull_symm_pull]
  exact partialTrace_commutator B _ _

/-- Actual finite marginals are independent of an arithmetic carrier cast. -/
theorem reducedDensityN_cast {N M : ℕ} (h : N=M) (k : ℕ) (hk : k ≤ N)
    (z : HilbertTensorPower ℂ H N) :
    reducedDensityN M k (by omega) (cIso h z) = reducedDensityN N k hk z := by
  cases h
  rfl

/-- Successive partial traces of an actual pure-state marginal equal the
actual smaller marginal, including all completed-split transports. -/
theorem reducedDensityN_trans (k m t : ℕ) (z : HilbertTensorPower ℂ H ((k+m)+t)) :
    splitTrace k m (reducedDensityN ((k+m)+t) (k+m) (by omega) z)
      (reducedDensity_finite _ _ (by omega) z) =
    reducedDensityN ((k+m)+t) k (by omega) z := by
  have h := splitTrace_trans k m t (InnerProductSpace.rankOne ℂ z z) (rankOne_finite z z)
  simp only [pull_rankOne,LinearIsometryEquiv.symm_symm,splitTrace_rankOne] at h
  exact h.trans (reducedDensityN_cast (Nat.add_assoc k m t) k (by omega) z)


/-- Exact lower-rank reduction of a prefix-supported placed commutator.
The lower-rank state is constructed by the further partial trace. -/
theorem nested_commutator_reduction (k m t : ℕ) (B : RankOperator H (k+m))
    (T : RankOperator H ((k+m)+t)) (hT : IsTraceClass T) :
    splitTrace k (m+t) (pull (cIso (Nat.add_assoc k m t)).symm
      (prefixLift (k+m) t B*T-T*prefixLift (k+m) t B))
      (by simpa only [IsTraceClass,traceNorm_pull] using
        commutator_finite (prefixLift (k+m) t B) T hT) =
    splitTrace k m (B*splitTrace (k+m) t T hT-splitTrace (k+m) t T hT*B)
      (commutator_finite B _ (splitTrace_finite (k+m) t T hT)) := by
  have h := splitTrace_trans k m t
    (prefixLift (k+m) t B*T-T*prefixLift (k+m) t B)
    (commutator_finite _ T hT)
  have hc := splitTrace_prefix_commutator (k+m) t B T hT
  simpa only [hc] using h.symm

end QuantumNLS.Prop001RfifteenNestedTrace


/-! Spectator permutation covariance of the actual general partial trace. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped InnerProductSpace BigOperators ENNReal
namespace QuantumNLS.Prop001RfifteenSymmetry
open TraceClass TraceIdeal TensorCarrier TensorPlacements PhysicalEnergyTrace
  Ext025B11TracePairing Ext025A12Trace Ext025A12Normal Ext025A12Tensor
  Ext025A12PartialTrace Ext025A12Collision Prop001 Prop001RfifteenTransport
  Prop001RfifteenNestedTrace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A spectator permutation commutes with every bounded visible observable. -/
theorem prefixLift_spectator_commute (k m : ℕ) (ρ : Equiv.Perm (Fin m))
    (B : RankOperator H k) :
    Commute (prefixLift k m B)
      (permRep ℂ H (k+m) (blockPerm (1 : Equiv.Perm (Fin k)) ρ) : RankOperator H (k+m)) := by
  let V : RankOperator H m := permRep ℂ H m ρ
  have hs (z : HilbertTensorPower ℂ H (k+m)) :
      splitIsometry k m ((permRep ℂ H (k+m)
        (blockPerm (1 : Equiv.Perm (Fin k)) ρ) : RankOperator H (k+m)) z) =
      htmap (ContinuousLinearMap.id ℂ _) V (splitIsometry k m z) := by
    simpa [V,permRep_apply,ContinuousLinearMap.one_def] using
      splitIsometry_blockPerm_apply (1 : Equiv.Perm (Fin k)) ρ z
  ext z
  apply (splitIsometry k m).injective
  simp only [mul_apply_eq_comp,prefixLift,pull_apply,
    LinearIsometryEquiv.apply_symm_apply,hs]
  exact congrArg (fun F : HilbertTensor ℂ (HilbertTensorPower ℂ H k)
    (HilbertTensorPower ℂ H m) →L[ℂ] _ => F (splitIsometry k m z))
      (disjoint_htmap_commute B V).eq

/-- Changing only traced slot labels leaves every partial trace unchanged. -/
theorem splitTrace_spectator_invariant (k m : ℕ) (ρ : Equiv.Perm (Fin m))
    (T : RankOperator H (k+m)) (hT : IsTraceClass T) :
    splitTrace k m (pull (permHilbertIsometry
      (blockPerm (1 : Equiv.Perm (Fin k)) ρ)) T)
      (by simpa only [IsTraceClass,traceNorm_pull] using hT) = splitTrace k m T hT := by
  apply tr_separates
  intro B
  rw [splitTrace_duality,splitTrace_duality]
  let e := permHilbertIsometry (𝕜 := ℂ) (E := H)
    (blockPerm (1 : Equiv.Perm (Fin k)) ρ)
  have hc : pull e (prefixLift k m B) = prefixLift k m B := by
    ext z
    apply e.injective
    simp only [pull_apply,LinearIsometryEquiv.apply_symm_apply]
    exact (congrArg (fun F : RankOperator H (k+m) => F z)
      (prefixLift_spectator_commute k m ρ B).eq)
  have hf : IsTraceClass (T*prefixLift k m B) := finite_right _ T hT
  have he := tr_pull e (T*prefixLift k m B) hf
  rw [pull_mul,hc] at he
  exact he

/-- Every vector in the actual symmetric sector is fixed by every slot unitary. -/
theorem symmetric_vector_perm (N : ℕ) (σ : Equiv.Perm (Fin N))
    (ψ : SymSector ℂ H N) : permHilbertIsometry σ (ψ : HilbertTensorPower ℂ H N) = ψ :=
  ψ.property σ

/-- The actual symmetric pure density is invariant under slot conjugation. -/
theorem symmetric_density_pull (N : ℕ) (σ : Equiv.Perm (Fin N))
    (ψ : SymSector ℂ H N) :
    pull (permHilbertIsometry σ) (InnerProductSpace.rankOne ℂ
      (ψ : HilbertTensorPower ℂ H N) (ψ : HilbertTensorPower ℂ H N)) = InnerProductSpace.rankOne ℂ
      (ψ : HilbertTensorPower ℂ H N) (ψ : HilbertTensorPower ℂ H N) := by
  rw [pull_rankOne]
  have he : (permHilbertIsometry σ).symm (ψ : HilbertTensorPower ℂ H N) = ψ := by
    apply (permHilbertIsometry σ).injective
    rw [LinearIsometryEquiv.apply_symm_apply,symmetric_vector_perm]
  rw [he]

/-- The traced commutator is unchanged when its placement is relabeled only
in the spectator block of an actual symmetric state. -/
theorem symmetric_commutator_spectator (k m : ℕ) (ρ : Equiv.Perm (Fin m))
    (B : RankOperator H (k+m)) (ψ : SymSector ℂ H (k+m)) :
    let P := InnerProductSpace.rankOne ℂ (ψ : HilbertTensorPower ℂ H (k+m)) (ψ : HilbertTensorPower ℂ H (k+m))
    let e := permHilbertIsometry (𝕜 := ℂ) (E := H)
      (blockPerm (1 : Equiv.Perm (Fin k)) ρ)
    splitTrace k m (pull e B*P-P*pull e B) (commutator_finite _ P (rankOne_finite _ _)) =
      splitTrace k m (B*P-P*B) (commutator_finite _ P (rankOne_finite _ _)) := by
  dsimp only
  have he := splitTrace_spectator_invariant k m ρ
    (B*InnerProductSpace.rankOne ℂ (ψ : HilbertTensorPower ℂ H (k+m)) (ψ : HilbertTensorPower ℂ H (k+m))-
      InnerProductSpace.rankOne ℂ (ψ : HilbertTensorPower ℂ H (k+m)) (ψ : HilbertTensorPower ℂ H (k+m))*B)
    (commutator_finite _ _ (rankOne_finite _ _))
  simpa only [pull_sub,pull_mul,symmetric_density_pull] using he

end QuantumNLS.Prop001RfifteenSymmetry


/-! Trace-norm derivative of the actual evolved finite marginals. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Filter Topology
open scoped InnerProductSpace BigOperators ENNReal
namespace QuantumNLS.Prop001RfifteenDerivative
open TraceClass TraceIdeal TensorCarrier TensorPlacements PlacementGrouping PhysicalTensor
  PhysicalEnergyTrace Ext025A12Trace Ext025A12Normal Ext025A12PartialTrace Ext025A12Collision
  Prop001 Prop001RfourteenRegrouping Prop001RfourteenTraceRegrouping
  Prop001RfourteenIdentification Prop001RfifteenTransport
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Adjoint of an actual raw subset placement. -/
theorem rawSubsetPlacement_adjoint (N r : ℕ) (hr : r ≤ N)
    (S : PlacementSubset r (N-r)) (A : SymSector ℂ H r →L[ℂ] SymSector ℂ H r) :
    (rawSubsetPlacement N r hr S A).adjoint = rawSubsetPlacement N r hr S A.adjoint := by
  unfold rawSubsetPlacement
  have hc {m n : ℕ} (h : m=n) (T : RankOperator H m) :
      (PlacementFusion.castTensorOperator h T).adjoint =
        PlacementFusion.castTensorOperator h T.adjoint := by cases h; rfl
  rw [hc]
  unfold subsetPlacement permutedPlacement
  simp only [ContinuousLinearMap.adjoint_comp,perm_adjoint,
    GenericUAdjoint.adjoint_firstPlacement,inv_inv,ContinuousLinearMap.comp_assoc]

/-- Self-adjointness on the full tensor carrier, prior to sector restriction. -/
theorem rawGenerator_selfAdjoint (A : Interactions H)
    (hA : ∀ n, IsSelfAdjoint (A n)) (N : ℕ) : IsSelfAdjoint (rawGenerator A N) := by
  rw [rawGenerator_subset_expansion]
  apply isSelfAdjoint_sum
  intro n _
  apply IsSelfAdjoint.smul (by simp [isSelfAdjoint_iff])
  unfold rawSubsetPlacementSum
  apply isSelfAdjoint_sum
  intro S _
  change (rawSubsetPlacement N (n.val+1) _ S (A n.val)).adjoint = _
  rw [rawSubsetPlacement_adjoint,show (A n.val).adjoint=A n.val from hA n.val]

/-- The literal ambient vector curve underlying every finite marginal. -/
def quantumVector (A : Interactions H) (N : ℕ) (ψ : SymSector ℂ H N) (t : ℝ) :
    HilbertTensorPower ℂ H N := quantumEvolution A N t ψ

theorem quantumVector_derivative (A : Interactions H) (N : ℕ)
    (ψ : SymSector ℂ H N) (t : ℝ) :
    HasDerivAt (quantumVector A N ψ)
      ((-Complex.I) • rawGenerator A N (quantumVector A N ψ t)) t := by
  have h := ((SymSector ℂ H N).subtypeL.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (quantumEvolution_derivative A N ψ t)
  have hc : ((SymSector ℂ H N).subtypeL.restrictScalars ℝ)
      ((-Complex.I) • generator A N (quantumEvolution A N t ψ)) =
      (-Complex.I) • rawGenerator A N (quantumVector A N ψ t) := by
    change (-Complex.I) • ((generator A N (quantumEvolution A N t ψ)) : HilbertTensorPower ℂ H N) = _
    simp only [quantumVector,rawGenerator_restrict]
  rw [hc] at h
  exact h


/-- Full-density trace-norm differentiation on the actual finite evolution. -/
theorem quantumDensity_derivative (A : Interactions H)
    (hA : ∀ n, IsSelfAdjoint (A n)) (N : ℕ) (ψ : SymSector ℂ H N) (t : ℝ) :
    let z := quantumVector A N ψ t
    Tendsto (fun s => traceNorm
      (slope (fun r => InnerProductSpace.rankOne ℂ (quantumVector A N ψ r)
        (quantumVector A N ψ r)) t s -
        (-Complex.I) • (rawGenerator A N*InnerProductSpace.rankOne ℂ z z-
          InnerProductSpace.rankOne ℂ z z*rawGenerator A N))) (𝓝[≠] t) (𝓝 0) := by
  dsimp only
  rw [← projector_commutator _ (rawGenerator_selfAdjoint A hA N)]
  exact Prop001RthirteenDerivative.projector_trace_derivative _ _ t
    (quantumVector_derivative A N ψ t)

/-- The actual marginal is the constructed general partial trace of the
actual full evolved density. -/
theorem marginal_eq_splitTrace (A : Interactions H) (k m : ℕ)
    (ψ : SymSector ℂ H (k+m)) (t : ℝ) :
    marginal A (k+m) k (by omega) t ψ =
      splitTrace k m (InnerProductSpace.rankOne ℂ (quantumVector A (k+m) ψ t)
        (quantumVector A (k+m) ψ t)) (rankOne_finite _ _) := by
  rw [splitTrace_rankOne]
  rfl

/-- Differentiation passes through the contractive actual partial trace. -/
theorem marginal_trace_derivative (A : Interactions H)
    (hA : ∀ n, IsSelfAdjoint (A n)) (k m : ℕ)
    (ψ : SymSector ℂ H (k+m)) (t : ℝ) :
    let z := quantumVector A (k+m) ψ t
    let P := InnerProductSpace.rankOne ℂ z z
    Tendsto (fun s => traceNorm
      (slope (fun r => marginal A (k+m) k (by omega) r ψ) t s -
        (-Complex.I) • splitTrace k m (rawGenerator A (k+m)*P-P*rawGenerator A (k+m))
          (commutator_finite _ P (rankOne_finite _ _)))) (𝓝[≠] t) (𝓝 0) := by
  dsimp only
  let P : ℝ → traceIdeal (HilbertTensorPower ℂ H (k+m)) := fun r =>
    ⟨InnerProductSpace.rankOne ℂ (quantumVector A (k+m) ψ r)
      (quantumVector A (k+m) ψ r),rankOne_finite _ _⟩
  let C := commutatorIdeal (rawGenerator A (k+m)) (P t)
  let E : ℝ → traceIdeal (HilbertTensorPower ℂ H (k+m)) :=
    fun s => (s-t)⁻¹ • (P s-P t)-(-Complex.I) • C
  have he (s : ℝ) :
      (splitMap k m (E s)).val =
      slope (fun r => marginal A (k+m) k (by omega) r ψ) t s -
        (-Complex.I) • splitTrace k m
          (rawGenerator A (k+m)*(P t).val-(P t).val*rawGenerator A (k+m))
          (commutator_finite _ _ (P t).property) := by
    simp only [E,map_sub,LinearMap.map_smul_of_tower,Submodule.coe_sub,
      Submodule.coe_smul_of_tower,splitMap_val,C,commutatorIdeal,slope_def_module]
    congr 1
    simp only [P,← marginal_eq_splitTrace]
  have h := quantumDensity_derivative A hA (k+m) ψ t
  change Tendsto (fun s => traceNorm (E s).val) (𝓝[≠] t) (𝓝 0) at h
  have hh : Tendsto (fun s => traceNorm (splitMap k m (E s)).val) (𝓝[≠] t) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
      (fun _ => bot_le) (fun s => splitTrace_bound k m (E s).val (E s).property)
  exact hh.congr' (.of_forall (fun s => congrArg traceNorm (he s)))


end QuantumNLS.Prop001RfifteenDerivative


/-! The actual finite one-overlap coefficient correction and its norm bound.
Its identification with the grouped finite Hamiltonian is a separate step. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped InnerProductSpace BigOperators ENNReal
namespace QuantumNLS.Prop001RfifteenRemainder
open TraceClass TensorCarrier TensorPlacements PlacementGrouping PlacementFusion
  Ext025A12Collision Prop001 Prop001RthirteenSeries
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The coefficient deficit applied to actual finite marginals. -/
def oneOverlapCorrection (D : ClassicalData H) (N k : ℕ)
    (ψ : SymSector ℂ H N) (hψ : ‖ψ‖ = 1) (t : ℝ) : RankOperator H (k+1) :=
  ∑ n ∈ Finset.range (N-(k+1)+1), ((alpha N (k+1) n-1 : ℝ) : ℂ) •
    sourceRankCollision k n (D.A n) (extendedMarginal D.A N ((k+1)+n) t ψ)
      (extendedMarginal_isTraceClass D.A D.selfAdjoint N t ψ hψ _)

/-- The printed 4 k²/N part of the budget, on the actual collision
operators and actual extended finite marginals. -/
theorem oneOverlapCorrection_bound (D : ClassicalData H) (N k : ℕ)
    (hN : 0 < N) (hk : k+1 ≤ N)
    (ψ : SymSector ℂ H N) (hψ : ‖ψ‖ = 1) (t : ℝ) :
    traceNorm (oneOverlapCorrection D N k ψ hψ t) ≤
      ENNReal.ofReal (4*((k+1 : ℕ) : ℝ)^2/N*
        ∑' n, ((n+1 : ℕ) : ℝ)^3*‖D.A n‖) := by
  let b : ℕ → ℝ := fun n => 2*(n+1 : ℕ)*(k+1 : ℕ)*(1-alpha N (k+1) n)*‖D.A n‖
  have hb (n : ℕ) : 0 ≤ b n := by
    dsimp only [b]
    exact mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr (alpha_le_one _ _ _))) (ContinuousLinearMap.opNorm_nonneg (D.A n))
  have hn (n : ℕ) :
      traceNorm (((alpha N (k+1) n-1 : ℝ) : ℂ) •
        sourceRankCollision k n (D.A n) (extendedMarginal D.A N ((k+1)+n) t ψ)
          (extendedMarginal_isTraceClass D.A D.selfAdjoint N t ψ hψ _)) ≤
        ENNReal.ofReal (b n) := by
    rw [traceNorm_smul]
    have he : ‖((alpha N (k+1) n-1 : ℝ) : ℂ)‖ = 1-alpha N (k+1) n := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr (alpha_le_one _ _ _))]
      ring
    rw [he]
    have hc := source_collision_bound D.A (fun j => extendedMarginal D.A N j t ψ)
      (extendedMarginal_isTraceClass D.A D.selfAdjoint N t ψ hψ) 1 (by norm_num)
      (fun j => by simpa only [ENNReal.ofReal_one] using
        extendedMarginal_traceNorm_le D.A D.selfAdjoint N t ψ hψ j) k n
    refine (mul_le_mul_of_nonneg_left hc (by positivity)).trans_eq ?_
    rw [← ENNReal.ofReal_mul (sub_nonneg.mpr (alpha_le_one _ _ _))]
    congr 1
    dsimp only [b]
    ring
  calc
    traceNorm (oneOverlapCorrection D N k ψ hψ t) ≤
        ∑ n ∈ Finset.range (N-(k+1)+1), traceNorm
          (((alpha N (k+1) n-1 : ℝ) : ℂ) • sourceRankCollision k n (D.A n)
            (extendedMarginal D.A N ((k+1)+n) t ψ)
            (extendedMarginal_isTraceClass D.A D.selfAdjoint N t ψ hψ _)) :=
      Fidelity.traceNorm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range (N-(k+1)+1), ENNReal.ofReal (b n) :=
      Finset.sum_le_sum (fun n _ => hn n)
    _ = ENNReal.ofReal (∑ n ∈ Finset.range (N-(k+1)+1), b n) :=
      (ENNReal.ofReal_sum_of_nonneg (fun n _ => hb n)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (oneOverlap_sum_bound D.A N (k+1) hN (by omega) hk D.cubic)

/-- A literal subset placement indexed by the subset in Fin N. -/
def setPlacement (N r : ℕ) (hr : r ≤ N) (Q : Finset (Fin N))
    (A : SymSector ℂ H r →L[ℂ] SymSector ℂ H r) : RankOperator H N := by
  classical
  exact if hQ : Q.card=r then rawSubsetPlacement N r hr
    ⟨Q.map (finCongr (Nat.add_sub_of_le hr).symm).toEmbedding,by simpa using hQ⟩ A else 0

theorem setPlacement_norm (N r : ℕ) (hr : r ≤ N) (Q : Finset (Fin N))
    (A : SymSector ℂ H r →L[ℂ] SymSector ℂ H r) : ‖setPlacement N r hr Q A‖ ≤ ‖A‖ := by
  classical
  unfold setPlacement
  split_ifs
  · rw [rawSubsetPlacement,norm_castTensorOperator,subsetPlacement]
    exact norm_permutedPlacement_le _ A
  · simpa only [norm_zero] using ContinuousLinearMap.opNorm_nonneg A

/-- Actual multi-overlap rank contribution with the source factorial weight. -/
def multipleRank (k m r : ℕ) (hr : r ≤ k+m) (P : Finset (Fin (k+m)))
    (A : SymSector ℂ H r →L[ℂ] SymSector ℂ H r)
    (T : RankOperator H (k+m)) (hT : IsTraceClass T) : RankOperator H k :=
  (((r.factorial : ℝ)*(k+m)/(k+m : ℝ)^r : ℝ) : ℂ) •
    ∑ Q ∈ multipleOverlapEvent P r, splitTrace k m
      (setPlacement (k+m) r hr Q A*T-T*setPlacement (k+m) r hr Q A)
      (commutator_finite _ T hT)

/-- The two-overlap event bound now controls an actual traced operator sum. -/
theorem multipleRank_bound (k m r : ℕ) (hr : r ≤ k+m) (P : Finset (Fin (k+m)))
    (hP : P.card=k) (A : SymSector ℂ H r →L[ℂ] SymSector ℂ H r)
    (T : RankOperator H (k+m)) (hT : IsTraceClass T) (hTN : traceNorm T ≤ 1) :
    traceNorm (multipleRank k m r hr P A T hT) ≤
      ENNReal.ofReal (2*(k+m)*theta (k+m) r*‖A‖*multipleOverlapProbability (k+m) k r) := by
  classical
  let c : ℝ := (r.factorial : ℝ)*(k+m)/(k+m : ℝ)^r
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hn (Q : Finset (Fin (k+m))) : traceNorm (splitTrace k m
      (setPlacement (k+m) r hr Q A*T-T*setPlacement (k+m) r hr Q A)
      (commutator_finite _ T hT)) ≤ 2*ENNReal.ofReal ‖A‖ := by
    refine (collision_commutator_bound k m _ T hT).trans ?_
    calc
      _ ≤ 2*ENNReal.ofReal ‖A‖*traceNorm T := by
        gcongr
        exact setPlacement_norm _ _ _ _ _
      _ ≤ 2*ENNReal.ofReal ‖A‖*1 := mul_le_mul_of_nonneg_left hTN (by positivity)
      _ = _ := by rw [mul_one]
  have hs : traceNorm (∑ Q ∈ multipleOverlapEvent P r, splitTrace k m
      (setPlacement (k+m) r hr Q A*T-T*setPlacement (k+m) r hr Q A)
      (commutator_finite _ T hT)) ≤
      ENNReal.ofReal (2*((multipleOverlapEvent P r).card : ℝ)*‖A‖) := by
    calc
      _ ≤ ∑ Q ∈ multipleOverlapEvent P r, traceNorm (splitTrace k m
          (setPlacement (k+m) r hr Q A*T-T*setPlacement (k+m) r hr Q A)
          (commutator_finite _ T hT)) := Fidelity.traceNorm_sum_le _ _
      _ ≤ ∑ _Q ∈ multipleOverlapEvent P r, 2*ENNReal.ofReal ‖A‖ :=
        Finset.sum_le_sum (fun Q _ => hn Q)
      _ = _ := by
        simp only [Finset.sum_const,nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (by positivity)]
        simp only [ENNReal.ofReal_ofNat,ENNReal.ofReal_natCast]
        ring
  unfold multipleRank
  rw [traceNorm_smul]
  change ENNReal.ofReal ‖(c : ℂ)‖ * _ ≤ _
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc]
  refine (mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq ?_
  rw [← ENNReal.ofReal_mul hc]
  congr 1
  rw [card_multipleOverlapEvent P hP]
  dsimp only [c,multipleOverlapProbability]
  have hco := generator_subset_coefficient (k+m) r hr
  push_cast at hco
  rw [← hco]
  ring

/-- The actual sum of all multi-overlap rank contributions. -/
def multipleRemainder (D : ClassicalData H) (k m : ℕ) (P : Finset (Fin (k+m)))
    (T : RankOperator H (k+m)) (hT : IsTraceClass T) : RankOperator H k :=
  ∑ n : Fin (k+m), multipleRank k m (n.val+1) (Nat.succ_le_of_lt n.isLt) P (D.A n.val) T hT

theorem multipleRemainder_bound (D : ClassicalData H) (k m : ℕ) (hN : 2 ≤ k+m)
    (P : Finset (Fin (k+m))) (hP : P.card=k)
    (T : RankOperator H (k+m)) (hT : IsTraceClass T) (hTN : traceNorm T ≤ 1) :
    traceNorm (multipleRemainder D k m P T hT) ≤
      ENNReal.ofReal (2*(k : ℝ)^2/(k+m)*∑' n, ((n+1 : ℕ) : ℝ)^3*‖D.A n‖) := by
  classical
  calc
    _ ≤ ∑ n : Fin (k+m), traceNorm
        (multipleRank k m (n.val+1) (Nat.succ_le_of_lt n.isLt) P (D.A n.val) T hT) :=
      Fidelity.traceNorm_sum_le _ _
    _ ≤ ∑ n : Fin (k+m), ENNReal.ofReal
        (2*(k+m)*theta (k+m) (n.val+1)*‖D.A n.val‖*
          multipleOverlapProbability (k+m) k (n.val+1)) :=
      Finset.sum_le_sum (fun n _ => multipleRank_bound k m (n.val+1) _ P hP _ T hT hTN)
    _ = ENNReal.ofReal (∑ n : Fin (k+m),
        2*(k+m)*theta (k+m) (n.val+1)*‖D.A n.val‖*
          multipleOverlapProbability (k+m) k (n.val+1)) :=
      (ENNReal.ofReal_sum_of_nonneg (fun n _ => by
        have ht := theta_nonneg (k+m) (n.val+1)
        have hp : 0 ≤ multipleOverlapProbability (k+m) k (n.val+1) := by
          unfold multipleOverlapProbability; positivity
        positivity)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      simpa only [Nat.cast_add] using multipleOverlap_sum_bound D.A (k+m) k hN (by omega) D.cubic)

/-- Concrete sum of the two finite correction operators. Its norm is
proved below; the full hierarchy equality still requires subset identification. -/
def finiteCorrection (D : ClassicalData H) (k m : ℕ)
    (ψ : SymSector ℂ H ((k+1)+m)) (hψ : ‖ψ‖ = 1) (t : ℝ) : RankOperator H (k+1) :=
  oneOverlapCorrection D ((k+1)+m) k ψ hψ t+
    multipleRemainder D (k+1) m (firstPositions (p := k+1) (q := m))
      (InnerProductSpace.rankOne ℂ (Prop001RfifteenDerivative.quantumVector D.A ((k+1)+m) ψ t)
        (Prop001RfifteenDerivative.quantumVector D.A ((k+1)+m) ψ t))
      (Prop001RfifteenTransport.rankOne_finite _ _)

/-- The exact C0 k²/N norm budget on the concrete finite correction,
with no norm or hierarchy equation supplied as a premise. -/
theorem finiteCorrection_bound (D : ClassicalData H) (k m : ℕ) (hN : 2 ≤ (k+1)+m)
    (ψ : SymSector ℂ H ((k+1)+m)) (hψ : ‖ψ‖ = 1) (t : ℝ) :
    traceNorm (finiteCorrection D k m ψ hψ t) ≤
      ENNReal.ofReal (errorSum D.A*((k+1 : ℕ) : ℝ)^2/((k+1)+m)) := by
  have hn : ‖Prop001RfifteenDerivative.quantumVector D.A ((k+1)+m) ψ t‖=1 :=
    (quantumEvolution_norm D.A D.selfAdjoint ((k+1)+m) t ψ).trans hψ
  have hp : traceNorm (InnerProductSpace.rankOne ℂ
      (Prop001RfifteenDerivative.quantumVector D.A ((k+1)+m) ψ t)
      (Prop001RfifteenDerivative.quantumVector D.A ((k+1)+m) ψ t)) ≤ 1 := by
    simpa only [hn,one_mul,ENNReal.ofReal_one] using Fidelity.traceNorm_rankOne_le
      (Prop001RfifteenDerivative.quantumVector D.A ((k+1)+m) ψ t)
      (Prop001RfifteenDerivative.quantumVector D.A ((k+1)+m) ψ t)
  have h1 := oneOverlapCorrection_bound D ((k+1)+m) k (by omega) (by omega) ψ hψ t
  have h2 := multipleRemainder_bound D (k+1) m hN
    (firstPositions (p := k+1) (q := m)) (card_firstPositions (k+1) m) _
    (Prop001RfifteenTransport.rankOne_finite _ _) hp
  refine (traceNorm_add_le _ _).trans ((add_le_add h1 h2).trans_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  unfold errorSum
  push_cast
  ring

end QuantumNLS.Prop001RfifteenRemainder

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001Rfifteen" then
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
  Lean.logInfo m!"Prop001RfifteenFinite audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."


#print axioms QuantumNLS.Prop001RfifteenNestedTrace.prefixLift
#print axioms QuantumNLS.Prop001RfifteenNestedTrace.splitTrace_duality
#print axioms QuantumNLS.Prop001RfifteenNestedTrace.split_assoc_ptC
#print axioms QuantumNLS.Prop001RfifteenNestedTrace.prefixLift_assoc
#print axioms QuantumNLS.Prop001RfifteenNestedTrace.splitTrace_trans
#print axioms QuantumNLS.Prop001RfifteenNestedTrace.splitTrace_prefix_commutator
#print axioms QuantumNLS.Prop001RfifteenNestedTrace.reducedDensityN_cast
#print axioms QuantumNLS.Prop001RfifteenNestedTrace.reducedDensityN_trans
#print axioms QuantumNLS.Prop001RfifteenNestedTrace.nested_commutator_reduction
#print axioms QuantumNLS.Prop001RfifteenSymmetry.prefixLift_spectator_commute
#print axioms QuantumNLS.Prop001RfifteenSymmetry.splitTrace_spectator_invariant
#print axioms QuantumNLS.Prop001RfifteenSymmetry.symmetric_vector_perm
#print axioms QuantumNLS.Prop001RfifteenSymmetry.symmetric_density_pull
#print axioms QuantumNLS.Prop001RfifteenSymmetry.symmetric_commutator_spectator
#print axioms QuantumNLS.Prop001RfifteenDerivative.rawSubsetPlacement_adjoint
#print axioms QuantumNLS.Prop001RfifteenDerivative.rawGenerator_selfAdjoint
#print axioms QuantumNLS.Prop001RfifteenDerivative.quantumVector
#print axioms QuantumNLS.Prop001RfifteenDerivative.quantumVector_derivative
#print axioms QuantumNLS.Prop001RfifteenDerivative.quantumDensity_derivative
#print axioms QuantumNLS.Prop001RfifteenDerivative.marginal_eq_splitTrace
#print axioms QuantumNLS.Prop001RfifteenDerivative.marginal_trace_derivative

#print axioms QuantumNLS.Prop001RfifteenRemainder.oneOverlapCorrection
#print axioms QuantumNLS.Prop001RfifteenRemainder.oneOverlapCorrection_bound

#print axioms QuantumNLS.Prop001RfifteenRemainder.setPlacement
#print axioms QuantumNLS.Prop001RfifteenRemainder.setPlacement_norm
#print axioms QuantumNLS.Prop001RfifteenRemainder.multipleRank
#print axioms QuantumNLS.Prop001RfifteenRemainder.multipleRank_bound
#print axioms QuantumNLS.Prop001RfifteenRemainder.multipleRemainder
#print axioms QuantumNLS.Prop001RfifteenRemainder.multipleRemainder_bound

#print axioms QuantumNLS.Prop001RfifteenRemainder.finiteCorrection
#print axioms QuantumNLS.Prop001RfifteenRemainder.finiteCorrection_bound

#print axioms QuantumNLS.Prop001RfifteenNestedTrace.splitTrace_finite
#print axioms QuantumNLS.Prop001RfifteenNestedTrace.reducedDensity_finite
