import QuantumNLS.Prop001RsixteenPlacement
import QuantumNLS.Prop001RsixteenCounting

/-! Actual symmetric densities remove the spectator labels of placements. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
open scoped InnerProductSpace BigOperators ENNReal
namespace QuantumNLS.Prop001RsixteenSpectator
open TraceClass TraceIdeal TensorCarrier TensorPlacements PlacementFusion PlacementGrouping
  PlacementOverlap PlacementUnionReindex PlacementFiberTransport PlacementFiberOperator
  PhysicalEnergyTrace RootOverlapCommutator Ext025A12Trace Ext025A12Normal
  Ext025A12PartialTrace Ext025A12Collision Prop001 Prop001RfifteenTransport
  Prop001RfifteenNestedTrace Prop001RfifteenSymmetry Prop001RfifteenRemainder
  Prop001RsixteenCounting
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Recasting the literal chosen set yields its original source placement. -/
theorem setPlacement_eq_source (N r : ℕ) (hr : r ≤ N) (Q : Finset (Fin N))
    (hQ : Q.card=r) (A : SymSector ℂ H r →L[ℂ] SymSector ℂ H r) :
    setPlacement N r hr Q A = rawSubsetPlacement N r hr (sourcePlacementOfSlots hr Q hQ) A := by
  simpa only [slots_sourcePlacementOfSlots] using
    setPlacement_slots N r hr (sourcePlacementOfSlots hr Q hQ) A

/-- The inverse of the actual permutation isometry is the inverse permutation. -/
theorem permHilbertIsometry_symm {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    (permHilbertIsometry (𝕜 := ℂ) (E := H) σ).symm = permHilbertIsometry σ⁻¹ := by
  ext x
  apply (permHilbertIsometry σ).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  simpa only [inv_inv,permRep_apply] using (permRep_cancel σ⁻¹ x).symm

/-- Relabeling an actual literal subset conjugates its actual placed operator. -/
theorem setPlacement_covariance (N r : ℕ) (hr : r ≤ N) (Q : Finset (Fin N))
    (hQ : Q.card=r) (σ : Equiv.Perm (Fin N))
    (A : SymSector ℂ H r →L[ℂ] SymSector ℂ H r) :
    pull (permHilbertIsometry σ).symm (setPlacement N r hr Q A) =
      setPlacement N r hr (Q.map σ.toEmbedding) A := by
  rw [setPlacement_eq_source N r hr Q hQ,
    setPlacement_eq_source N r hr (Q.map σ.toEmbedding)
      (by simpa only [Finset.card_map] using hQ),sourcePlacementOfSlots_relabel]
  unfold rawSubsetPlacement
  ext x
  simp only [pull_apply,permHilbertIsometry_symm]
  exact congrArg (fun F : RankOperator H N => F x)
    (castSubsetPlacement_conjugate (Nat.add_sub_of_le hr) σ (sourcePlacementOfSlots hr Q hQ) A)

/-- The original actual placed commutators have equal partial traces under
spectator relabeling, on actual symmetric pure states. -/
theorem setPlacement_spectator_invariant (k m r : ℕ) (hr : r ≤ k+m)
    (Q : Finset (Fin (k+m))) (hQ : Q.card=r) (ρ : Equiv.Perm (Fin m))
    (A : SymSector ℂ H r →L[ℂ] SymSector ℂ H r)
    (ψ : SymSector ℂ H (k+m)) :
    let P := InnerProductSpace.rankOne ℂ (ψ : HilbertTensorPower ℂ H (k+m))
      (ψ : HilbertTensorPower ℂ H (k+m))
    splitTrace k m
      (setPlacement (k+m) r hr (Q.map (blockPerm (1 : Equiv.Perm (Fin k)) ρ).toEmbedding) A*P-
        P*setPlacement (k+m) r hr (Q.map (blockPerm (1 : Equiv.Perm (Fin k)) ρ).toEmbedding) A)
      (commutator_finite _ P (rankOne_finite _ _)) =
    splitTrace k m (setPlacement (k+m) r hr Q A*P-P*setPlacement (k+m) r hr Q A)
      (commutator_finite _ P (rankOne_finite _ _)) := by
  have h := symmetric_commutator_spectator k m ρ⁻¹ (setPlacement (k+m) r hr Q A) ψ
  have he : permHilbertIsometry (𝕜 := ℂ) (E := H)
      (blockPerm (1 : Equiv.Perm (Fin k)) ρ⁻¹) =
      (permHilbertIsometry (blockPerm (1 : Equiv.Perm (Fin k)) ρ)).symm := by
    rw [permHilbertIsometry_symm,blockPerm_inv,inv_one]
  dsimp only at h ⊢
  rw [he,setPlacement_covariance (k+m) r hr Q hQ] at h
  exact h

/-- A literal active set is the disjoint union of its observed and spectator
coordinates. This constructor keeps those coordinates explicit. -/
def joinedSlots (k m : ℕ) (U : Finset (Fin k)) (V : Finset (Fin m)) :
    Finset (Fin (k+m)) :=
  U.map (Fin.castAddEmb m) ∪ V.map (Fin.natAddEmb k)

theorem joinedSlots_card (k m : ℕ) (U : Finset (Fin k)) (V : Finset (Fin m)) :
    (joinedSlots k m U V).card=U.card+V.card := by
  classical
  unfold joinedSlots
  rw [Finset.card_union_of_disjoint,Finset.card_map,Finset.card_map]
  rw [Finset.disjoint_left]
  intro x hx hy
  obtain ⟨i,_,hi⟩ := Finset.mem_map.mp hx
  obtain ⟨j,_,hj⟩ := Finset.mem_map.mp hy
  have hh := congrArg Fin.val (hi.trans hj.symm)
  simp only [Fin.castAddEmb_apply,Fin.natAddEmb_apply,Fin.val_castAdd,Fin.val_natAdd] at hh
  have := i.isLt
  omega

/-- A spectator permutation preserves the observed coordinates pointwise. -/
theorem joinedSlots_relabel (k m : ℕ) (U : Finset (Fin k)) (V : Finset (Fin m))
    (ρ : Equiv.Perm (Fin m)) :
    (joinedSlots k m U V).map (blockPerm (1 : Equiv.Perm (Fin k)) ρ).toEmbedding =
      joinedSlots k m U (V.map ρ.toEmbedding) := by
  classical
  unfold joinedSlots
  rw [Finset.map_union,Finset.map_map,Finset.map_map]
  congr 1
  · congr 1
    ext i
    simp only [Function.Embedding.trans_apply,Equiv.coe_toEmbedding,Fin.castAddEmb_apply,
      blockPerm_castAdd,Equiv.Perm.one_apply]
  · rw [Finset.map_map]
    congr 1
    ext i
    simp only [Function.Embedding.trans_apply,Equiv.coe_toEmbedding,Fin.natAddEmb_apply,
      blockPerm_natAdd]

/-- Equal-size subsets of the spectator block are related by an actual
permutation of that block. -/
theorem exists_spectator_permutation {m : ℕ} (V W : Finset (Fin m)) (hc : V.card=W.card) :
    ∃ ρ : Equiv.Perm (Fin m), V.map ρ.toEmbedding=W := by
  classical
  obtain ⟨ρ,hρ,_⟩ := exists_perm_two_sets V ∅ W ∅ (by simp) (by simp) hc (by simp)
  exact ⟨ρ,hρ⟩

/-- For a fixed observed subset, every spectator choice has exactly the
same actual traced commutator. This is the operator fact needed before
multiplying by the binomial spectator count. -/
theorem traced_placement_independent_of_spectators (k m r : ℕ) (hr : r ≤ k+m)
    (U : Finset (Fin k)) (V W : Finset (Fin m)) (hV : U.card+V.card=r)
    (hc : V.card=W.card) (A : SymSector ℂ H r →L[ℂ] SymSector ℂ H r)
    (ψ : SymSector ℂ H (k+m)) :
    let P := InnerProductSpace.rankOne ℂ (ψ : HilbertTensorPower ℂ H (k+m))
      (ψ : HilbertTensorPower ℂ H (k+m))
    splitTrace k m
      (setPlacement (k+m) r hr (joinedSlots k m U V) A*P-
        P*setPlacement (k+m) r hr (joinedSlots k m U V) A)
      (commutator_finite _ P (rankOne_finite _ _)) =
    splitTrace k m
      (setPlacement (k+m) r hr (joinedSlots k m U W) A*P-
        P*setPlacement (k+m) r hr (joinedSlots k m U W) A)
      (commutator_finite _ P (rankOne_finite _ _)) := by
  obtain ⟨ρ,hρ⟩ := exists_spectator_permutation V W hc
  have hh := setPlacement_spectator_invariant k m r hr (joinedSlots k m U V)
    ((joinedSlots_card k m U V).trans hV) ρ A ψ
  rw [joinedSlots_relabel,hρ] at hh
  exact hh.symm


/-- Summing the actual placed commutators over all spectator choices gives
the exact binomial coefficient for a fixed observed subset. -/
theorem sum_spectator_placements (k m r n : ℕ) (hr : r ≤ k+m)
    (U : Finset (Fin k)) (hU : U.card+n=r) (W : Finset (Fin m)) (hW : W.card=n)
    (A : SymSector ℂ H r →L[ℂ] SymSector ℂ H r) (ψ : SymSector ℂ H (k+m)) :
    let P := InnerProductSpace.rankOne ℂ (ψ : HilbertTensorPower ℂ H (k+m))
      (ψ : HilbertTensorPower ℂ H (k+m))
    (∑ V ∈ (Finset.univ : Finset (Fin m)).powersetCard n,
      splitTrace k m (setPlacement (k+m) r hr (joinedSlots k m U V) A*P-
        P*setPlacement (k+m) r hr (joinedSlots k m U V) A)
        (commutator_finite _ P (rankOne_finite _ _))) =
    (m.choose n) • splitTrace k m
      (setPlacement (k+m) r hr (joinedSlots k m U W) A*P-
        P*setPlacement (k+m) r hr (joinedSlots k m U W) A)
      (commutator_finite _ P (rankOne_finite _ _)) := by
  classical
  dsimp only
  calc
    _ = ∑ _V ∈ (Finset.univ : Finset (Fin m)).powersetCard n,
        splitTrace k m
          (setPlacement (k+m) r hr (joinedSlots k m U W) A*
            InnerProductSpace.rankOne ℂ (ψ : HilbertTensorPower ℂ H (k+m))
              (ψ : HilbertTensorPower ℂ H (k+m))-
            InnerProductSpace.rankOne ℂ (ψ : HilbertTensorPower ℂ H (k+m))
              (ψ : HilbertTensorPower ℂ H (k+m))*
              setPlacement (k+m) r hr (joinedSlots k m U W) A)
          (commutator_finite _ _ (rankOne_finite _ _)) := by
      apply Finset.sum_congr rfl
      intro V hV
      have hc := (Finset.mem_powersetCard.mp hV).2
      exact traced_placement_independent_of_spectators k m r hr U V W
        (by omega) (hc.trans hW.symm) A ψ
    _ = _ := by simp only [Finset.sum_const,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin]

end QuantumNLS.Prop001RsixteenSpectator


/-! Canonical one-overlap subsets and the actual further marginal. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
open scoped InnerProductSpace BigOperators ENNReal
namespace QuantumNLS.Prop001RsixteenCanonical
open TraceClass TraceIdeal TensorCarrier TensorPlacements PlacementFusion PlacementGrouping
  PlacementOverlap PlacementUnionReindex PlacementFiberTransport PlacementFiberOperator
  PhysicalTensor PhysicalEnergyTrace RootOverlapCommutator Ext025A12Trace Ext025A12Normal
  Ext025A12PartialTrace Ext025A12Collision Prop001 Prop001RfifteenTransport
  Prop001RfifteenNestedTrace Prop001RfifteenSymmetry Prop001RfifteenRemainder
  Prop001RsixteenCounting Prop001RsixteenSpectator Prop001RsixteenPlacement
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem prefixLift_cast {a b t : ℕ} (h : a=b) (B : RankOperator H a) :
    castTensorOperator (congrArg (fun u => u+t) h) (prefixLift a t B) =
      prefixLift b t (castTensorOperator h B) := by
  cases h
  rfl

theorem castTensorOperator_trans {a b c : ℕ} (h : a=b) (h' : b=c)
    (B : RankOperator H a) :
    castTensorOperator h' (castTensorOperator h B) = castTensorOperator (h.trans h') B := by
  cases h
  cases h'
  rfl

theorem castTensorOperator_pull {a b : ℕ} (h : a=b) (B : RankOperator H a) :
    castTensorOperator h B = pull (cIso h).symm B := by
  cases h
  rfl

/-- Any raw subset placement with the specified literal active coordinates
is exactly setPlacement, including its arithmetic carrier transport. -/
theorem castSubsetPlacement_eq_setPlacement {N r s : ℕ} (h : r+s=N) (hr : r ≤ N)
    (S : PlacementSubset r s) (Q : Finset (Fin N)) (hQ : castSlotSet h S.val=Q)
    (A : SymSector ℂ H r →L[ℂ] SymSector ℂ H r) :
    castTensorOperator h (subsetPlacement S A)=setPlacement N r hr Q A := by
  have hs : s=N-r := by omega
  subst s
  rw [← hQ,setPlacement_slots]
  rfl

/-- Extending the source's one-overlap placement keeps precisely the same
observed slot and the first n spectator slots. -/
theorem oneOverlap_prefix_slots (k n t : ℕ) (j : Fin (k+1)) :
    castSlotSet (by omega : (n+1)+(k+t)=(k+1)+(n+t))
      (prefixPlacementSubset (t := t) (oneOverlapSubset k n j)).val =
      joinedSlots (k+1) (n+t) {j} (firstPositions (p := n) (q := t)) := by
  classical
  simp only [prefixPlacementSubset,oneOverlapSubset,castSlotSet_eq_map,Finset.map_map,
    Finset.map_insert,joinedSlots,Finset.map_singleton,Finset.singleton_union,firstPositions]
  congr 1

/-- Equality of the literal canonical placed operator and the prefix lift
of the lower-rank source collision operator. -/
theorem oneOverlap_prefix_operator (k n t : ℕ) (j : Fin (k+1))
    (A : SymSector ℂ H (n+1) →L[ℂ] SymSector ℂ H (n+1)) :
    pull (cIso (Nat.add_assoc (k+1) n t)).symm
      (prefixLift ((k+1)+n) t
        (placedInteraction k n (subsetRepresentative (oneOverlapSubset k n j)) A)) =
      setPlacement ((k+1)+(n+t)) (n+1) (by omega)
        (joinedSlots (k+1) (n+t) {j} (firstPositions (p := n) (q := t))) A := by
  let h : n+1+k=(k+1)+n := by omega
  let h' : (n+1)+(k+t)=(k+1)+(n+t) := by omega
  let S := oneOverlapSubset k n j
  calc
    _ = castTensorOperator (Nat.add_assoc (k+1) n t)
        (prefixLift ((k+1)+n) t (castTensorOperator h (subsetPlacement S A))) := by
      rw [castTensorOperator_pull]
      rfl
    _ = castTensorOperator (Nat.add_assoc (k+1) n t)
        (castTensorOperator (congrArg (fun u => u+t) h)
          (prefixLift (n+1+k) t (subsetPlacement S A))) := by
      rw [prefixLift_cast]
    _ = castTensorOperator h' (castTensorOperator (Nat.add_assoc (n+1) k t)
          (prefixLift (n+1+k) t (subsetPlacement S A))) := by
      rw [castTensorOperator_trans,castTensorOperator_trans]
    _ = castTensorOperator h' (subsetPlacement (prefixPlacementSubset (t := t) S) A) := by
      rw [raw_prefix_placement]
    _ = _ := castSubsetPlacement_eq_setPlacement h' (by omega) _ _
      (oneOverlap_prefix_slots k n t j) A

/-- A canonical one-overlap commutator on the full state equals the
commutator on the actual lower-rank marginal. -/
theorem canonical_oneOverlap_reduction (k n t : ℕ) (j : Fin (k+1))
    (A : SymSector ℂ H (n+1) →L[ℂ] SymSector ℂ H (n+1))
    (z : HilbertTensorPower ℂ H (((k+1)+n)+t)) :
    let z' := cIso (Nat.add_assoc (k+1) n t) z
    let P' := InnerProductSpace.rankOne ℂ z' z'
    let B := placedInteraction k n (subsetRepresentative (oneOverlapSubset k n j)) A
    let Γ := reducedDensityN (((k+1)+n)+t) ((k+1)+n) (by omega) z
    splitTrace (k+1) (n+t)
      (setPlacement ((k+1)+(n+t)) (n+1) (by omega)
        (joinedSlots (k+1) (n+t) {j} (firstPositions (p := n) (q := t))) A*P'-
        P'*setPlacement ((k+1)+(n+t)) (n+1) (by omega)
          (joinedSlots (k+1) (n+t) {j} (firstPositions (p := n) (q := t))) A)
      (commutator_finite _ P' (rankOne_finite _ _)) =
    splitTrace (k+1) n (B*Γ-Γ*B)
      (commutator_finite _ Γ (reducedDensity_finite _ _ (by omega) z)) := by
  dsimp only
  have h := nested_commutator_reduction (k+1) n t
    (placedInteraction k n (subsetRepresentative (oneOverlapSubset k n j)) A)
    (InnerProductSpace.rankOne ℂ z z) (rankOne_finite z z)
  simpa only [pull_sub,pull_mul,pull_rankOne,LinearIsometryEquiv.symm_symm,
    oneOverlap_prefix_operator,splitTrace_rankOne] using h

end QuantumNLS.Prop001RsixteenCanonical


/-! Zero-overlap cancellation on actual canonical and relabeled placements. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
open scoped InnerProductSpace BigOperators ENNReal
namespace QuantumNLS.Prop001RsixteenZero
open TraceClass TraceIdeal TensorCarrier TensorPlacements PlacementFusion PlacementGrouping
  PlacementOverlap PlacementUnionReindex PlacementFiberTransport PlacementFiberOperator
  PhysicalEnergyTrace RootOverlapCommutator Ext025A12Trace Ext025A12Normal
  Ext025A12PartialTrace Ext025A12Collision Prop001 Prop001RfifteenTransport
  Prop001RfifteenNestedTrace Prop001RfifteenSymmetry Prop001RfifteenRemainder
  Prop001RsixteenCounting Prop001RsixteenSpectator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The canonical zero-overlap subset is precisely the middle block. -/
theorem empty_joinedSlots_eq_slotsB (k r t : ℕ) :
    joinedSlots k (r+t) ∅ (firstPositions (p := r) (q := t))=slotsB k r t := by
  classical
  simp [joinedSlots,firstPositions,slotsB,Finset.map_eq_image,Finset.image_image,
    Function.comp_def,Fin.natAddEmb_apply]

/-- The literal canonical zero-overlap raw placement acts in the spectator
block, with no compression or unknown operator in the conclusion. -/
theorem empty_canonical_placement (k r t : ℕ)
    (A : SymSector ℂ H r →L[ℂ] SymSector ℂ H r) :
    setPlacement (k+(r+t)) r (by omega)
      (joinedSlots k (r+t) ∅ (firstPositions (p := r) (q := t))) A = midPlacement k r t A := by
  classical
  rw [empty_joinedSlots_eq_slotsB]
  rw [setPlacement_eq_source _ _ _ _ (card_slotsB k r t)]
  exact rawMid k r t A (k+(r+t)-r) (by omega) _
    (slots_sourcePlacementOfSlots (by omega) _ (card_slotsB k r t))

/-- The canonical zero-overlap commutator has zero partial trace on every
trace-class input, including mixed states. -/
theorem splitTrace_mid_commutator_zero (k r t : ℕ)
    (A : SymSector ℂ H r →L[ℂ] SymSector ℂ H r)
    (T : RankOperator H (k+(r+t))) (hT : IsTraceClass T) :
    splitTrace k (r+t) (midPlacement k r t A*T-T*midPlacement k r t A)
      (commutator_finite _ T hT)=0 := by
  have hm : pull (splitIsometry k (r+t)).symm (midPlacement k r t A) =
      htmap (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ H k)) (firstPlacement (q := t) A) := by
    ext x
    simp only [pull_apply,LinearIsometryEquiv.symm_symm,midPlacement,
      ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_toLinearIsometry,
      LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.apply_symm_apply]
  unfold splitTrace
  simp only [pull_sub,pull_mul,hm]
  exact spectator_commutator_zero (firstPlacement (q := t) A)
    (pull (splitIsometry k (r+t)).symm T)
    (by simpa only [IsTraceClass,traceNorm_pull] using hT)

/-- Every actual zero-overlap spectator choice cancels, using its actual
block permutation and the actual symmetric density. -/
theorem empty_observed_traced_placement_zero (k m r : ℕ) (hr : r ≤ m)
    (V : Finset (Fin m)) (hV : V.card=r)
    (A : SymSector ℂ H r →L[ℂ] SymSector ℂ H r) (ψ : SymSector ℂ H (k+m)) :
    let P := InnerProductSpace.rankOne ℂ (ψ : HilbertTensorPower ℂ H (k+m))
      (ψ : HilbertTensorPower ℂ H (k+m))
    splitTrace k m
      (setPlacement (k+m) r (by omega) (joinedSlots k m ∅ V) A*P-
        P*setPlacement (k+m) r (by omega) (joinedSlots k m ∅ V) A)
      (commutator_finite _ P (rankOne_finite _ _))=0 := by
  obtain ⟨t,ht⟩ := Nat.exists_eq_add_of_le hr
  subst m
  have hh := traced_placement_independent_of_spectators k (r+t) r (by omega) ∅ V
    (firstPositions (p := r) (q := t)) (by simpa using hV)
    (hV.trans (card_firstPositions r t).symm) A ψ
  dsimp only at hh ⊢
  rw [empty_canonical_placement] at hh
  exact hh.trans (splitTrace_mid_commutator_zero k r t A _ (rankOne_finite _ _))

end QuantumNLS.Prop001RsixteenZero


/-! A concrete product index for every fixed-overlap source subset. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
open scoped BigOperators
namespace QuantumNLS.Prop001RsixteenFiber
open TensorCarrier TensorPlacements PlacementOverlap Prop001RsixteenSpectator

/-- Read back the actual observed coordinates of a literal subset. -/
def observedPart (k m : ℕ) (Q : Finset (Fin (k+m))) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter (fun i => Fin.castAdd m i ∈ Q)

/-- Read back the actual spectator coordinates of a literal subset. -/
def spectatorPart (k m : ℕ) (Q : Finset (Fin (k+m))) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => Fin.natAdd k i ∈ Q)

theorem castAdd_mem_joinedSlots (k m : ℕ) (U : Finset (Fin k)) (V : Finset (Fin m))
    (i : Fin k) : Fin.castAdd m i ∈ joinedSlots k m U V ↔ i ∈ U := by
  classical
  simp only [joinedSlots,Finset.mem_union,Finset.mem_map,Fin.castAddEmb_apply,Fin.natAddEmb_apply]
  constructor
  · rintro (⟨j,hj,he⟩|⟨j,_,he⟩)
    · have hij : j=i := Fin.castAdd_inj.mp he
      simpa only [hij] using hj
    · have he' := congrArg Fin.val he
      simp only [Fin.val_natAdd,Fin.val_castAdd] at he'
      have := i.isLt
      omega
  · intro hi
    exact Or.inl ⟨i,hi,rfl⟩

theorem natAdd_mem_joinedSlots (k m : ℕ) (U : Finset (Fin k)) (V : Finset (Fin m))
    (i : Fin m) : Fin.natAdd k i ∈ joinedSlots k m U V ↔ i ∈ V := by
  classical
  simp only [joinedSlots,Finset.mem_union,Finset.mem_map,Fin.castAddEmb_apply,Fin.natAddEmb_apply]
  constructor
  · rintro (⟨j,_,he⟩|⟨j,hj,he⟩)
    · have he' := congrArg Fin.val he
      simp only [Fin.val_natAdd,Fin.val_castAdd] at he'
      have := j.isLt
      omega
    · have he' := congrArg Fin.val he
      simp only [Fin.val_natAdd] at he'
      have hij : j=i := Fin.ext (by omega)
      simpa only [hij] using hj
  · intro hi
    exact Or.inr ⟨i,hi,rfl⟩

theorem observedPart_joinedSlots (k m : ℕ) (U : Finset (Fin k)) (V : Finset (Fin m)) :
    observedPart k m (joinedSlots k m U V)=U := by
  classical
  ext i
  simp only [observedPart,Finset.mem_filter,Finset.mem_univ,true_and,castAdd_mem_joinedSlots]

theorem spectatorPart_joinedSlots (k m : ℕ) (U : Finset (Fin k)) (V : Finset (Fin m)) :
    spectatorPart k m (joinedSlots k m U V)=V := by
  classical
  ext i
  simp only [spectatorPart,Finset.mem_filter,Finset.mem_univ,true_and,natAdd_mem_joinedSlots]

theorem joinedSlots_parts (k m : ℕ) (Q : Finset (Fin (k+m))) :
    joinedSlots k m (observedPart k m Q) (spectatorPart k m Q)=Q := by
  classical
  ext x
  refine Fin.addCases (fun i => ?_) (fun i => ?_) x
  · simp only [castAdd_mem_joinedSlots,observedPart,Finset.mem_filter,Finset.mem_univ,true_and]
  · simp only [natAdd_mem_joinedSlots,spectatorPart,Finset.mem_filter,Finset.mem_univ,true_and]

/-- The visible overlap really is the chosen observed subset. -/
theorem joinedSlots_inter_first (k m : ℕ) (U : Finset (Fin k)) (V : Finset (Fin m)) :
    (joinedSlots k m U V) ∩ firstPositions = U.map (Fin.castAddEmb m) := by
  classical
  ext x
  refine Fin.addCases (fun i => ?_) (fun i => ?_) x
  · have hh : Fin.castAdd m i ∈ firstPositions (p := k) (q := m) :=
      (mem_firstPositions _).mpr ⟨i,rfl⟩
    simp only [Finset.mem_inter,castAdd_mem_joinedSlots,hh,and_true]
    simp
  · have hn : Fin.natAdd k i ∉ firstPositions (p := k) (q := m) := by
      intro hh
      obtain ⟨j,hj⟩ := (mem_firstPositions _).mp hh
      have hv := congrArg Fin.val hj
      simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
      have := j.isLt
      omega
    simp only [Finset.mem_inter,hn,and_false,false_iff,Finset.mem_map,Fin.castAddEmb_apply]
    rintro ⟨j,_,he⟩
    have he' := congrArg Fin.val he
    simp only [Fin.val_castAdd,Fin.val_natAdd] at he'
    have := j.isLt
    omega

/-- Full operator-valued reindexing by observed and spectator subsets.
The original active subset is retained by its literal disjoint union. -/
theorem sum_overlap_joined (k m r ell : ℕ) (hell : ell ≤ r)
    {M : Type*} [AddCommMonoid M] (F : Finset (Fin (k+m)) → M) :
    (∑ Q ∈ overlapFiber (firstPositions (p := k) (q := m)) r ell, F Q) =
    ∑ U ∈ (Finset.univ : Finset (Fin k)).powersetCard ell,
      ∑ V ∈ (Finset.univ : Finset (Fin m)).powersetCard (r-ell),
        F (joinedSlots k m U V) := by
  classical
  symm
  rw [← Finset.sum_product']
  refine Finset.sum_bij (fun UV _ => joinedSlots k m UV.1 UV.2) ?_ ?_ ?_ ?_
  · intro UV hUV
    obtain ⟨hU,hV⟩ := Finset.mem_product.mp hUV
    have hcU := (Finset.mem_powersetCard.mp hU).2
    have hcV := (Finset.mem_powersetCard.mp hV).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,?_⟩,?_⟩
    · rw [joinedSlots_card,hcU,hcV]
      omega
    · rw [Finset.inter_comm,joinedSlots_inter_first,Finset.card_map,hcU]
  · intro UV _ UW _ he
    exact Prod.ext
      (by simpa only [observedPart_joinedSlots] using congrArg (observedPart k m) he)
      (by simpa only [spectatorPart_joinedSlots] using congrArg (spectatorPart k m) he)
  · intro Q hQ
    obtain ⟨hQc,hQi⟩ := Finset.mem_filter.mp hQ
    have hcard := (Finset.mem_powersetCard.mp hQc).2
    have hU : (observedPart k m Q).card=ell := by
      have hh := congrArg (fun Z => (Z ∩ firstPositions (p := k) (q := m)).card)
        (joinedSlots_parts k m Q)
      rw [joinedSlots_inter_first,Finset.card_map,Finset.inter_comm,hQi] at hh
      exact hh
    have hV : (spectatorPart k m Q).card=r-ell := by
      have hh := congrArg Finset.card (joinedSlots_parts k m Q)
      rw [joinedSlots_card,hU,hcard] at hh
      omega
    refine ⟨(observedPart k m Q,spectatorPart k m Q),?_,joinedSlots_parts k m Q⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hU⟩,
        Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hV⟩⟩
  · intro _ _
    rfl

end QuantumNLS.Prop001RsixteenFiber

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
open scoped InnerProductSpace BigOperators ENNReal
namespace QuantumNLS.Prop001RsixteenAssembly
open TraceClass TraceIdeal TensorCarrier TensorPlacements PlacementFusion PlacementGrouping
  PlacementOverlap PlacementUnionReindex PlacementFiberTransport PlacementFiberOperator
  PhysicalEnergyTrace RootOverlapCommutator Ext025A12Trace Ext025A12Normal
  Ext025A12PartialTrace Ext025A12Collision Prop001 Prop001RfifteenTransport
  Prop001RfifteenNestedTrace Prop001RfifteenSymmetry Prop001RfifteenRemainder
  Prop001RfourteenRegrouping Prop001RfourteenTraceRegrouping
  Prop001RsixteenCounting Prop001RsixteenSpectator Prop001RsixteenFiber Prop001RsixteenZero
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The frozen actual overlap partition is exactly the double sum over
observed and spectator coordinates. -/
theorem overlap_trace_joined (k m r ell : ℕ) (hr : r ≤ k+m) (hell : ell ≤ r)
    (A : SymSector ℂ H r →L[ℂ] SymSector ℂ H r)
    (T : RankOperator H (k+m)) (hT : IsTraceClass T) :
    (splitMap k m (overlapIdeal (k+m) k r ell (by omega) hr A ⟨T,hT⟩)).val =
      ∑ U ∈ (Finset.univ : Finset (Fin k)).powersetCard ell,
        ∑ V ∈ (Finset.univ : Finset (Fin m)).powersetCard (r-ell),
          splitTrace k m (setPlacement (k+m) r hr (joinedSlots k m U V) A*T-
            T*setPlacement (k+m) r hr (joinedSlots k m U V) A)
            (commutator_finite _ T hT) := by
  classical
  calc
    _ = ∑ S ∈ (Finset.univ : Finset (PlacementSubset r (k+m-r))).filter
        (fun S => overlap (k+m) k r (by omega) hr S=ell),
        splitTrace k m (rawSubsetPlacement (k+m) r hr S A*T-
          T*rawSubsetPlacement (k+m) r hr S A) (commutator_finite _ T hT) := by
      simp only [overlapIdeal,map_sum,Submodule.coe_sum,splitMap_val,commutatorIdeal]
    _ = ∑ Q ∈ overlapFiber (firstPositions (p := k) (q := m)) r ell,
        splitTrace k m (setPlacement (k+m) r hr Q A*T-T*setPlacement (k+m) r hr Q A)
          (commutator_finite _ T hT) := by
      have h := sum_overlap_subsets (k+m) k r ell (by omega) hr
        (fun Q => splitTrace k m
          (setPlacement (k+m) r hr Q A*T-T*setPlacement (k+m) r hr Q A)
            (commutator_finite _ T hT))
      have hp : castSlotSet (Nat.add_sub_of_le (show k ≤ k+m by omega))
          (firstPositions (p := k) (q := k+m-k)) = firstPositions (p := k) (q := m) := by
        unfold castSlotSet firstPositions
        rw [Finset.map_map]
        apply congrArg (fun e : Fin k ↪ Fin (k+m) => Finset.univ.map e)
        apply Function.Embedding.ext
        intro i
        apply Fin.ext
        change (Equiv.cast (congrArg Fin (Nat.add_sub_of_le (show k ≤ k+m by omega)))
          (Fin.castAdd (k+m-k) i)).val = (Fin.castAdd m i).val
        rw [equivCast_eq_finCast (Nat.add_sub_of_le (show k ≤ k+m by omega))
          (Fin.castAdd (k+m-k) i)]; rfl
      simpa only [setPlacement_slots,hp] using h
    _ = _ := sum_overlap_joined k m r ell hell _

/-- The exact operator-valued binomial coefficient, now on the original
overlapIdeal and actual symmetric density. No invariance fact is assumed. -/
theorem overlap_trace_counted (k m r ell : ℕ) (hr : r ≤ k+m) (hell : ell ≤ r)
    (W : Finset (Fin m)) (hW : W.card=r-ell)
    (A : SymSector ℂ H r →L[ℂ] SymSector ℂ H r) (ψ : SymSector ℂ H (k+m)) :
    let P := InnerProductSpace.rankOne ℂ (ψ : HilbertTensorPower ℂ H (k+m))
      (ψ : HilbertTensorPower ℂ H (k+m))
    (splitMap k m (overlapIdeal (k+m) k r ell (by omega) hr A ⟨P,rankOne_finite _ _⟩)).val =
      ∑ U ∈ (Finset.univ : Finset (Fin k)).powersetCard ell,
        (m.choose (r-ell)) • splitTrace k m
          (setPlacement (k+m) r hr (joinedSlots k m U W) A*P-
            P*setPlacement (k+m) r hr (joinedSlots k m U W) A)
          (commutator_finite _ P (rankOne_finite _ _)) := by
  classical
  dsimp only
  rw [overlap_trace_joined k m r ell hr hell]
  apply Finset.sum_congr rfl
  intro U hU
  exact sum_spectator_placements k m r (r-ell) hr U
    (by have hh := (Finset.mem_powersetCard.mp hU).2; omega) W hW A ψ

/-- Zero-overlap cancellation for the literal frozen overlapIdeal on the
actual symmetric state, including the case of an empty spectator fiber. -/
theorem overlap_trace_zero (k m r : ℕ) (hr : r ≤ k+m)
    (A : SymSector ℂ H r →L[ℂ] SymSector ℂ H r) (ψ : SymSector ℂ H (k+m)) :
    let P := InnerProductSpace.rankOne ℂ (ψ : HilbertTensorPower ℂ H (k+m))
      (ψ : HilbertTensorPower ℂ H (k+m))
    (splitMap k m (overlapIdeal (k+m) k r 0 (by omega) hr A ⟨P,rankOne_finite _ _⟩)).val=0 := by
  classical
  dsimp only
  rw [overlap_trace_joined k m r 0 hr (Nat.zero_le r)]
  simp only [Finset.powersetCard_zero,Finset.sum_singleton,Nat.sub_zero]
  apply Finset.sum_eq_zero
  intro V hV
  have hc := (Finset.mem_powersetCard.mp hV).2
  have hm : r ≤ m := by
    have hh := Finset.card_le_card (Finset.subset_univ V)
    simpa only [Finset.card_univ,Fintype.card_fin,hc] using hh
  exact empty_observed_traced_placement_zero k m r hm V hc A ψ

end QuantumNLS.Prop001RsixteenAssembly

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
open scoped InnerProductSpace BigOperators ENNReal
namespace QuantumNLS.Prop001RsixteenOne
open TraceClass TraceIdeal TensorCarrier TensorPlacements PlacementFusion PlacementGrouping
  PlacementOverlap PlacementUnionReindex PlacementFiberTransport PlacementFiberOperator
  PhysicalTensor PhysicalEnergyTrace RootOverlapCommutator Ext025A12Trace Ext025A12Normal
  Ext025A12PartialTrace Ext025A12Collision Prop001 Prop001RfifteenTransport
  Prop001RfifteenNestedTrace Prop001RfifteenSymmetry Prop001RfifteenRemainder
  Prop001RfourteenRegrouping Prop001RfourteenTraceRegrouping
  Prop001RsixteenCounting Prop001RsixteenSpectator Prop001RsixteenFiber Prop001RsixteenZero
  Prop001RsixteenAssembly Prop001RsixteenCanonical
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Sum over observed singleton subsets, with the observed coordinate retained. -/
theorem sum_singleton_subsets (k : ℕ) {M : Type*} [AddCommMonoid M]
    (F : Finset (Fin k) → M) :
    (∑ U ∈ (Finset.univ : Finset (Fin k)).powersetCard 1,F U) = ∑ j : Fin k,F {j} := by
  classical
  symm
  refine Finset.sum_bij (fun j _ => {j}) ?_ ?_ ?_ ?_
  · intro j _
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,Finset.card_singleton _⟩
  · intro j _ l _ he
    exact Finset.singleton_injective he
  · intro U hU
    obtain ⟨j,hj⟩ := Finset.card_eq_one.mp (Finset.mem_powersetCard.mp hU).2
    exact ⟨j,Finset.mem_univ _,hj.symm⟩
  · intro _ _
    rfl

/-- For every admissible interaction rank, the full weighted one-overlap
fiber equals r alpha times the canonical collision on the actual marginal. -/
theorem oneOverlap_weighted_identification (k n t : ℕ)
    (A : SymSector ℂ H (n+1) →L[ℂ] SymSector ℂ H (n+1))
    (ψ : SymSector ℂ H ((k+1)+(n+t))) :
    let N := (k+1)+(n+t)
    let P := InnerProductSpace.rankOne ℂ (ψ : HilbertTensorPower ℂ H N)
      (ψ : HilbertTensorPower ℂ H N)
    let Γ := reducedDensityN N ((k+1)+n) (by omega) (ψ : HilbertTensorPower ℂ H N)
    (((((n+1).factorial : ℝ)*N/(N : ℝ)^(n+1)) : ℝ) : ℂ) •
      (splitMap (k+1) (n+t) (overlapIdeal N (k+1) (n+1) 1 (by omega) (by omega)
        A ⟨P,rankOne_finite _ _⟩)).val =
    (alpha N (k+1) n : ℂ) • sourceRankCollision k n A Γ
      (reducedDensity_finite N ((k+1)+n) (by omega) (ψ : HilbertTensorPower ℂ H N)) := by
  classical
  dsimp only
  let z : HilbertTensorPower ℂ H (((k+1)+n)+t) :=
    (cIso (Nat.add_assoc (k+1) n t)).symm (ψ : HilbertTensorPower ℂ H ((k+1)+(n+t)))
  have hΓ := reducedDensityN_cast (Nat.add_assoc (k+1) n t) ((k+1)+n) (by omega) z
  dsimp only [z] at hΓ
  simp only [LinearIsometryEquiv.apply_symm_apply] at hΓ
  have hj (j : Fin (k+1)) := canonical_oneOverlap_reduction k n t j A z
  dsimp only [z] at hj
  simp only [LinearIsometryEquiv.apply_symm_apply,← hΓ] at hj
  have he := overlap_trace_counted (k+1) (n+t) (n+1) 1 (by omega) (by omega)
    (firstPositions (p := n) (q := t)) (by simp only [card_firstPositions,Nat.add_sub_cancel]) A ψ
  dsimp only at he
  rw [sum_singleton_subsets] at he
  rw [he]
  simp only [Nat.add_sub_cancel] at *
  simp_rw [hj]
  simp_rw [← Nat.cast_smul_eq_nsmul ℂ]
  rw [← Finset.smul_sum,smul_smul]
  unfold sourceRankCollision rankCollision
  rw [smul_smul]
  congr 1
  have hc := hierarchyCoefficient_one ((k+1)+(n+t)) (k+1) n (by omega)
  unfold hierarchyCoefficient at hc
  have hm : (k+1)+(n+t)-(k+1)=n+t := by omega
  rw [Nat.add_sub_cancel,hm] at hc
  have hh := congrArg (fun x : ℝ => (x : ℂ)) hc
  push_cast at hh ⊢
  exact hh.trans (mul_comm _ _)

end QuantumNLS.Prop001RsixteenOne

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001Rsixteen" then
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
  Lean.logInfo m!"Prop001RsixteenReduction audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."



#print axioms QuantumNLS.Prop001RsixteenSpectator.setPlacement_eq_source
#print axioms QuantumNLS.Prop001RsixteenSpectator.permHilbertIsometry_symm
#print axioms QuantumNLS.Prop001RsixteenSpectator.setPlacement_covariance
#print axioms QuantumNLS.Prop001RsixteenSpectator.setPlacement_spectator_invariant
#print axioms QuantumNLS.Prop001RsixteenSpectator.joinedSlots
#print axioms QuantumNLS.Prop001RsixteenSpectator.joinedSlots_card
#print axioms QuantumNLS.Prop001RsixteenSpectator.joinedSlots_relabel
#print axioms QuantumNLS.Prop001RsixteenSpectator.exists_spectator_permutation
#print axioms QuantumNLS.Prop001RsixteenSpectator.traced_placement_independent_of_spectators
#print axioms QuantumNLS.Prop001RsixteenSpectator.sum_spectator_placements
#print axioms QuantumNLS.Prop001RsixteenCanonical.prefixLift_cast
#print axioms QuantumNLS.Prop001RsixteenCanonical.castTensorOperator_trans
#print axioms QuantumNLS.Prop001RsixteenCanonical.castTensorOperator_pull
#print axioms QuantumNLS.Prop001RsixteenCanonical.castSubsetPlacement_eq_setPlacement
#print axioms QuantumNLS.Prop001RsixteenCanonical.oneOverlap_prefix_slots
#print axioms QuantumNLS.Prop001RsixteenCanonical.oneOverlap_prefix_operator
#print axioms QuantumNLS.Prop001RsixteenCanonical.canonical_oneOverlap_reduction
#print axioms QuantumNLS.Prop001RsixteenZero.empty_joinedSlots_eq_slotsB
#print axioms QuantumNLS.Prop001RsixteenZero.empty_canonical_placement
#print axioms QuantumNLS.Prop001RsixteenZero.splitTrace_mid_commutator_zero
#print axioms QuantumNLS.Prop001RsixteenZero.empty_observed_traced_placement_zero
#print axioms QuantumNLS.Prop001RsixteenFiber.observedPart
#print axioms QuantumNLS.Prop001RsixteenFiber.spectatorPart
#print axioms QuantumNLS.Prop001RsixteenFiber.castAdd_mem_joinedSlots
#print axioms QuantumNLS.Prop001RsixteenFiber.natAdd_mem_joinedSlots
#print axioms QuantumNLS.Prop001RsixteenFiber.observedPart_joinedSlots
#print axioms QuantumNLS.Prop001RsixteenFiber.spectatorPart_joinedSlots
#print axioms QuantumNLS.Prop001RsixteenFiber.joinedSlots_parts
#print axioms QuantumNLS.Prop001RsixteenFiber.joinedSlots_inter_first
#print axioms QuantumNLS.Prop001RsixteenFiber.sum_overlap_joined

#print axioms QuantumNLS.Prop001RsixteenAssembly.overlap_trace_joined
#print axioms QuantumNLS.Prop001RsixteenAssembly.overlap_trace_counted
#print axioms QuantumNLS.Prop001RsixteenAssembly.overlap_trace_zero

#print axioms QuantumNLS.Prop001RsixteenOne.sum_singleton_subsets
#print axioms QuantumNLS.Prop001RsixteenOne.oneOverlap_weighted_identification
