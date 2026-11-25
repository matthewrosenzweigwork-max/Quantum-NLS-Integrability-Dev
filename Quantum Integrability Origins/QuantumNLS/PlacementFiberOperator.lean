/-
QuantumNLS.PlacementFiberOperator — raw operator contributions of ambient
union fibers for LOCAL-011.

PlacementFiberTransport.round25 is frozen and imported read-only.  The
operators below keep the full-tensor pair product visible until the complete
pair sum has been formed; the intermediate symmetric projection is removed
only by the already-proved full-sum identity.
-/
import QuantumNLS.PlacementFiberTransport

set_option maxHeartbeats 5000000

open scoped InnerProductSpace TensorProduct
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements
  QuantumNLS.KernelDefinition QuantumNLS.PlacementFusion
  QuantumNLS.PlacementOverlap QuantumNLS.PlacementProduct
  QuantumNLS.PlacementCovariance QuantumNLS.PlacementGrouping
  QuantumNLS.PlacementUnionReindex QuantumNLS.PlacementFiberTransport

noncomputable section

namespace QuantumNLS.PlacementFiberOperator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Extend an arbitrary full-tensor operator on the first `r` slots by the
identity on the final `t` slots. -/
def prefixTensorLift {r t : ℕ}
    (T : HilbertTensorPower ℂ H r →L[ℂ] HilbertTensorPower ℂ H r) :
    HilbertTensorPower ℂ H (r + t) →L[ℂ] HilbertTensorPower ℂ H (r + t) := by
  let e := splitIsometry (𝕜 := ℂ) (E := H) r t
  exact e.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((htmap (𝕜 := ℂ) T (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ H t))).comp
      e.toLinearIsometry.toContinuousLinearMap)

omit [CompleteSpace H] in
theorem prefixTensorLift_comp {r t : ℕ}
    (T U : HilbertTensorPower ℂ H r →L[ℂ] HilbertTensorPower ℂ H r) :
    (prefixTensorLift (H := H) (r := r) (t := t) T).comp
      (prefixTensorLift (H := H) (r := r) (t := t) U) =
    prefixTensorLift (H := H) (r := r) (t := t) (T.comp U) := by
  let e := splitIsometry (𝕜 := ℂ) (E := H) r t
  let I := ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ H t)
  ext x
  change e.symm (htmap (𝕜 := ℂ) T I
      (e (e.symm (htmap (𝕜 := ℂ) U I (e x))))) =
    e.symm (htmap (𝕜 := ℂ) (T.comp U) I (e x))
  rw [e.apply_symm_apply]
  congr 1
  have hcomp : (htmap (𝕜 := ℂ) T I).comp (htmap (𝕜 := ℂ) U I) =
      htmap (𝕜 := ℂ) (T.comp U) I := by
    simpa [I] using (htmap_comp T U I I).symm
  simpa [ContinuousLinearMap.comp_apply] using
    congrArg (fun f : _ →L[ℂ] _ => f (e x)) hcomp

omit [CompleteSpace H] in
theorem prefixTensorLift_add {r t : ℕ}
    (T U : HilbertTensorPower ℂ H r →L[ℂ] HilbertTensorPower ℂ H r) :
    prefixTensorLift (H := H) (r := r) (t := t) (T + U) =
      prefixTensorLift T + prefixTensorLift U := by
  ext x
  simp [prefixTensorLift, htmap_add_left, ContinuousLinearMap.comp_apply]

omit [CompleteSpace H] in
theorem prefixTensorLift_smul {r t : ℕ} (c : ℂ)
    (T : HilbertTensorPower ℂ H r →L[ℂ] HilbertTensorPower ℂ H r) :
    prefixTensorLift (H := H) (r := r) (t := t) (c • T) =
      c • prefixTensorLift T := by
  ext x
  simp [prefixTensorLift, htmap_smul_left, ContinuousLinearMap.comp_apply]

omit [CompleteSpace H] in
theorem prefixTensorLift_zero {r t : ℕ} :
    prefixTensorLift (H := H) (r := r) (t := t) (0 :
      HilbertTensorPower ℂ H r →L[ℂ] HilbertTensorPower ℂ H r) = 0 := by
  rw [← zero_smul ℂ (ContinuousLinearMap.id ℂ
      (HilbertTensorPower ℂ H r)), prefixTensorLift_smul]
  simp

omit [CompleteSpace H] in
theorem prefixTensorLift_finset_sum {r t : ℕ} {ι : Type*}
    (s : Finset ι)
    (F : ι → HilbertTensorPower ℂ H r →L[ℂ] HilbertTensorPower ℂ H r) :
    prefixTensorLift (H := H) (r := r) (t := t) (∑ i ∈ s, F i) =
      ∑ i ∈ s, prefixTensorLift (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [prefixTensorLift_zero]
  | @insert i s his ih =>
      simp only [Finset.sum_insert his, prefixTensorLift_add, ih]

omit [CompleteSpace H] in
theorem prefixTensorLift_sum {r t : ℕ} {ι : Type*} [Fintype ι]
    (F : ι → HilbertTensorPower ℂ H r →L[ℂ] HilbertTensorPower ℂ H r) :
    prefixTensorLift (H := H) (r := r) (t := t) (∑ i, F i) =
      ∑ i, prefixTensorLift (F i) := by
  simpa using prefixTensorLift_finset_sum (H := H) (r := r) (t := t)
    Finset.univ F

private def prefixBlockPermRep (r t : ℕ) :
    Equiv.Perm (Fin r) →* unitary
      (HilbertTensorPower ℂ H (r + t) →L[ℂ] HilbertTensorPower ℂ H (r + t)) where
  toFun π := permRep ℂ H (r + t) (blockPerm π (1 : Equiv.Perm (Fin t)))
  map_one' := by
    have h : blockPerm (1 : Equiv.Perm (Fin r)) (1 : Equiv.Perm (Fin t)) = 1 := by
      ext x
      simp [blockPerm]
    rw [h, map_one]
  map_mul' π τ := by
    have h : blockPerm (π * τ) (1 : Equiv.Perm (Fin t)) =
        blockPerm π (1 : Equiv.Perm (Fin t)) * blockPerm τ 1 := by
      ext x
      simp [blockPerm]
    rw [h, map_mul]

omit [CompleteSpace H] in
theorem prefixTensorLift_permRep {r t : ℕ} (π : Equiv.Perm (Fin r)) :
    prefixTensorLift (H := H) (r := r) (t := t) (permRep ℂ H r π) =
      (permRep ℂ H (r + t) (blockPerm π (1 : Equiv.Perm (Fin t))) :
        HilbertTensorPower ℂ H (r + t) →L[ℂ] HilbertTensorPower ℂ H (r + t)) := by
  ext x
  rw [prefixTensorLift]
  change (splitIsometry r t).symm
      (htmap (𝕜 := ℂ) (permRep ℂ H r π)
        (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ H t))
        (splitIsometry r t x)) =
    (permRep ℂ H (r + t) (blockPerm π (1 : Equiv.Perm (Fin t))) : _ →L[ℂ] _) x
  rw [permRep_blockPerm_apply]
  have h₁ : (permRep ℂ H t (1 : Equiv.Perm (Fin t)) :
      HilbertTensorPower ℂ H t →L[ℂ] HilbertTensorPower ℂ H t) =
      ContinuousLinearMap.id ℂ _ := by
    rw [map_one (permRep ℂ H t)]
    rfl
  rw [h₁]

omit [CompleteSpace H] in
theorem prefixTensorLift_symProj_eq_groupAverage (r t : ℕ) :
    prefixTensorLift (H := H) (r := r) (t := t) (symProj ℂ H r) =
      groupAverage (prefixBlockPermRep (H := H) r t) := by
  calc
    _ = prefixTensorLift
        (((r.factorial : ℂ)⁻¹) • ∑ π : Equiv.Perm (Fin r),
          (permRep ℂ H r π : _ →L[ℂ] _)) := by
          rw [symProj_eq_factorial_average]
    _ = ((r.factorial : ℂ)⁻¹) •
        ∑ π : Equiv.Perm (Fin r),
          (permRep ℂ H (r + t) (blockPerm π (1 : Equiv.Perm (Fin t))) : _ →L[ℂ] _) := by
          rw [prefixTensorLift_smul, prefixTensorLift_sum]
          simp only [prefixTensorLift_permRep]
    _ = groupAverage (prefixBlockPermRep (H := H) r t) := by
          simp [groupAverage, prefixBlockPermRep, Fintype.card_perm, Fintype.card_fin]

omit [CompleteSpace H] in
theorem prefixTensorLift_symProj_fixes_globalSector {r t : ℕ}
    (x : SymSector ℂ H (r + t)) :
    prefixTensorLift (H := H) (r := r) (t := t) (symProj ℂ H r) x.1 = x.1 := by
  rw [prefixTensorLift_symProj_eq_groupAverage]
  apply groupAverage_apply_of_mem
  intro π
  exact x.property (blockPerm π (1 : Equiv.Perm (Fin t)))

omit [CompleteSpace H] in
theorem symProj_comp_prefixTensorLift_symProj (r t : ℕ) :
    (symProj ℂ H (r + t)).comp
      (prefixTensorLift (H := H) (r := r) (t := t) (symProj ℂ H r)) =
      symProj ℂ H (r + t) := by
  rw [prefixTensorLift_symProj_eq_groupAverage]
  unfold symProj
  change groupAverage (permRep ℂ H (r + t)) *
      groupAverage (prefixBlockPermRep (H := H) r t) = _
  change groupAverage (permRep ℂ H (r + t)) *
      (((Fintype.card (Equiv.Perm (Fin r)) : ℂ)⁻¹) •
        ∑ π : Equiv.Perm (Fin r),
          (permRep ℂ H (r + t) (blockPerm π (1 : Equiv.Perm (Fin t))) : _ →L[ℂ] _)) = _
  rw [mul_smul_comm, Finset.mul_sum]
  simp_rw [groupAverage_mul_rep]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [Fintype.card_perm, Fintype.card_fin]
  have hfac : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  rw [inv_mul_cancel₀ hfac, one_smul]

omit [CompleteSpace H] in
/-- A local symmetric compression inside a lifted raw operator is harmless
after compression to the globally symmetric sector. The right local
projection fixes globally symmetric inputs, and the left one is erased by
the outer global projection. This is a local-prefix statement; it does not
remove an intermediate global projection from individual placement-pair
summands. -/
theorem localSymmetricCompression_disappears_after_globalCompression
    {r t : ℕ}
    (T : HilbertTensorPower ℂ H r →L[ℂ] HilbertTensorPower ℂ H r) :
    (symProjToSector (r + t)).comp
        ((prefixTensorLift (H := H) (r := r) (t := t)
          (extendSymKernel ((symProjToSector r).comp
            (T.comp (SymSector ℂ H r).subtypeL)))).comp
          (SymSector ℂ H (r + t)).subtypeL) =
      (symProjToSector (r + t)).comp
        ((prefixTensorLift (H := H) (r := r) (t := t) T).comp
          (SymSector ℂ H (r + t)).subtypeL) := by
  let P := symProj ℂ H r
  have hext : extendSymKernel
      ((symProjToSector r).comp (T.comp (SymSector ℂ H r).subtypeL)) =
        (P.comp T).comp P := by
    ext x
    rfl
  ext x
  change symProj ℂ H (r + t)
      (prefixTensorLift (H := H) (r := r) (t := t)
        (extendSymKernel ((symProjToSector r).comp
          (T.comp (SymSector ℂ H r).subtypeL))) x.1) =
    symProj ℂ H (r + t)
      (prefixTensorLift (H := H) (r := r) (t := t) T x.1)
  rw [hext, ← prefixTensorLift_comp (P.comp T) P,
    ← prefixTensorLift_comp P T]
  simp only [ContinuousLinearMap.comp_apply]
  rw [prefixTensorLift_symProj_fixes_globalSector (r := r) (t := t) x]
  have houter (y : HilbertTensorPower ℂ H (r + t)) :
      symProj ℂ H (r + t)
          (prefixTensorLift (H := H) (r := r) (t := t)
            (symProj ℂ H r) y) = symProj ℂ H (r + t) y := by
    have h := congrArg (fun F : HilbertTensorPower ℂ H (r + t) →L[ℂ]
        HilbertTensorPower ℂ H (r + t) => F y)
      (symProj_comp_prefixTensorLift_symProj (H := H) r t)
    simpa [ContinuousLinearMap.comp_apply] using h
  rw [houter]

/-- The uncompressed ordered pair operator on the literal N-slot tensor
power, obtained by casting each source placement to `Fin N` slots. -/
def ambientRawPairOperator (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N)
    (z : ActualPairPlacement N p q)
    (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) :
    HilbertTensorPower ℂ H N →L[ℂ] HilbertTensorPower ℂ H N :=
  (castTensorOperator (Nat.add_sub_of_le hp) (subsetPlacement z.1 A)).comp
    (castTensorOperator (Nat.add_sub_of_le hq) (subsetPlacement z.2 B))

/-- Compress one raw ambient pair contribution globally, after its full
ordered operator product has been formed. -/
def globallyCompressedRawPairTerm (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N)
    (z : ActualPairPlacement N p q)
    (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) :
    SymSector ℂ H N →L[ℂ] SymSector ℂ H N :=
  (symProjToSector N).comp
    ((ambientRawPairOperator N p q hp hq z A B).comp
      (SymSector ℂ H N).subtypeL)

/-- The unnormalized globally compressed raw pair sum on one ambient union
fiber. -/
def globallyCompressedAmbientFiberSum
    (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N)
    (b : PairPlacementBase N p q)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    SymSector ℂ H N →L[ℂ] SymSector ℂ H N :=
  ∑ z : pairUnionFiber hp hq b,
    globallyCompressedRawPairTerm N p q hp hq z.1 A Bop

/-- The globally compressed raw pair contribution of one actual union fiber,
normalized by the number of canonical pair configurations in that fiber.
This is the operator-valued object to be identified with placement of the
averaged local overlap kernel. -/
def globallyCompressedAmbientFiberContribution
    (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N)
    (b : PairPlacementBase N p q)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    SymSector ℂ H N →L[ℂ] SymSector ℂ H N :=
  ((Fintype.card (pairUnionFiber hp hq b) : ℂ)⁻¹) •
    globallyCompressedAmbientFiberSum N p q hp hq b A Bop

/-- Place the N-independent averaged overlap kernel on the literal ambient
union selected by `b`, with its output compressed to the global symmetric
sector. -/
def averagedOverlapKernelPlacement
    (N p q : ℕ)
    (b : PairPlacementBase N p q)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    SymSector ℂ H N →L[ℂ] SymSector ℂ H N := by
  let s := overlapSizeOfBase b
  let hsP := overlapLeftBound b
  let hsQ := overlapRightBound b
  let r := unionSize p q s
  have hr : r ≤ N := pairPlacementBase_unionSize_le_N b
  have hU : b.1.2.card = r := b.2
  exact arbitraryNSectorSubsetPlacement N r hr
    (sourcePlacementOfSlots hr b.1.2 hU)
    (averagedOverlapKernel hsP hsQ A Bop)

/-- Transport a permutation back along the canonical cast between equal
finite slot types. -/
def castPermBack {m n : ℕ} (h : m = n) (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin m) :=
  ((Equiv.cast (congrArg Fin h)).trans σ).trans
    (Equiv.cast (congrArg Fin h)).symm

theorem castPermBack_inv {m n : ℕ} (h : m = n) (σ : Equiv.Perm (Fin n)) :
    castPermBack h σ⁻¹ = (castPermBack h σ)⁻¹ := by
  ext x
  simp [castPermBack]

theorem canonicalRightDimensionEq (p q s : ℕ) (hsp : s ≤ p) (hsq : s ≤ q) :
    q + (p - s) = p + (q - s) := by omega

/-- A permutation of ambient slots can be chosen to carry the canonical
enumeration of any fixed union onto the first `r` ambient slots. -/
theorem exists_unionSlotEmbedding_to_prefix_perm {N r : ℕ}
    (hr : r ≤ N) (U : Finset (Fin N)) (hU : U.card = r) :
    ∃ σ : Equiv.Perm (Fin N),
      ∀ i : Fin r, σ (unionSlotEmbedding U hU i) = Fin.castLE hr i := by
  let eU := unionSlotEmbedding U hU
  let ep : Fin r ↪ Fin N := Fin.castLEEmb hr
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair eU ep
    eU.injective ep.injective
  exact ⟨σ, hσ⟩

/-- Under the chosen ambient permutation, every canonical subset of a union
is carried to the corresponding subset of the first `r` slots. -/
theorem perm_map_pushUnionSlots_eq_prefix {N r : ℕ}
    (hr : r ≤ N) (U : Finset (Fin N)) (hU : U.card = r)
    (σ : Equiv.Perm (Fin N))
    (hσ : ∀ i : Fin r,
      σ (unionSlotEmbedding U hU i) = Fin.castLE hr i)
    (S : Finset (Fin r)) :
    (pushUnionSlots U hU S).map σ.toEmbedding =
      S.map (Fin.castLEEmb hr) := by
  classical
  ext j
  simp only [Finset.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
    exact ⟨i, hi, (hσ i).symm⟩
  · rintro ⟨i, hi, hj⟩
    refine ⟨unionSlotEmbedding U hU i, ?_, ?_⟩
    · exact Finset.mem_map.mpr ⟨i, hi, rfl⟩
    · exact (hσ i).trans hj

private theorem finCast_proof_irrel {m n : ℕ} (h₁ h₂ : m = n) :
    Equiv.cast (congrArg Fin h₁) = Equiv.cast (congrArg Fin h₂) := by
  have hh : h₁ = h₂ := Subsingleton.elim _ _
  cases hh
  rfl

/-- Relabel a canonical local overlap configuration by one permutation of its
union slots. -/
def relabelOverlapConfiguration {p q s : ℕ} (hsp : s ≤ p) (hsq : s ≤ q)
    (σ : Equiv.Perm (Fin (p + (q - s))))
    (C : OverlapConfiguration p q s hsp hsq) :
    OverlapConfiguration p q s hsp hsq := by
  let e := overlapSlotEquiv hsp hsq
  let Q := C.right.1.map e.toEmbedding
  let L' := C.left.1.map σ.toEmbedding
  let Q' := Q.map σ.toEmbedding
  let hqr := canonicalRightDimensionEq p q s hsp hsq
  let τ := castPermBack hqr σ
  let R' := C.right.1.map τ.toEmbedding
  have hR' : R'.map e.toEmbedding = Q' := by
    dsimp [R', Q', Q, τ, hqr, e]
    rw [Finset.map_map, Finset.map_map]
    congr 1
    ext x
    simp [castPermBack, overlapSlotEquiv]
  refine ⟨⟨L', by simp [L', C.left.2]⟩,
    ⟨R', ?_⟩, ?_, ?_⟩
  · dsimp [R']
    rw [Finset.card_map]
    exact C.right.2
  · rw [hR']
    change (L' ∩ Q').card = s
    dsimp [L', Q', Q]
    rw [← Finset.map_inter, Finset.card_map]
    exact C.overlap_card
  · rw [hR']
    change L' ∪ Q' = Finset.univ
    dsimp [L', Q']
    rw [← Finset.map_union]
    rw [C.covers_union]
    simp

omit [CompleteSpace H] in
private theorem permHilbertIsometry_mul_apply {n : ℕ}
    (σ τ : Equiv.Perm (Fin n)) (x : HilbertTensorPower ℂ H n) :
    permHilbertIsometry (𝕜 := ℂ) (E := H) σ
        (permHilbertIsometry (𝕜 := ℂ) (E := H) τ x) =
      permHilbertIsometry (𝕜 := ℂ) (E := H) (σ * τ) x := by
  have h := map_mul (permHom ℂ H n) σ τ
  simpa [permHom] using (congrArg (fun f : _ ≃ₗᵢ[ℂ] _ => f x) h).symm

/-- Conjugation by a slot permutation transports a placement permutation by
left multiplication. -/
theorem permutedPlacement_conjugate {p q : ℕ}
    (σ τ : Equiv.Perm (Fin (p + q)))
    (A : BoundedSymmetricKernel H p) :
    ((permRep ℂ H (p + q) σ : HilbertTensorPower ℂ H (p + q) →L[ℂ]
        HilbertTensorPower ℂ H (p + q)).comp (permutedPlacement τ A)).comp
        (permRep ℂ H (p + q) σ⁻¹ : HilbertTensorPower ℂ H (p + q) →L[ℂ]
          HilbertTensorPower ℂ H (p + q)) = permutedPlacement (σ * τ) A := by
  ext x
  simp [permutedPlacement, permRep_apply, permHilbertIsometry_mul_apply]

private theorem finset_map_perm_mul {α : Type*} [DecidableEq α] (s : Finset α)
    (σ τ : Equiv.Perm α) :
    s.map (σ * τ).toEmbedding = (s.map τ.toEmbedding).map σ.toEmbedding := by
  rw [Finset.map_map]
  congr 1

/-- The subset placement transforms covariantly when its selected slots are
relabelled. -/
def relabelPlacementSubset {p q : ℕ} (σ : Equiv.Perm (Fin (p + q)))
    (S : PlacementSubset p q) : PlacementSubset p q :=
  ⟨S.1.map σ.toEmbedding, by simpa using S.2⟩

theorem permutedPlacement_conjugate_subset {p q : ℕ}
    (σ : Equiv.Perm (Fin (p + q))) (S : PlacementSubset p q)
    (A : BoundedSymmetricKernel H p) :
    ((permRep ℂ H (p + q) σ : HilbertTensorPower ℂ H (p + q) →L[ℂ]
        HilbertTensorPower ℂ H (p + q)).comp (subsetPlacement S A)).comp
        (permRep ℂ H (p + q) σ⁻¹ : HilbertTensorPower ℂ H (p + q) →L[ℂ]
          HilbertTensorPower ℂ H (p + q)) =
      subsetPlacement (relabelPlacementSubset σ S) A := by
  let T := relabelPlacementSubset σ S
  have himage : placementSubsetOfPerm (σ * subsetRepresentative S) = T := by
    apply Subtype.ext
    change (firstPositions (p := p) (q := q)).map
        (σ * subsetRepresentative S).toEmbedding = T.1
    rw [finset_map_perm_mul]
    simpa [T, relabelPlacementSubset, placementSubsetOfPerm] using
      congrArg (fun z : PlacementSubset p q => z.1) (subsetRepresentative_maps S)
  calc
    _ = permutedPlacement (σ * subsetRepresentative S) A := by
      simpa [subsetPlacement] using permutedPlacement_conjugate σ
        (subsetRepresentative S) A
    _ = subsetPlacement T A :=
      permutedPlacement_eq_subsetPlacement _ T himage A

omit [CompleteSpace H] in
theorem castTensorOperator_conjugate {m n : ℕ} (h : m = n)
    (σ : Equiv.Perm (Fin n))
    (T : HilbertTensorPower ℂ H m →L[ℂ] HilbertTensorPower ℂ H m) :
    ((permRep ℂ H n σ : HilbertTensorPower ℂ H n →L[ℂ]
        HilbertTensorPower ℂ H n).comp (castTensorOperator h T)).comp
        (permRep ℂ H n σ⁻¹ : HilbertTensorPower ℂ H n →L[ℂ]
          HilbertTensorPower ℂ H n) =
      castTensorOperator h
        (((permRep ℂ H m (castPermBack h σ) : HilbertTensorPower ℂ H m →L[ℂ]
            HilbertTensorPower ℂ H m).comp T).comp
          (permRep ℂ H m (castPermBack h σ)⁻¹ : HilbertTensorPower ℂ H m →L[ℂ]
            HilbertTensorPower ℂ H m)) := by
  cases h
  simp [castTensorOperator, castPermBack]

theorem castSubsetPlacement_conjugate {n p q : ℕ}
    (h : p + q = n) (σ : Equiv.Perm (Fin n))
    (S : PlacementSubset p q) (A : BoundedSymmetricKernel H p) :
    ((permRep ℂ H n σ : HilbertTensorPower ℂ H n →L[ℂ]
        HilbertTensorPower ℂ H n).comp
      (castTensorOperator h (subsetPlacement S A))).comp
      (permRep ℂ H n σ⁻¹ : HilbertTensorPower ℂ H n →L[ℂ]
        HilbertTensorPower ℂ H n) =
      castTensorOperator h
        (subsetPlacement (relabelPlacementSubset (castPermBack h σ) S) A) := by
  rw [castTensorOperator_conjugate h σ (subsetPlacement S A)]
  rw [permutedPlacement_conjugate_subset (castPermBack h σ) S A]

theorem arbitraryNSectorSubsetPlacement_relabel
    (N r : ℕ) (hr : r ≤ N) (σ : Equiv.Perm (Fin N))
    (S : PlacementSubset r (N - r)) (K : BoundedSymmetricKernel H r) :
    arbitraryNSectorSubsetPlacement N r hr
        (relabelPlacementSubset (castPermBack (Nat.add_sub_of_le hr) σ) S) K =
      arbitraryNSectorSubsetPlacement N r hr S K := by
  let h := Nat.add_sub_of_le hr
  let τ := castPermBack h σ
  have hinner :
      actualSectorSubsetPlacement (relabelPlacementSubset τ S) K =
        actualSectorSubsetPlacement S K := by
    unfold actualSectorSubsetPlacement
    rw [← permutedPlacement_conjugate_subset τ S K]
    rw [← ContinuousLinearMap.comp_assoc]
    exact PlacementCovariance.symmetricCompression_conj_eq τ (subsetPlacement S K)
  unfold arbitraryNSectorSubsetPlacement
  exact congrArg (castSymSectorOperator h) hinner

/-- Relabel both source subsets by the same ambient permutation, transported
back along their canonical particle-count casts. -/
def relabelActualPair {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N)
    (σ : Equiv.Perm (Fin N)) (z : ActualPairPlacement N p q) :
    ActualPairPlacement N p q :=
  (relabelPlacementSubset (castPermBack (Nat.add_sub_of_le hp) σ) z.1,
    relabelPlacementSubset (castPermBack (Nat.add_sub_of_le hq) σ) z.2)

private theorem castSlotSet_relabelPlacementSubset {n p q : ℕ}
    (h : p + q = n) (σ : Equiv.Perm (Fin n))
    (S : PlacementSubset p q) :
    castSlotSet h (relabelPlacementSubset (castPermBack h σ) S).1 =
      (castSlotSet h S.1).map σ.toEmbedding := by
  cases h
  simp [castSlotSet, relabelPlacementSubset, castPermBack]

theorem leftSlots_relabelActualPair
    (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N)
    (σ : Equiv.Perm (Fin N)) (z : ActualPairPlacement N p q) :
    leftSlots hp (relabelActualPair hp hq σ z) =
      (leftSlots hp z).map σ.toEmbedding := by
  simp [leftSlots, relabelActualPair, castSlotSet_relabelPlacementSubset]

theorem rightSlots_relabelActualPair
    (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N)
    (σ : Equiv.Perm (Fin N)) (z : ActualPairPlacement N p q) :
    rightSlots hq (relabelActualPair hp hq σ z) =
      (rightSlots hq z).map σ.toEmbedding := by
  simp [rightSlots, relabelActualPair, castSlotSet_relabelPlacementSubset]

/-- Relabel an ambient union key by the same permutation acting on its slot
set; its overlap size is unchanged. -/
def relabelPairPlacementBase {N p q : ℕ}
    (σ : Equiv.Perm (Fin N)) (b : PairPlacementBase N p q) :
    PairPlacementBase N p q := by
  refine ⟨(b.1.1, b.1.2.map σ.toEmbedding), ?_⟩
  simpa using b.2

theorem sourcePlacementOfSlots_relabel
    {N r : ℕ} (hr : r ≤ N) (σ : Equiv.Perm (Fin N))
    (U : Finset (Fin N)) (hU : U.card = r) :
    sourcePlacementOfSlots hr (U.map σ.toEmbedding)
        (by rw [Finset.card_map]; exact hU) =
      relabelPlacementSubset (castPermBack (Nat.add_sub_of_le hr) σ)
        (sourcePlacementOfSlots hr U hU) := by
  apply Subtype.ext
  apply Finset.map_injective (Equiv.cast
    (congrArg Fin (Nat.add_sub_of_le hr))).toEmbedding
  calc
    _ = U.map σ.toEmbedding :=
      slots_sourcePlacementOfSlots hr (U.map σ.toEmbedding)
        (by rw [Finset.card_map]; exact hU)
    _ = (castSlotSet (Nat.add_sub_of_le hr)
        (sourcePlacementOfSlots hr U hU).1).map σ.toEmbedding := by
      rw [slots_sourcePlacementOfSlots]
    _ = castSlotSet (Nat.add_sub_of_le hr)
        (relabelPlacementSubset (castPermBack (Nat.add_sub_of_le hr) σ)
          (sourcePlacementOfSlots hr U hU)).1 :=
      (castSlotSet_relabelPlacementSubset (Nat.add_sub_of_le hr) σ
        (sourcePlacementOfSlots hr U hU)).symm

/-- The placed averaged kernel is independent of which ambient union subset
is used to represent its `r` active slots. -/
theorem averagedOverlapKernelPlacement_relabel
    (N p q : ℕ) (σ : Equiv.Perm (Fin N))
    (b : PairPlacementBase N p q)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    averagedOverlapKernelPlacement N p q (relabelPairPlacementBase σ b) A Bop =
      averagedOverlapKernelPlacement N p q b A Bop := by
  let s := overlapSizeOfBase b
  let r := unionSize p q s
  have hr : r ≤ N := pairPlacementBase_unionSize_le_N b
  have hU : b.1.2.card = r := b.2
  change arbitraryNSectorSubsetPlacement N r hr
      (sourcePlacementOfSlots hr (b.1.2.map σ.toEmbedding)
        (by rw [Finset.card_map]; exact hU))
      (averagedOverlapKernel (overlapLeftBound b)
        (overlapRightBound b) A Bop) =
    arbitraryNSectorSubsetPlacement N r hr
      (sourcePlacementOfSlots hr b.1.2 hU)
      (averagedOverlapKernel (overlapLeftBound b)
        (overlapRightBound b) A Bop)
  rw [sourcePlacementOfSlots_relabel]
  exact arbitraryNSectorSubsetPlacement_relabel N r hr σ
    (sourcePlacementOfSlots hr b.1.2 hU)
    (averagedOverlapKernel (overlapLeftBound b)
      (overlapRightBound b) A Bop)

theorem pairPlacementKey_relabelActualPair
    (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N)
    (σ : Equiv.Perm (Fin N)) (z : ActualPairPlacement N p q) :
    pairPlacementKey hp hq (relabelActualPair hp hq σ z) =
      relabelPairPlacementBase σ (pairPlacementKey hp hq z) := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    change (leftSlots hp (relabelActualPair hp hq σ z) ∩
        rightSlots hq (relabelActualPair hp hq σ z)).card =
      (leftSlots hp z ∩ rightSlots hq z).card
    rw [leftSlots_relabelActualPair, rightSlots_relabelActualPair,
      ← Finset.map_inter]
    simp
  · change leftSlots hp (relabelActualPair hp hq σ z) ∪
        rightSlots hq (relabelActualPair hp hq σ z) =
      (leftSlots hp z ∪ rightSlots hq z).map σ.toEmbedding
    rw [leftSlots_relabelActualPair, rightSlots_relabelActualPair,
      ← Finset.map_union]

theorem relabelPairPlacementBase_inv {N p q : ℕ}
    (σ : Equiv.Perm (Fin N)) (b : PairPlacementBase N p q) :
    relabelPairPlacementBase σ⁻¹ (relabelPairPlacementBase σ b) = b := by
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext rfl
  · simp [relabelPairPlacementBase, Finset.map_map]

/-- The union key with the same overlap and the first `r` ambient slots. -/
def canonicalPrefixPairBase {N p q : ℕ}
    (b : PairPlacementBase N p q) : PairPlacementBase N p q := by
  let r := unionSize p q b.1.1
  have hr : r ≤ N := pairPlacementBase_unionSize_le_N b
  refine ⟨(b.1.1, Finset.univ.map (Fin.castLEEmb hr)), ?_⟩
  simp only [Finset.card_map, Finset.card_univ, Fintype.card_fin]
  rfl

theorem exists_relabel_pairBase_eq_canonicalPrefix
    {N p q : ℕ} (b : PairPlacementBase N p q) :
    ∃ σ : Equiv.Perm (Fin N),
      relabelPairPlacementBase σ b = canonicalPrefixPairBase b := by
  let r := unionSize p q b.1.1
  have hr : r ≤ N := pairPlacementBase_unionSize_le_N b
  have hU : b.1.2.card = r := b.2
  obtain ⟨σ, hσ⟩ := exists_unionSlotEmbedding_to_prefix_perm hr b.1.2 hU
  have hset : b.1.2.map σ.toEmbedding =
      Finset.univ.map (Fin.castLEEmb hr) := by
    calc
      _ = (pushUnionSlots b.1.2 hU Finset.univ).map σ.toEmbedding := by
        rw [pushUnionSlots_univ]
      _ = Finset.univ.map (Fin.castLEEmb hr) :=
        perm_map_pushUnionSlots_eq_prefix hr b.1.2 hU σ hσ Finset.univ
  refine ⟨σ, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    rfl
  · exact hset

theorem relabelActualPair_inv (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N)
    (σ : Equiv.Perm (Fin N)) (z : ActualPairPlacement N p q) :
    relabelActualPair hp hq σ⁻¹ (relabelActualPair hp hq σ z) = z := by
  apply Prod.ext <;>
    apply Subtype.ext <;>
    simp [relabelActualPair, relabelPlacementSubset, Finset.map_map,
      castPermBack_inv]

/-- Relabelling restricts to an equivalence between the corresponding
ambient union fibers. -/
def pairUnionFiberRelabelEquiv {N p q : ℕ}
    (hp : p ≤ N) (hq : q ≤ N) (σ : Equiv.Perm (Fin N))
    (b : PairPlacementBase N p q) :
    pairUnionFiber hp hq b ≃
      pairUnionFiber hp hq (relabelPairPlacementBase σ b) where
  toFun z := by
    refine ⟨relabelActualPair hp hq σ z.1, ?_⟩
    calc
      pairPlacementKey hp hq (relabelActualPair hp hq σ z.1) =
          relabelPairPlacementBase σ (pairPlacementKey hp hq z.1) :=
        pairPlacementKey_relabelActualPair N p q hp hq σ z.1
      _ = relabelPairPlacementBase σ b :=
        congrArg (relabelPairPlacementBase σ) z.2
  invFun z := by
    refine ⟨relabelActualPair hp hq σ⁻¹ z.1, ?_⟩
    calc
      pairPlacementKey hp hq (relabelActualPair hp hq σ⁻¹ z.1) =
          relabelPairPlacementBase σ⁻¹ (pairPlacementKey hp hq z.1) :=
        pairPlacementKey_relabelActualPair N p q hp hq σ⁻¹ z.1
      _ = relabelPairPlacementBase σ⁻¹
          (relabelPairPlacementBase σ b) :=
        congrArg (relabelPairPlacementBase σ⁻¹) z.2
      _ = b := relabelPairPlacementBase_inv σ b
  left_inv z := by
    apply Subtype.ext
    exact relabelActualPair_inv N p q hp hq σ z.1
  right_inv z := by
    apply Subtype.ext
    simpa [relabelActualPair_inv] using
      relabelActualPair_inv N p q hp hq σ⁻¹ z.1

/-- The ordered raw pair product is covariant under a common ambient slot
permutation. -/
theorem ambientRawPairOperator_conjugate
    (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N)
    (σ : Equiv.Perm (Fin N)) (z : ActualPairPlacement N p q)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    ((permRep ℂ H N σ : HilbertTensorPower ℂ H N →L[ℂ]
        HilbertTensorPower ℂ H N).comp
      (ambientRawPairOperator N p q hp hq z A Bop)).comp
      (permRep ℂ H N σ⁻¹ : HilbertTensorPower ℂ H N →L[ℂ]
        HilbertTensorPower ℂ H N) =
      ambientRawPairOperator N p q hp hq
        (relabelActualPair hp hq σ z) A Bop := by
  let U : HilbertTensorPower ℂ H N →L[ℂ] HilbertTensorPower ℂ H N :=
    permRep ℂ H N σ
  let Ui : HilbertTensorPower ℂ H N →L[ℂ] HilbertTensorPower ℂ H N :=
    permRep ℂ H N σ⁻¹
  have hcancel_apply (x : HilbertTensorPower ℂ H N) : Ui (U x) = x := by
    change permHilbertIsometry (𝕜 := ℂ) (E := H) σ⁻¹
      (permHilbertIsometry (𝕜 := ℂ) (E := H) σ x) = x
    calc
      _ = permHilbertIsometry (𝕜 := ℂ) (E := H) (σ⁻¹ * σ) x :=
        permHilbertIsometry_mul_apply σ⁻¹ σ x
      _ = permHilbertIsometry (𝕜 := ℂ) (E := H) 1 x := by rw [inv_mul_cancel]
      _ = x := by
        have hone := map_one (permHom ℂ H N)
        simpa [permHom] using
          congrArg (fun f : _ ≃ₗᵢ[ℂ] _ => f x) hone
  rw [ambientRawPairOperator, ambientRawPairOperator]
  change (U.comp
      ((castTensorOperator (Nat.add_sub_of_le hp) (subsetPlacement z.1 A)).comp
        (castTensorOperator (Nat.add_sub_of_le hq) (subsetPlacement z.2 Bop)))).comp Ui = _
  calc
    _ = ((U.comp
          (castTensorOperator (Nat.add_sub_of_le hp) (subsetPlacement z.1 A))).comp Ui).comp
        ((U.comp
          (castTensorOperator (Nat.add_sub_of_le hq) (subsetPlacement z.2 Bop))).comp Ui) := by
      ext x
      simp only [ContinuousLinearMap.comp_apply]
      rw [hcancel_apply]
    _ = _ := by
      rw [castSubsetPlacement_conjugate, castSubsetPlacement_conjugate]
      rfl

/-- Global symmetric compression erases the common slot relabelling of an
ordered raw pair term. -/
theorem globallyCompressedRawPairTerm_conjugate
    (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N)
    (σ : Equiv.Perm (Fin N)) (z : ActualPairPlacement N p q)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    globallyCompressedRawPairTerm N p q hp hq
        (relabelActualPair hp hq σ z) A Bop =
      globallyCompressedRawPairTerm N p q hp hq z A Bop := by
  unfold globallyCompressedRawPairTerm
  rw [← ambientRawPairOperator_conjugate]
  rw [← ContinuousLinearMap.comp_assoc]
  exact PlacementCovariance.symmetricCompression_conj_eq σ
    (ambientRawPairOperator N p q hp hq z A Bop)

/-- The complete globally compressed contribution of a fiber is invariant
under relabelling its ambient union key. -/
theorem globallyCompressedAmbientFiberContribution_relabel
    (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N)
    (σ : Equiv.Perm (Fin N)) (b : PairPlacementBase N p q)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    globallyCompressedAmbientFiberContribution N p q hp hq
        (relabelPairPlacementBase σ b) A Bop =
      globallyCompressedAmbientFiberContribution N p q hp hq b A Bop := by
  classical
  let E := pairUnionFiberRelabelEquiv hp hq σ b
  change (Fintype.card (pairUnionFiber hp hq (relabelPairPlacementBase σ b)) : ℂ)⁻¹ •
      (∑ z : pairUnionFiber hp hq (relabelPairPlacementBase σ b),
        globallyCompressedRawPairTerm N p q hp hq z.1 A Bop) =
    (Fintype.card (pairUnionFiber hp hq b) : ℂ)⁻¹ •
      (∑ z : pairUnionFiber hp hq b,
        globallyCompressedRawPairTerm N p q hp hq z.1 A Bop)
  have hcard := Fintype.card_congr E
  rw [hcard]
  congr 1
  calc
    _ = ∑ z : pairUnionFiber hp hq (relabelPairPlacementBase σ b),
          globallyCompressedRawPairTerm N p q hp hq (E.symm z).1 A Bop := by
      apply Finset.sum_congr rfl
      intro z hz
      change globallyCompressedRawPairTerm N p q hp hq z.1 A Bop =
        globallyCompressedRawPairTerm N p q hp hq
          (relabelActualPair hp hq σ⁻¹ z.1) A Bop
      exact (globallyCompressedRawPairTerm_conjugate N p q hp hq
        σ⁻¹ z.1 A Bop).symm
    _ = ∑ z : pairUnionFiber hp hq b,
          globallyCompressedRawPairTerm N p q hp hq z.1 A Bop := by
      symm
      simpa [E] using
        (Equiv.sum_comp E
          (fun z => globallyCompressedRawPairTerm N p q hp hq
            (E.symm z).1 A Bop))

/-- It is enough to identify the fiber contribution when its union is the
canonical prefix: arbitrary ambient unions are permutation-conjugate to it. -/
theorem globallyCompressedAmbientFiberContribution_eq_canonicalPrefix
    {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N)
    (b : PairPlacementBase N p q)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    globallyCompressedAmbientFiberContribution N p q hp hq b A Bop =
      globallyCompressedAmbientFiberContribution N p q hp hq
        (canonicalPrefixPairBase b) A Bop := by
  obtain ⟨σ, hσ⟩ := exists_relabel_pairBase_eq_canonicalPrefix b
  calc
    _ = globallyCompressedAmbientFiberContribution N p q hp hq
        (relabelPairPlacementBase σ b) A Bop :=
      (globallyCompressedAmbientFiberContribution_relabel
        N p q hp hq σ b A Bop).symm
    _ = _ := by rw [hσ]

/-- The requested fiber-operator equality reduces exactly to the case where
the union is the canonical prefix; both sides are invariant under the same
ambient slot relabelling. -/
theorem fiberOperatorIdentity_iff_canonicalPrefix
    {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N)
    (b : PairPlacementBase N p q)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    (globallyCompressedAmbientFiberContribution N p q hp hq b A Bop =
      averagedOverlapKernelPlacement N p q b A Bop) ↔
    (globallyCompressedAmbientFiberContribution N p q hp hq
        (canonicalPrefixPairBase b) A Bop =
      averagedOverlapKernelPlacement N p q (canonicalPrefixPairBase b) A Bop) := by
  obtain ⟨σ, hσ⟩ := exists_relabel_pairBase_eq_canonicalPrefix b
  have hleft := globallyCompressedAmbientFiberContribution_eq_canonicalPrefix
    hp hq b A Bop
  have hright :
      averagedOverlapKernelPlacement N p q (canonicalPrefixPairBase b) A Bop =
        averagedOverlapKernelPlacement N p q b A Bop := by
    rw [← hσ]
    exact averagedOverlapKernelPlacement_relabel N p q σ b A Bop
  rw [hleft, hright]

private theorem relabelRightPlacementSubset {p q s : ℕ}
    (hsp : s ≤ p) (hsq : s ≤ q)
    (σ : Equiv.Perm (Fin (p + (q - s))))
    (C : OverlapConfiguration p q s hsp hsq) :
    (relabelOverlapConfiguration hsp hsq σ C).right =
      relabelPlacementSubset (castPermBack
        (canonicalRightDimensionEq p q s hsp hsq) σ) C.right := by
  apply Subtype.ext
  rfl

theorem rightPlacement_relabel_conjugate {p q s : ℕ}
    (hsp : s ≤ p) (hsq : s ≤ q)
    (σ : Equiv.Perm (Fin (p + (q - s))))
    (C : OverlapConfiguration p q s hsp hsq)
    (Bop : BoundedSymmetricKernel H q) :
    ((permRep ℂ H (p + (q - s)) σ : HilbertTensorPower ℂ H (p + (q - s)) →L[ℂ]
        HilbertTensorPower ℂ H (p + (q - s))).comp (rightPlacement C Bop)).comp
        (permRep ℂ H (p + (q - s)) σ⁻¹ : HilbertTensorPower ℂ H (p + (q - s)) →L[ℂ]
          HilbertTensorPower ℂ H (p + (q - s))) =
      rightPlacement (relabelOverlapConfiguration hsp hsq σ C) Bop := by
  let h : q + (p - s) = p + (q - s) := by omega
  let τ := castPermBack h σ
  have hset := relabelRightPlacementSubset hsp hsq σ C
  rw [rightPlacement, rightPlacement]
  rw [castTensorOperator_conjugate h σ (subsetPlacement C.right Bop)]
  rw [permutedPlacement_conjugate_subset τ C.right Bop]
  rw [hset]

/-- The full sum of sector-compressed pair placements is the single global
compression of the full uncompressed pair sum.  This is deliberately a
full-sum statement: it does not assert summandwise elimination of the middle
symmetric projection. -/
theorem actualPairSectorSum_eq_globalRawCompression
    (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    (∑ S : PlacementSubset p (N - p),
      ∑ T : PlacementSubset q (N - q),
        (arbitraryNSectorSubsetPlacement N p hp S A).comp
          (arbitraryNSectorSubsetPlacement N q hq T Bop)) =
      (symProjToSector N).comp
        ((rawSubsetPlacementSum N p hp A).comp
          ((rawSubsetPlacementSum N q hq Bop).comp
            (SymSector ℂ H N).subtypeL)) := by
  classical
  exact PlacementGrouping.actualPairSum_eq_singleCompression
    N p q hp hq A Bop

/-- Reindex the globally compressed raw pair contributions by ambient union
keys and the canonical local overlap configurations. The raw products and the
global projection remain explicit for the subsequent slot-transport proof. -/
theorem globalRawPairSum_eq_canonicalFiberSum
    (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    (∑ z : ActualPairPlacement N p q,
        globallyCompressedRawPairTerm N p q hp hq z A Bop) =
      ∑ y : Σ b : PairPlacementBase N p q,
          OverlapConfiguration p q (overlapSizeOfBase b)
            (overlapLeftBound b) (overlapRightBound b),
        globallyCompressedRawPairTerm N p q hp hq
          ((pairPlacementCanonicalUnionEquiv hp hq).symm y) A Bop := by
  classical
  let E := pairPlacementCanonicalUnionEquiv hp hq
  let F := fun z : ActualPairPlacement N p q =>
    globallyCompressedRawPairTerm N p q hp hq z A Bop
  simpa [E, F] using Equiv.sum_comp E (fun y => F (E.symm y))

/-- The frozen local kernel is exactly the normalized finite sum of the
compressed ordered placement products on the canonical union slots. -/
theorem averagedOverlapKernel_eq_normalizedLocalFiberSum
    {p q s : ℕ} (hsp : s ≤ p) (hsq : s ≤ q)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    averagedOverlapKernel hsp hsq A Bop =
      ((Fintype.card (OverlapConfiguration p q s hsp hsq) : ℂ)⁻¹) •
        ∑ C : OverlapConfiguration p q s hsp hsq,
          (symProjToSector (unionSize p q s)).comp
            (((subsetPlacement C.left A).comp (rightPlacement C Bop)).comp
              (SymSector ℂ H (unionSize p q s)).subtypeL) := by
  exact averagedOverlapKernel_eq_concreteLocalPairAverage hsp hsq A Bop

/-- The unnormalized compressed local overlap sum is exactly the number of
canonical configurations times the frozen normalized overlap kernel.  This
is an operator-valued finite-average identity; it does not remove any
intermediate projection summandwise. -/
theorem localCompressedOverlapSum_eq_card_smul_averagedOverlapKernel
    {p q s : ℕ} (hsp : s ≤ p) (hsq : s ≤ q)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    (∑ C : OverlapConfiguration p q s hsp hsq,
        overlapFusionKernel C A Bop) =
      (Fintype.card (OverlapConfiguration p q s hsp hsq) : ℂ) •
        averagedOverlapKernel hsp hsq A Bop := by
  let n : ℂ := Fintype.card (OverlapConfiguration p q s hsp hsq)
  have hn : n ≠ 0 := by
    dsimp [n]
    rw [card_overlapConfiguration]
    exact_mod_cast Nat.ne_of_gt (Nat.mul_pos
      (Nat.choose_pos (show p ≤ p + (q - s) by omega))
      (Nat.choose_pos hsp))
  rw [averagedOverlapKernel_eq_average]
  change (∑ C : OverlapConfiguration p q s hsp hsq,
      overlapFusionKernel C A Bop) =
    n • (n⁻¹ • ∑ C : OverlapConfiguration p q s hsp hsq,
      overlapFusionKernel C A Bop)
  rw [smul_smul]
  simp [n, hn]

#print axioms QuantumNLS.PlacementFiberOperator.ambientRawPairOperator
#print axioms QuantumNLS.PlacementFiberOperator.globallyCompressedRawPairTerm
#print axioms QuantumNLS.PlacementFiberOperator.globallyCompressedAmbientFiberContribution
#print axioms QuantumNLS.PlacementFiberOperator.averagedOverlapKernelPlacement
#print axioms QuantumNLS.PlacementFiberOperator.prefixTensorLift
#print axioms QuantumNLS.PlacementFiberOperator.prefixTensorLift_comp
#print axioms QuantumNLS.PlacementFiberOperator.prefixTensorLift_add
#print axioms QuantumNLS.PlacementFiberOperator.prefixTensorLift_smul
#print axioms QuantumNLS.PlacementFiberOperator.prefixTensorLift_zero
#print axioms QuantumNLS.PlacementFiberOperator.prefixTensorLift_finset_sum
#print axioms QuantumNLS.PlacementFiberOperator.prefixTensorLift_sum
#print axioms QuantumNLS.PlacementFiberOperator.prefixTensorLift_permRep
#print axioms QuantumNLS.PlacementFiberOperator.prefixTensorLift_symProj_eq_groupAverage
#print axioms QuantumNLS.PlacementFiberOperator.prefixTensorLift_symProj_fixes_globalSector
#print axioms QuantumNLS.PlacementFiberOperator.symProj_comp_prefixTensorLift_symProj
#print axioms QuantumNLS.PlacementFiberOperator.localSymmetricCompression_disappears_after_globalCompression
#print axioms QuantumNLS.PlacementFiberOperator.castPermBack_inv
#print axioms QuantumNLS.PlacementFiberOperator.exists_unionSlotEmbedding_to_prefix_perm
#print axioms QuantumNLS.PlacementFiberOperator.perm_map_pushUnionSlots_eq_prefix
#print axioms QuantumNLS.PlacementFiberOperator.relabelOverlapConfiguration
#print axioms QuantumNLS.PlacementFiberOperator.permutedPlacement_conjugate
#print axioms QuantumNLS.PlacementFiberOperator.permutedPlacement_conjugate_subset
#print axioms QuantumNLS.PlacementFiberOperator.castTensorOperator_conjugate
#print axioms QuantumNLS.PlacementFiberOperator.castSubsetPlacement_conjugate
#print axioms QuantumNLS.PlacementFiberOperator.arbitraryNSectorSubsetPlacement_relabel
#print axioms QuantumNLS.PlacementFiberOperator.relabelActualPair
#print axioms QuantumNLS.PlacementFiberOperator.leftSlots_relabelActualPair
#print axioms QuantumNLS.PlacementFiberOperator.rightSlots_relabelActualPair
#print axioms QuantumNLS.PlacementFiberOperator.relabelPairPlacementBase
#print axioms QuantumNLS.PlacementFiberOperator.sourcePlacementOfSlots_relabel
#print axioms QuantumNLS.PlacementFiberOperator.averagedOverlapKernelPlacement_relabel
#print axioms QuantumNLS.PlacementFiberOperator.pairPlacementKey_relabelActualPair
#print axioms QuantumNLS.PlacementFiberOperator.relabelPairPlacementBase_inv
#print axioms QuantumNLS.PlacementFiberOperator.relabelActualPair_inv
#print axioms QuantumNLS.PlacementFiberOperator.pairUnionFiberRelabelEquiv
#print axioms QuantumNLS.PlacementFiberOperator.canonicalPrefixPairBase
#print axioms QuantumNLS.PlacementFiberOperator.exists_relabel_pairBase_eq_canonicalPrefix
#print axioms QuantumNLS.PlacementFiberOperator.ambientRawPairOperator_conjugate
#print axioms QuantumNLS.PlacementFiberOperator.globallyCompressedRawPairTerm_conjugate
#print axioms QuantumNLS.PlacementFiberOperator.globallyCompressedAmbientFiberContribution_relabel
#print axioms QuantumNLS.PlacementFiberOperator.globallyCompressedAmbientFiberContribution_eq_canonicalPrefix
#print axioms QuantumNLS.PlacementFiberOperator.fiberOperatorIdentity_iff_canonicalPrefix
#print axioms QuantumNLS.PlacementFiberOperator.rightPlacement_relabel_conjugate
#print axioms QuantumNLS.PlacementFiberOperator.actualPairSectorSum_eq_globalRawCompression
#print axioms QuantumNLS.PlacementFiberOperator.globalRawPairSum_eq_canonicalFiberSum
#print axioms QuantumNLS.PlacementFiberOperator.averagedOverlapKernel_eq_normalizedLocalFiberSum
#print axioms QuantumNLS.PlacementFiberOperator.localCompressedOverlapSum_eq_card_smul_averagedOverlapKernel

end QuantumNLS.PlacementFiberOperator
