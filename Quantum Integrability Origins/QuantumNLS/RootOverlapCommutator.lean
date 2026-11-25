import QuantumNLS.OverlapMoments
import QuantumNLS.PlacementFiberGrouping

/-!
# R-32EBD5C1 `lem:root-overlap`, stage 1: the commutator bound `eq:root-overlap-bound`
(ROOT_transfer_involution.tex:25)

Statement proved (`root_overlap_bound`): for `p, q ≤ N` and bounded kernels `A : Sym^p H → Sym^p H`,
`B : Sym^q H → Sym^q H` on a generic complex Hilbert space,
`N ‖[Q_{N,p}(A), Q_{N,q}(B)]‖ ≤ 2 p q ‖A‖ ‖B‖`, where `Q_{N,r}(·) = genericU_N_r N r` is the realized
DEF-009 operator `P_N (A ⊗ 1) P_N` on `Sym^N H` (KernelDefinition).  Also `commutator_norm_le`
(the same for `N ≥ 1` as `‖[Q_p,Q_q]‖ ≤ 2‖A‖‖B‖ pq/N`).
Bridge to the printed definition ("average over p-element subsets of tensor positions"):
frozen `genericU_eq_rawSubsetAverageOnSector` (PlacementGrouping) and
`rawSubsetAverage_eq_rawSubsetPlacementSum`: `Q_{N,p}(A)` is the restriction to `Sym^N` of
`C(N,p)⁻¹ Σ_S P_S(A)` over actual `p`-subsets `S` (`PlacementSubset`), `P_S = rawSubsetPlacement`.
Printed proof followed: expand both averages over independent subsets `I, J`; disjoint placements
commute (`rawPlacement_commute_of_disjoint`); every other commutator has norm `≤ 2‖A‖‖B‖`
(`norm_pair_comm_le`); the number of intersecting pairs is `C(N,p)C(N,q) ℙ(I∩J ≠ ∅)` with
`ℙ(I∩J≠∅) ≤ E|I∩J| = pq/N` (`card_badPairs_le`, from OverlapMoments `prob_intersect_le`).
The disjoint-commutation proof: transport by a slot permutation (`exists_perm_two_sets`,
`castSubsetPlacement_conjugate`) to the standard block configuration `A | B | rest`, where
`P_{[0,p)}(A) = firstPlacement` and `P_{middle}(B) = 1 ⊗ (B⊗1)` (`mid_eq`, a product-vector
computation with the block rearrangement `Psi`), which commute by `htmap_comp` (`first_comm_mid`).
Not part of stage 1: the fixed-order limit (eq:root-overlap-limit).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped InnerProductSpace TensorProduct
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements QuantumNLS.KernelDefinition
  QuantumNLS.PlacementFusion QuantumNLS.PlacementOverlap QuantumNLS.PlacementProduct
  QuantumNLS.PlacementCovariance QuantumNLS.PlacementGrouping QuantumNLS.PlacementUnionReindex
  QuantumNLS.PlacementFiberOperator

namespace QuantumNLS.RootOverlapCommutator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Product vector in the completed tensor power. -/
abbrev ptC {n : ℕ} (f : Fin n → H) : HilbertTensorPower ℂ H n :=
  ((ptprod f : AlgTensorPower ℂ H n) : HilbertTensorPower ℂ H n)

/-- Two bounded operators on a completed tensor power that agree on product vectors agree. -/
theorem eq_of_eq_on_ptC {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (F G : HilbertTensorPower ℂ H n →L[ℂ] X)
    (h : ∀ f : Fin n → H, F (ptC f) = G (ptC f)) : F = G := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq F.continuous G.continuous
  | ih a =>
    induction a using AlgTensorPower.induction_on with
    | smul_ptprod r f =>
      rw [UniformSpace.Completion.coe_smul, map_smul, map_smul, h f]
    | add x y hx hy =>
      rw [UniformSpace.Completion.coe_add, map_add, map_add, hx, hy]

/-- The canonical isometry between tensor powers along an equality of particle numbers. -/
def cIso {m n : ℕ} (h : m = n) : HilbertTensorPower ℂ H m ≃ₗᵢ[ℂ] HilbertTensorPower ℂ H n := by
  cases h
  exact LinearIsometryEquiv.refl ℂ _

theorem cIso_ptC {m n : ℕ} (h : m = n) (f : Fin m → H) :
    (cIso h (ptC f) : HilbertTensorPower ℂ H n) = ptC (fun i => f (Fin.cast h.symm i)) := by
  cases h
  rfl

theorem castTensorOperator_eq_conj {m n : ℕ} (h : m = n)
    (T : HilbertTensorPower ℂ H m →L[ℂ] HilbertTensorPower ℂ H m)
    (x : HilbertTensorPower ℂ H n) :
    castTensorOperator h T x = cIso h (T ((cIso h).symm x)) := by
  cases h
  rfl

section Blocks

/-- Block rearrangement `[B | A | C] ↦ [A | B | C]` of tensor positions. -/
def Psi (p q r : ℕ) : Fin (q + (p + r)) ≃ Fin (p + (q + r)) :=
  (finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv.symm)).trans
    (((Equiv.sumAssoc _ _ _).symm.trans
      ((Equiv.sumCongr (Equiv.sumComm _ _) (Equiv.refl _)).trans (Equiv.sumAssoc _ _ _))).trans
      ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv))

theorem Psi_castAdd (p q r : ℕ) (j : Fin q) :
    Psi p q r (Fin.castAdd (p + r) j) = Fin.natAdd p (Fin.castAdd r j) := by
  simp [Psi]

theorem Psi_natAdd_castAdd (p q r : ℕ) (l : Fin p) :
    Psi p q r (Fin.natAdd q (Fin.castAdd r l)) = Fin.castAdd (q + r) l := by
  simp [Psi]

theorem Psi_natAdd_natAdd (p q r : ℕ) (l : Fin r) :
    Psi p q r (Fin.natAdd q (Fin.natAdd p l)) = Fin.natAdd p (Fin.natAdd q l) := by
  simp [Psi]

/-- Rearranging blocks: `append a (append b c) ∘ Ψ = append b (append a c)`. -/
theorem append3_Psi {α : Type*} {p q r : ℕ} (a : Fin p → α) (b : Fin q → α) (c : Fin r → α) :
    (fun i => Fin.append a (Fin.append b c) (Psi p q r i)) = Fin.append b (Fin.append a c) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · rw [Psi_castAdd]; simp
  · refine Fin.addCases (fun l => ?_) (fun l => ?_) k
    · rw [Psi_natAdd_castAdd]; simp
    · rw [Psi_natAdd_natAdd]; simp

theorem eq_append3 {α : Type*} {p q r : ℕ} (f : Fin (p + (q + r)) → α) :
    f = Fin.append (fun i => f (Fin.castAdd (q + r) i))
      (Fin.append (fun i => f (Fin.natAdd p (Fin.castAdd r i)))
        (fun i => f (Fin.natAdd p (Fin.natAdd q i)))) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · simp
  · refine Fin.addCases (fun l => ?_) (fun l => ?_) k
    · simp
    · simp

end Blocks

theorem permRep_ptC {n : ℕ} (σ : Equiv.Perm (Fin n)) (g : Fin n → H) :
    (permRep ℂ H n σ : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n) (ptC g) =
      ptC (fun i => g (σ.symm i)) := by
  rw [permRep_apply, permHilbertIsometry_coe, permLinearEquiv_ptprod]

theorem cIso_symm_ptC {m n : ℕ} (h : m = n) (f : Fin n → H) :
    ((cIso h).symm (ptC f) : HilbertTensorPower ℂ H m) = ptC (fun i => f (Fin.cast h i)) := by
  cases h
  rfl

theorem split_symm_ptC {k m : ℕ} (a : Fin k → H) (b : Fin m → H) :
    (splitIsometry (𝕜 := ℂ) (E := H) k m).symm (htmul (ptC a) (ptC b)) =
      ptC (Fin.append a b) := by
  rw [LinearIsometryEquiv.symm_apply_eq]
  exact (splitIsometry_ptprod_append a b).symm

section Mid

/-- `1_p ⊗ (B ⊗ 1_r)` on the three blocks `p | q | r`. -/
def midPlacement (p q r : ℕ) (B : SymSector ℂ H q →L[ℂ] SymSector ℂ H q) :
    HilbertTensorPower ℂ H (p + (q + r)) →L[ℂ] HilbertTensorPower ℂ H (p + (q + r)) :=
  (splitIsometry (𝕜 := ℂ) (E := H) p (q + r)).symm.toLinearIsometry.toContinuousLinearMap.comp
    ((htmap (𝕜 := ℂ) (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ H p))
      (firstPlacement (q := r) B)).comp
      (splitIsometry (𝕜 := ℂ) (E := H) p (q + r)).toLinearIsometry.toContinuousLinearMap)

end Mid

section Mid2

variable {A F : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- `y ↦ x ⊗ y`. -/
def htR (x : A) : F →L[ℂ] HilbertTensor ℂ A F :=
  LinearMap.mkContinuous
    { toFun := fun y => htmul x y
      map_add' := fun y y' => htmul_add_right x y y'
      map_smul' := fun c y => htmul_smul_right c x y } ‖x‖ (by
    intro y
    simp only [LinearMap.coe_mk, AddHom.coe_mk, norm_htmul]
    exact le_refl _)

/-- `x ↦ x ⊗ y`. -/
def htL (y : F) : A →L[ℂ] HilbertTensor ℂ A F :=
  LinearMap.mkContinuous
    { toFun := fun x => htmul x y
      map_add' := fun x x' => htmul_add_left x x' y
      map_smul' := fun c x => htmul_smul_left c x y } ‖y‖ (by
    intro x
    simp only [LinearMap.coe_mk, AddHom.coe_mk, norm_htmul]
    exact le_of_eq (mul_comm _ _))

theorem htR_apply (x : A) (y : F) : htR x y = htmul x y := rfl
theorem htL_apply (y : F) (x : A) : htL y x = htmul x y := rfl

end Mid2

section Mid3

/-- The permutation of the `B`-native slots realizing `[B | A | C] → [A | B | C]`. -/
def tauB (p q r : ℕ) (h2 : q + (p + r) = p + (q + r)) : Equiv.Perm (Fin (q + (p + r))) :=
  (Psi p q r).trans (finCongr h2.symm)

theorem tauB_symm_apply (p q r : ℕ) (h2 : q + (p + r) = p + (q + r)) (i : Fin (q + (p + r))) :
    (tauB p q r h2).symm i = (Psi p q r).symm (Fin.cast h2 i) := by
  simp [tauB]

theorem insert_eq (p q r : ℕ) (h2 : q + (p + r) = p + (q + r))
    (a : Fin p → H) (c : Fin r → H) (v : HilbertTensorPower ℂ H q) :
    (cIso h2 ((permRep ℂ H (q + (p + r)) (tauB p q r h2) :
        HilbertTensorPower ℂ H (q + (p + r)) →L[ℂ] HilbertTensorPower ℂ H (q + (p + r)))
      ((splitIsometry (𝕜 := ℂ) (E := H) q (p + r)).symm (htmul v (ptC (Fin.append a c)))))) =
    (splitIsometry (𝕜 := ℂ) (E := H) p (q + r)).symm
      (htmul (ptC a) ((splitIsometry (𝕜 := ℂ) (E := H) q r).symm (htmul v (ptC c)))) := by
  let Lc : HilbertTensorPower ℂ H q →L[ℂ] HilbertTensorPower ℂ H (p + (q + r)) :=
    (cIso h2).toLinearIsometry.toContinuousLinearMap.comp
      ((permRep ℂ H (q + (p + r)) (tauB p q r h2) :
        HilbertTensorPower ℂ H (q + (p + r)) →L[ℂ] HilbertTensorPower ℂ H (q + (p + r))).comp
        ((splitIsometry (𝕜 := ℂ) (E := H) q (p + r)).symm.toLinearIsometry.toContinuousLinearMap.comp
          (htL (ptC (Fin.append a c)))))
  let Rc : HilbertTensorPower ℂ H q →L[ℂ] HilbertTensorPower ℂ H (p + (q + r)) :=
    (splitIsometry (𝕜 := ℂ) (E := H) p (q + r)).symm.toLinearIsometry.toContinuousLinearMap.comp
      ((htR (ptC a)).comp
        ((splitIsometry (𝕜 := ℂ) (E := H) q r).symm.toLinearIsometry.toContinuousLinearMap.comp
          (htL (ptC c))))
  have hLR : Lc = Rc := by
    refine eq_of_eq_on_ptC Lc Rc (fun b => ?_)
    simp only [Lc, Rc, ContinuousLinearMap.comp_apply, htL_apply, htR_apply,
      LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometry.coe_toContinuousLinearMap]
    rw [split_symm_ptC, split_symm_ptC, split_symm_ptC, permRep_ptC, cIso_ptC]
    congr 1
    funext i
    have h1 := congrFun (append3_Psi a b c) ((Psi p q r).symm (Fin.cast h2 (Fin.cast h2.symm i)))
    simp only [tauB_symm_apply]
    simp at h1 ⊢
    exact h1.symm
  exact congrArg (fun F : HilbertTensorPower ℂ H q →L[ℂ] _ => F v) hLR

theorem mid_eq (p q r : ℕ) (h2 : q + (p + r) = p + (q + r))
    (B : SymSector ℂ H q →L[ℂ] SymSector ℂ H q) :
    castTensorOperator h2 (permutedPlacement (tauB p q r h2) B) = midPlacement p q r B := by
  refine eq_of_eq_on_ptC _ _ (fun f => ?_)
  obtain ⟨a, b, c, rfl⟩ : ∃ (a : Fin p → H) (b : Fin q → H) (c : Fin r → H),
      f = Fin.append a (Fin.append b c) :=
    ⟨_, _, _, eq_append3 f⟩
  rw [castTensorOperator_eq_conj, cIso_symm_ptC]
  simp only [permutedPlacement, ContinuousLinearMap.comp_apply]
  rw [permRep_ptC]
  have hg : (fun i : Fin (q + (p + r)) =>
      (fun i => (Fin.append a (Fin.append b c)) (Fin.cast h2 i))
        (((tauB p q r h2)⁻¹).symm i)) = Fin.append b (Fin.append a c) := by
    rw [← append3_Psi a b c]
    funext i
    simp [tauB, Equiv.Perm.inv_def]
  rw [hg]
  unfold firstPlacement
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometry.coe_toContinuousLinearMap]
  rw [splitIsometry_ptprod_append, htmap_htmul, ContinuousLinearMap.id_apply]
  rw [insert_eq]
  unfold midPlacement
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometry.coe_toContinuousLinearMap]
  rw [splitIsometry_ptprod_append, htmap_htmul]
  have hG : (firstPlacement (q := r) B : HilbertTensorPower ℂ H (q + r) →L[ℂ]
        HilbertTensorPower ℂ H (q + r)) (ptC (Fin.append b c)) =
      (splitIsometry (𝕜 := ℂ) (E := H) q r).symm
        (htmul (extendSymKernel B (ptC b)) (ptC c)) := by
    unfold firstPlacement
    simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toLinearIsometry,
      LinearIsometry.coe_toContinuousLinearMap]
    rw [splitIsometry_ptprod_append, htmap_htmul, ContinuousLinearMap.id_apply]
  rw [hG]
  rfl

theorem first_comm_mid (p q r : ℕ) (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p)
    (B : SymSector ℂ H q →L[ℂ] SymSector ℂ H q) :
    (firstPlacement (q := q + r) A).comp (midPlacement p q r B) =
      (midPlacement p q r B).comp (firstPlacement (q := q + r) A) := by
  let e := splitIsometry (𝕜 := ℂ) (E := H) p (q + r)
  let E := extendSymKernel A
  let G := firstPlacement (q := r) B
  let I1 := ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ H p)
  let I2 := ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ H (q + r))
  have h1 : (htmap (𝕜 := ℂ) E I2).comp (htmap (𝕜 := ℂ) I1 G) =
      htmap (𝕜 := ℂ) E G := by
    rw [← htmap_comp]; congr 1 <;> ext x <;> simp [I1, I2]
  have h2 : (htmap (𝕜 := ℂ) I1 G).comp (htmap (𝕜 := ℂ) E I2) =
      htmap (𝕜 := ℂ) E G := by
    rw [← htmap_comp]; congr 1 <;> ext x <;> simp [I1, I2]
  ext x
  change e.symm (htmap (𝕜 := ℂ) E I2 (e (e.symm (htmap (𝕜 := ℂ) I1 G (e x))))) =
    e.symm (htmap (𝕜 := ℂ) I1 G (e (e.symm (htmap (𝕜 := ℂ) E I2 (e x)))))
  rw [e.apply_symm_apply, e.apply_symm_apply]
  congr 1
  have := congrArg (fun F : _ →L[ℂ] _ => F (e x)) h1
  have h' := congrArg (fun F : _ →L[ℂ] _ => F (e x)) h2
  simp only [ContinuousLinearMap.comp_apply] at this h'
  rw [this, h']

end Mid3

section Transport

theorem exists_perm_two_sets {N : ℕ} (L M L' M' : Finset (Fin N)) (hLM : Disjoint L M)
    (hLM' : Disjoint L' M') (hL : L.card = L'.card) (hM : M.card = M'.card) :
    ∃ σ : Equiv.Perm (Fin N), L.map σ.toEmbedding = L' ∧ M.map σ.toEmbedding = M' := by
  classical
  let f : {x // x ∈ L} ⊕ {x // x ∈ M} → Fin N := Sum.elim (fun x => (x : Fin N)) (fun x => (x : Fin N))
  let g : {x // x ∈ L} ⊕ {x // x ∈ M} → Fin N :=
    Sum.elim (fun x => ((L.equivOfCardEq hL) x : Fin N)) (fun x => ((M.equivOfCardEq hM) x : Fin N))
  have hf : Function.Injective f := by
    rintro (x | x) (y | y) h
    · exact congrArg Sum.inl (Subtype.ext h)
    · have h' : (x : Fin N) = (y : Fin N) := h
      have : (x : Fin N) ∈ M := by rw [h']; exact y.2
      exact absurd this (Finset.disjoint_left.mp hLM x.2)
    · have h' : (x : Fin N) = (y : Fin N) := h
      have : (x : Fin N) ∈ L := by rw [h']; exact y.2
      exact absurd x.2 (Finset.disjoint_left.mp hLM this)
    · exact congrArg Sum.inr (Subtype.ext h)
  have hg : Function.Injective g := by
    rintro (x | x) (y | y) h
    · exact congrArg Sum.inl ((L.equivOfCardEq hL).injective (Subtype.ext h))
    · have h' : ((L.equivOfCardEq hL) x : Fin N) = ((M.equivOfCardEq hM) y : Fin N) := h
      have : ((L.equivOfCardEq hL) x : Fin N) ∈ M' := by rw [h']; exact ((M.equivOfCardEq hM) y).2
      exact absurd this (Finset.disjoint_left.mp hLM' ((L.equivOfCardEq hL) x).2)
    · have h' : ((M.equivOfCardEq hM) x : Fin N) = ((L.equivOfCardEq hL) y : Fin N) := h
      have h2 : ((M.equivOfCardEq hM) x : Fin N) ∈ L' := by rw [h']; exact ((L.equivOfCardEq hL) y).2
      exact absurd ((M.equivOfCardEq hM) x).2 (Finset.disjoint_left.mp hLM' h2)
    · exact congrArg Sum.inr ((M.equivOfCardEq hM).injective (Subtype.ext h))
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  refine ⟨σ, ?_, ?_⟩
  · refine Finset.eq_of_subset_of_card_le (fun b hb => ?_) (by simp [hL])
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hb
    have := hσ (Sum.inl ⟨a, ha⟩)
    simp only [f, g, Sum.elim_inl] at this
    simp only [Equiv.coe_toEmbedding]
    rw [this]; exact ((L.equivOfCardEq hL) ⟨a, ha⟩).2
  · refine Finset.eq_of_subset_of_card_le (fun b hb => ?_) (by simp [hM])
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hb
    have := hσ (Sum.inr ⟨a, ha⟩)
    simp only [f, g, Sum.elim_inr] at this
    simp only [Equiv.coe_toEmbedding]
    rw [this]; exact ((M.equivOfCardEq hM) ⟨a, ha⟩).2

end Transport

theorem equivCast_eq_finCast {m n : ℕ} (h : m = n) (i : Fin m) :
    (Equiv.cast (congrArg Fin h)) i = Fin.cast h i := by
  cases h; rfl

section Standard

/-- Slots of the first block `[A]` in `p | q | r`. -/
def slotsA (p q r : ℕ) : Finset (Fin (p + (q + r))) := firstPositions (p := p) (q := q + r)

/-- Slots of the middle block `[B]` in `p | q | r`. -/
def slotsB (p q r : ℕ) : Finset (Fin (p + (q + r))) :=
  Finset.univ.image (fun j : Fin q => Fin.natAdd p (Fin.castAdd r j))

theorem card_slotsA (p q r : ℕ) : (slotsA p q r).card = p := card_firstPositions p (q + r)

theorem card_slotsB (p q r : ℕ) : (slotsB p q r).card = q := by
  unfold slotsB
  rw [Finset.card_image_of_injective _ (fun a b h => by
    simpa [Fin.ext_iff] using h)]
  simp

theorem disjoint_slots (p q r : ℕ) : Disjoint (slotsA p q r) (slotsB p q r) := by
  rw [Finset.disjoint_left]
  intro x hxA hxB
  simp only [slotsA, firstPositions, Finset.mem_map, Finset.mem_univ, true_and,
    Fin.castAddEmb_apply] at hxA
  simp only [slotsB, Finset.mem_image, Finset.mem_univ, true_and] at hxB
  obtain ⟨i, rfl⟩ := hxA
  obtain ⟨j, hj⟩ := hxB
  have := congrArg Fin.val hj
  simp at this
  have hi := i.2
  omega

theorem rawFirst (p q r : ℕ) (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p) (m1 : ℕ)
    (h1 : p + m1 = p + (q + r)) (S : PlacementSubset p m1)
    (hS : castSlotSet h1 S.1 = slotsA p q r) :
    castTensorOperator h1 (subsetPlacement S A) = firstPlacement (q := q + r) A := by
  have hm1 : m1 = q + r := by omega
  subst hm1
  cases h1
  have hS' : S.1 = firstPositions (p := p) (q := q + r) := by
    simpa [castSlotSet, slotsA] using hS
  have hperm : placementSubsetOfPerm (p := p) (q := q + r) (1 : Equiv.Perm (Fin (p + (q + r)))) = S := by
    apply Subtype.ext
    simp only [placementSubsetOfPerm, hS']
    ext x; simp [Equiv.Perm.one_def]
  have := permutedPlacement_eq_subsetPlacement (1 : Equiv.Perm (Fin (p + (q + r)))) S hperm A
  show subsetPlacement S A = _
  rw [← this]
  have hb : (1 : Equiv.Perm (Fin (p + (q + r)))) =
      blockPerm (1 : Equiv.Perm (Fin p)) (1 : Equiv.Perm (Fin (q + r))) := by
    ext i; simp [blockPerm]
  rw [hb]
  exact permutedPlacement_blockPerm_eq 1 1 A

theorem rawMid (p q r : ℕ) (B : SymSector ℂ H q →L[ℂ] SymSector ℂ H q) (m2 : ℕ)
    (h2 : q + m2 = p + (q + r)) (T : PlacementSubset q m2)
    (hT : castSlotSet h2 T.1 = slotsB p q r) :
    castTensorOperator h2 (subsetPlacement T B) = midPlacement p q r B := by
  have hm2 : m2 = p + r := by omega
  subst hm2
  have hset : placementSubsetOfPerm (p := q) (q := p + r) (tauB p q r h2) = T := by
    apply Subtype.ext
    have hT' : T.1 = (slotsB p q r).map (Equiv.cast (congrArg Fin h2.symm)).toEmbedding := by
      have := congrArg (castSlotSet h2.symm) hT
      rw [QuantumNLS.PlacementFiberTransport.castSlotSet_symm] at this
      exact this
    rw [hT']
    ext x
    simp only [placementSubsetOfPerm, firstPositions, Finset.mem_map, Finset.mem_univ, true_and,
      Fin.castAddEmb_apply, Equiv.coe_toEmbedding, slotsB, Finset.mem_image]
    constructor
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      refine ⟨Fin.natAdd p (Fin.castAdd r j), ⟨j, rfl⟩, ?_⟩
      simp [tauB, Psi_castAdd, Equiv.cast_apply, Fin.cast_eq_cast]
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      refine ⟨_, ⟨j, rfl⟩, ?_⟩
      simp [tauB, Psi_castAdd, Equiv.cast_apply, Fin.cast_eq_cast]
  have := permutedPlacement_eq_subsetPlacement (tauB p q r h2) T hset B
  rw [← this]
  exact mid_eq p q r h2 B

end Standard

section Disjoint

open QuantumNLS.PlacementFiberTransport

theorem card_leftSlots {N p q : ℕ} (hp : p ≤ N) (z : ActualPairPlacement N p q) :
    (leftSlots hp z).card = p := by
  simp [leftSlots, castSlotSet, z.1.2]

theorem card_rightSlots {N p q : ℕ} (hq : q ≤ N) (z : ActualPairPlacement N p q) :
    (rightSlots hq z).card = q := by
  simp [rightSlots, castSlotSet, z.2.2]

theorem permHilbertIsometry_mul_apply' {n : ℕ}
    (σ τ : Equiv.Perm (Fin n)) (x : HilbertTensorPower ℂ H n) :
    permHilbertIsometry (𝕜 := ℂ) (E := H) σ
        (permHilbertIsometry (𝕜 := ℂ) (E := H) τ x) =
      permHilbertIsometry (𝕜 := ℂ) (E := H) (σ * τ) x := by
  have h := map_mul (permHom ℂ H n) σ τ
  simpa [permHom] using (congrArg (fun f : _ ≃ₗᵢ[ℂ] _ => f x) h).symm

theorem permRep_cancel {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : HilbertTensorPower ℂ H n) :
    (permRep ℂ H n σ⁻¹ : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n)
      ((permRep ℂ H n σ : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n) x) = x := by
  change permHilbertIsometry (𝕜 := ℂ) (E := H) σ⁻¹
    (permHilbertIsometry (𝕜 := ℂ) (E := H) σ x) = x
  rw [permHilbertIsometry_mul_apply', inv_mul_cancel]
  have hone := map_one (permHom ℂ H n)
  simpa [permHom] using congrArg (fun f : _ ≃ₗᵢ[ℂ] _ => f x) hone

/-- Conjugation-invariance of commutation. -/
theorem comm_of_conj {n : ℕ} (σ : Equiv.Perm (Fin n))
    (X Y : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n)
    (h : (((permRep ℂ H n σ : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n).comp X).comp
        (permRep ℂ H n σ⁻¹ : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n)).comp
      (((permRep ℂ H n σ : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n).comp Y).comp
        (permRep ℂ H n σ⁻¹ : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n)) =
      (((permRep ℂ H n σ : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n).comp Y).comp
        (permRep ℂ H n σ⁻¹ : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n)).comp
      (((permRep ℂ H n σ : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n).comp X).comp
        (permRep ℂ H n σ⁻¹ : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n))) :
    X.comp Y = Y.comp X := by
  ext x
  have hx := congrArg (fun F : _ →L[ℂ] _ =>
    (permRep ℂ H n σ⁻¹ : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n)
      (F ((permRep ℂ H n σ : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n) x))) h
  simp only [ContinuousLinearMap.comp_apply] at hx
  have c : ∀ y, (permRep ℂ H n σ⁻¹ : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n)
      ((permRep ℂ H n σ : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n) y) = y :=
    permRep_cancel σ
  rw [c, c] at hx
  simpa only [c, ContinuousLinearMap.comp_apply] using hx

/-- **Disjoint placements commute** (stage 1, item 1), for `N = p + (q + r)`: two actual raw
placements `P_S(A)`, `P_T(B)` whose slot sets in `Fin N` are disjoint commute. -/
theorem rawPlacement_commute_of_disjoint_aux (p q r : ℕ)
    (hp : p ≤ p + (q + r)) (hq : q ≤ p + (q + r))
    (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q)
    (z : ActualPairPlacement (p + (q + r)) p q)
    (hdisj : Disjoint (leftSlots hp z) (rightSlots hq z)) :
    (rawSubsetPlacement (p + (q + r)) p hp z.1 A).comp
        (rawSubsetPlacement (p + (q + r)) q hq z.2 B) =
      (rawSubsetPlacement (p + (q + r)) q hq z.2 B).comp
        (rawSubsetPlacement (p + (q + r)) p hp z.1 A) := by
  obtain ⟨σ, hσL, hσM⟩ := exists_perm_two_sets (leftSlots hp z) (rightSlots hq z)
    (slotsA p q r) (slotsB p q r) hdisj (disjoint_slots p q r)
    (by rw [card_leftSlots, card_slotsA]) (by rw [card_rightSlots, card_slotsB])
  let z' := relabelActualPair hp hq σ z
  have hz1 : leftSlots hp z' = slotsA p q r := by
    rw [leftSlots_relabelActualPair]; exact hσL
  have hz2 : rightSlots hq z' = slotsB p q r := by
    rw [rightSlots_relabelActualPair]; exact hσM
  have hP' : rawSubsetPlacement (p + (q + r)) p hp z'.1 A = firstPlacement (q := q + r) A :=
    rawFirst p q r A _ (Nat.add_sub_of_le hp) z'.1 hz1
  have hT' : rawSubsetPlacement (p + (q + r)) q hq z'.2 B = midPlacement p q r B :=
    rawMid p q r B _ (Nat.add_sub_of_le hq) z'.2 hz2
  have hcomm := first_comm_mid p q r A B
  rw [← hP', ← hT'] at hcomm
  refine comm_of_conj σ _ _ ?_
  have e1 : ((permRep ℂ H (p + (q + r)) σ : HilbertTensorPower ℂ H (p + (q + r)) →L[ℂ]
        HilbertTensorPower ℂ H (p + (q + r))).comp
        (rawSubsetPlacement (p + (q + r)) p hp z.1 A)).comp
        (permRep ℂ H (p + (q + r)) σ⁻¹ : HilbertTensorPower ℂ H (p + (q + r)) →L[ℂ]
          HilbertTensorPower ℂ H (p + (q + r))) =
      rawSubsetPlacement (p + (q + r)) p hp z'.1 A :=
    castSubsetPlacement_conjugate (Nat.add_sub_of_le hp) σ z.1 A
  have e2 : ((permRep ℂ H (p + (q + r)) σ : HilbertTensorPower ℂ H (p + (q + r)) →L[ℂ]
        HilbertTensorPower ℂ H (p + (q + r))).comp
        (rawSubsetPlacement (p + (q + r)) q hq z.2 B)).comp
        (permRep ℂ H (p + (q + r)) σ⁻¹ : HilbertTensorPower ℂ H (p + (q + r)) →L[ℂ]
          HilbertTensorPower ℂ H (p + (q + r))) =
      rawSubsetPlacement (p + (q + r)) q hq z'.2 B :=
    castSubsetPlacement_conjugate (Nat.add_sub_of_le hq) σ z.2 B
  rw [e1, e2]
  exact hcomm

/-- Disjoint placements commute, for arbitrary `N ≥ p + q`. -/
theorem rawPlacement_commute_of_disjoint (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N)
    (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q)
    (z : ActualPairPlacement N p q) (hdisj : Disjoint (leftSlots hp z) (rightSlots hq z)) :
    (rawSubsetPlacement N p hp z.1 A).comp (rawSubsetPlacement N q hq z.2 B) =
      (rawSubsetPlacement N q hq z.2 B).comp (rawSubsetPlacement N p hp z.1 A) := by
  have hpq : p + q ≤ N := by
    have := Finset.card_union_of_disjoint hdisj
    rw [card_leftSlots, card_rightSlots] at this
    have h2 := Finset.card_le_univ (leftSlots hp z ∪ rightSlots hq z)
    simp only [Fintype.card_fin] at h2
    omega
  obtain ⟨r, rfl⟩ : ∃ r, N = p + (q + r) := ⟨N - p - q, by omega⟩
  exact rawPlacement_commute_of_disjoint_aux p q r hp hq A B z hdisj

end Disjoint

#print axioms rawPlacement_commute_of_disjoint

section Counting

open QuantumNLS.PlacementFiberTransport QuantumNLS.OverlapMoments

/-- The number of `q`-subsets of `Fin N` meeting a fixed `p`-subset `P` is the sum over
overlap sizes `s ≥ 1` of the hypergeometric numerators. -/
theorem card_meeting {N p q : ℕ} (P : Finset (Fin N)) (hP : P.card = p) :
    (((Finset.univ : Finset (Fin N)).powersetCard q).filter (fun Q => ¬ Disjoint P Q)).card =
      ∑ s ∈ (Finset.range (q + 1)).filter (fun s => 1 ≤ s),
        p.choose s * (N - p).choose (q - s) := by
  classical
  set S := ((Finset.univ : Finset (Fin N)).powersetCard q).filter (fun Q => ¬ Disjoint P Q)
    with hS
  have hmaps : ∀ Q ∈ S, (P ∩ Q).card ∈ (Finset.range (q + 1)).filter (fun s => 1 ≤ s) := by
    intro Q hQ
    obtain ⟨hQ1, hQ2⟩ := Finset.mem_filter.mp hQ
    have hq : Q.card = q := (Finset.mem_powersetCard.mp hQ1).2
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, ?_⟩
    · have := Finset.card_le_card (Finset.inter_subset_right (s₁ := P) (s₂ := Q))
      omega
    · exact Finset.card_pos.mpr (Finset.not_disjoint_iff_nonempty_inter.mp hQ2)
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  obtain ⟨hs1, hs2⟩ := Finset.mem_filter.mp hs
  have hsq : s ≤ q := by have := Finset.mem_range.mp hs1; omega
  rw [← card_overlapFiber P hP hsq]
  congr 1
  ext Q
  simp only [hS, overlapFiber, Finset.mem_filter]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩
    refine ⟨⟨h1, ?_⟩, h3⟩
    rw [Finset.not_disjoint_iff_nonempty_inter, ← Finset.card_pos, h3]
    omega

theorem card_meeting_placements {N p q : ℕ} (hq : q ≤ N) (P : Finset (Fin N)) (hP : P.card = p) :
    (Finset.univ.filter (fun T : PlacementSubset q (N - q) =>
        ¬ Disjoint P (castSlotSet (Nat.add_sub_of_le hq) T.1))).card =
      ∑ s ∈ (Finset.range (q + 1)).filter (fun s => 1 ≤ s),
        p.choose s * (N - p).choose (q - s) := by
  classical
  rw [← card_meeting (q := q) P hP]
  refine Finset.card_bij (fun T _ => castSlotSet (Nat.add_sub_of_le hq) T.1) ?_ ?_ ?_
  · intro T hT
    obtain ⟨_, h2⟩ := Finset.mem_filter.mp hT
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩, h2⟩
    simp [castSlotSet, T.2]
  · intro T1 _ T2 _ h
    apply Subtype.ext
    exact Finset.map_injective _ h
  · intro Q hQ
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hQ
    have hcard : Q.card = q := (Finset.mem_powersetCard.mp h1).2
    refine ⟨sourcePlacementOfSlots hq Q hcard, ?_, slots_sourcePlacementOfSlots hq Q hcard⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [slots_sourcePlacementOfSlots]; exact h2

theorem card_badPairs {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N) :
    (Finset.univ.filter (fun z : ActualPairPlacement N p q =>
        ¬ Disjoint (leftSlots hp z) (rightSlots hq z))).card =
      N.choose p * ∑ s ∈ (Finset.range (q + 1)).filter (fun s => 1 ≤ s),
        p.choose s * (N - p).choose (q - s) := by
  classical
  rw [Finset.card_filter, Fintype.sum_prod_type]
  have h : ∀ S : PlacementSubset p (N - p),
      (∑ T : PlacementSubset q (N - q),
        if ¬ Disjoint (leftSlots hp (S, T)) (rightSlots hq (S, T)) then 1 else 0) =
      ∑ s ∈ (Finset.range (q + 1)).filter (fun s => 1 ≤ s),
        p.choose s * (N - p).choose (q - s) := by
    intro S
    have hP : (castSlotSet (Nat.add_sub_of_le hp) S.1).card = p := by
      simp [castSlotSet, S.2]
    rw [← card_meeting_placements hq _ hP, Finset.card_filter]
    rfl
  rw [Finset.sum_congr rfl (fun S _ => h S), Finset.sum_const, Finset.card_univ,
    card_placementSubset, smul_eq_mul]
  rw [Nat.add_sub_of_le hp]

theorem card_badPairs_le {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N) (hN : 1 ≤ N) :
    ((Finset.univ.filter (fun z : ActualPairPlacement N p q =>
        ¬ Disjoint (leftSlots hp z) (rightSlots hq z))).card : ℝ) ≤
      (N.choose p : ℝ) * (N.choose q : ℝ) * ((p * q : ℝ) / N) := by
  rw [card_badPairs hp hq]
  have hden : (N.choose q : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hq
  have hprob := prob_intersect_le hp hq hN
  have hsum : ((∑ s ∈ (Finset.range (q + 1)).filter (fun s => 1 ≤ s),
      p.choose s * (N - p).choose (q - s) : ℕ) : ℝ) =
      (N.choose q : ℝ) * ∑ s ∈ (Finset.range (q + 1)).filter (fun s => 1 ≤ s),
        overlapCoefficient N p q s := by
    rw [Finset.mul_sum, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    have hsq : s ≤ q := by
      have := Finset.mem_range.mp (Finset.mem_filter.mp hs).1; omega
    rw [overlapCoefficient_of_le hsq]
    field_simp
  push_cast
  have hsum' : ((∑ s ∈ (Finset.range (q + 1)).filter (fun s => 1 ≤ s),
      (p.choose s : ℝ) * ((N - p).choose (q - s) : ℝ))) =
      (N.choose q : ℝ) * ∑ s ∈ (Finset.range (q + 1)).filter (fun s => 1 ≤ s),
        overlapCoefficient N p q s := by
    rw [← hsum]; push_cast; rfl
  rw [hsum']
  have hC : 0 ≤ (N.choose p : ℝ) * (N.choose q : ℝ) := by positivity
  calc (N.choose p : ℝ) * ((N.choose q : ℝ) * ∑ s ∈ (Finset.range (q + 1)).filter (fun s => 1 ≤ s),
        overlapCoefficient N p q s)
      = ((N.choose p : ℝ) * (N.choose q : ℝ)) * ∑ s ∈ (Finset.range (q + 1)).filter (fun s => 1 ≤ s),
        overlapCoefficient N p q s := by ring
    _ ≤ ((N.choose p : ℝ) * (N.choose q : ℝ)) * ((p * q : ℝ) / N) :=
        mul_le_mul_of_nonneg_left hprob hC

end Counting

section Bound

theorem norm_rawSubsetPlacement_le (N r : ℕ) (hr : r ≤ N) (S : PlacementSubset r (N - r))
    (A : BoundedSymmetricKernel H r) : ‖rawSubsetPlacement N r hr S A‖ ≤ ‖A‖ := by
  unfold rawSubsetPlacement
  rw [norm_castTensorOperator]
  exact norm_permutedPlacement_le _ A

theorem norm_pair_comm_le (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N)
    (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q)
    (z : ActualPairPlacement N p q) :
    ‖(rawSubsetPlacement N p hp z.1 A).comp (rawSubsetPlacement N q hq z.2 B) -
      (rawSubsetPlacement N q hq z.2 B).comp (rawSubsetPlacement N p hp z.1 A)‖ ≤
      2 * (‖A‖ * ‖B‖) := by
  have h1 := norm_rawSubsetPlacement_le N p hp z.1 A
  have h2 := norm_rawSubsetPlacement_le N q hq z.2 B
  have c1 := ContinuousLinearMap.opNorm_comp_le (rawSubsetPlacement N p hp z.1 A)
    (rawSubsetPlacement N q hq z.2 B)
  have c2 := ContinuousLinearMap.opNorm_comp_le (rawSubsetPlacement N q hq z.2 B)
    (rawSubsetPlacement N p hp z.1 A)
  refine (norm_sub_le _ _).trans ?_
  have e1 : ‖rawSubsetPlacement N p hp z.1 A‖ * ‖rawSubsetPlacement N q hq z.2 B‖ ≤
      ‖A‖ * ‖B‖ := mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg A)
  have e2 : ‖rawSubsetPlacement N q hq z.2 B‖ * ‖rawSubsetPlacement N p hp z.1 A‖ ≤
      ‖A‖ * ‖B‖ := by
    calc _ = ‖rawSubsetPlacement N p hp z.1 A‖ * ‖rawSubsetPlacement N q hq z.2 B‖ := mul_comm _ _
      _ ≤ _ := e1
  linarith

/-- The commutator of the two full-tensor averages is the normalized double sum of the
commutators of the individual placements. -/
theorem average_commutator_eq (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N)
    (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) :
    (rawSubsetAverage N p hp A).comp (rawSubsetAverage N q hq B) -
        (rawSubsetAverage N q hq B).comp (rawSubsetAverage N p hp A) =
      (((N.choose p : ℂ)⁻¹) * ((N.choose q : ℂ)⁻¹)) •
        ∑ S : PlacementSubset p (N - p), ∑ T : PlacementSubset q (N - q),
          ((rawSubsetPlacement N p hp S A).comp (rawSubsetPlacement N q hq T B) -
            (rawSubsetPlacement N q hq T B).comp (rawSubsetPlacement N p hp S A)) := by
  rw [rawSubsetAverage_eq_rawSubsetPlacementSum, rawSubsetAverage_eq_rawSubsetPlacementSum]
  unfold rawSubsetPlacementSum
  rw [smul_sum_comp_smul_sum, smul_sum_comp_smul_sum, mul_comm ((N.choose q : ℂ)⁻¹),
    ← smul_sub, Finset.sum_comm (f := fun T S => (rawSubsetPlacement N q hq T B).comp
      (rawSubsetPlacement N p hp S A))]
  congr 1
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [← Finset.sum_sub_distrib]

theorem average_commutator_norm_le (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N) (hN : 1 ≤ N)
    (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) :
    ‖(rawSubsetAverage N p hp A).comp (rawSubsetAverage N q hq B) -
        (rawSubsetAverage N q hq B).comp (rawSubsetAverage N p hp A)‖ ≤
      2 * (‖A‖ * ‖B‖) * ((p * q : ℝ) / N) := by
  classical
  rw [average_commutator_eq, norm_smul]
  have hcp : (N.choose p : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hp
  have hcq : (N.choose q : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hq
  have hnorm : ‖((N.choose p : ℂ)⁻¹) * ((N.choose q : ℂ)⁻¹)‖ =
      ((N.choose p : ℝ) * (N.choose q : ℝ))⁻¹ := by
    rw [norm_mul, norm_inv, norm_inv, Complex.norm_natCast, Complex.norm_natCast, mul_inv]
  rw [hnorm]
  set c : ℝ := 2 * (‖A‖ * ‖B‖) with hc
  let bad : ActualPairPlacement N p q → Prop := fun z =>
    ¬ Disjoint (leftSlots hp z) (rightSlots hq z)
  have hsum : ‖∑ S : PlacementSubset p (N - p), ∑ T : PlacementSubset q (N - q),
      ((rawSubsetPlacement N p hp S A).comp (rawSubsetPlacement N q hq T B) -
        (rawSubsetPlacement N q hq T B).comp (rawSubsetPlacement N p hp S A))‖ ≤
      (Finset.univ.filter bad).card * c := by
    refine (norm_sum_le _ _).trans ?_
    have h1 : ∀ S : PlacementSubset p (N - p),
        ‖∑ T : PlacementSubset q (N - q),
          ((rawSubsetPlacement N p hp S A).comp (rawSubsetPlacement N q hq T B) -
            (rawSubsetPlacement N q hq T B).comp (rawSubsetPlacement N p hp S A))‖ ≤
        ∑ T : PlacementSubset q (N - q), ‖((rawSubsetPlacement N p hp S A).comp
          (rawSubsetPlacement N q hq T B) -
            (rawSubsetPlacement N q hq T B).comp (rawSubsetPlacement N p hp S A))‖ :=
      fun S => norm_sum_le _ _
    refine (Finset.sum_le_sum (fun S _ => h1 S)).trans ?_
    rw [← Fintype.sum_prod_type (f := fun z : PlacementSubset p (N - p) × PlacementSubset q (N - q) =>
      ‖((rawSubsetPlacement N p hp z.1 A).comp (rawSubsetPlacement N q hq z.2 B) -
        (rawSubsetPlacement N q hq z.2 B).comp (rawSubsetPlacement N p hp z.1 A))‖)]
    have h2 : ∀ z : ActualPairPlacement N p q,
        ‖((rawSubsetPlacement N p hp z.1 A).comp (rawSubsetPlacement N q hq z.2 B) -
          (rawSubsetPlacement N q hq z.2 B).comp (rawSubsetPlacement N p hp z.1 A))‖ ≤
        if bad z then c else 0 := by
      intro z
      by_cases hz : bad z
      · rw [if_pos hz]; exact norm_pair_comm_le N p q hp hq A B z
      · rw [if_neg hz]
        have hd : Disjoint (leftSlots hp z) (rightSlots hq z) := not_not.mp hz
        rw [rawPlacement_commute_of_disjoint N p q hp hq A B z hd, sub_self, norm_zero]
    refine (Finset.sum_le_sum (fun z _ => h2 z)).trans (le_of_eq ?_)
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hbad := card_badPairs_le hp hq hN
  have hcnn : 0 ≤ c := by positivity
  calc ((N.choose p : ℝ) * (N.choose q : ℝ))⁻¹ * ‖∑ S : PlacementSubset p (N - p),
        ∑ T : PlacementSubset q (N - q),
      ((rawSubsetPlacement N p hp S A).comp (rawSubsetPlacement N q hq T B) -
        (rawSubsetPlacement N q hq T B).comp (rawSubsetPlacement N p hp S A))‖
      ≤ ((N.choose p : ℝ) * (N.choose q : ℝ))⁻¹ * ((Finset.univ.filter bad).card * c) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ ((N.choose p : ℝ) * (N.choose q : ℝ))⁻¹ *
          ((N.choose p : ℝ) * (N.choose q : ℝ) * ((p * q : ℝ) / N) * c) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right hbad hcnn
    _ = c * ((p * q : ℝ) / N) := by
        field_simp

theorem coe_genericU (N r : ℕ) (hr : r ≤ N) (A : BoundedSymmetricKernel H r)
    (x : SymSector ℂ H N) :
    ((genericU_N_r N r hr A x : SymSector ℂ H N) : HilbertTensorPower ℂ H N) =
      rawSubsetAverage N r hr A (x : HilbertTensorPower ℂ H N) := by
  rw [genericU_eq_rawSubsetAverageOnSector]
  rfl

/-- **`eq:root-overlap-bound` (R-32EBD5C1, stage 1)**, in the normalization `‖[Q_{N,p}(A),Q_{N,q}(B)]‖ ≤
2pq‖A‖‖B‖/N` for `N ≥ 1`. -/
theorem commutator_norm_le (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N) (hN : 1 ≤ N)
    (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) :
    ‖(genericU_N_r N p hp A).comp (genericU_N_r N q hq B) -
        (genericU_N_r N q hq B).comp (genericU_N_r N p hp A)‖ ≤
      2 * (‖A‖ * ‖B‖) * ((p * q : ℝ) / N) := by
  have hK := average_commutator_norm_le N p q hp hq hN A B
  refine ContinuousLinearMap.opNorm_le_bound _ (le_trans (norm_nonneg _) hK) (fun x => ?_)
  rw [← Submodule.norm_coe]
  have e : (((genericU_N_r N p hp A).comp (genericU_N_r N q hq B) -
        (genericU_N_r N q hq B).comp (genericU_N_r N p hp A)) x :
          HilbertTensorPower ℂ H N) =
      ((rawSubsetAverage N p hp A).comp (rawSubsetAverage N q hq B) -
        (rawSubsetAverage N q hq B).comp (rawSubsetAverage N p hp A))
          (x : HilbertTensorPower ℂ H N) := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, Submodule.coe_sub,
      coe_genericU]
  rw [e]
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  exact mul_le_mul_of_nonneg_right hK (norm_nonneg _)

/-- **R-32EBD5C1 `eq:root-overlap-bound`**:
`N ‖[Q_{N,p}(A), Q_{N,q}(B)]‖ ≤ 2 p q ‖A‖ ‖B‖` for `p, q ≤ N` and bounded `A, B`. -/
theorem root_overlap_bound (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N)
    (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) :
    (N : ℝ) * ‖(genericU_N_r N p hp A).comp (genericU_N_r N q hq B) -
        (genericU_N_r N q hq B).comp (genericU_N_r N p hp A)‖ ≤
      2 * (p * q : ℝ) * ‖A‖ * ‖B‖ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Nat.cast_zero, zero_mul]
    positivity
  · have h := commutator_norm_le N p q hp hq hN A B
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    calc (N : ℝ) * _ ≤ (N : ℝ) * (2 * (‖A‖ * ‖B‖) * ((p * q : ℝ) / N)) :=
          mul_le_mul_of_nonneg_left h hNr.le
      _ = 2 * (p * q : ℝ) * ‖A‖ * ‖B‖ := by field_simp

end Bound

#print axioms root_overlap_bound
#print axioms commutator_norm_le
#print axioms rawPlacement_commute_of_disjoint
#print axioms card_badPairs_le

end QuantumNLS.RootOverlapCommutator
