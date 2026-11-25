import LiebLiniger.FixedPeriod.Quantum.SymmetricTensorBridges
import LiebLiniger.FixedPeriod.Quantum.SectorNormalization

/-!
Concrete finite-sector Wick construction using the product-L² realization.
No target estimate is assumed. All coordinate/tensor maps and projections are
constructed upstream; the exact factorial scalar is the source coefficient.
Compiler validation belongs to the single root queue.
-/

noncomputable section
open MeasureTheory
open scoped TensorProduct BigOperators

namespace LiebLiniger.FixedPeriod.Quantum

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
variable [IsFiniteMeasure μ]

abbrev sectorMeasure (n : ℕ) : Measure (Fin n → X) := Measure.pi fun _ => μ

/-- Transport between equal sector indices, preserving every norm. -/
def symmetricSectorCast {m n : ℕ} (h : m = n) :
    SymmetricSector μ m ≃ₗᵢ[ℂ] SymmetricSector μ n := by
  subst n
  exact LinearIsometryEquiv.refl ℂ _

/-- Canonical extension of A by zero on the orthogonal complement of its
symmetric input space. On the symmetric input it agrees literally with A. -/
def fullSectorExtension {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) :
    ProductL2 μ (Fin p) →L[ℂ] ProductL2 μ (Fin q) :=
  (symmetricSectorInclusion μ q).toContinuousLinearMap ∘L A ∘L symmetricSectorProjection μ p

@[simp] theorem fullSectorExtension_on_symmetric {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (v : SymmetricSector μ p) :
    fullSectorExtension μ A (v : ProductL2 μ (Fin p)) =
      (A v : ProductL2 μ (Fin q)) := by
  change symmetricSectorInclusion μ q
    (A (symmetricSectorProjection μ p (symmetricSectorInclusion μ p v))) = _
  rw [symmetricSectorProjection_inclusion]
  rfl

theorem norm_fullSectorExtension_le {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) :
    ‖fullSectorExtension μ A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (fullSectorExtension μ A)
    (ContinuousLinearMap.opNorm_nonneg A)
  intro f
  change ‖symmetricSectorInclusion μ q (A (symmetricSectorProjection μ p f))‖ ≤ _
  rw [LinearIsometry.norm_map]
  exact (A.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (norm_symmetricSectorProjection_apply_le μ p f)
      (ContinuousLinearMap.opNorm_nonneg A))

/-- The genuine A tensor identity map on complete, unsymmetrized sectors.
The spectators are exactly k coordinates. -/
def fullTensorLift {p q : ℕ}
    (B : ProductL2 μ (Fin p) →L[ℂ] ProductL2 μ (Fin q)) (k : ℕ) :
    ProductL2 μ (Fin (p + k)) →L[ℂ] ProductL2 μ (Fin (q + k)) :=
  (unregroupL2 μ q k).toContinuousLinearMap ∘L
    (spatialTensorEquiv (sectorMeasure μ q) (sectorMeasure μ k)).toLinearIsometry.toContinuousLinearMap ∘L
    (B.rTensor (ProductL2 μ (Fin k))).completion ∘L
    (spatialTensorEquiv (sectorMeasure μ p) (sectorMeasure μ k)).symm.toLinearIsometry.toContinuousLinearMap ∘L
    (regroupL2 μ p k).toContinuousLinearMap

theorem norm_fullTensorLift_le {p q : ℕ}
    (B : ProductL2 μ (Fin p) →L[ℂ] ProductL2 μ (Fin q)) (k : ℕ) :
    ‖fullTensorLift μ B k‖ ≤ ‖B‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (fullTensorLift μ B k)
    (ContinuousLinearMap.opNorm_nonneg B)
  intro f
  change ‖unregroupL2 μ q k
    (spatialTensorEquiv (sectorMeasure μ q) (sectorMeasure μ k)
      ((B.rTensor (ProductL2 μ (Fin k))).completion
        ((spatialTensorEquiv (sectorMeasure μ p) (sectorMeasure μ k)).symm
          (regroupL2 μ p k f))))‖ ≤ ‖B‖ * ‖f‖
  rw [LinearIsometry.norm_map, LinearIsometryEquiv.norm_map]
  calc
    _ ≤ ‖(B.rTensor (ProductL2 μ (Fin k))).completion‖ *
        ‖(spatialTensorEquiv (sectorMeasure μ p) (sectorMeasure μ k)).symm (regroupL2 μ p k f)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖B‖ *
        ‖(spatialTensorEquiv (sectorMeasure μ p) (sectorMeasure μ k)).symm (regroupL2 μ p k f)‖ :=
      mul_le_mul_of_nonneg_right
        ((LLFPSectorCandidate.norm_completion_le _).trans
          (ContinuousLinearMap.norm_rTensor_le (ProductL2 μ (Fin k)) B)) (norm_nonneg _)
    _ = ‖B‖ * ‖f‖ := by rw [LinearIsometryEquiv.norm_map, LinearIsometry.norm_map]

/-- Spatial tensor realization sends an actual elementary Hilbert tensor to
its separated kernel. This is proved, not a normalization postulate. -/
theorem spatialTensorEquiv_tmul {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    (ν : Measure Y) (τ : Measure Z) [SigmaFinite ν] [SigmaFinite τ]
    [IsFiniteMeasure ν] [IsFiniteMeasure τ] (f : Lp ℂ 2 ν) (g : Lp ℂ 2 τ) :
    spatialTensorEquiv ν τ
      ((f ⊗ₜ[ℂ] g : Lp ℂ 2 ν ⊗[ℂ] Lp ℂ 2 τ) :
        UniformSpace.Completion (Lp ℂ 2 ν ⊗[ℂ] Lp ℂ 2 τ)) = separatedL2 ν τ f g := by
  change (spatialTensorIsometry ν τ).fromCompletion
    ((f ⊗ₜ[ℂ] g : Lp ℂ 2 ν ⊗[ℂ] Lp ℂ 2 τ) :
      UniformSpace.Completion (Lp ℂ 2 ν ⊗[ℂ] Lp ℂ 2 τ)) = _
  rw [LinearIsometry.fromCompletion_apply_coe]
  rfl

theorem spatialTensorEquiv_symm_separated {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    (ν : Measure Y) (τ : Measure Z) [SigmaFinite ν] [SigmaFinite τ]
    [IsFiniteMeasure ν] [IsFiniteMeasure τ] (f : Lp ℂ 2 ν) (g : Lp ℂ 2 τ) :
    (spatialTensorEquiv ν τ).symm (separatedL2 ν τ f g) =
      ((f ⊗ₜ[ℂ] g : Lp ℂ 2 ν ⊗[ℂ] Lp ℂ 2 τ) :
        UniformSpace.Completion (Lp ℂ 2 ν ⊗[ℂ] Lp ℂ 2 τ)) := by
  apply (spatialTensorEquiv ν τ).injective
  rw [LinearIsometryEquiv.apply_symm_apply, spatialTensorEquiv_tmul]

/-- The transported operator acts as B on the chosen coordinates and as the
identity on every spectator vector, fixing its tensor ordering. -/
theorem fullTensorLift_separated {p q : ℕ}
    (B : ProductL2 μ (Fin p) →L[ℂ] ProductL2 μ (Fin q)) (k : ℕ)
    (f : ProductL2 μ (Fin p)) (g : ProductL2 μ (Fin k)) :
    fullTensorLift μ B k
      (unregroupL2 μ p k (separatedL2 (sectorMeasure μ p) (sectorMeasure μ k) f g)) =
    unregroupL2 μ q k (separatedL2 (sectorMeasure μ q) (sectorMeasure μ k) (B f) g) := by
  change unregroupL2 μ q k
    (spatialTensorEquiv (sectorMeasure μ q) (sectorMeasure μ k)
      ((B.rTensor (ProductL2 μ (Fin k))).completion
        ((spatialTensorEquiv (sectorMeasure μ p) (sectorMeasure μ k)).symm
          (regroupL2 μ p k (unregroupL2 μ p k
            (separatedL2 (sectorMeasure μ p) (sectorMeasure μ k) f g)))))) = _
  rw [regroupL2_unregroupL2, spatialTensorEquiv_symm_separated,
    ContinuousLinearMap.completion_apply_coe, ContinuousLinearMap.rTensor_tmul,
    spatialTensorEquiv_tmul]

/-- Source A tensor identity on elementary symmetric-input tensors. -/
theorem fullSectorExtension_tensor_symmetric {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (k : ℕ)
    (f : SymmetricSector μ p) (g : ProductL2 μ (Fin k)) :
    fullTensorLift μ (fullSectorExtension μ A) k
      (unregroupL2 μ p k (separatedL2 (sectorMeasure μ p) (sectorMeasure μ k)
        (f : ProductL2 μ (Fin p)) g)) =
    unregroupL2 μ q k (separatedL2 (sectorMeasure μ q) (sectorMeasure μ k)
      (A f : ProductL2 μ (Fin q)) g) := by
  rw [fullTensorLift_separated, fullSectorExtension_on_symmetric]

/-- The spatial first-block pullback acts on an elementary kernel in the
first factor. Quotient representatives are compared almost everywhere. -/
theorem firstBlockPermutationL2_separated (p k : ℕ) (σ : Equiv.Perm (Fin p))
    (f : ProductL2 μ (Fin p)) (g : ProductL2 μ (Fin k)) :
    firstBlockPermutationL2 μ p k σ
      (separatedL2 (sectorMeasure μ p) (sectorMeasure μ k) f g) =
    separatedL2 (sectorMeasure μ p) (sectorMeasure μ k) (permutationL2 μ σ f) g := by
  change Lp.compMeasurePreserving _ _
    ((separatedProduct_memLp (sectorMeasure μ p) (sectorMeasure μ k) f g).toLp _) = _
  rw [Lp.toLp_compMeasurePreserving]
  apply MemLp.toLp_congr
  have hp : permutationL2 μ σ f =ᵐ[sectorMeasure μ p] f ∘ coordinatePermutation σ :=
    Lp.coeFn_compMeasurePreserving f (coordinatePermutation_measurePreserving μ σ)
  filter_upwards [(Measure.quasiMeasurePreserving_fst
      (μ := sectorMeasure μ p) (ν := sectorMeasure μ k)).ae_eq_comp hp] with z hz
  dsimp only [Function.comp_apply] at hz
  change f (coordinatePermutation σ z.1) * g z.2 = (permutationL2 μ σ f) z.1 * g z.2
  rw [hz]

/-- Tensoring the actual permutation unitary with identity agrees with the
actual first-block spatial pullback, on the whole completed Hilbert tensor. -/
theorem spatialTensorEquiv_firstBlockPermutation (p k : ℕ) (σ : Equiv.Perm (Fin p))
    (x : UniformSpace.Completion (ProductL2 μ (Fin p) ⊗[ℂ] ProductL2 μ (Fin k))) :
    spatialTensorEquiv (sectorMeasure μ p) (sectorMeasure μ k)
      (((permutationL2 μ σ).toContinuousLinearMap.rTensor (ProductL2 μ (Fin k))).completion x) =
    firstBlockPermutationL2 μ p k σ
      (spatialTensorEquiv (sectorMeasure μ p) (sectorMeasure μ k) x) := by
  refine UniformSpace.Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  induction a using TensorProduct.induction_on with
  | zero => simp only [map_zero, UniformSpace.Completion.coe_zero]
  | tmul f g =>
    rw [ContinuousLinearMap.completion_apply_coe, ContinuousLinearMap.rTensor_tmul,
      spatialTensorEquiv_tmul, spatialTensorEquiv_tmul, firstBlockPermutationL2_separated]
    rfl
  | add a b ha hb =>
    simp only [UniformSpace.Completion.coe_add, map_add, ha, hb]

/-- Every tensor permutation on the first block fixes the tensor realization
of a globally symmetric state. -/
theorem firstBlockTensorPermutation_fixed (p k : ℕ) (σ : Equiv.Perm (Fin p))
    (f : SymmetricSector μ (p + k)) :
    (((permutationL2 μ σ).toContinuousLinearMap.rTensor (ProductL2 μ (Fin k))).completion
      ((spatialTensorEquiv (sectorMeasure μ p) (sectorMeasure μ k)).symm
        (regroupL2 μ p k (f : ProductL2 μ (Fin (p + k)))))) =
    (spatialTensorEquiv (sectorMeasure μ p) (sectorMeasure μ k)).symm
      (regroupL2 μ p k (f : ProductL2 μ (Fin (p + k)))) := by
  apply (spatialTensorEquiv (sectorMeasure μ p) (sectorMeasure μ k)).injective
  rw [spatialTensorEquiv_firstBlockPermutation, LinearIsometryEquiv.apply_symm_apply,
    firstBlockPermutationL2_regroup_symmetric]

/-- Finite sums commute with the canonical completion embedding. -/
theorem completion_coe_finset_sum {E I : Type*} [NormedAddCommGroup E]
    (s : Finset I) (v : I → E) :
    ((∑ i ∈ s, v i : E) : UniformSpace.Completion E) =
      ∑ i ∈ s, (v i : UniformSpace.Completion E) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, UniformSpace.Completion.coe_zero]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha, UniformSpace.Completion.coe_add, ih]

/-- The actual normalized symmetrizer tensors to the normalized sum of the
actual tensor permutation maps. This also includes p=0. -/
theorem tensorSymmetrize_formula (p k : ℕ)
    (x : UniformSpace.Completion (ProductL2 μ (Fin p) ⊗[ℂ] ProductL2 μ (Fin k))) :
    ((symmetrizeL2 (ι := Fin p) μ).rTensor (ProductL2 μ (Fin k))).completion x =
      (Fintype.card (Equiv.Perm (Fin p)) : ℂ)⁻¹ •
        ∑ σ : Equiv.Perm (Fin p),
          (((permutationL2 μ σ).toContinuousLinearMap.rTensor (ProductL2 μ (Fin k))).completion x) := by
  let Q : UniformSpace.Completion (ProductL2 μ (Fin p) ⊗[ℂ] ProductL2 μ (Fin k)) →L[ℂ]
      UniformSpace.Completion (ProductL2 μ (Fin p) ⊗[ℂ] ProductL2 μ (Fin k)) :=
    ((symmetrizeL2 (ι := Fin p) μ).rTensor (ProductL2 μ (Fin k))).completion
  let V : UniformSpace.Completion (ProductL2 μ (Fin p) ⊗[ℂ] ProductL2 μ (Fin k)) →L[ℂ]
      UniformSpace.Completion (ProductL2 μ (Fin p) ⊗[ℂ] ProductL2 μ (Fin k)) :=
    (Fintype.card (Equiv.Perm (Fin p)) : ℂ)⁻¹ • ∑ σ : Equiv.Perm (Fin p),
      ((permutationL2 μ σ).toContinuousLinearMap.rTensor (ProductL2 μ (Fin k))).completion
  have hV (z : UniformSpace.Completion
      (ProductL2 μ (Fin p) ⊗[ℂ] ProductL2 μ (Fin k))) :
      V z = (Fintype.card (Equiv.Perm (Fin p)) : ℂ)⁻¹ •
        ∑ σ : Equiv.Perm (Fin p),
          (((permutationL2 μ σ).toContinuousLinearMap.rTensor
            (ProductL2 μ (Fin k))).completion z) := by
    simp only [V, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply]
  rw [← hV x]
  change Q x = V x
  refine UniformSpace.Completion.induction_on x (isClosed_eq Q.continuous V.continuous) ?_
  intro a
  induction a using TensorProduct.induction_on with
  | zero => simp only [UniformSpace.Completion.coe_zero, map_zero]
  | tmul f g =>
    simp only [Q, V, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.completion_apply_coe, ContinuousLinearMap.rTensor_tmul,
      symmetrizeL2_apply, ← TensorProduct.smul_tmul', TensorProduct.sum_tmul,
      UniformSpace.Completion.coe_smul, completion_coe_finset_sum] <;> rfl
  | add a b ha hb => simp only [UniformSpace.Completion.coe_add, map_add, ha, hb]

/-- The first-block symmetrizer acts identically on the tensor realization
of each genuine symmetric n-particle input. -/
theorem firstBlockTensorSymmetrization_fixed (p k : ℕ) (f : SymmetricSector μ (p + k)) :
    ((symmetrizeL2 (ι := Fin p) μ).rTensor (ProductL2 μ (Fin k))).completion
      ((spatialTensorEquiv (sectorMeasure μ p) (sectorMeasure μ k)).symm
        (regroupL2 μ p k (f : ProductL2 μ (Fin (p + k))))) =
    (spatialTensorEquiv (sectorMeasure μ p) (sectorMeasure μ k)).symm
      (regroupL2 μ p k (f : ProductL2 μ (Fin (p + k)))) := by
  have hc : (Fintype.card (Equiv.Perm (Fin p)) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [tensorSymmetrize_formula]
  simp only [firstBlockTensorPermutation_fixed, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- The canonical first-input-block projection is redundant on a genuine
symmetric sector. Thus extension by that projection changes no source input. -/
theorem fullTensorLift_symmetrizer_on_symmetric (p k : ℕ) (f : SymmetricSector μ (p + k)) :
    fullTensorLift μ (symmetrizeL2 (ι := Fin p) μ) k
      (f : ProductL2 μ (Fin (p + k))) = (f : ProductL2 μ (Fin (p + k))) := by
  change unregroupL2 μ p k
    (spatialTensorEquiv (sectorMeasure μ p) (sectorMeasure μ k)
      (((symmetrizeL2 (ι := Fin p) μ).rTensor (ProductL2 μ (Fin k))).completion
        ((spatialTensorEquiv (sectorMeasure μ p) (sectorMeasure μ k)).symm
          (regroupL2 μ p k (f : ProductL2 μ (Fin (p + k))))))) = _
  rw [firstBlockTensorSymmetrization_fixed, LinearIsometryEquiv.apply_symm_apply,
    unregroupL2_regroupL2]

/-- The unscaled Wick block with the actual output symmetrization. -/
def unscaledWickAdded {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (k : ℕ) :
    SymmetricSector μ (p + k) →L[ℂ] SymmetricSector μ (q + k) :=
  symmetricSectorProjection μ (q + k) ∘L
    fullTensorLift μ (fullSectorExtension μ A) k ∘L
    (symmetricSectorInclusion μ (p + k)).toContinuousLinearMap

theorem norm_unscaledWickAdded_le {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (k : ℕ) :
    ‖unscaledWickAdded μ A k‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (unscaledWickAdded μ A k)
    (ContinuousLinearMap.opNorm_nonneg A)
  intro f
  change ‖symmetricSectorProjection μ (q + k)
    (fullTensorLift μ (fullSectorExtension μ A) k (symmetricSectorInclusion μ (p + k) f))‖ ≤ _
  calc
    _ ≤ ‖fullTensorLift μ (fullSectorExtension μ A) k (symmetricSectorInclusion μ (p + k) f)‖ :=
      norm_symmetricSectorProjection_apply_le μ (q + k) _
    _ ≤ ‖fullTensorLift μ (fullSectorExtension μ A) k‖ *
        ‖symmetricSectorInclusion μ (p + k) f‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖A‖ * ‖symmetricSectorInclusion μ (p + k) f‖ :=
      mul_le_mul_of_nonneg_right
        ((norm_fullTensorLift_le μ _ k).trans (norm_fullSectorExtension_le μ A)) (norm_nonneg _)
    _ = ‖A‖ * ‖f‖ := by rw [LinearIsometry.norm_map]

/-- Source coefficient times the actual bounded Wick block for n=p+k. -/
def wickSectorAdded (epsilon : ℝ) {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (k : ℕ) :
    SymmetricSector μ (p + k) →L[ℂ] SymmetricSector μ (q + k) :=
  (LLFPSectorCandidate.wickCoefficient epsilon p q (p + k) : ℂ) • unscaledWickAdded μ A k

theorem norm_wickSectorAdded_le_coefficient (epsilon : ℝ) {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (k : ℕ) (he : 0 ≤ epsilon) :
    ‖wickSectorAdded μ epsilon A k‖ ≤
      LLFPSectorCandidate.wickCoefficient epsilon p q (p + k) * ‖A‖ := by
  unfold wickSectorAdded
  have hc : 0 ≤ LLFPSectorCandidate.wickCoefficient epsilon p q (p + k) :=
    LLFPSectorCandidate.wickCoefficient_nonneg epsilon p q (p + k) he
  calc
    _ ≤ ‖(LLFPSectorCandidate.wickCoefficient epsilon p q (p + k) : ℂ)‖ *
        ‖unscaledWickAdded μ A k‖ :=
      ContinuousLinearMap.opNorm_smul_le
        (LLFPSectorCandidate.wickCoefficient epsilon p q (p + k) : ℂ) (unscaledWickAdded μ A k)
    _ = LLFPSectorCandidate.wickCoefficient epsilon p q (p + k) *
        ‖unscaledWickAdded μ A k‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
    _ ≤ LLFPSectorCandidate.wickCoefficient epsilon p q (p + k) * ‖A‖ :=
      mul_le_mul_of_nonneg_left (norm_unscaledWickAdded_le μ A k) hc

/-- Exact finite-sector Wick map, with zero whenever the annihilation degree
exceeds the particle number. The output index is n+q-p, not total degree. -/
def wickSectorMap (epsilon : ℝ) {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (n : ℕ) :
    SymmetricSector μ n →L[ℂ] SymmetricSector μ (n + q - p) :=
  if hn : p ≤ n then
    (symmetricSectorCast μ (show q + (n - p) = n + q - p by omega)).toLinearIsometry.toContinuousLinearMap ∘L
      wickSectorAdded μ epsilon A (n - p) ∘L
      (symmetricSectorCast μ (show n = p + (n - p) by omega)).toLinearIsometry.toContinuousLinearMap
  else 0

@[simp] theorem wickSectorMap_of_lt (epsilon : ℝ) {p q n : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (hn : n < p) :
    wickSectorMap μ epsilon A n = 0 := by
  simp only [wickSectorMap, dif_neg (Nat.not_le.mpr hn)]

/-- Literal source factorial normalization, with the canonical reindexings shown.
The annihilation degree is guarded before any natural subtraction is used. -/
theorem wickSectorMap_eq_factorial (epsilon : ℝ) {p q n : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (hn : p ≤ n) :
    wickSectorMap μ epsilon A n =
      ((epsilon ^ (((p : ℝ) + (q : ℝ)) / 2) *
        Real.sqrt ((n.factorial : ℝ) * ((n + q - p).factorial : ℝ)) /
          ((n - p).factorial : ℝ) : ℝ) : ℂ) •
      ((symmetricSectorCast μ (show q + (n - p) = n + q - p by omega)).toLinearIsometry.toContinuousLinearMap ∘L
        unscaledWickAdded μ A (n - p) ∘L
        (symmetricSectorCast μ (show n = p + (n - p) by omega)).toLinearIsometry.toContinuousLinearMap) := by
  have hc : LLFPSectorCandidate.wickCoefficient epsilon p q (p + (n - p)) =
      epsilon ^ (((p : ℝ) + (q : ℝ)) / 2) *
        Real.sqrt ((n.factorial : ℝ) * ((n + q - p).factorial : ℝ)) /
          ((n - p).factorial : ℝ) := by
    rw [show p + (n - p) = n by omega]
    unfold LLFPSectorCandidate.wickCoefficient
    rw [if_pos hn]
  apply ContinuousLinearMap.ext
  intro f
  simp only [wickSectorMap, dif_pos hn, wickSectorAdded, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, map_smul, hc]

/-- The source coefficient controls the concrete operator, including zero sectors. -/
theorem wickSectorMap_norm_le_coefficient (epsilon : ℝ) {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (n : ℕ) (he : 0 ≤ epsilon) :
    ‖wickSectorMap μ epsilon A n‖ ≤ LLFPSectorCandidate.wickCoefficient epsilon p q n * ‖A‖ := by
  by_cases hn : p ≤ n
  · apply ContinuousLinearMap.opNorm_le_bound (wickSectorMap μ epsilon A n)
      (mul_nonneg (LLFPSectorCandidate.wickCoefficient_nonneg epsilon p q n he)
        (ContinuousLinearMap.opNorm_nonneg A))
    intro f
    simp only [wickSectorMap, dif_pos hn, ContinuousLinearMap.comp_apply]
    change ‖symmetricSectorCast μ (show q + (n - p) = n + q - p by omega)
      (wickSectorAdded μ epsilon A (n - p)
        (symmetricSectorCast μ (show n = p + (n - p) by omega) f))‖ ≤ _
    rw [LinearIsometryEquiv.norm_map]
    calc
      _ ≤ ‖wickSectorAdded μ epsilon A (n - p)‖ *
          ‖symmetricSectorCast μ (show n = p + (n - p) by omega) f‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ (LLFPSectorCandidate.wickCoefficient epsilon p q (p + (n - p)) * ‖A‖) *
          ‖symmetricSectorCast μ (show n = p + (n - p) by omega) f‖ :=
        mul_le_mul_of_nonneg_right (norm_wickSectorAdded_le_coefficient μ epsilon A (n - p) he)
          (norm_nonneg _)
      _ = _ := by rw [LinearIsometryEquiv.norm_map, show p + (n - p) = n by omega]
  · simp only [wickSectorMap, dif_neg hn, ContinuousLinearMap.opNorm_zero, LLFPSectorCandidate.wickCoefficient,
      if_neg hn, zero_mul, le_refl]

/-- LLFP-Q1-010 norm estimate on the actual finite symmetric sector. -/
theorem wickSectorMap_norm_le (epsilon : ℝ) {p q n : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (he : 0 < epsilon) (hn : p ≤ n) :
    ‖wickSectorMap μ epsilon A n‖ ≤ epsilon ^ (((p : ℝ) + (q : ℝ)) / 2) *
      Real.sqrt ((n.descFactorial p : ℝ) * ((n + q - p).descFactorial q : ℝ)) * ‖A‖ := by
  simpa only [LLFPSectorCandidate.wickCoefficient_eq_falling epsilon p q n hn] using
    wickSectorMap_norm_le_coefficient μ epsilon A n he.le

/-- LLFP-Q1-011: both number-preserving inequalities, with no n≥r restriction. -/
theorem wickNumberMap_norm_le (epsilon : ℝ) {r n : ℕ}
    (A : SymmetricSector μ r →L[ℂ] SymmetricSector μ r) (he : 0 < epsilon) :
    ‖wickSectorMap μ epsilon A n‖ ≤ epsilon ^ r * (n.descFactorial r : ℝ) * ‖A‖ ∧
      epsilon ^ r * (n.descFactorial r : ℝ) * ‖A‖ ≤ (epsilon * (n : ℝ)) ^ r * ‖A‖ := by
  constructor
  · by_cases hn : r ≤ n
    · simpa only [LLFPSectorCandidate.wickCoefficient_number epsilon r n hn] using
        wickSectorMap_norm_le_coefficient μ epsilon A n he.le
    · simp only [wickSectorMap_of_lt μ epsilon A (Nat.lt_of_not_ge hn), ContinuousLinearMap.opNorm_zero,
        Nat.descFactorial_of_lt (Nat.lt_of_not_ge hn), Nat.cast_zero, mul_zero, zero_mul, le_refl]
  · exact mul_le_mul_of_nonneg_right
      (LLFPSectorCandidate.scaled_falling_le_power epsilon r n he.le)
      (ContinuousLinearMap.opNorm_nonneg A)

/-- The number-preserving Wick map with its output index transported to n,
so coefficient operators of all degrees have one common endomorphism type. -/
def wickNumberMap (epsilon : ℝ) {r : ℕ}
    (A : SymmetricSector μ r →L[ℂ] SymmetricSector μ r) (n : ℕ) :
    SymmetricSector μ n →L[ℂ] SymmetricSector μ n :=
  (symmetricSectorCast μ (Nat.add_sub_cancel n r)).toLinearIsometry.toContinuousLinearMap ∘L
    wickSectorMap μ epsilon A n

@[simp] theorem norm_wickNumberMap_eq (epsilon : ℝ) {r : ℕ}
    (A : SymmetricSector μ r →L[ℂ] SymmetricSector μ r) (n : ℕ) :
    ‖wickNumberMap μ epsilon A n‖ = ‖wickSectorMap μ epsilon A n‖ := by
  exact ContinuousLinearMap.opNorm_linearIsometryEquiv_comp
    (symmetricSectorCast μ (Nat.add_sub_cancel n r)) (wickSectorMap μ epsilon A n)

@[simp] theorem wickNumberMap_of_lt (epsilon : ℝ) {r n : ℕ}
    (A : SymmetricSector μ r →L[ℂ] SymmetricSector μ r) (hn : n < r) :
    wickNumberMap μ epsilon A n = 0 := by
  simp only [wickNumberMap, wickSectorMap_of_lt μ epsilon A hn, ContinuousLinearMap.comp_zero]

/-- The endomorphism form consumed by finite-sector transfer sums. -/
theorem wickNumber_norm_le (epsilon : ℝ) {r n : ℕ}
    (A : SymmetricSector μ r →L[ℂ] SymmetricSector μ r) (he : 0 < epsilon) :
    ‖wickNumberMap μ epsilon A n‖ ≤ epsilon ^ r * (n.descFactorial r : ℝ) * ‖A‖ ∧
      epsilon ^ r * (n.descFactorial r : ℝ) * ‖A‖ ≤ (epsilon * (n : ℝ)) ^ r * ‖A‖ := by
  rw [norm_wickNumberMap_eq]
  exact wickNumberMap_norm_le μ epsilon A he

end LiebLiniger.FixedPeriod.Quantum
