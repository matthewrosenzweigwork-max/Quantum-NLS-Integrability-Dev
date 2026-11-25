import LiebLiniger.FixedPeriod.Quantum.SymmetricSector
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
Literal scalar and completed tensor bridges for the spatial product-L² sectors.
The empty product has total measure one, independently of the one-particle measure.
-/

noncomputable section
open MeasureTheory
open scoped TensorProduct InnerProductSpace BigOperators ENNReal

namespace LiebLiniger.FixedPeriod.Quantum

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

/-- Right invariance follows by reindexing the actual finite permutation average. -/
theorem symmetrizeL2_permutationL2 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : Equiv.Perm ι) (f : ProductL2 μ ι) :
    symmetrizeL2 μ (permutationL2 μ τ f) = symmetrizeL2 μ f := by
  simp only [symmetrizeL2_apply, permutationL2_mul]
  exact congrArg (fun z : ProductL2 μ ι =>
      (Fintype.card (Equiv.Perm ι) : ℂ)⁻¹ • z)
    (Function.Bijective.sum_comp (Group.mulRight_bijective τ)
      (fun σ => permutationL2 μ σ f))

section ZeroSector

local instance emptyProduct_isProbabilityMeasure :
    IsProbabilityMeasure (Measure.pi fun _ : Fin 0 => μ) :=
  ⟨Measure.pi_empty_univ _⟩

/-- A scalar regarded as a wave function on the empty configuration space. -/
def zeroSectorConst : ℂ →ₗᵢ[ℂ] ProductL2 μ (Fin 0) where
  toLinearMap := Lp.constₗ 2 (Measure.pi fun _ : Fin 0 => μ) ℂ
  norm_map' c := by
    change ‖Lp.const 2 (Measure.pi fun _ : Fin 0 => μ) c‖ = ‖c‖
    rw [Lp.norm_const' 2 (Measure.pi fun _ : Fin 0 => μ) c
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
    simp only [measureReal_def, Measure.pi_empty_univ, ENNReal.toReal_one,
      Real.one_rpow, mul_one]

/-- Every zero-particle wave function is a scalar constant; no point evaluation
on a positive-dimensional `L²` space is used. -/
theorem zeroSectorConst_surjective : Function.Surjective (zeroSectorConst μ) := by
  intro f
  let x₀ : Fin 0 → X := Fin.elim0
  refine ⟨f x₀, ?_⟩
  apply Lp.ext
  change Lp.const 2 (Measure.pi fun _ : Fin 0 => μ) (f x₀) =ᵐ[_] f
  filter_upwards [Lp.coeFn_const 2 (Measure.pi fun _ : Fin 0 => μ) (f x₀)] with x hx
  exact hx.trans (congrArg f (Subsingleton.elim x₀ x))

/-- The source's literal `Sym⁰ H = ℂ` at the unsymmetrized spatial carrier. -/
def zeroProductL2Equiv : ProductL2 μ (Fin 0) ≃ₗᵢ[ℂ] ℂ :=
  (LinearIsometryEquiv.ofSurjective (zeroSectorConst μ) (zeroSectorConst_surjective μ)).symm

@[simp] theorem zeroProductL2Equiv_const (z : ℂ) :
    zeroProductL2Equiv μ (zeroSectorConst μ z) = z :=
  (zeroProductL2Equiv μ).apply_symm_apply z

/-- The scalar zero-particle vector is unchanged by symmetrization. -/
@[simp] theorem zeroProductL2Equiv_symmetrize (f : ProductL2 μ (Fin 0)) :
    zeroProductL2Equiv μ (symmetrizeL2 μ f) = zeroProductL2Equiv μ f := by
  rw [symmetrizeL2_zero]

/-- In the zero-particle sector the fixed subspace is the whole scalar carrier. -/
def zeroSymmetricSectorInclusionEquiv :
    SymmetricSector μ 0 ≃ₗᵢ[ℂ] ProductL2 μ (Fin 0) :=
  LinearIsometryEquiv.ofSurjective (symmetricSectorInclusion μ 0) (by
    intro f
    exact ⟨⟨f, (mem_symmetricSectorSpace μ 0 f).mpr (symmetrizeL2_zero μ f)⟩, rfl⟩)

/-- The symmetric zero-particle sector is literally isometrically equivalent to ℂ. -/
def zeroSymmetricSectorEquiv : SymmetricSector μ 0 ≃ₗᵢ[ℂ] ℂ :=
  (zeroSymmetricSectorInclusionEquiv μ).trans (zeroProductL2Equiv μ)

/-- The empty pure tensor is exactly the scalar one vector. -/
theorem pureTensorL2_zero_eq_one (u : Lp ℂ 2 μ) :
    pureTensorL2 (ι := Fin 0) μ u = zeroSectorConst μ 1 := by
  apply Lp.ext
  filter_upwards [(pureTensorFunction_memLp (ι := Fin 0) μ u).coeFn_toLp,
    Lp.coeFn_const 2 (Measure.pi fun _ : Fin 0 => μ) (1 : ℂ)] with x hx hy
  change zeroSectorConst μ 1 x = 1 at hy
  exact hx.trans (by simpa only [Finset.univ_eq_empty, Finset.prod_empty] using hy.symm)

@[simp] theorem zeroProductL2Equiv_pureTensorL2 (u : Lp ℂ 2 μ) :
    zeroProductL2Equiv μ (pureTensorL2 (ι := Fin 0) μ u) = 1 := by
  rw [pureTensorL2_zero_eq_one, zeroProductL2Equiv_const]

end ZeroSector

section OneSector

/-- The one-coordinate product space is literally the original one-particle L² space. -/
def oneProductL2ToOneParticle : ProductL2 μ (Fin 1) →ₗᵢ[ℂ] Lp ℂ 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℂ
    (MeasurableEquiv.piUnique (fun _ : Fin 1 => X)).symm
    (measurePreserving_piUnique (fun _ : Fin 1 => μ)).symm

def oneParticleToOneProductL2 : Lp ℂ 2 μ →ₗᵢ[ℂ] ProductL2 μ (Fin 1) :=
  Lp.compMeasurePreservingₗᵢ ℂ (MeasurableEquiv.piUnique (fun _ : Fin 1 => X))
    (measurePreserving_piUnique (fun _ : Fin 1 => μ))

@[simp] theorem oneProductL2ToOneParticle_inverse (f : Lp ℂ 2 μ) :
    oneProductL2ToOneParticle μ (oneParticleToOneProductL2 μ f) = f := by
  change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
  rw [← Lp.compMeasurePreserving_comp_apply]
  have hid : (MeasurableEquiv.piUnique (fun _ : Fin 1 => X)) ∘
      (MeasurableEquiv.piUnique (fun _ : Fin 1 => X)).symm = id := by
    funext x
    exact (MeasurableEquiv.piUnique (fun _ : Fin 1 => X)).apply_symm_apply x
  simpa only [hid] using Lp.compMeasurePreserving_id_apply f

@[simp] theorem oneParticleToOneProductL2_inverse (f : ProductL2 μ (Fin 1)) :
    oneParticleToOneProductL2 μ (oneProductL2ToOneParticle μ f) = f := by
  change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
  rw [← Lp.compMeasurePreserving_comp_apply]
  have hid : (MeasurableEquiv.piUnique (fun _ : Fin 1 => X)).symm ∘
      (MeasurableEquiv.piUnique (fun _ : Fin 1 => X)) = id := by
    funext x
    exact (MeasurableEquiv.piUnique (fun _ : Fin 1 => X)).symm_apply_apply x
  simpa only [hid] using Lp.compMeasurePreserving_id_apply f

def oneProductL2Equiv : ProductL2 μ (Fin 1) ≃ₗᵢ[ℂ] Lp ℂ 2 μ where
  toLinearEquiv :=
    { toLinearMap := (oneProductL2ToOneParticle μ).toLinearMap
      invFun := oneParticleToOneProductL2 μ
      left_inv := oneParticleToOneProductL2_inverse μ
      right_inv := oneProductL2ToOneParticle_inverse μ }
  norm_map' := (oneProductL2ToOneParticle μ).norm_map

/-- The one-particle carrier identification preserves the literal pure tensor. -/
theorem oneProductL2Equiv_symm_eq_pureTensorL2 (u : Lp ℂ 2 μ) :
    (oneProductL2Equiv μ).symm u = pureTensorL2 (ι := Fin 1) μ u := by
  change oneParticleToOneProductL2 μ u = pureTensorL2 (ι := Fin 1) μ u
  apply Lp.ext
  have hl := Lp.coeFn_compMeasurePreserving u
    (measurePreserving_piUnique (fun _ : Fin 1 => μ))
  have hr := (pureTensorFunction_memLp (ι := Fin 1) μ u).coeFn_toLp
  filter_upwards [hl, hr] with x hl hr
  change oneParticleToOneProductL2 μ u x = u (x default) at hl
  change pureTensorL2 (ι := Fin 1) μ u x = ∏ i : Fin 1, u (x i) at hr
  rw [Fintype.prod_unique] at hr
  exact hl.trans hr.symm

end OneSector

/-- Coordinate concatenation as an actual linear isometry equivalence. -/
def regroupL2Equiv (p k : ℕ) : ProductL2 μ (Fin (p + k)) ≃ₗᵢ[ℂ]
    Lp ℂ 2 ((Measure.pi fun _ : Fin p => μ).prod (Measure.pi fun _ : Fin k => μ)) where
  toLinearEquiv :=
    { toLinearMap := (regroupL2 μ p k).toLinearMap
      invFun := unregroupL2 μ p k
      left_inv := unregroupL2_regroupL2 μ p k
      right_inv := regroupL2_unregroupL2 μ p k }
  norm_map' := (regroupL2 μ p k).norm_map

/-- Extend a permutation of the first p coordinates by the identity on k spectators. -/
def firstBlockPermutation (p k : ℕ) (σ : Equiv.Perm (Fin p)) :
    Equiv.Perm (Fin (p + k)) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr σ (Equiv.refl (Fin k))).trans finSumFinEquiv)

@[simp] theorem joinCoordinates_apply_sum (p k : ℕ)
    (z : (Fin p → X) × (Fin k → X)) (i : Fin p ⊕ Fin k) :
    joinCoordinates (X := X) p k z (finSumFinEquiv i) = Sum.elim z.1 z.2 i := by
  change (MeasurableEquiv.piCongrLeft (fun _ : Fin (p + k) => X) finSumFinEquiv)
    (Sum.elim z.1 z.2) (finSumFinEquiv i) = _
  exact MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun _ : Fin (p + k) => X) finSumFinEquiv (Sum.elim z.1 z.2) i

/-- The literal coordinate equality behind A tensor identity on the first block. -/
theorem joinCoordinates_firstBlockPermutation (p k : ℕ) (σ : Equiv.Perm (Fin p))
    (z : (Fin p → X) × (Fin k → X)) :
    joinCoordinates p k (coordinatePermutation σ z.1, z.2) =
      coordinatePermutation (firstBlockPermutation p k σ) (joinCoordinates p k z) := by
  funext i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
  cases j with
  | inl j =>
    simp only [joinCoordinates_apply_sum, Sum.elim_inl, coordinatePermutation_apply,
      firstBlockPermutation, Equiv.trans_apply, Equiv.symm_apply_apply,
      Equiv.sumCongr_apply, Sum.map_inl, Equiv.refl_apply]
  | inr j =>
    simp only [joinCoordinates_apply_sum, Sum.elim_inr, coordinatePermutation_apply,
      firstBlockPermutation, Equiv.trans_apply, Equiv.symm_apply_apply,
      Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply]

/-- Pure tensor functions factor exactly under coordinate concatenation. -/
theorem pureTensorFunction_joinCoordinates (p k : ℕ) (u : X → ℂ)
    (z : (Fin p → X) × (Fin k → X)) :
    (∏ i : Fin (p + k), u (joinCoordinates p k z i)) =
      (∏ i : Fin p, u (z.1 i)) * ∏ i : Fin k, u (z.2 i) := by
  calc
    _ = ∏ i : Fin p ⊕ Fin k, u (joinCoordinates p k z (finSumFinEquiv i)) :=
      (Equiv.prod_comp finSumFinEquiv (fun i => u (joinCoordinates p k z i))).symm
    _ = _ := by
      simp only [joinCoordinates_apply_sum, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]

/-- The genuine L² pure tensor factors into the separated product of its two
coordinate blocks; all null-set representatives are handled explicitly. -/
theorem regroupL2_pureTensorL2 (p k : ℕ) (u : Lp ℂ 2 μ) :
    regroupL2 μ p k (pureTensorL2 (ι := Fin (p + k)) μ u) =
      separatedL2 (Measure.pi fun _ : Fin p => μ) (Measure.pi fun _ : Fin k => μ)
        (pureTensorL2 (ι := Fin p) μ u) (pureTensorL2 (ι := Fin k) μ u) := by
  apply Lp.ext
  have hl := Lp.coeFn_compMeasurePreserving (pureTensorL2 (ι := Fin (p + k)) μ u)
    (joinCoordinates_measurePreserving μ p k)
  have hr := (joinCoordinates_measurePreserving μ p k).quasiMeasurePreserving.ae_eq_comp
    (pureTensorFunction_memLp (ι := Fin (p + k)) μ u).coeFn_toLp
  have hp := (Measure.quasiMeasurePreserving_fst
    (μ := Measure.pi fun _ : Fin p => μ) (ν := Measure.pi fun _ : Fin k => μ)).ae_eq_comp
    (pureTensorFunction_memLp (ι := Fin p) μ u).coeFn_toLp
  have hk := (Measure.quasiMeasurePreserving_snd
    (μ := Measure.pi fun _ : Fin p => μ) (ν := Measure.pi fun _ : Fin k => μ)).ae_eq_comp
    (pureTensorFunction_memLp (ι := Fin k) μ u).coeFn_toLp
  have hs := separatedL2_coeFn (Measure.pi fun _ : Fin p => μ)
    (Measure.pi fun _ : Fin k => μ) (pureTensorL2 (ι := Fin p) μ u)
    (pureTensorL2 (ι := Fin k) μ u)
  filter_upwards [hl, hr, hp, hk, hs] with z hl hr hp hk hs
  calc
    _ = pureTensorL2 (ι := Fin (p + k)) μ u (joinCoordinates p k z) := hl
    _ = ∏ i : Fin (p + k), u (joinCoordinates p k z i) := hr
    _ = (∏ i : Fin p, u (z.1 i)) * ∏ i : Fin k, u (z.2 i) :=
      pureTensorFunction_joinCoordinates p k u z
    _ = pureTensorL2 (ι := Fin p) μ u z.1 * pureTensorL2 (ι := Fin k) μ u z.2 :=
      congrArg₂ (· * ·) hp.symm hk.symm
    _ = _ := hs.symm

/-- The actual L² pullback of a permutation of just the first coordinate block. -/
def firstBlockPermutationL2 (p k : ℕ) (σ : Equiv.Perm (Fin p)) :
    Lp ℂ 2 ((Measure.pi fun _ : Fin p => μ).prod (Measure.pi fun _ : Fin k => μ)) →ₗᵢ[ℂ]
      Lp ℂ 2 ((Measure.pi fun _ : Fin p => μ).prod (Measure.pi fun _ : Fin k => μ)) :=
  Lp.compMeasurePreservingₗᵢ ℂ (Prod.map (coordinatePermutation σ) id)
    ((coordinatePermutation_measurePreserving μ σ).prod (MeasurePreserving.id _))

/-- Regrouping intertwines the global embedded permutation with its genuine
first-block action on the spatial product. -/
theorem regroupL2_firstBlockPermutation (p k : ℕ) (σ : Equiv.Perm (Fin p))
    (f : ProductL2 μ (Fin (p + k))) :
    regroupL2 μ p k (permutationL2 μ (firstBlockPermutation p k σ) f) =
      firstBlockPermutationL2 μ p k σ (regroupL2 μ p k f) := by
  change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) =
    Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f)
  rw [← Lp.compMeasurePreserving_comp_apply, ← Lp.compMeasurePreserving_comp_apply]
  have hc : coordinatePermutation (X := X) (firstBlockPermutation p k σ) ∘
      joinCoordinates p k = joinCoordinates p k ∘ Prod.map (coordinatePermutation σ) id := by
    funext z
    exact (joinCoordinates_firstBlockPermutation p k σ z).symm
  simp only [hc]

/-- A globally symmetric state is invariant under each actual first-block
permutation after regrouping. This removes the input-symmetrizer obligation
at the concrete coordinate level. -/
theorem firstBlockPermutationL2_regroup_symmetric (p k : ℕ)
    (σ : Equiv.Perm (Fin p)) (f : SymmetricSector μ (p + k)) :
    firstBlockPermutationL2 μ p k σ (regroupL2 μ p k (f : ProductL2 μ (Fin (p + k)))) =
      regroupL2 μ p k (f : ProductL2 μ (Fin (p + k))) := by
  rw [← regroupL2_firstBlockPermutation]
  have hf := (symmetrizeL2_eq_self_iff μ (f : ProductL2 μ (Fin (p + k)))).mp
    (symmetricSector_fixed μ (p + k) f)
  rw [hf (firstBlockPermutation p k σ)]

section FiniteMeasure
variable [IsFiniteMeasure μ]

/-- The genuine Hilbert tensor bridge for arbitrary finite blocks of particles.
In combination with zeroProductL2Equiv and oneProductL2Equiv, these equivalences
realize the spatial family as the completed finite Hilbert tensor powers of H. -/
def completedProductTensorEquiv (p k : ℕ) :
    UniformSpace.Completion (ProductL2 μ (Fin p) ⊗[ℂ] ProductL2 μ (Fin k)) ≃ₗᵢ[ℂ]
      ProductL2 μ (Fin (p + k)) :=
  (spatialTensorEquiv (Measure.pi fun _ : Fin p => μ)
    (Measure.pi fun _ : Fin k => μ)).trans (regroupL2Equiv μ p k).symm

/-- The completed tensor bridge has the exact elementary-kernel normalization. -/
theorem completedProductTensorEquiv_tmul (p k : ℕ)
    (f : ProductL2 μ (Fin p)) (g : ProductL2 μ (Fin k)) :
    completedProductTensorEquiv μ p k
      ((f ⊗ₜ[ℂ] g : ProductL2 μ (Fin p) ⊗[ℂ] ProductL2 μ (Fin k)) :
        UniformSpace.Completion (ProductL2 μ (Fin p) ⊗[ℂ] ProductL2 μ (Fin k))) =
      unregroupL2 μ p k (separatedL2 (Measure.pi fun _ : Fin p => μ)
        (Measure.pi fun _ : Fin k => μ) f g) := by
  change unregroupL2 μ p k
    ((spatialTensorIsometry (Measure.pi fun _ : Fin p => μ)
      (Measure.pi fun _ : Fin k => μ)).fromCompletion
      ((f ⊗ₜ[ℂ] g : ProductL2 μ (Fin p) ⊗[ℂ] ProductL2 μ (Fin k)) :
        UniformSpace.Completion (ProductL2 μ (Fin p) ⊗[ℂ] ProductL2 μ (Fin k)))) = _
  rw [LinearIsometry.fromCompletion_apply_coe]
  rfl

/-- Completed elementary pure tensors agree exactly with the full spatial pure tensor. -/
theorem completedProductTensorEquiv_pureTensorL2 (p k : ℕ) (u : Lp ℂ 2 μ) :
    completedProductTensorEquiv μ p k
      ((pureTensorL2 (ι := Fin p) μ u ⊗ₜ[ℂ] pureTensorL2 (ι := Fin k) μ u :
          ProductL2 μ (Fin p) ⊗[ℂ] ProductL2 μ (Fin k)) :
        UniformSpace.Completion (ProductL2 μ (Fin p) ⊗[ℂ] ProductL2 μ (Fin k))) =
      pureTensorL2 (ι := Fin (p + k)) μ u := by
  rw [completedProductTensorEquiv_tmul]
  apply (regroupL2 μ p k).injective
  rw [regroupL2_unregroupL2, regroupL2_pureTensorL2]

/-- Orthogonality and contraction hold on the concrete Hilbert tensor carrier,
without any assumed projection or symmetrization law. -/
theorem productTensor_symmetrization_contraction (n : ℕ) :
    (symmetrizeL2 (ι := Fin n) μ).toLinearMap.IsSymmetricProjection ∧
      ‖symmetrizeL2 (ι := Fin n) μ‖ ≤ 1 :=
  ⟨symmetrizeL2_isSymmetricProjection μ, norm_symmetrizeL2_le_one μ⟩

end FiniteMeasure
end LiebLiniger.FixedPeriod.Quantum

namespace LiebLiniger.FixedPeriod.Quantum

/-- A bundled complete complex Hilbert space, used only to make recursive
completed tensor powers carry their inherited instances definitionally. -/
structure CompleteComplexHilbert where
  carrier : Type
  [normedAddCommGroup : NormedAddCommGroup carrier]
  [innerProductSpace : InnerProductSpace ℂ carrier]
  [completeSpace : CompleteSpace carrier]

instance : CoeSort CompleteComplexHilbert Type := ⟨CompleteComplexHilbert.carrier⟩
attribute [instance] CompleteComplexHilbert.normedAddCommGroup
  CompleteComplexHilbert.innerProductSpace CompleteComplexHilbert.completeSpace

/-- Bundle the already established instances of a genuine Hilbert space. -/
def CompleteComplexHilbert.of (E : Type) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] : CompleteComplexHilbert :=
  { carrier := E }

/-- Literal completed Hilbert tensor powers: zero is ℂ and every successor
is the completion of the algebraic Hilbert tensor product with H. -/
def recursiveHilbertTensorPower (H : CompleteComplexHilbert) : ℕ → CompleteComplexHilbert
  | 0 => CompleteComplexHilbert.of ℂ
  | n + 1 => CompleteComplexHilbert.of
      (UniformSpace.Completion (H ⊗[ℂ] recursiveHilbertTensorPower H n))

section CompletionCongr
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A genuine linear isometry equivalence extends to the completions. -/
def completionIsometryEquiv (e : E ≃ₗᵢ[ℂ] F) :
    UniformSpace.Completion E ≃ₗᵢ[ℂ] UniformSpace.Completion F where
  toLinearEquiv :=
    { toLinearMap := e.toLinearIsometry.completion.toLinearMap
      invFun := e.symm.toLinearIsometry.completion
      left_inv := by
        intro x
        refine UniformSpace.Completion.induction_on x
          (p := fun y => e.symm.toLinearIsometry.completion
            (e.toLinearIsometry.completion y) = y) ?_ ?_
        · exact isClosed_eq
            (e.symm.toLinearIsometry.completion.continuous.comp
              e.toLinearIsometry.completion.continuous) continuous_id
        · intro a
          simp only [LinearIsometry.completion_apply_coe]
          change (↑(e.symm (e a)) : UniformSpace.Completion E) =
            (a : UniformSpace.Completion E)
          exact congrArg (fun y : E => (y : UniformSpace.Completion E)) (e.symm_apply_apply a)
      right_inv := by
        intro x
        refine UniformSpace.Completion.induction_on x
          (p := fun y => e.toLinearIsometry.completion
            (e.symm.toLinearIsometry.completion y) = y) ?_ ?_
        · exact isClosed_eq
            (e.toLinearIsometry.completion.continuous.comp
              e.symm.toLinearIsometry.completion.continuous) continuous_id
        · intro a
          simp only [LinearIsometry.completion_apply_coe]
          change (↑(e (e.symm a)) : UniformSpace.Completion F) =
            (a : UniformSpace.Completion F)
          exact congrArg (fun y : F => (y : UniformSpace.Completion F)) (e.apply_symm_apply a) }
  norm_map' := e.toLinearIsometry.completion.norm_map

@[simp] theorem completionIsometryEquiv_coe (e : E ≃ₗᵢ[ℂ] F) (x : E) :
    completionIsometryEquiv e (x : UniformSpace.Completion E) =
      (e x : UniformSpace.Completion F) :=
  e.toLinearIsometry.completion_apply_coe x

end CompletionCongr

section RecursiveSpatialRealization
variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

/-- Equality of particle numbers induces the literal carrier transport. -/
def productL2Cast {m n : ℕ} (h : m = n) :
    ProductL2 μ (Fin m) ≃ₗᵢ[ℂ] ProductL2 μ (Fin n) := by
  subst n
  exact LinearIsometryEquiv.refl ℂ _

abbrev SpatialHilbertTensorPower (n : ℕ) :=
  recursiveHilbertTensorPower (CompleteComplexHilbert.of (Lp ℂ 2 μ)) n

/-- The actual n-fold completed Hilbert tensor power of one-particle L² is
isometrically equivalent to the spatial n-coordinate L² carrier. The proof
constructs every successor through the genuine completed binary tensor bridge. -/
def spatialTensorPowerEquiv : (n : ℕ) →
    SpatialHilbertTensorPower μ n ≃ₗᵢ[ℂ] ProductL2 μ (Fin n)
  | 0 => (zeroProductL2Equiv μ).symm
  | n + 1 =>
    ((completionIsometryEquiv
      (TensorProduct.congrIsometry (oneProductL2Equiv μ).symm
        (spatialTensorPowerEquiv n))).trans (completedProductTensorEquiv μ 1 n)).trans
      (productL2Cast μ (Nat.add_comm 1 n))

/-- The actual recursive elementary tensor, beginning with scalar one. -/
def recursiveHilbertPureTensor (u : Lp ℂ 2 μ) :
    (n : ℕ) → SpatialHilbertTensorPower μ n
  | 0 => (1 : ℂ)
  | n + 1 =>
    ((u ⊗ₜ[ℂ] recursiveHilbertPureTensor u n :
        Lp ℂ 2 μ ⊗[ℂ] SpatialHilbertTensorPower μ n) :
      UniformSpace.Completion (Lp ℂ 2 μ ⊗[ℂ] SpatialHilbertTensorPower μ n))

@[simp] theorem productL2Cast_pureTensorL2 {m n : ℕ} (h : m = n) (u : Lp ℂ 2 μ) :
    productL2Cast μ h (pureTensorL2 (ι := Fin m) μ u) =
      pureTensorL2 (ι := Fin n) μ u := by
  subst n
  rfl

/-- The tensor realization preserves the source's pure tensors at every order. -/
theorem spatialTensorPowerEquiv_pureTensor (u : Lp ℂ 2 μ) (n : ℕ) :
    spatialTensorPowerEquiv μ n (recursiveHilbertPureTensor μ u n) =
      pureTensorL2 (ι := Fin n) μ u := by
  induction n with
  | zero =>
    change (zeroProductL2Equiv μ).symm 1 = pureTensorL2 (ι := Fin 0) μ u
    rw [pureTensorL2_zero_eq_one]
    rfl
  | succ n ih =>
    change productL2Cast μ (Nat.add_comm 1 n)
      (completedProductTensorEquiv μ 1 n
        (completionIsometryEquiv
          (TensorProduct.congrIsometry (oneProductL2Equiv μ).symm
            (spatialTensorPowerEquiv μ n))
          ((u ⊗ₜ[ℂ] recursiveHilbertPureTensor μ u n :
              Lp ℂ 2 μ ⊗[ℂ] SpatialHilbertTensorPower μ n) :
            UniformSpace.Completion (Lp ℂ 2 μ ⊗[ℂ] SpatialHilbertTensorPower μ n)))) = _
    rw [completionIsometryEquiv_coe]
    change productL2Cast μ (Nat.add_comm 1 n)
      (completedProductTensorEquiv μ 1 n
        (((oneProductL2Equiv μ).symm u ⊗ₜ[ℂ]
            spatialTensorPowerEquiv μ n (recursiveHilbertPureTensor μ u n) :
              ProductL2 μ (Fin 1) ⊗[ℂ] ProductL2 μ (Fin n)) :
          UniformSpace.Completion (ProductL2 μ (Fin 1) ⊗[ℂ] ProductL2 μ (Fin n)))) = _
    rw [oneProductL2Equiv_symm_eq_pureTensorL2, ih,
      completedProductTensorEquiv_pureTensorL2, productL2Cast_pureTensorL2]

/-- The genuine unitary coordinate permutation, including its inverse. -/
def permutationL2Equiv (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    ProductL2 μ (Fin n) ≃ₗᵢ[ℂ] ProductL2 μ (Fin n) where
  toLinearEquiv :=
    { toLinearMap := (permutationL2 μ σ).toLinearMap
      invFun := permutationL2 μ σ⁻¹
      left_inv := by
        intro f
        change permutationL2 μ σ⁻¹ (permutationL2 μ σ f) = f
        rw [permutationL2_mul, inv_mul_cancel, permutationL2_one]
      right_inv := by
        intro f
        change permutationL2 μ σ (permutationL2 μ σ⁻¹ f) = f
        rw [permutationL2_mul, mul_inv_cancel, permutationL2_one] }
  norm_map' := (permutationL2 μ σ).norm_map

/-- Coordinate permutation transported along the established tensor realization. -/
def hilbertTensorPermutation (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    SpatialHilbertTensorPower μ n ≃ₗᵢ[ℂ] SpatialHilbertTensorPower μ n :=
  ((spatialTensorPowerEquiv μ n).trans (permutationL2Equiv μ n σ)).trans
    (spatialTensorPowerEquiv μ n).symm

/-- Symmetrization on the literal completed tensor power is the transported
actual normalized permutation average. -/
def hilbertTensorSymmetrize (n : ℕ) :
    SpatialHilbertTensorPower μ n →L[ℂ] SpatialHilbertTensorPower μ n :=
  (spatialTensorPowerEquiv μ n).symm.toLinearIsometry.toContinuousLinearMap ∘L
    symmetrizeL2 μ ∘L (spatialTensorPowerEquiv μ n).toLinearIsometry.toContinuousLinearMap

@[simp] theorem hilbertTensorSymmetrize_apply (n : ℕ)
    (f : SpatialHilbertTensorPower μ n) :
    hilbertTensorSymmetrize μ n f = (spatialTensorPowerEquiv μ n).symm
      (symmetrizeL2 μ (spatialTensorPowerEquiv μ n f)) := rfl

/-- On the literal completed tensor carrier the operator is exactly the
normalized finite average of the transported permutation unitaries. -/
theorem hilbertTensorSymmetrize_eq_average (n : ℕ) :
    hilbertTensorSymmetrize μ n =
      isometryAverage (fun σ : Equiv.Perm (Fin n) =>
        (hilbertTensorPermutation μ n σ).toLinearIsometry) := by
  apply ContinuousLinearMap.ext
  intro f
  rw [hilbertTensorSymmetrize_apply, symmetrizeL2_apply, isometryAverage_apply,
    map_smul, map_sum]
  rfl

/-- Every actual recursive pure tensor is fixed by the tensor permutation average. -/
@[simp] theorem hilbertTensorSymmetrize_pureTensor (u : Lp ℂ 2 μ) (n : ℕ) :
    hilbertTensorSymmetrize μ n (recursiveHilbertPureTensor μ u n) =
      recursiveHilbertPureTensor μ u n := by
  apply (spatialTensorPowerEquiv μ n).injective
  simp only [hilbertTensorSymmetrize_apply, LinearIsometryEquiv.apply_symm_apply,
    spatialTensorPowerEquiv_pureTensor, symmetrizeL2_pureTensorL2]

/-- The exact Hilbert tensor carrier, with no supplied projection hypotheses,
has an orthogonal permutation average of operator norm at most one. -/
theorem hilbertTensorSymmetrize_contraction (n : ℕ) :
    (hilbertTensorSymmetrize μ n).toLinearMap.IsSymmetricProjection ∧
      ‖hilbertTensorSymmetrize μ n‖ ≤ 1 := by
  constructor
  · constructor
    · apply LinearMap.ext
      intro f
      change hilbertTensorSymmetrize μ n (hilbertTensorSymmetrize μ n f) =
        hilbertTensorSymmetrize μ n f
      simp only [hilbertTensorSymmetrize_apply, LinearIsometryEquiv.apply_symm_apply,
        symmetrizeL2_idempotent]
    · intro f g
      change ⟪hilbertTensorSymmetrize μ n f, g⟫_ℂ =
        ⟪f, hilbertTensorSymmetrize μ n g⟫_ℂ
      have hf := (spatialTensorPowerEquiv μ n).inner_map_map
        (hilbertTensorSymmetrize μ n f) g
      have hg := (spatialTensorPowerEquiv μ n).inner_map_map
        f (hilbertTensorSymmetrize μ n g)
      rw [← hf, ← hg]
      simp only [hilbertTensorSymmetrize_apply, LinearIsometryEquiv.apply_symm_apply]
      exact symmetrizeL2_isSymmetric μ _ _
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro f
    change ‖(spatialTensorPowerEquiv μ n).symm
      (symmetrizeL2 μ (spatialTensorPowerEquiv μ n f))‖ ≤ 1 * ‖f‖
    rw [LinearIsometryEquiv.norm_map, one_mul]
    exact (norm_symmetrizeL2_apply_le μ _).trans_eq
      ((spatialTensorPowerEquiv μ n).norm_map f)

end RecursiveSpatialRealization
end LiebLiniger.FixedPeriod.Quantum
