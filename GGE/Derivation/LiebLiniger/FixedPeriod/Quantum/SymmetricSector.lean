import LiebLiniger.FixedPeriod.Quantum.TransferKernel
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
Concrete closed symmetric sectors and the canonical regrouping of product-L²
coordinates. Candidate only; author does not run the shared compiler queue.
No supplied splitting/operator estimate is assumed.
-/

noncomputable section
open MeasureTheory
open scoped TensorProduct ENNReal

namespace LiebLiniger.FixedPeriod.Quantum

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

/-- The closed subspace of permutation-invariant n-particle wave functions.
The definition uses the actual normalized permutation average. -/
def SymmetricSectorSpace (n : ℕ) : Submodule ℂ (ProductL2 μ (Fin n)) :=
  (symmetrizeL2 μ - ContinuousLinearMap.id ℂ (ProductL2 μ (Fin n))).ker

abbrev SymmetricSector (n : ℕ) := SymmetricSectorSpace μ n

theorem mem_symmetricSectorSpace (n : ℕ) (f : ProductL2 μ (Fin n)) :
    f ∈ SymmetricSectorSpace μ n ↔ symmetrizeL2 μ f = f := by
  change symmetrizeL2 μ f - f = 0 ↔ symmetrizeL2 μ f = f
  exact sub_eq_zero

theorem symmetricSectorSpace_isClosed (n : ℕ) :
    IsClosed (SymmetricSectorSpace μ n : Set (ProductL2 μ (Fin n))) :=
  (symmetrizeL2 μ - ContinuousLinearMap.id ℂ (ProductL2 μ (Fin n))).isClosed_ker

instance symmetricSector_completeSpace (n : ℕ) : CompleteSpace (SymmetricSector μ n) := by
  unfold SymmetricSector SymmetricSectorSpace
  infer_instance

/-- The canonical inclusion preserves the Hilbert norm. -/
def symmetricSectorInclusion (n : ℕ) :
    SymmetricSector μ n →ₗᵢ[ℂ] ProductL2 μ (Fin n) :=
  (SymmetricSectorSpace μ n).subtypeₗᵢ

@[simp] theorem symmetricSector_fixed (n : ℕ) (f : SymmetricSector μ n) :
    symmetrizeL2 μ (f : ProductL2 μ (Fin n)) = f :=
  (mem_symmetricSectorSpace μ n f).mp f.property

/-- The actual permutation average with codomain restricted to its fixed space. -/
def symmetricSectorProjection (n : ℕ) :
    ProductL2 μ (Fin n) →L[ℂ] SymmetricSector μ n :=
  (symmetrizeL2 μ).codRestrict (SymmetricSectorSpace μ n) fun f =>
    (mem_symmetricSectorSpace μ n _).mpr (symmetrizeL2_idempotent μ f)

@[simp] theorem symmetricSectorProjection_coe (n : ℕ) (f : ProductL2 μ (Fin n)) :
    (symmetricSectorProjection μ n f : ProductL2 μ (Fin n)) = symmetrizeL2 μ f := rfl

@[simp] theorem symmetricSectorProjection_inclusion (n : ℕ) (f : SymmetricSector μ n) :
    symmetricSectorProjection μ n (symmetricSectorInclusion μ n f) = f := by
  apply Subtype.ext
  exact symmetricSector_fixed μ n f

theorem norm_symmetricSectorProjection_apply_le (n : ℕ) (f : ProductL2 μ (Fin n)) :
    ‖symmetricSectorProjection μ n f‖ ≤ ‖f‖ :=
  norm_symmetrizeL2_apply_le μ f

theorem norm_symmetricSectorProjection_le_one (n : ℕ) :
    ‖symmetricSectorProjection μ n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using norm_symmetricSectorProjection_apply_le μ n f

/-- Concatenate the first p coordinates and the last k coordinates, preserving
product measures exactly. This includes p=0 and k=0. -/
def joinCoordinates (p k : ℕ) :
    ((Fin p → X) × (Fin k → X)) ≃ᵐ (Fin (p + k) → X) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin p ⊕ Fin k => X)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (p + k) => X) finSumFinEquiv)

theorem joinCoordinates_measurePreserving (p k : ℕ) :
    MeasurePreserving (joinCoordinates (X := X) p k)
      ((Measure.pi fun _ : Fin p => μ).prod (Measure.pi fun _ : Fin k => μ))
      (Measure.pi fun _ : Fin (p + k) => μ) := by
  exact (measurePreserving_piCongrLeft (fun _ : Fin (p + k) => μ) finSumFinEquiv).comp
    (measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin p ⊕ Fin k => μ))

/-- Canonical isometric regrouping of a wave function into its two coordinate
blocks; this is not yet an identification with a completed Hilbert tensor. -/
def regroupL2 (p k : ℕ) :
    ProductL2 μ (Fin (p + k)) →ₗᵢ[ℂ]
      Lp ℂ 2 ((Measure.pi fun _ : Fin p => μ).prod (Measure.pi fun _ : Fin k => μ)) :=
  Lp.compMeasurePreservingₗᵢ ℂ (joinCoordinates p k)
    (joinCoordinates_measurePreserving μ p k)

/-- The inverse coordinate regrouping is also an actual pullback isometry. -/
def unregroupL2 (p k : ℕ) :
    Lp ℂ 2 ((Measure.pi fun _ : Fin p => μ).prod (Measure.pi fun _ : Fin k => μ)) →ₗᵢ[ℂ]
      ProductL2 μ (Fin (p + k)) :=
  Lp.compMeasurePreservingₗᵢ ℂ (joinCoordinates (X := X) p k).symm
    (joinCoordinates_measurePreserving μ p k).symm

@[simp] theorem unregroupL2_regroupL2 (p k : ℕ) (f : ProductL2 μ (Fin (p + k))) :
    unregroupL2 μ p k (regroupL2 μ p k f) = f := by
  change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
  rw [← Lp.compMeasurePreserving_comp_apply]
  have hid : (joinCoordinates (X := X) p k) ∘ (joinCoordinates p k).symm = id := by
    funext x
    exact (joinCoordinates p k).apply_symm_apply x
  simpa only [hid] using Lp.compMeasurePreserving_id_apply f

@[simp] theorem regroupL2_unregroupL2 (p k : ℕ)
    (f : Lp ℂ 2 ((Measure.pi fun _ : Fin p => μ).prod (Measure.pi fun _ : Fin k => μ))) :
    regroupL2 μ p k (unregroupL2 μ p k f) = f := by
  change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
  rw [← Lp.compMeasurePreserving_comp_apply]
  have hid : (joinCoordinates (X := X) p k).symm ∘ (joinCoordinates p k) = id := by
    funext x
    exact (joinCoordinates p k).symm_apply_apply x
  simpa only [hid] using Lp.compMeasurePreserving_id_apply f

/-- The source sector embeds isometrically into the coordinate-regrouped L²
space. Converting that space to (Sym^p H) tensor H^k remains a separate theorem. -/
def symmetricSectorRegrouping (p k : ℕ) :
    SymmetricSector μ (p + k) →ₗᵢ[ℂ]
      Lp ℂ 2 ((Measure.pi fun _ : Fin p => μ).prod (Measure.pi fun _ : Fin k => μ)) :=
  (regroupL2 μ p k).comp (symmetricSectorInclusion μ (p + k))

end LiebLiniger.FixedPeriod.Quantum


namespace LiebLiniger.FixedPeriod.Quantum

section SpatialTensor
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]

/-- An elementary separated spatial kernel is square integrable. -/
theorem separatedProduct_memLp (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    MemLp (fun z : X × Y => f z.1 * g z.2) 2 (μ.prod ν) := by
  have hm : AEStronglyMeasurable (fun z : X × Y => f z.1 * g z.2) (μ.prod ν) :=
    ((Lp.aestronglyMeasurable f).comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν))).mul
      ((Lp.aestronglyMeasurable g).comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)))
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  simpa only [norm_mul, mul_pow] using
    ((Lp.memLp f).norm.integrable_sq).mul_prod ((Lp.memLp g).norm.integrable_sq)

/-- The elementary spatial tensor f(x)g(y), constructed after integrability. -/
def separatedL2 (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) : Lp ℂ 2 (μ.prod ν) :=
  (separatedProduct_memLp μ ν f g).toLp (fun z => f z.1 * g z.2)

theorem separatedL2_coeFn (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    separatedL2 μ ν f g =ᵐ[μ.prod ν] (fun z => f z.1 * g z.2) :=
  MemLp.coeFn_toLp (separatedProduct_memLp μ ν f g)

/-- The spatial realization has exactly the Hilbert tensor inner product;
no unspecified tensor norm or normalization is used. -/
theorem separatedL2_inner (f f' : Lp ℂ 2 μ) (g g' : Lp ℂ 2 ν) :
    inner ℂ (separatedL2 μ ν f g) (separatedL2 μ ν f' g') =
      inner ℂ f f' * inner ℂ g g' := by
  rw [L2.inner_def, L2.inner_def, L2.inner_def]
  calc
    _ = ∫ z : X × Y, inner ℂ (f z.1) (f' z.1) * inner ℂ (g z.2) (g' z.2) ∂μ.prod ν := by
      apply integral_congr_ae
      filter_upwards [separatedL2_coeFn μ ν f g, separatedL2_coeFn μ ν f' g'] with z hz hz'
      rw [hz, hz']
      simp only [RCLike.inner_apply, map_mul]
      ring
    _ = _ := integral_prod_mul (μ := μ) (ν := ν)
      (fun x : X => inner ℂ (f x) (f' x)) (fun y : Y => inner ℂ (g y) (g' y))


theorem separatedL2_add_left (f f' : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    separatedL2 μ ν (f + f') g = separatedL2 μ ν f g + separatedL2 μ ν f' g := by
  apply Lp.ext
  filter_upwards [separatedL2_coeFn μ ν (f + f') g,
    separatedL2_coeFn μ ν f g, separatedL2_coeFn μ ν f' g,
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae_eq_comp (Lp.coeFn_add f f'),
    Lp.coeFn_add (separatedL2 μ ν f g) (separatedL2 μ ν f' g)] with z h₁ h₂ h₃ h₄ h₅
  dsimp only [Function.comp_apply, Pi.add_apply] at h₄ h₅
  rw [h₁, h₅, h₂, h₃, h₄]
  exact add_mul (f z.1) (f' z.1) (g z.2)

theorem separatedL2_add_right (f : Lp ℂ 2 μ) (g g' : Lp ℂ 2 ν) :
    separatedL2 μ ν f (g + g') = separatedL2 μ ν f g + separatedL2 μ ν f g' := by
  apply Lp.ext
  filter_upwards [separatedL2_coeFn μ ν f (g + g'),
    separatedL2_coeFn μ ν f g, separatedL2_coeFn μ ν f g',
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae_eq_comp (Lp.coeFn_add g g'),
    Lp.coeFn_add (separatedL2 μ ν f g) (separatedL2 μ ν f g')] with z h₁ h₂ h₃ h₄ h₅
  dsimp only [Function.comp_apply, Pi.add_apply] at h₄ h₅
  rw [h₁, h₅, h₂, h₃, h₄]
  exact mul_add (f z.1) (g z.2) (g' z.2)

theorem separatedL2_smul_left (c : ℂ) (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    separatedL2 μ ν (c • f) g = c • separatedL2 μ ν f g := by
  apply Lp.ext
  filter_upwards [separatedL2_coeFn μ ν (c • f) g, separatedL2_coeFn μ ν f g,
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae_eq_comp (Lp.coeFn_smul c f),
    Lp.coeFn_smul c (separatedL2 μ ν f g)] with z h₁ h₂ h₃ h₄
  dsimp only [Function.comp_apply, Pi.smul_apply] at h₃ h₄
  rw [h₁, h₄, h₂, h₃]
  exact mul_assoc c (f z.1) (g z.2)

theorem separatedL2_smul_right (c : ℂ) (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    separatedL2 μ ν f (c • g) = c • separatedL2 μ ν f g := by
  apply Lp.ext
  filter_upwards [separatedL2_coeFn μ ν f (c • g), separatedL2_coeFn μ ν f g,
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae_eq_comp (Lp.coeFn_smul c g),
    Lp.coeFn_smul c (separatedL2 μ ν f g)] with z h₁ h₂ h₃ h₄
  dsimp only [Function.comp_apply, Pi.smul_apply] at h₃ h₄
  rw [h₁, h₄, h₂, h₃]
  simp only [smul_eq_mul]
  ring

/-- The actual bilinear map of separated spatial kernels. -/
def separatedL2Bilinear : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 (μ.prod ν) where
  toFun f :=
    { toFun := separatedL2 μ ν f
      map_add' := separatedL2_add_right μ ν f
      map_smul' := fun c g => separatedL2_smul_right μ ν c f g }
  map_add' f f' := LinearMap.ext (fun g => separatedL2_add_left μ ν f f' g)
  map_smul' c f := LinearMap.ext (fun g => separatedL2_smul_left μ ν c f g)

/-- Spatial realization on the algebraic Hilbert tensor product. -/
def spatialTensorLinear :
    (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) →ₗ[ℂ] Lp ℂ 2 (μ.prod ν) :=
  TensorProduct.lift (separatedL2Bilinear μ ν)

@[simp] theorem spatialTensorLinear_tmul (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    spatialTensorLinear μ ν (f ⊗ₜ[ℂ] g) = separatedL2 μ ν f g := rfl

/-- Fubini proves the full tensor inner-product identity before completion. -/
theorem spatialTensorLinear_inner (x y : Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) :
    inner ℂ (spatialTensorLinear μ ν x) (spatialTensorLinear μ ν y) = inner ℂ x y := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, inner_zero_left]
  | tmul f g =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero, inner_zero_right]
    | tmul f' g' =>
      rw [spatialTensorLinear_tmul, spatialTensorLinear_tmul, separatedL2_inner,
        TensorProduct.inner_tmul]
    | add y z hy hz => simp only [map_add, inner_add_right, hy, hz]
  | add x y hx hy => simp only [map_add, inner_add_left, hx, hy]

/-- The actual separated-kernel map is an isometry, not an assumed one. -/
def spatialTensorIsometry :
    (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) →ₗᵢ[ℂ] Lp ℂ 2 (μ.prod ν) :=
  (spatialTensorLinear μ ν).isometryOfInner (spatialTensorLinear_inner μ ν)

/-- The spatial tensor norm is inherited from the already established
Hilbert tensor isometry; this avoids alternate scalar-instance presentations. -/
theorem norm_separatedL2 (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    ‖separatedL2 μ ν f g‖ = ‖f‖ * ‖g‖ := by
  change ‖spatialTensorIsometry μ ν (f ⊗ₜ[ℂ] g)‖ = ‖f‖ * ‖g‖
  rw [LinearIsometry.norm_map]
  exact TensorProduct.norm_tmul f g

/-- Its canonical extension to the completed Hilbert tensor product.
Surjectivity/density is deliberately not assumed or asserted. -/
def spatialTensorCompletion :
    UniformSpace.Completion (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) →ₗᵢ[ℂ] Lp ℂ 2 (μ.prod ν) :=
  (spatialTensorIsometry μ ν).fromCompletion


/-- Vanishing rectangle integrals determine an integrable spatial kernel.
The pi-system argument proves the required density ingredient. -/
theorem ae_eq_zero_of_rectangle_integrals (f : X × Y → ℂ)
    (hf : Integrable f (μ.prod ν))
    (hrect : ∀ (s : Set X) (t : Set Y), MeasurableSet s → MeasurableSet t →
      ∫ z in s ×ˢ t, f z ∂μ.prod ν = 0) : f =ᵐ[μ.prod ν] 0 := by
  have hu : ∫ z, f z ∂μ.prod ν = 0 := by
    simpa only [Set.univ_prod_univ, setIntegral_univ] using hrect Set.univ Set.univ .univ .univ
  have hall : ∀ s : Set (X × Y), MeasurableSet s → ∫ z in s, f z ∂μ.prod ν = 0 := by
    refine MeasurableSpace.induction_on_inter
      (C := fun s _ => ∫ z in s, f z ∂μ.prod ν = 0)
      generateFrom_prod.symm isPiSystem_prod ?_ ?_ ?_ ?_
    · simp only [setIntegral_empty]
    · rintro _ ⟨s, hs, t, ht, rfl⟩
      exact hrect s t hs ht
    · intro s hs hzero
      have h := integral_add_compl hs hf
      rw [hzero, zero_add, hu] at h
      exact h
    · intro s hdisj hs hzero
      rw [integral_iUnion hs hdisj hf.integrableOn]
      simp only [hzero, tsum_zero]
  exact ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite
    (fun _ _ _ => hf.integrableOn) (fun s hs _ => hall s hs)

theorem separatedL2_indicator (s : Set X) (t : Set Y) (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hμs : μ s ≠ ∞) (hνt : ν t ≠ ∞) :
    separatedL2 μ ν (indicatorConstLp 2 hs hμs (1 : ℂ))
      (indicatorConstLp 2 ht hνt (1 : ℂ)) =
    indicatorConstLp 2 (hs.prod ht)
      (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hμs hνt) (1 : ℂ) := by
  apply Lp.ext
  filter_upwards [separatedL2_coeFn μ ν (indicatorConstLp 2 hs hμs (1 : ℂ))
      (indicatorConstLp 2 ht hνt (1 : ℂ)),
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae_eq_comp (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := (1 : ℂ))),
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae_eq_comp (indicatorConstLp_coeFn (p := 2) (hs := ht) (hμs := hνt) (c := (1 : ℂ))),
    indicatorConstLp_coeFn (p := 2) (hs := hs.prod ht)
      (hμs := by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hμs hνt) (c := (1 : ℂ))] with z h₁ h₂ h₃ h₄
  simp only [Function.comp_apply] at h₂ h₃
  rw [h₁, h₂, h₃, h₄]
  by_cases hx : z.1 ∈ s <;> by_cases hy : z.2 ∈ t <;> simp [hx, hy, Set.mem_prod]

section FiniteSpatialMeasures
variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- Separated spatial kernels span a dense subspace of the product L² space.
Finite measure is used only to put an arbitrary L² vector in L¹; physical
fixed-period Lebesgue measures satisfy it. -/
theorem spatialTensorLinear_dense :
    (LinearMap.range (spatialTensorLinear μ ν)).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro f hf
  have hint : Integrable f (μ.prod ν) := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      integrableOn_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim
        (measure_ne_top (μ.prod ν) Set.univ)
  have hrect : ∀ (s : Set X) (t : Set Y), MeasurableSet s → MeasurableSet t →
      ∫ z in s ×ˢ t, f z ∂μ.prod ν = 0 := by
    intro s t hs ht
    have hfin : (μ.prod ν) (s ×ˢ t) ≠ ∞ := measure_ne_top _ _
    rw [← L2.inner_indicatorConstLp_one (hs.prod ht) hfin f]
    apply (LinearMap.range (spatialTensorLinear μ ν)).inner_right_of_mem_orthogonal ?_ hf
    refine ⟨(indicatorConstLp 2 hs (measure_ne_top _ _) (1 : ℂ)) ⊗ₜ[ℂ]
      (indicatorConstLp 2 ht (measure_ne_top _ _) (1 : ℂ)), ?_⟩
    rw [spatialTensorLinear_tmul, separatedL2_indicator]
  apply Lp.ext
  exact (ae_eq_zero_of_rectangle_integrals μ ν f hint hrect).trans (Lp.coeFn_zero ℂ 2 (μ.prod ν)).symm

/-- Completion gives the entire spatial L² space, by the proved density result. -/
theorem spatialTensorCompletion_surjective : Function.Surjective (spatialTensorCompletion μ ν) := by
  let K : Submodule ℂ (Lp ℂ 2 (μ.prod ν)) :=
    LinearMap.range (spatialTensorCompletion μ ν).toLinearMap
  have hclosed : IsClosed (K : Set (Lp ℂ 2 (μ.prod ν))) :=
    (spatialTensorCompletion μ ν).isometry.isClosedEmbedding.isClosed_range
  have hrange : LinearMap.range (spatialTensorLinear μ ν) ≤ K := by
    rintro _ ⟨x, rfl⟩
    refine ⟨(x : UniformSpace.Completion (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν)), ?_⟩
    exact (spatialTensorIsometry μ ν).fromCompletion_apply_coe x
  have htop : K = ⊤ := by
    apply top_unique
    rw [← spatialTensorLinear_dense μ ν]
    exact Submodule.topologicalClosure_minimal _ hrange hclosed
  intro f
  have hf : f ∈ K := by rw [htop]; trivial
  exact hf

/-- The genuine spatial realization of the completed Hilbert tensor product. -/
def spatialTensorEquiv :
    UniformSpace.Completion (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) ≃ₗᵢ[ℂ] Lp ℂ 2 (μ.prod ν) :=
  LinearIsometryEquiv.ofSurjective (spatialTensorCompletion μ ν)
    (spatialTensorCompletion_surjective μ ν)

end FiniteSpatialMeasures
end SpatialTensor
end LiebLiniger.FixedPeriod.Quantum
