import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Data.Fintype.Perm

/-!
Concrete permutation averaging on product `L²` spaces.

This file does not identify product `L²` with a completed Hilbert tensor power.
The average is constructed from coordinate permutations, rather than postulated
as an orthogonal projection. All finite-index constructions include the empty
index type and hence the zero-particle sector.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace LiebLiniger.FixedPeriod.Quantum

section FiniteAverage

variable {G E : Type*} [Fintype G] [Nonempty G]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The normalized average of a finite family of actual linear isometries. -/
def isometryAverage (U : G → E →ₗᵢ[ℂ] E) : E →L[ℂ] E :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g, (U g).toContinuousLinearMap

@[simp] theorem isometryAverage_apply (U : G → E →ₗᵢ[ℂ] E) (x : E) :
    isometryAverage U x = (Fintype.card G : ℂ)⁻¹ • ∑ g, U g x := by
  simp [isometryAverage]

/-- Averaging isometries, with the counting measure normalized to mass one,
never increases a vector's norm. No projection property is assumed. -/
theorem norm_isometryAverage_apply_le (U : G → E →ₗᵢ[ℂ] E) (x : E) :
    ‖isometryAverage U x‖ ≤ ‖x‖ := by
  have hc : (Fintype.card G : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [isometryAverage_apply, norm_smul, norm_inv, Complex.norm_natCast]
  calc
    (Fintype.card G : ℝ)⁻¹ * ‖∑ g, U g x‖ ≤
        (Fintype.card G : ℝ)⁻¹ * ∑ g, ‖U g x‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = ‖x‖ := by
      simp only [LinearIsometry.norm_map, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact inv_mul_cancel_left₀ hc ‖x‖

theorem norm_isometryAverage_le_one (U : G → E →ₗᵢ[ℂ] E) :
    ‖isometryAverage U‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using norm_isometryAverage_apply_le U x

/-- An invariant vector is unchanged by the actual finite average. -/
theorem isometryAverage_of_fixed (U : G → E →ₗᵢ[ℂ] E) (x : E)
    (hx : ∀ g, U g x = x) : isometryAverage U x = x := by
  have hc : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [isometryAverage_apply, hx, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]

end FiniteAverage

section ProductL2

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The coordinate reindexing `x ↦ x ∘ σ`. -/
def coordinatePermutation (σ : Equiv.Perm ι) : (ι → X) → (ι → X) :=
  MeasurableEquiv.piCongrLeft (fun _ : ι => X) σ.symm

@[simp] theorem coordinatePermutation_apply (σ : Equiv.Perm ι) (x : ι → X) (i : ι) :
    coordinatePermutation σ x i = x (σ i) := by
  simpa only [coordinatePermutation, Equiv.symm_apply_apply] using
    (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : ι => X) σ.symm x (σ i))

/-- Permuting coordinates preserves the product of identical measures. -/
theorem coordinatePermutation_measurePreserving (σ : Equiv.Perm ι) :
    MeasurePreserving (coordinatePermutation (X := X) σ)
      (Measure.pi fun _ : ι => μ) (Measure.pi fun _ : ι => μ) :=
  measurePreserving_piCongrLeft (fun _ : ι => μ) σ.symm

abbrev ProductL2 (ι : Type*) [Fintype ι] :=
  Lp ℂ 2 (Measure.pi fun _ : ι => μ)

/-- The genuine unitary pullback induced by a permutation of coordinates. -/
def permutationL2 (σ : Equiv.Perm ι) : ProductL2 μ ι →ₗᵢ[ℂ] ProductL2 μ ι :=
  Lp.compMeasurePreservingₗᵢ ℂ (coordinatePermutation σ)
    (coordinatePermutation_measurePreserving μ σ)

/-- Symmetrization is the normalized sum of the actual permutation pullbacks. -/
def symmetrizeL2 : ProductL2 μ ι →L[ℂ] ProductL2 μ ι :=
  isometryAverage (permutationL2 μ)

@[simp] theorem symmetrizeL2_apply (f : ProductL2 μ ι) :
    symmetrizeL2 μ f = (Fintype.card (Equiv.Perm ι) : ℂ)⁻¹ •
      ∑ σ : Equiv.Perm ι, permutationL2 μ σ f :=
  isometryAverage_apply _ _

/-- The finite-particle averaging coefficient is exactly `1 / n!`. -/
theorem symmetrizeL2_apply_fin (n : ℕ) (f : ProductL2 μ (Fin n)) :
    symmetrizeL2 μ f = (n.factorial : ℂ)⁻¹ •
      ∑ σ : Equiv.Perm (Fin n), permutationL2 μ σ f := by
  have hc : Fintype.card (Equiv.Perm (Fin n)) = n.factorial :=
    (Fintype.card_perm (α := Fin n)).trans (congrArg Nat.factorial (Fintype.card_fin n))
  have hs : (Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹ = (n.factorial : ℂ)⁻¹ :=
    congrArg (fun m : ℕ => (m : ℂ)⁻¹) hc
  calc
    symmetrizeL2 μ f = (Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹ •
        ∑ σ : Equiv.Perm (Fin n), permutationL2 μ σ f := symmetrizeL2_apply μ f
    _ = _ := congrArg (fun z : ℂ => z •
      ∑ σ : Equiv.Perm (Fin n), permutationL2 μ σ f) hs

/-- The `L²` norm contraction used for transfer kernels. -/
theorem norm_symmetrizeL2_apply_le (f : ProductL2 μ ι) :
    ‖symmetrizeL2 μ f‖ ≤ ‖f‖ :=
  norm_isometryAverage_apply_le _ _

theorem norm_symmetrizeL2_le_one :
    ‖symmetrizeL2 (ι := ι) μ‖ ≤ 1 :=
  norm_isometryAverage_le_one _

/-- Symmetrization fixes every permutation-invariant `L²` function. -/
theorem symmetrizeL2_of_fixed (f : ProductL2 μ ι)
    (hf : ∀ σ : Equiv.Perm ι, permutationL2 μ σ f = f) :
    symmetrizeL2 μ f = f :=
  isometryAverage_of_fixed _ _ hf

@[simp] theorem permutationL2_one (f : ProductL2 μ ι) :
    permutationL2 μ (1 : Equiv.Perm ι) f = f := by
  have hc : coordinatePermutation (X := X) (1 : Equiv.Perm ι) = id := by
    ext x i
    simp only [coordinatePermutation_apply, Equiv.Perm.one_apply, id_eq]
  change Lp.compMeasurePreserving _ _ f = f
  simpa only [hc] using Lp.compMeasurePreserving_id_apply f

@[simp] theorem permutationL2_mul (σ τ : Equiv.Perm ι) (f : ProductL2 μ ι) :
    permutationL2 μ σ (permutationL2 μ τ f) = permutationL2 μ (σ * τ) f := by
  have hc : coordinatePermutation (X := X) τ ∘ coordinatePermutation σ =
      coordinatePermutation (σ * τ) := by
    ext x i
    simp only [Function.comp_apply, coordinatePermutation_apply, Equiv.Perm.mul_apply]
  change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) =
    Lp.compMeasurePreserving _ _ f
  rw [← Lp.compMeasurePreserving_comp_apply]
  simp only [hc]

/-- Every permutation fixes the normalized permutation average. -/
theorem permutationL2_symmetrizeL2 (τ : Equiv.Perm ι) (f : ProductL2 μ ι) :
    permutationL2 μ τ (symmetrizeL2 μ f) = symmetrizeL2 μ f := by
  simp only [symmetrizeL2_apply, map_smul, map_sum, permutationL2_mul]
  exact congrArg (fun z : ProductL2 μ ι =>
      (Fintype.card (Equiv.Perm ι) : ℂ)⁻¹ • z)
    (Function.Bijective.sum_comp (Group.mulLeft_bijective τ)
      (fun σ => permutationL2 μ σ f))

/-- Idempotence follows from the actual permutation action. -/
@[simp] theorem symmetrizeL2_idempotent (f : ProductL2 μ ι) :
    symmetrizeL2 μ (symmetrizeL2 μ f) = symmetrizeL2 μ f :=
  symmetrizeL2_of_fixed μ _ (fun σ => permutationL2_symmetrizeL2 μ σ f)

/-- The fixed points of the average are exactly the permutation-invariant functions. -/
theorem symmetrizeL2_eq_self_iff (f : ProductL2 μ ι) :
    symmetrizeL2 μ f = f ↔ ∀ σ : Equiv.Perm ι, permutationL2 μ σ f = f := by
  constructor
  · intro hf σ
    calc
      permutationL2 μ σ f = permutationL2 μ σ (symmetrizeL2 μ f) :=
        congrArg (permutationL2 μ σ) hf.symm
      _ = symmetrizeL2 μ f := permutationL2_symmetrizeL2 μ σ f
      _ = f := hf
  · exact symmetrizeL2_of_fixed μ f

/-- Taking the inverse permutation gives the Hilbert adjoint. -/
theorem inner_permutationL2 (σ : Equiv.Perm ι) (f g : ProductL2 μ ι) :
    ⟪permutationL2 μ σ f, g⟫_ℂ = ⟪f, permutationL2 μ σ⁻¹ g⟫_ℂ := by
  have hg : permutationL2 μ σ (permutationL2 μ σ⁻¹ g) = g := by
    rw [permutationL2_mul, mul_inv_cancel, permutationL2_one]
  conv_lhs => rw [← hg]
  exact LinearIsometry.inner_map_map _ _ _

/-- The normalized average is symmetric, by reindexing its adjoints by inversion. -/
theorem symmetrizeL2_isSymmetric :
    (symmetrizeL2 (ι := ι) μ).toLinearMap.IsSymmetric := by
  intro f g
  change ⟪symmetrizeL2 μ f, g⟫_ℂ = ⟪f, symmetrizeL2 μ g⟫_ℂ
  simp only [symmetrizeL2_apply, inner_smul_left, inner_smul_right, sum_inner,
    inner_sum, map_inv₀, map_natCast]
  congr 1
  simp_rw [inner_permutationL2]
  exact Equiv.sum_comp (Equiv.inv (Equiv.Perm ι)) (fun σ => ⟪f, permutationL2 μ σ g⟫_ℂ)

/-- The concrete average is an orthogonal (symmetric idempotent) projection. -/
theorem symmetrizeL2_isSymmetricProjection :
    (symmetrizeL2 (ι := ι) μ).toLinearMap.IsSymmetricProjection := by
  constructor
  · exact LinearMap.ext (fun f => symmetrizeL2_idempotent μ f)
  · exact symmetrizeL2_isSymmetric μ

/-- The raw pure tensor function is invariant under coordinate permutations,
including an empty product in the zero-particle sector. -/
theorem pureTensorFunction_coordinatePermutation (u : X → ℂ)
    (σ : Equiv.Perm ι) (x : ι → X) :
    (∏ i, u (coordinatePermutation σ x i)) = ∏ i, u (x i) := by
  simp only [coordinatePermutation_apply]
  exact Equiv.prod_comp σ (fun i => u (x i))

/-- A pure tensor of an arbitrary one-particle `L²` vector is square integrable.
Integrability is established before the quotient element is constructed. -/
theorem pureTensorFunction_memLp (u : Lp ℂ 2 μ) :
    MemLp (fun x : ι → X => ∏ i, u (x i)) 2 (Measure.pi fun _ : ι => μ) := by
  have hm : AEStronglyMeasurable (fun x : ι → X => ∏ i, u (x i))
      (Measure.pi fun _ : ι => μ) := by
    apply Finset.aestronglyMeasurable_fun_prod
    intro i _
    exact (Lp.aestronglyMeasurable u).comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_eval (fun _ : ι => μ) i)
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  simpa only [norm_prod, Finset.prod_pow] using
    (Integrable.fintype_prod (fun _ : ι => (Lp.memLp u).norm.integrable_sq))

/-- The actual pure tensor in the product-`L²` realization. -/
def pureTensorL2 (u : Lp ℂ 2 μ) : ProductL2 μ ι :=
  (pureTensorFunction_memLp (ι := ι) μ u).toLp (fun x => ∏ i, u (x i))

@[simp] theorem permutationL2_pureTensorL2 (σ : Equiv.Perm ι) (u : Lp ℂ 2 μ) :
    permutationL2 μ σ (pureTensorL2 (ι := ι) μ u) = pureTensorL2 μ u := by
  change Lp.compMeasurePreserving _ _
    ((pureTensorFunction_memLp μ u).toLp _) = (pureTensorFunction_memLp μ u).toLp _
  rw [Lp.toLp_compMeasurePreserving]
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall (fun x => pureTensorFunction_coordinatePermutation u σ x)

/-- Pure tensors are fixed by the constructed permutation average. -/
@[simp] theorem symmetrizeL2_pureTensorL2 (u : Lp ℂ 2 μ) :
    symmetrizeL2 μ (pureTensorL2 (ι := ι) μ u) = pureTensorL2 μ u :=
  symmetrizeL2_of_fixed μ _ (fun σ => permutationL2_pureTensorL2 μ σ u)

/-- On the zero-coordinate product space, the average is the identity. -/
@[simp] theorem symmetrizeL2_zero (f : ProductL2 μ (Fin 0)) :
    symmetrizeL2 μ f = f := by
  apply symmetrizeL2_of_fixed
  intro σ
  have hσ : σ = 1 := Subsingleton.elim _ _
  rw [hσ, permutationL2_one]

end ProductL2

section KernelL2

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The square-integrable unsymmetrized kernel carrier, with input and output
coordinates kept separate. -/
abbrev KernelL2 := Lp ℂ 2
  ((Measure.pi fun _ : ι => μ).prod (Measure.pi fun _ : κ => μ))

/-- Independent permutations of the output and input blocks are genuine `L²`
isometries. -/
def kernelPermutationL2 (σ : Equiv.Perm ι × Equiv.Perm κ) :
    KernelL2 (ι := ι) (κ := κ) μ →ₗᵢ[ℂ] KernelL2 (ι := ι) (κ := κ) μ :=
  Lp.compMeasurePreservingₗᵢ ℂ
    (Prod.map (coordinatePermutation σ.1) (coordinatePermutation σ.2))
    ((coordinatePermutation_measurePreserving μ σ.1).prod
      (coordinatePermutation_measurePreserving μ σ.2))

/-- Separate input/output symmetrization, normalized by `|S_ι| |S_κ|`. -/
def symmetrizeKernelL2 : KernelL2 (ι := ι) (κ := κ) μ →L[ℂ]
    KernelL2 (ι := ι) (κ := κ) μ :=
  isometryAverage (kernelPermutationL2 μ)

@[simp] theorem symmetrizeKernelL2_apply (K : KernelL2 (ι := ι) (κ := κ) μ) :
    symmetrizeKernelL2 μ K =
      (Fintype.card (Equiv.Perm ι × Equiv.Perm κ) : ℂ)⁻¹ •
        ∑ σ : Equiv.Perm ι × Equiv.Perm κ, kernelPermutationL2 μ σ K :=
  isometryAverage_apply _ _

/-- Both permutation groups are normalized, with the factorials required by
separate input/output symmetrization. -/
theorem symmetrizeKernelL2_apply_fin (p q : ℕ)
    (K : KernelL2 (ι := Fin p) (κ := Fin q) μ) :
    symmetrizeKernelL2 μ K = ((p.factorial : ℂ) * (q.factorial : ℂ))⁻¹ •
      ∑ σ : Equiv.Perm (Fin p) × Equiv.Perm (Fin q), kernelPermutationL2 μ σ K := by
  have hp : Fintype.card (Equiv.Perm (Fin p)) = p.factorial :=
    (Fintype.card_perm (α := Fin p)).trans (congrArg Nat.factorial (Fintype.card_fin p))
  have hq : Fintype.card (Equiv.Perm (Fin q)) = q.factorial :=
    (Fintype.card_perm (α := Fin q)).trans (congrArg Nat.factorial (Fintype.card_fin q))
  have hc : Fintype.card (Equiv.Perm (Fin p) × Equiv.Perm (Fin q)) =
      p.factorial * q.factorial := by
    exact (Fintype.card_prod (Equiv.Perm (Fin p)) (Equiv.Perm (Fin q))).trans
      (congrArg₂ Nat.mul hp hq)
  have hs : (Fintype.card (Equiv.Perm (Fin p) × Equiv.Perm (Fin q)) : ℂ)⁻¹ =
      ((p.factorial : ℂ) * (q.factorial : ℂ))⁻¹ := by
    rw [hc, Nat.cast_mul]
  calc
    symmetrizeKernelL2 μ K =
        (Fintype.card (Equiv.Perm (Fin p) × Equiv.Perm (Fin q)) : ℂ)⁻¹ •
          ∑ σ : Equiv.Perm (Fin p) × Equiv.Perm (Fin q), kernelPermutationL2 μ σ K :=
      symmetrizeKernelL2_apply μ K
    _ = _ := congrArg (fun z : ℂ => z •
      ∑ σ : Equiv.Perm (Fin p) × Equiv.Perm (Fin q), kernelPermutationL2 μ σ K) hs

theorem norm_symmetrizeKernelL2_le_one :
    ‖symmetrizeKernelL2 (ι := ι) (κ := κ) μ‖ ≤ 1 :=
  norm_isometryAverage_le_one _

/-- The actual separate input/output permutation average contracts the kernel's
`L²` norm. Neither Hilbert--Schmidt status nor a projection is assumed. -/
theorem norm_symmetrizeKernelL2_apply_le (K : KernelL2 (ι := ι) (κ := κ) μ) :
    ‖symmetrizeKernelL2 μ K‖ ≤ ‖K‖ :=
  norm_isometryAverage_apply_le _ _

end KernelL2

end LiebLiniger.FixedPeriod.Quantum
