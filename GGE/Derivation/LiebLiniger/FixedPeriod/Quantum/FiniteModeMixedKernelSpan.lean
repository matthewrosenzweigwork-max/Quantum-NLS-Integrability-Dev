import LiebLiniger.FixedPeriod.Quantum.SymmetricSubspacePureSpan
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! Actual ambient finite-mode compressed kernels are spanned by rank-one
mixed symmetric spatial tensors. The actual sector totality and occupation
basis are existing checked providers; only their operator-space consequence is
assembled here. SOURCE ONLY / UNCOMPILED, no formal-polynomial transport. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate
namespace LiebLiniger.FixedPeriod.Quantum

/-- Earned completeness of the SAME closed finite-mode spatial subspace.
This is only the definitional bridge to the existing checked closed-subspace
provider. It is not an additional caller premise or alternative completion. -/
private instance finiteModeSymmetricSpace_completeSpace_cache
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    {d : ℕ} (e : Fin d → Lp ℂ 2 μ) (n : ℕ) :
    CompleteSpace (finiteModeSymmetricSpace μ e n) := by
  change CompleteSpace (symmetricSubspace μ (oneParticleModeSpace μ e) n)
  exact symmetricSubspace_completeSpace μ (oneParticleModeSpace μ e) n

/-- The literal source finite-mode range therefore has its genuine orthogonal
projection. Place the CLOSED head instance before any public starProjection
statement, so no open completeness/projection problem is delegated to callers. -/
private instance finiteModeSymmetricSpace_hasOrthogonalProjection_cache
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    {d : ℕ} (e : Fin d → Lp ℂ 2 μ) (n : ℕ) :
    (finiteModeSymmetricSpace μ e n).HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace (finiteModeSymmetricSpace μ e n)

private theorem compression_eq_sum_rankOne {ι κ E F : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (K : Submodule ℂ E) (J : Submodule ℂ F)
    [K.HasOrthogonalProjection] [J.HasOrthogonalProjection]
    (b : OrthonormalBasis ι ℂ K) (c : OrthonormalBasis κ ℂ J) (A : E →L[ℂ] F) :
    (J.starProjection.comp A).comp K.starProjection =
      ∑ i : ι, ∑ j : κ, inner ℂ (c j : F) (A (b i : E)) •
        InnerProductSpace.rankOne ℂ (c j : F) (b i : E) := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  have hb : K.starProjection x = ∑ i : ι, inner ℂ (b i : E) x • (b i : E) := by
    have h := congrArg (fun v : K => (v : E)) (b.orthogonalProjectionOnto_apply_eq_sum x)
    simpa only [Submodule.starProjection_apply,
      Submodule.coe_sum, Submodule.coe_smul] using h
  have hc (y : E) : J.starProjection (A y) =
      ∑ j : κ, inner ℂ (c j : F) (A y) • (c j : F) := by
    have h := congrArg (fun v : J => (v : F)) (c.orthogonalProjectionOnto_apply_eq_sum (A y))
    simpa only [Submodule.starProjection_apply,
      Submodule.coe_sum, Submodule.coe_smul] using h
  change J.starProjection (A (K.starProjection x)) = _
  calc
    _ = J.starProjection (A (∑ i : ι, inner ℂ (b i : E) x • (b i : E))) :=
      congrArg (fun y : E => J.starProjection (A y)) hb
    _ = ∑ i : ι, inner ℂ (b i : E) x • J.starProjection (A (b i : E)) := by
      rw [map_sum, map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_smul, map_smul]
    _ = ∑ i : ι, inner ℂ (b i : E) x •
        (∑ j : κ, inner ℂ (c j : F) (A (b i : E)) • (c j : F)) :=
      Finset.sum_congr rfl (fun i hi => congrArg (fun v : F => inner ℂ (b i : E) x • v) (hc _))
    _ = _ := by
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
        InnerProductSpace.rankOne_apply, Finset.smul_sum, smul_smul]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact congrArg (fun z : ℂ => z • (c j : F)) (mul_comm _ _)

/-- Localize the finite sum/projection calculation in abstract Hilbert spaces
before any concrete Lp sector carrier is substituted. Its membership premise
is discharged below for each actual occupation rank-one map. -/
private theorem compression_mem_submodule_of_basis_rankOne
    {ι κ E F : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (K : Submodule ℂ E) (J : Submodule ℂ F)
    [K.HasOrthogonalProjection] [J.HasOrthogonalProjection]
    (b : OrthonormalBasis ι ℂ K) (c : OrthonormalBasis κ ℂ J)
    (A : E →L[ℂ] F) (S : Submodule ℂ (E →L[ℂ] F))
    (h : ∀ i : ι, ∀ j : κ,
      InnerProductSpace.rankOne ℂ (c j : F) (b i : E) ∈ S) :
    (J.starProjection.comp A).comp K.starProjection ∈ S := by
  classical
  have hs : (∑ i : ι, ∑ j : κ,
      inner ℂ (c j : F) (A (b i : E)) •
        InnerProductSpace.rankOne ℂ (c j : F) (b i : E)) ∈ S := by
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.sum_mem
    intro j hj
    exact S.smul_mem _ (h i j)
  exact (congrArg (fun T : E →L[ℂ] F => T ∈ S)
    (compression_eq_sum_rankOne K J b c A)).mpr hs

private theorem rankOne_smul_vectors {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (a b : ℂ) (x : F) (y : E) :
    InnerProductSpace.rankOne ℂ (a • x) (b • y) =
      (a * conj b) • InnerProductSpace.rankOne ℂ x y := by
  apply ContinuousLinearMap.ext
  intro z
  simp only [InnerProductSpace.rankOne_apply, inner_smul_left, smul_smul,
    ContinuousLinearMap.smul_apply]
  exact congrArg (fun c : ℂ => c • x) (by ring)

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

private theorem intrinsicModeBasis_coe_word {n d : ℕ} (e : Fin d → Lp ℂ 2 μ)
    (he : Orthonormal ℂ e) (a : RealizedOccupation n d) :
    (intrinsicFiniteModeOccupationBasis (n := n) μ e he a : SymmetricSector μ n) =
      normalizedOccupationWordVector μ e (occupationRepresentative a) := by
  simp only [intrinsicFiniteModeOccupationBasis, finiteModeOccupationBasis,
    OrthonormalBasis.map_apply, OrthonormalBasis.coe_mk,
    LinearIsometryEquiv.coe_ofEq_apply, occupationBasisVector]

/-- Actual finite ONbasis expansion of the SAME ambient compressed kernel.
No finite-rank, support identity or operator transport is supplied as a premise. -/
theorem finiteModeKernelCompression_eq_sum_occupationRankOne {d : ℕ}
    (e : Fin d → Lp ℂ 2 μ) (he : Orthonormal ℂ e) (p q : ℕ)
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) :
    ((finiteModeSymmetricSpace μ e q).starProjection.comp A).comp
        (finiteModeSymmetricSpace μ e p).starProjection =
      ∑ a : RealizedOccupation p d, ∑ b : RealizedOccupation q d,
        inner ℂ (intrinsicFiniteModeOccupationBasis (n := q) μ e he b : SymmetricSector μ q)
          (A (intrinsicFiniteModeOccupationBasis (n := p) μ e he a : SymmetricSector μ p)) •
        InnerProductSpace.rankOne ℂ
          (intrinsicFiniteModeOccupationBasis (n := q) μ e he b : SymmetricSector μ q)
          (intrinsicFiniteModeOccupationBasis (n := p) μ e he a : SymmetricSector μ p) :=
  compression_eq_sum_rankOne (finiteModeSymmetricSpace μ e p) (finiteModeSymmetricSpace μ e q)
    (intrinsicFiniteModeOccupationBasis (n := p) μ e he)
    (intrinsicFiniteModeOccupationBasis (n := q) μ e he) A

/-- WHOLE finite-mode matrix spanning step for source Wick polynomial assembly:
the actual compressed ambient kernel lies in the complex span of actual
rank-one mixed symmetric spatial monomials, all p/q/d zero cases retained. -/
theorem finiteModeKernelCompression_mem_mixedRankOne_span {d : ℕ}
    (e : Fin d → Lp ℂ 2 μ) (he : Orthonormal ℂ e) (p q : ℕ)
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) :
    ((finiteModeSymmetricSpace μ e q).starProjection.comp A).comp
        (finiteModeSymmetricSpace μ e p).starProjection ∈
      Submodule.span ℂ (Set.range (fun fg : (Fin q → Fin d) × (Fin p → Fin d) =>
        InnerProductSpace.rankOne ℂ
          (symmetricTensorContinuousMultilinear μ q (fun i => e (fg.1 i)))
          (symmetricTensorContinuousMultilinear μ p (fun i => e (fg.2 i))))) := by
  classical
  let S := Submodule.span ℂ (Set.range (fun fg : (Fin q → Fin d) × (Fin p → Fin d) =>
    InnerProductSpace.rankOne ℂ
      (symmetricTensorContinuousMultilinear μ q (fun i => e (fg.1 i)))
      (symmetricTensorContinuousMultilinear μ p (fun i => e (fg.2 i)))))
  let bp : OrthonormalBasis (RealizedOccupation p d) ℂ
      (finiteModeSymmetricSpace μ e p) :=
    intrinsicFiniteModeOccupationBasis (n := p) μ e he
  let bq : OrthonormalBasis (RealizedOccupation q d) ℂ
      (finiteModeSymmetricSpace μ e q) :=
    intrinsicFiniteModeOccupationBasis (n := q) μ e he
  change ((finiteModeSymmetricSpace μ e q).starProjection.comp A).comp
    (finiteModeSymmetricSpace μ e p).starProjection ∈ S
  apply compression_mem_submodule_of_basis_rankOne
    (finiteModeSymmetricSpace μ e p) (finiteModeSymmetricSpace μ e q) bp bq A S
  intro a b
  have hp : (bp a : SymmetricSector μ p) =
      normalizedOccupationWordVector μ e (occupationRepresentative a) :=
    intrinsicModeBasis_coe_word μ e he a
  have hq : (bq b : SymmetricSector μ q) =
      normalizedOccupationWordVector μ e (occupationRepresentative b) :=
    intrinsicModeBasis_coe_word μ e he b
  have hword : InnerProductSpace.rankOne ℂ
      (normalizedOccupationWordVector μ e (occupationRepresentative b))
      (normalizedOccupationWordVector μ e (occupationRepresentative a)) ∈ S := by
    unfold normalizedOccupationWordVector
    rw [rankOne_smul_vectors]
    apply Submodule.smul_mem
    exact Submodule.subset_span
      ⟨(occupationRepresentative b, occupationRepresentative a), rfl⟩
  exact (congrArg (fun T : SymmetricSector μ p →L[ℂ] SymmetricSector μ q => T ∈ S)
    (congrArg₂ (fun (x : SymmetricSector μ q) (y : SymmetricSector μ p) =>
      InnerProductSpace.rankOne ℂ x y) hq hp)).mpr hword

end LiebLiniger.FixedPeriod.Quantum
