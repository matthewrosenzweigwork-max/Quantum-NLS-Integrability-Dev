import NlsGge.Analysis.RegularizedDeterminant.FiniteRank
import NlsGge.Analysis.RegularizedDeterminant.MatrixLipschitz

/-!
G2: the dimension-free Hilbert--Schmidt Lipschitz estimate for the intrinsic finite-rank
regularized determinant in an arbitrary (possibly infinite-dimensional, nonseparable) real
Hilbert space:

`|det₂(I+A) - det₂(I+B)| ≤ ‖A-B‖₂ exp (2 (‖A‖₂ + ‖B‖₂ + 1)^2)`

for finite-rank Hilbert--Schmidt `A, B`.  The matrix of the restriction of a finite-rank map to
a finite-dimensional containing subspace, in an orthonormal basis of that subspace, has
Frobenius norm at most the Hilbert--Schmidt norm of the map (Bessel along an orthonormal
family, extended to a Hilbert basis of the ambient space).
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators InnerProductSpace

namespace NlsGge.Analysis.RegularizedDeterminant

open HilbertSchmidt

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Bessel-type bound: an orthonormal finite family sees at most the HS energy. -/
theorem sum_norm_sq_orthonormal_le (T : HilbertSchmidt H H) {ι : Type*} [Fintype ι]
    (v : ι → H) (hv : Orthonormal ℝ v) :
    ∑ j, ‖toCLM T (v j)‖ ^ 2 ≤ ‖T‖ ^ 2 := by
  classical
  have hinj : Function.Injective v := hv.linearIndependent.injective
  have hs : Orthonormal ℝ ((↑) : Set.range v → H) := (orthonormal_subtype_range hinj).mpr hv
  obtain ⟨w, b, hsw, hb⟩ := hs.exists_hilbertBasis_extension
  have hsum := HilbertSchmidt.hasSum_basis_sq T b
  let g : ι → w := fun j => ⟨v j, hsw ⟨j, rfl⟩⟩
  have hg : Function.Injective g := by
    intro i j hij
    exact hinj (congrArg Subtype.val hij)
  calc ∑ j, ‖toCLM T (v j)‖ ^ 2
        = ∑ i ∈ Finset.univ.map ⟨g, hg⟩, ‖toCLM T (b i)‖ ^ 2 := by
          rw [Finset.sum_map]
          apply Finset.sum_congr rfl
          intro j _
          simp [g, hb]
    _ ≤ ‖T‖ ^ 2 := sum_le_hasSum _ (fun _ _ => sq_nonneg _) hsum

/-- The Frobenius norm of the restricted matrix is bounded by the HS norm. -/
theorem frob_restricted_le (T : HilbertSchmidt H H) (V : Submodule ℝ H)
    [FiniteDimensional ℝ V] (hV : LinearMap.range (toCLM T).toLinearMap ≤ V)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℝ V) :
    frob (LinearMap.toMatrix b.toBasis b.toBasis
      (restrictedEnd (toCLM T).toLinearMap V hV)) ≤ ‖T‖ := by
  have hcol (j : ι) :
      ∑ i, (LinearMap.toMatrix b.toBasis b.toBasis
        (restrictedEnd (toCLM T).toLinearMap V hV)) i j ^ 2 =
        ‖toCLM T ((b j : V) : H)‖ ^ 2 := by
    simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_apply_apply]
    set y : V := restrictedEnd (toCLM T).toLinearMap V hV (b j)
    have h := b.sum_inner_mul_inner y y
    rw [real_inner_self_eq_norm_sq] at h
    have hy : ‖y‖ = ‖toCLM T ((b j : V) : H)‖ := rfl
    rw [← hy, ← h]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm y (b i), sq]
  have hv : Orthonormal ℝ (fun j => ((b j : V) : H)) :=
    b.orthonormal.comp_linearIsometry V.subtypeₗᵢ
  have hle := sum_norm_sq_orthonormal_le T (fun j => ((b j : V) : H)) hv
  unfold frob
  rw [Finset.sum_comm]
  simp only [hcol]
  calc Real.sqrt (∑ j, ‖toCLM T ((b j : V) : H)‖ ^ 2) ≤ Real.sqrt (‖T‖ ^ 2) :=
        Real.sqrt_le_sqrt hle
    _ = ‖T‖ := Real.sqrt_sq (norm_nonneg T)

/-- Restriction is additive in the operator. -/
theorem restrictedEnd_sub (A B : H →ₗ[ℝ] H) (V : Submodule ℝ H)
    (hA : LinearMap.range A ≤ V) (hB : LinearMap.range B ≤ V)
    (hAB : LinearMap.range (A - B) ≤ V) :
    restrictedEnd A V hA - restrictedEnd B V hB = restrictedEnd (A - B) V hAB := by
  ext x
  rfl

theorem range_sub_le (A B : H →ₗ[ℝ] H) (V : Submodule ℝ H)
    (hA : LinearMap.range A ≤ V) (hB : LinearMap.range B ≤ V) :
    LinearMap.range (A - B) ≤ V := by
  rintro z ⟨x, rfl⟩
  exact V.sub_mem (hA ⟨x, rfl⟩) (hB ⟨x, rfl⟩)

/-- **G2.** Dimension-free HS Lipschitz estimate for the intrinsic finite-rank `det₂`. -/
theorem finiteRankDet2_lipschitz (A B : HilbertSchmidt H H)
    (hA : HasFiniteRank (toCLM A)) (hB : HasFiniteRank (toCLM B)) :
    |finiteRankDet2 (toCLM A).toLinearMap hA - finiteRankDet2 (toCLM B).toLinearMap hB| ≤
      ‖A - B‖ * Real.exp (2 * (‖A‖ + ‖B‖ + 1) ^ 2) := by
  classical
  letI : FiniteDimensional ℝ (LinearMap.range (toCLM A).toLinearMap) := hA
  letI : FiniteDimensional ℝ (LinearMap.range (toCLM B).toLinearMap) := hB
  set V : Submodule ℝ H :=
    LinearMap.range (toCLM A).toLinearMap ⊔ LinearMap.range (toCLM B).toLinearMap
  have hVA : LinearMap.range (toCLM A).toLinearMap ≤ V := le_sup_left
  have hVB : LinearMap.range (toCLM B).toLinearMap ≤ V := le_sup_right
  have hVD : LinearMap.range (toCLM (A - B)).toLinearMap ≤ V := by
    rw [toCLM_sub, ContinuousLinearMap.coe_sub]
    exact range_sub_le _ _ V hVA hVB
  let b := stdOrthonormalBasis ℝ V
  rw [finiteRankDet2_eq_restriction _ hA V hVA, finiteRankDet2_eq_restriction _ hB V hVB,
    finiteDet2_eq_matrix b.toBasis, finiteDet2_eq_matrix b.toBasis]
  have hsub : LinearMap.toMatrix b.toBasis b.toBasis
        (restrictedEnd (toCLM A).toLinearMap V hVA) -
      LinearMap.toMatrix b.toBasis b.toBasis (restrictedEnd (toCLM B).toLinearMap V hVB) =
      LinearMap.toMatrix b.toBasis b.toBasis
        (restrictedEnd (toCLM (A - B)).toLinearMap V hVD) := by
    rw [← map_sub]
    congr 1
  refine (matrixDet2_lipschitz _ _).trans ?_
  rw [hsub]
  have h1 := frob_restricted_le (A - B) V hVD b
  have h2 := frob_restricted_le A V hVA b
  have h3 := frob_restricted_le B V hVB b
  have h2' := frob_nonneg (LinearMap.toMatrix b.toBasis b.toBasis
      (restrictedEnd (toCLM A).toLinearMap V hVA))
  have h3' := frob_nonneg (LinearMap.toMatrix b.toBasis b.toBasis
      (restrictedEnd (toCLM B).toLinearMap V hVB))
  gcongr

end NlsGge.Analysis.RegularizedDeterminant
