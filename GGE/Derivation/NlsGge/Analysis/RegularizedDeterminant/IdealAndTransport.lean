import NlsGge.Analysis.RegularizedDeterminant.ColumnsAndCompleteness

/-!
Rectangular two-sided HS ideal estimates, real adjoints, real isometric
transport, and membership of every finite-rank bounded map.  This module makes
no determinant-continuity or determinant-nonvanishing assumption.
-/
set_option autoImplicit false
noncomputable section
open scoped ENNReal BigOperators

namespace NlsGge.Analysis.RegularizedDeterminant

variable {E F G H : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem energy_adjoint (T : E →L[ℝ] F) :
    energy (ContinuousLinearMap.adjoint T) = energy T := by
  exact (NlsGge.Pilot.ennreal_basis_energy_eq_adjoint_basis
    T (basis E) (basis F)).symm

theorem isHilbertSchmidt_adjoint_iff (T : E →L[ℝ] F) :
    IsHilbertSchmidt (ContinuousLinearMap.adjoint T) ↔ IsHilbertSchmidt T := by
  unfold IsHilbertSchmidt
  rw [energy_adjoint]

theorem bounded_image_sq (A : F →L[ℝ] G) (y : F) :
    norm (A y) ^ 2 ≤ norm A ^ 2 * norm y ^ 2 := by
  have h := (sq_le_sq₀ (norm_nonneg (A y))
    (mul_nonneg (norm_nonneg A) (norm_nonneg y))).mpr (A.le_opNorm y)
  simpa only [mul_pow] using h

namespace HilbertSchmidt

/-- Actual composition on the codomain side. -/
def postcompose (A : F →L[ℝ] G) (T : HilbertSchmidt E F) : HilbertSchmidt E G :=
  ofCLM (A.comp (toCLM T)) (by
    apply isHilbertSchmidt_of_summable (basis E)
    apply Summable.of_nonneg_of_le (fun i => sq_nonneg _)
      (fun i => bounded_image_sq A (toCLM T (basis E i)))
    exact (hasSum_columns_sq T).summable.mul_left (norm A ^ 2))

@[simp] theorem toCLM_postcompose (A : F →L[ℝ] G) (T : HilbertSchmidt E F) :
    toCLM (postcompose A T) = A.comp (toCLM T) := rfl

theorem norm_postcompose_le (A : F →L[ℝ] G) (T : HilbertSchmidt E F) :
    norm (postcompose A T) ≤ norm A * norm T := by
  have hS := hasSum_columns_sq (postcompose A T)
  have hT := hasSum_columns_sq T
  have hsq : norm (postcompose A T) ^ 2 ≤ norm A ^ 2 * norm T ^ 2 := by
    rw [← hS.tsum_eq, ← hT.tsum_eq, ← hT.summable.tsum_mul_left (norm A ^ 2)]
    exact Summable.tsum_le_tsum
      (fun i => bounded_image_sq A (toCLM T (basis E i)))
      hS.summable (hT.summable.mul_left (norm A ^ 2))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg A) (norm_nonneg T))).mp
  simpa only [mul_pow] using hsq

/-- Real adjoint, bundled after proving its finite energy. -/
def adjoint (T : HilbertSchmidt E F) : HilbertSchmidt F E :=
  ofCLM (ContinuousLinearMap.adjoint (toCLM T))
    ((isHilbertSchmidt_adjoint_iff (toCLM T)).mpr (membership T))

@[simp] theorem toCLM_adjoint (T : HilbertSchmidt E F) :
    toCLM (adjoint T) = ContinuousLinearMap.adjoint (toCLM T) := rfl

@[simp] theorem norm_adjoint (T : HilbertSchmidt E F) : norm (adjoint T) = norm T := by
  rw [norm_eq_sqrt_energy, toCLM_adjoint, energy_adjoint, ← norm_eq_sqrt_energy T]

@[simp] theorem adjoint_adjoint (T : HilbertSchmidt E F) : adjoint (adjoint T) = T := by
  apply ext
  intro x
  simp only [toCLM_adjoint, ContinuousLinearMap.adjoint_adjoint]

/-- Actual composition on the domain side, derived through real adjoints. -/
def precompose (T : HilbertSchmidt F G) (A : E →L[ℝ] F) : HilbertSchmidt E G :=
  adjoint (postcompose (ContinuousLinearMap.adjoint A) (adjoint T))

@[simp] theorem toCLM_precompose (T : HilbertSchmidt F G) (A : E →L[ℝ] F) :
    toCLM (precompose T A) = (toCLM T).comp A := by
  simp only [precompose, toCLM_adjoint, toCLM_postcompose,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]

theorem norm_precompose_le (T : HilbertSchmidt F G) (A : E →L[ℝ] F) :
    norm (precompose T A) ≤ norm T * norm A := by
  rw [precompose, norm_adjoint]
  calc
    norm (postcompose (ContinuousLinearMap.adjoint A) (adjoint T))
        ≤ norm (ContinuousLinearMap.adjoint A) * norm (adjoint T) :=
      norm_postcompose_le _ _
    _ = norm T * norm A := by
      rw [norm_adjoint, ContinuousLinearMap.adjoint.norm_map]
      exact mul_comm _ _

@[simp] theorem postcompose_add (A : F →L[ℝ] G) (S T : HilbertSchmidt E F) :
    postcompose A (S + T) = postcompose A S + postcompose A T := by
  apply ext
  intro x
  simp [toCLM_postcompose]

@[simp] theorem postcompose_smul (A : F →L[ℝ] G) (c : ℝ) (T : HilbertSchmidt E F) :
    postcompose A (c • T) = c • postcompose A T := by
  apply ext
  intro x
  simp [toCLM_postcompose]

/-- A bounded linear map on HS spaces; the bound is the operator norm of A. -/
def postcomposeContinuous (A : F →L[ℝ] G) :
    HilbertSchmidt E F →L[ℝ] HilbertSchmidt E G :=
  ({ toFun := postcompose A
     map_add' := postcompose_add A
     map_smul' := postcompose_smul A } :
    HilbertSchmidt E F →ₗ[ℝ] HilbertSchmidt E G).mkContinuous (norm A)
      (norm_postcompose_le A)

end HilbertSchmidt

/-- Every bounded map out of a finite-dimensional real Hilbert space is HS. -/
theorem isHilbertSchmidt_of_finiteDomain [FiniteDimensional ℝ E] (T : E →L[ℝ] F) :
    IsHilbertSchmidt T := by
  let b := (stdOrthonormalBasis ℝ E).toHilbertBasis
  apply isHilbertSchmidt_of_summable b
  exact (hasSum_fintype (fun i => norm (T (b i)) ^ 2)).summable

/-- The codomain version does not require the domain to be finite dimensional. -/
theorem isHilbertSchmidt_of_finiteCodomain [FiniteDimensional ℝ F] (T : E →L[ℝ] F) :
    IsHilbertSchmidt T :=
  (isHilbertSchmidt_adjoint_iff T).mp (isHilbertSchmidt_of_finiteDomain
    (ContinuousLinearMap.adjoint T))

/-- Every finite-rank bounded real-linear map belongs to the new carrier. -/
theorem isHilbertSchmidt_of_finiteRank (T : E →L[ℝ] F)
    (hT : HilbertSchmidt.HasFiniteRank T) : IsHilbertSchmidt T := by
  let W := LinearMap.range T.toLinearMap
  letI : FiniteDimensional ℝ W := hT
  let T' : E →L[ℝ] W := T.codRestrict W (fun x => Exists.intro x rfl)
  let S : HilbertSchmidt E W := HilbertSchmidt.ofCLM T'
    (isHilbertSchmidt_of_finiteCodomain T')
  have h : (HilbertSchmidt.postcompose W.subtypeL S).toCLM = T := by
    ext x
    rfl
  rw [← h]
  exact HilbertSchmidt.membership _

/-- Transport of the underlying rectangular bounded real-linear operator. -/
def transportOperator (T : E →L[ℝ] F) (e : E ≃ₗᵢ[ℝ] G) (f : F ≃ₗᵢ[ℝ] H) :
    G →L[ℝ] H :=
  f.toLinearIsometry.toContinuousLinearMap.comp
    (T.comp e.symm.toLinearIsometry.toContinuousLinearMap)

theorem energy_transport (T : E →L[ℝ] F) (e : E ≃ₗᵢ[ℝ] G) (f : F ≃ₗᵢ[ℝ] H) :
    energy (transportOperator T e f) = energy T := by
  classical
  let bE := basis E
  let bG : HilbertBasis (basisIndex E) ℝ G := ⟨e.symm.trans bE.repr⟩
  have hb (i : basisIndex E) : bG i = e (bE i) := by
    rw [← bG.repr_symm_single i, ← bE.repr_symm_single i]
    change (e.symm.trans bE.repr).symm (lp.single 2 i (1 : ℝ)) =
      e (bE.repr.symm (lp.single 2 i (1 : ℝ)))
    rfl
  rw [energy_eq_basis _ bG, energy_eq_basis T bE]
  apply tsum_congr
  intro i
  rw [hb]
  simp [transportOperator]

namespace HilbertSchmidt

/-- Real isometries on both sides preserve HS membership and the full real norm. -/
def transport (T : HilbertSchmidt E F) (e : E ≃ₗᵢ[ℝ] G) (f : F ≃ₗᵢ[ℝ] H) :
    HilbertSchmidt G H :=
  ofCLM (transportOperator (toCLM T) e f) (by
    unfold IsHilbertSchmidt
    rw [energy_transport]
    exact membership T)

@[simp] theorem toCLM_transport (T : HilbertSchmidt E F)
    (e : E ≃ₗᵢ[ℝ] G) (f : F ≃ₗᵢ[ℝ] H) :
    toCLM (transport T e f) = transportOperator (toCLM T) e f := rfl

@[simp] theorem norm_transport (T : HilbertSchmidt E F)
    (e : E ≃ₗᵢ[ℝ] G) (f : F ≃ₗᵢ[ℝ] H) : norm (transport T e f) = norm T := by
  rw [norm_eq_sqrt_energy, toCLM_transport, energy_transport, ← norm_eq_sqrt_energy T]

end HilbertSchmidt
end NlsGge.Analysis.RegularizedDeterminant
