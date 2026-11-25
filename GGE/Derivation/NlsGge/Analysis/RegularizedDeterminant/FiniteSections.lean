import NlsGge.Analysis.RegularizedDeterminant.IdealAndTransport
import Mathlib.Analysis.Normed.Group.Tannery

/-!
The operator-theoretic part of D4.  The convergence is in the genuine HS norm,
for arbitrary filters and possibly noncountable Hilbert bases.  The only sum-limit
interchange is the pinned Tannery theorem with an explicit summable majorant.
This module does NOT assert convergence of a not-yet-constructed determinant.
-/
set_option autoImplicit false
noncomputable section
open scoped ENNReal BigOperators Topology

namespace NlsGge.Analysis.RegularizedDeterminant
namespace HilbertSchmidt

variable {E F G : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

@[simp] theorem adjoint_sub (S T : HilbertSchmidt E F) :
    adjoint (S - T) = adjoint S - adjoint T := by
  apply ext
  intro x
  simp only [toCLM_adjoint, toCLM_sub, map_sub, ContinuousLinearMap.sub_apply]

/-- Strong convergence to zero on the left upgrades to HS convergence on a fixed HS map. -/
theorem tendsto_postcompose_zero {J : Type*} (l : Filter J)
    (A : J → (F →L[ℝ] G)) (T : HilbertSchmidt E F) (M : ℝ) (hM : 0 ≤ M)
    (hbound : Filter.Eventually (fun n => norm (A n) ≤ M) l)
    (hstrong : forall y : F, Filter.Tendsto (fun n => A n y) l (nhds 0)) :
    Filter.Tendsto (fun n => postcompose (A n) T) l (nhds 0) := by
  have hsum : Summable (fun i => M ^ 2 * norm (toCLM T (basis E i)) ^ 2) :=
    (hasSum_columns_sq T).summable.mul_left (M ^ 2)
  have hpoint (i : basisIndex E) :
      Filter.Tendsto (fun n => norm (A n (toCLM T (basis E i))) ^ 2) l (nhds (0 : ℝ)) := by
    simpa using (hstrong (toCLM T (basis E i))).norm.pow 2
  have hdom : Filter.Eventually (fun n => forall i : basisIndex E,
      norm (norm (A n (toCLM T (basis E i))) ^ 2) ≤
        M ^ 2 * norm (toCLM T (basis E i)) ^ 2) l := by
    filter_upwards [hbound] with n hn
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (bounded_image_sq (A n) (toCLM T (basis E i))).trans
      (mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) hM).mpr hn) (sq_nonneg _))
  have hs : Filter.Tendsto
      (fun n => tsum (fun i => norm (A n (toCLM T (basis E i))) ^ 2)) l (nhds (0 : ℝ)) := by
    simpa only [tsum_zero] using
      (tendsto_tsum_of_dominated_convergence (f := fun n i =>
        norm (A n (toCLM T (basis E i))) ^ 2) (g := fun _ => (0 : ℝ))
        hsum hpoint hdom)
  have hs' : Filter.Tendsto (fun n => norm (postcompose (A n) T) ^ 2) l (nhds (0 : ℝ)) :=
    hs.congr' (Filter.Eventually.of_forall (fun n =>
      (hasSum_columns_sq (postcompose (A n) T)).tsum_eq))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hroot := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hs'
  change Filter.Tendsto (fun n => Real.sqrt (norm (postcompose (A n) T) ^ 2)) l
    (nhds (Real.sqrt 0)) at hroot
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hroot

/-- The genuine orthogonal projection is contractive, including the zero subspace. -/
theorem projection_opNorm_le (V : Submodule ℝ E) [CompleteSpace V] :
    norm V.starProjection ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simpa only [one_mul] using V.norm_starProjection_apply_le x

theorem projection_adjoint (V : Submodule ℝ E) [CompleteSpace V] :
    ContinuousLinearMap.adjoint V.starProjection = V.starProjection := by
  simp only [Submodule.starProjection, ContinuousLinearMap.adjoint_comp,
    Submodule.adjoint_subtypeL, Submodule.adjoint_orthogonalProjectionOnto]

/-- Two-sided compression is defined using actual orthogonal projections. -/
def compression (V : Submodule ℝ E) [CompleteSpace V] (T : HilbertSchmidt E E) :
    HilbertSchmidt E E := postcompose V.starProjection (precompose T V.starProjection)

@[simp] theorem toCLM_compression (V : Submodule ℝ E) [CompleteSpace V]
    (T : HilbertSchmidt E E) :
    toCLM (compression V T) = V.starProjection.comp ((toCLM T).comp V.starProjection) := by
  simp only [compression, toCLM_postcompose, toCLM_precompose]

@[simp] theorem compression_sub (V : Submodule ℝ E) [CompleteSpace V]
    (S T : HilbertSchmidt E E) : compression V (S - T) = compression V S - compression V T := by
  apply ext
  intro x
  simp [toCLM_compression]

theorem norm_compression_le (V : Submodule ℝ E) [CompleteSpace V]
    (T : HilbertSchmidt E E) : norm (compression V T) ≤ norm T := by
  calc
    norm (compression V T)
        ≤ norm V.starProjection * norm (precompose T V.starProjection) :=
      norm_postcompose_le _ _
    _ ≤ 1 * norm (precompose T V.starProjection) :=
      mul_le_mul_of_nonneg_right (projection_opNorm_le V) (norm_nonneg _)
    _ = norm (precompose T V.starProjection) := one_mul _
    _ ≤ norm T * norm V.starProjection := norm_precompose_le _ _
    _ ≤ norm T * 1 := mul_le_mul_of_nonneg_left (projection_opNorm_le V) (norm_nonneg T)
    _ = norm T := mul_one _

theorem compression_finiteRank (V : Submodule ℝ E) [FiniteDimensional ℝ V]
    (T : HilbertSchmidt E E) : HasFiniteRank (toCLM (compression V T)) := by
  have hV : LinearMap.range (toCLM (compression V T)).toLinearMap ≤ V := by
    rintro z ⟨x, rfl⟩
    change toCLM (compression V T) x ∈ V
    rw [toCLM_compression]
    exact V.starProjection_apply_mem _
  let j : LinearMap.range (toCLM (compression V T)).toLinearMap →ₗ[ℝ] V :=
    { toFun := fun z => Subtype.mk z.val (hV z.property)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact FiniteDimensional.of_injective j (fun x y h =>
    Subtype.ext (congrArg (fun z : V => (z : E)) h))

/-- The two one-sided projection errors converge to zero in HS norm. -/
theorem projection_errors_tendsto {J : Type*} (l : Filter J)
    (V : J → Submodule ℝ E) [forall n, CompleteSpace (V n)]
    (hstrong : forall x : E, Filter.Tendsto (fun n => (V n).starProjection x) l (nhds x))
    (T : HilbertSchmidt E E) :
    Filter.Tendsto (fun n => norm (postcompose (V n).starProjection T - T)) l (nhds 0) ∧
    Filter.Tendsto (fun n => norm (precompose T (V n).starProjection - T)) l (nhds 0) := by
  have hleft (S : HilbertSchmidt E E) :
      Filter.Tendsto (fun n => postcompose (V n).starProjection S - S) l (nhds 0) := by
    let A : J → (E →L[ℝ] E) := fun n => (V n).starProjection - ContinuousLinearMap.id ℝ E
    have hA (n : J) : norm (A n) ≤ 2 := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      intro x
      change norm ((V n).starProjection x - x) ≤ 2 * norm x
      have h := (norm_sub_le ((V n).starProjection x) x).trans
        (add_le_add ((V n).norm_starProjection_apply_le x) (le_refl (norm x)))
      linarith
    have hstrongA (x : E) : Filter.Tendsto (fun n => A n x) l (nhds 0) := by
      have hx : Filter.Tendsto (fun _ : J => x) l (nhds x) := tendsto_const_nhds
      simpa only [A, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, sub_self]
        using (hstrong x).sub hx
    have hz := tendsto_postcompose_zero l A S 2 (by norm_num)
      (Filter.Eventually.of_forall hA) hstrongA
    apply hz.congr'
    apply Filter.Eventually.of_forall
    intro n
    apply ext
    intro x
    simp [A, toCLM_postcompose]
  constructor
  · simpa only [norm_zero] using (hleft T).norm
  · have h := (hleft (adjoint T)).norm
    have hnorm (n : J) :
        norm (postcompose (V n).starProjection (adjoint T) - adjoint T) =
          norm (precompose T (V n).starProjection - T) := by
      rw [← norm_adjoint (precompose T (V n).starProjection - T), adjoint_sub]
      simp only [precompose, adjoint_adjoint, projection_adjoint]
    simpa only [hnorm, norm_zero] using h

/-- Strong orthogonal projections give two-sided HS convergence; no operator-norm limit is assumed. -/
theorem tendsto_compression {J : Type*} (l : Filter J)
    (V : J → Submodule ℝ E) [forall n, CompleteSpace (V n)]
    (hstrong : forall x : E, Filter.Tendsto (fun n => (V n).starProjection x) l (nhds x))
    (T : HilbertSchmidt E E) :
    Filter.Tendsto (fun n => compression (V n) T) l (nhds T) := by
  have herrors := projection_errors_tendsto l V hstrong T
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero (g := fun n =>
    norm (precompose T (V n).starProjection - T) +
      norm (postcompose (V n).starProjection T - T)) (fun n => norm_nonneg _) ?_ ?_
  · intro n
    have heq : compression (V n) T - T =
        postcompose (V n).starProjection (precompose T (V n).starProjection - T) +
          (postcompose (V n).starProjection T - T) := by
      apply ext
      intro x
      simp [toCLM_compression, toCLM_postcompose, toCLM_precompose] <;> abel
    rw [heq]
    refine (norm_add_le _ _).trans ?_
    have hfirst :
        norm (postcompose (V n).starProjection (precompose T (V n).starProjection - T)) ≤
          norm (precompose T (V n).starProjection - T) := by
      calc
        norm (postcompose (V n).starProjection (precompose T (V n).starProjection - T))
            ≤ norm (V n).starProjection * norm (precompose T (V n).starProjection - T) :=
          norm_postcompose_le _ _
        _ ≤ 1 * norm (precompose T (V n).starProjection - T) :=
          mul_le_mul_of_nonneg_right (projection_opNorm_le (V n)) (norm_nonneg _)
        _ = norm (precompose T (V n).starProjection - T) := one_mul _
    exact add_le_add hfirst (le_refl _)
  · simpa only [zero_add] using herrors.2.add herrors.1

/-- The varying-operator form required for Galerkin and varying-base-point inputs. -/
theorem tendsto_compression_varying {J : Type*} (l : Filter J)
    (V : J → Submodule ℝ E) [forall n, CompleteSpace (V n)]
    (hstrong : forall x : E, Filter.Tendsto (fun n => (V n).starProjection x) l (nhds x))
    (A : J → HilbertSchmidt E E) (B : HilbertSchmidt E E)
    (hA : Filter.Tendsto A l (nhds B)) :
    Filter.Tendsto (fun n => compression (V n) (A n)) l (nhds B) := by
  have hB := tendsto_compression l V hstrong B
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero (g := fun n => norm (A n - B) + norm (compression (V n) B - B))
    (fun n => norm_nonneg _) ?_ ?_
  · intro n
    have heq : compression (V n) (A n) - B =
        compression (V n) (A n - B) + (compression (V n) B - B) := by
      rw [compression_sub]
      abel
    rw [heq]
    refine (norm_add_le _ _).trans ?_
    exact add_le_add (norm_compression_le _ _) (le_refl _)
  · have hAnorm := tendsto_iff_norm_sub_tendsto_zero.mp hA
    have hBnorm := tendsto_iff_norm_sub_tendsto_zero.mp hB
    simpa only [zero_add] using hAnorm.add hBnorm

/-- This is only a continuous HS-valued input theorem, not a nonlinear-NLS realization. -/
theorem tendsto_compression_of_continuousAt {J X : Type*} [TopologicalSpace X]
    (l : Filter J) (V : J → Submodule ℝ E) [forall n, CompleteSpace (V n)]
    (hstrong : forall y : E, Filter.Tendsto (fun n => (V n).starProjection y) l (nhds y))
    (A : X → HilbertSchmidt E E) (x : X) (a : J → X)
    (hA : ContinuousAt A x) (ha : Filter.Tendsto a l (nhds x)) :
    Filter.Tendsto (fun n => compression (V n) (A (a n))) l (nhds (A x)) :=
  tendsto_compression_varying l V hstrong (fun n => A (a n)) (A x) (hA.tendsto.comp ha)

end HilbertSchmidt
end NlsGge.Analysis.RegularizedDeterminant
