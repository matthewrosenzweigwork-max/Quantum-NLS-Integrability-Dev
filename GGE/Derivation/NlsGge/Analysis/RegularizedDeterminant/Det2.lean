import NlsGge.Analysis.RegularizedDeterminant.FiniteRankLipschitz
import NlsGge.Analysis.RegularizedDeterminant.DenseExtension

/-!
G3: the real Hilbert--Schmidt regularized determinant `det₂(I+B)` on an arbitrary real Hilbert
space (no separability, no trace-class, smallness, selfadjointness, positivity or invertibility
assumption, no complexification in the definition).

Definition: the intrinsic finite-rank value `finiteRankDet2` (determinant/trace formula on the
range, independent of the containing finite-dimensional subspace) is locally Lipschitz in the HS
norm with the dimension-free constant of `finiteRankDet2_lipschitz`; finite-rank operators are
HS-dense; `det2` is its (unique) continuous extension.
-/
set_option autoImplicit false
noncomputable section
open scoped Topology

namespace NlsGge.Analysis.RegularizedDeterminant

open HilbertSchmidt

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The monotone continuous Lipschitz weight; equal to `exp (2 (t+1)^2)` for `t ≥ 0`. -/
def det2Weight (t : ℝ) : ℝ := Real.exp (2 * (max t 0 + 1) ^ 2)

theorem continuous_det2Weight : Continuous det2Weight := by
  unfold det2Weight; fun_prop

theorem monotone_det2Weight : Monotone det2Weight := by
  intro s t hst
  unfold det2Weight
  apply Real.exp_le_exp.mpr
  have h1 : max s 0 ≤ max t 0 := max_le_max hst le_rfl
  have h2 : 0 ≤ max s 0 + 1 := by positivity
  nlinarith

theorem det2Weight_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    det2Weight t = Real.exp (2 * (t + 1) ^ 2) := by
  simp [det2Weight, max_eq_left ht]

/-- The set of finite-rank Hilbert--Schmidt operators. -/
def finiteRankSet (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] :
    Set (HilbertSchmidt H H) := {T | HasFiniteRank (toCLM T)}

theorem dense_finiteRankSet : Dense (finiteRankSet H) := dense_finiteRank

open Classical in
/-- The finite-rank determinant, totalized by `0` off finite rank (this value is never used
off the dense set: see `det2_of_finiteRank`). -/
def det2Pre (T : HilbertSchmidt H H) : ℝ :=
  if h : HasFiniteRank (toCLM T) then finiteRankDet2 (toCLM T).toLinearMap h else 0

theorem det2Pre_of_finiteRank (T : HilbertSchmidt H H) (h : HasFiniteRank (toCLM T)) :
    det2Pre T = finiteRankDet2 (toCLM T).toLinearMap h := by
  classical
  unfold det2Pre
  rw [dif_pos h]

theorem det2Pre_lipschitz :
    ∀ a ∈ finiteRankSet H, ∀ b ∈ finiteRankSet H,
      |det2Pre a - det2Pre b| ≤ ‖a - b‖ * det2Weight (‖a‖ + ‖b‖) := by
  intro a ha b hb
  rw [det2Pre_of_finiteRank a ha, det2Pre_of_finiteRank b hb,
    det2Weight_of_nonneg (by positivity)]
  exact finiteRankDet2_lipschitz a b ha hb

theorem exists_det2 :
    ∃ g : HilbertSchmidt H H → ℝ, (∀ a ∈ finiteRankSet H, g a = det2Pre a) ∧
      (∀ x y, |g x - g y| ≤ ‖x - y‖ * det2Weight (‖x‖ + ‖y‖)) :=
  exists_extension_of_dense_locallyLipschitz (finiteRankSet H) dense_finiteRankSet det2Pre
    det2Weight continuous_det2Weight monotone_det2Weight det2Pre_lipschitz

/-- **The real Hilbert--Schmidt regularized determinant** `det2 B = det₂(I + B)`. -/
def det2 (B : HilbertSchmidt H H) : ℝ := Classical.choose (exists_det2 (H := H)) B

/-- Finite-rank formula: on finite rank, `det2` is the intrinsic finite-rank value. -/
theorem det2_of_finiteRank (B : HilbertSchmidt H H) (hB : HasFiniteRank (toCLM B)) :
    det2 B = finiteRankDet2 (toCLM B).toLinearMap hB := by
  rw [det2, (Classical.choose_spec (exists_det2 (H := H))).1 B hB, det2Pre_of_finiteRank B hB]

/-- **G3 HS-continuity estimate** (all HS operators, dimension-free). -/
theorem det2_lipschitz (A B : HilbertSchmidt H H) :
    |det2 A - det2 B| ≤ ‖A - B‖ * Real.exp (2 * (‖A‖ + ‖B‖ + 1) ^ 2) := by
  have h := (Classical.choose_spec (exists_det2 (H := H))).2 A B
  rwa [det2Weight_of_nonneg (by positivity)] at h

/-- Continuity of `det2` in the Hilbert--Schmidt norm. -/
theorem tendsto_det2 {J : Type*} (l : Filter J) (A : J → HilbertSchmidt H H)
    (B : HilbertSchmidt H H) (hA : Filter.Tendsto A l (𝓝 B)) :
    Filter.Tendsto (fun n => det2 (A n)) l (𝓝 (det2 B)) :=
  tendsto_of_locallyLipschitz det2 det2Weight continuous_det2Weight
    (Classical.choose_spec (exists_det2 (H := H))).2 l A B hA

theorem continuous_det2 : Continuous (det2 (H := H)) :=
  continuous_iff_continuousAt.mpr fun B =>
    tendsto_det2 (𝓝 B) id B Filter.tendsto_id

/-- Uniqueness: `det2` is the only continuous function extending the finite-rank values, so the
choice in its definition is immaterial. -/
theorem det2_unique (g : HilbertSchmidt H H → ℝ) (hg : Continuous g)
    (hfr : ∀ B (hB : HasFiniteRank (toCLM B)), g B = finiteRankDet2 (toCLM B).toLinearMap hB) :
    g = det2 := by
  apply Continuous.ext_on dense_finiteRankSet hg continuous_det2
  intro B hB
  rw [hfr B hB, det2_of_finiteRank B hB]

theorem finiteRank_zero : HasFiniteRank (toCLM (0 : HilbertSchmidt H H)) := by
  change FiniteDimensional ℝ (LinearMap.range (0 : H →L[ℝ] H).toLinearMap)
  rw [ContinuousLinearMap.coe_zero, LinearMap.range_zero]
  infer_instance

@[simp] theorem det2_zero : det2 (0 : HilbertSchmidt H H) = 1 := by
  rw [det2_of_finiteRank 0 finiteRank_zero]
  exact finiteRankDet2_zero _

/-- Finite matrix formula for `det2` on finite rank, in any (not necessarily orthonormal) basis
of any finite-dimensional subspace containing the range. -/
theorem det2_eq_matrix (B : HilbertSchmidt H H) (hB : HasFiniteRank (toCLM B))
    (V : Submodule ℝ H) [FiniteDimensional ℝ V]
    (hV : LinearMap.range (toCLM B).toLinearMap ≤ V)
    {I : Type*} [Fintype I] [DecidableEq I] (b : Module.Basis I ℝ V) :
    det2 B =
      Matrix.det (1 + LinearMap.toMatrix b b (restrictedEnd (toCLM B).toLinearMap V hV)) *
        Real.exp (-Matrix.trace
          (LinearMap.toMatrix b b (restrictedEnd (toCLM B).toLinearMap V hV))) := by
  rw [det2_of_finiteRank B hB]
  exact finiteRankDet2_eq_matrix _ hB V hV b

/-- `det2` of a compression to a finite-dimensional subspace is the finite regularized
determinant of the compressed operator on that subspace. -/
theorem det2_compression (V : Submodule ℝ H) [FiniteDimensional ℝ V]
    (T : HilbertSchmidt H H) :
    det2 (compression V T) =
      finiteDet2 (restrictedEnd (toCLM (compression V T)).toLinearMap V (by
        rintro z ⟨x, rfl⟩
        change toCLM (compression V T) x ∈ V
        rw [toCLM_compression]
        exact V.starProjection_apply_mem _)) := by
  rw [det2_of_finiteRank _ (compression_finiteRank V T)]
  exact compression_finiteRankDet2_formula V T

/-- **Finite-section convergence with varying operators**: for orthogonal projections onto
finite-dimensional subspaces converging strongly to the identity (along any filter) and HS
operators `A n → B` in HS norm, the finite regularized determinants of the compressions
`P_n A_n P_n` on `V_n` converge to `det2 B`. -/
theorem tendsto_finiteSection_det2 {J : Type*} (l : Filter J)
    (V : J → Submodule ℝ H) [∀ n, FiniteDimensional ℝ (V n)]
    (hstrong : ∀ x : H, Filter.Tendsto (fun n => (V n).starProjection x) l (𝓝 x))
    (A : J → HilbertSchmidt H H) (B : HilbertSchmidt H H)
    (hA : Filter.Tendsto A l (𝓝 B)) :
    Filter.Tendsto (fun n => det2 (compression (V n) (A n))) l (𝓝 (det2 B)) :=
  tendsto_det2 l _ B (tendsto_compression_varying l V hstrong A B hA)

/-- The same statement written with the finite-dimensional determinants explicitly. -/
theorem tendsto_finiteSection_finiteDet2 {J : Type*} (l : Filter J)
    (V : J → Submodule ℝ H) [∀ n, FiniteDimensional ℝ (V n)]
    (hstrong : ∀ x : H, Filter.Tendsto (fun n => (V n).starProjection x) l (𝓝 x))
    (A : J → HilbertSchmidt H H) (B : HilbertSchmidt H H)
    (hA : Filter.Tendsto A l (𝓝 B)) :
    Filter.Tendsto (fun n => finiteDet2 (restrictedEnd
        (toCLM (compression (V n) (A n))).toLinearMap (V n) (by
          rintro z ⟨x, rfl⟩
          change toCLM (compression (V n) (A n)) x ∈ V n
          rw [toCLM_compression]
          exact (V n).starProjection_apply_mem _))) l (𝓝 (det2 B)) := by
  have h := tendsto_finiteSection_det2 l V hstrong A B hA
  refine h.congr' (Filter.Eventually.of_forall fun n => ?_)
  exact det2_compression (V n) (A n)

end NlsGge.Analysis.RegularizedDeterminant
