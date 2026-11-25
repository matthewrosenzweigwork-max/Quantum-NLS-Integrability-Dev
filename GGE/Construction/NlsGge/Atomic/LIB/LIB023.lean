import NlsGge.Atomic.LIB.LIB021
import NlsGge.Atomic.LIB.LIB022
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Real.Sqrt

/-!
# Square-summable Hilbert-basis columns give compact operators

The projection is the actual orthogonal projection onto the span of the chosen
finite basis set. The error is `T - T.comp P`, so it discards input columns.
The sharp constant-one norm estimate follows from finite Cauchy--Schwarz and
Bessel before passing to the genuine basis expansion. Compactness uses the net
of all finite subsets; no enumeration or countability premise is introduced.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped ENNReal InnerProductSpace Topology Classical

namespace NlsGge.Atomic.LIB023

variable {𝕜 ι E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The operator norm is controlled by the actual summable squared basis columns. -/
theorem opNorm_le_sqrt_columns (b : HilbertBasis ι 𝕜 E) (T : E →L[𝕜] F)
    (h : Summable (fun i => ‖T (b i)‖ ^ 2)) :
    ‖T‖ ≤ Real.sqrt (∑' i, ‖T (b i)‖ ^ 2) := by
  apply T.opNorm_le_bound (Real.sqrt_nonneg _)
  intro x
  have hlim := (T.hasSum (b.hasSum_repr x)).norm
  apply le_of_tendsto' hlim
  intro s
  calc
    ‖∑ i ∈ s, T (b.repr x i • b i)‖
        ≤ ∑ i ∈ s, ‖b.repr x i‖ * ‖T (b i)‖ := by
      simpa only [map_smul, norm_smul] using
        (norm_sum_le s (fun i => T (b.repr x i • b i)))
    _ ≤ Real.sqrt (∑ i ∈ s, ‖b.repr x i‖ ^ 2) *
          Real.sqrt (∑ i ∈ s, ‖T (b i)‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt s _ _
    _ ≤ ‖x‖ * Real.sqrt (∑' i, ‖T (b i)‖ ^ 2) := by
      apply mul_le_mul ?_ ?_ (Real.sqrt_nonneg _) (norm_nonneg _)
      · apply (Real.sqrt_le_sqrt _).trans_eq (Real.sqrt_sq (norm_nonneg x))
        simpa only [b.repr_apply_apply] using b.orthonormal.sum_inner_products_le x
      · exact Real.sqrt_le_sqrt (h.sum_le_tsum s (fun _ _ => sq_nonneg _))
    _ = Real.sqrt (∑' i, ‖T (b i)‖ ^ 2) * ‖x‖ := mul_comm _ _

/-- The actual finite-dimensional span of the selected basis vectors. -/
def basisSpan (b : HilbertBasis ι 𝕜 E) (s : Finset ι) : Submodule 𝕜 E := by
  classical
  exact Submodule.span 𝕜 (s.image b : Set E)

instance basisSpan_finiteDimensional (b : HilbertBasis ι 𝕜 E) (s : Finset ι) :
    FiniteDimensional 𝕜 (basisSpan b s) := by
  classical
  exact FiniteDimensional.span_of_finite 𝕜 (s.image b).finite_toSet

/-- Canonical orthogonal projection onto exactly the finite basis span. -/
def basisProjection (b : HilbertBasis ι 𝕜 E) (s : Finset ι) : E →L[𝕜] E :=
  (basisSpan b s).starProjection

/-- Explicit coefficient formula fixes the projection and conjugation convention. -/
theorem basisProjection_apply (b : HilbertBasis ι 𝕜 E) (s : Finset ι) (x : E) :
    basisProjection b s x = ∑ i ∈ s, inner 𝕜 (b i) x • b i := by
  classical
  have hp := (OrthonormalBasis.span b.orthonormal s).starProjection_eq_sum_rankOne
  change (Submodule.span 𝕜 (s.image b : Set E)).starProjection x = _
  rw [hp]
  simp only [sum_apply, InnerProductSpace.rankOne_apply,
    OrthonormalBasis.span_apply]
  exact Finset.sum_coe_sort s (fun i => inner 𝕜 (b i) x • b i)

@[simp]
theorem basisProjection_basis (b : HilbertBasis ι 𝕜 E) (s : Finset ι) (i : ι) :
    basisProjection b s (b i) = if i ∈ s then b i else 0 := by
  classical
  simp [basisProjection_apply, orthonormal_iff_ite.mp b.orthonormal]

/-- Finite input-column truncations have genuinely finite-dimensional range. -/
theorem basisProjection_finiteRank (b : HilbertBasis ι 𝕜 E) (s : Finset ι) :
    FiniteDimensional 𝕜 (LinearMap.range (basisProjection b s).toLinearMap) := by
  have hrange : LinearMap.range (basisProjection b s).toLinearMap ≤ basisSpan b s := by
    rintro y ⟨x, rfl⟩
    exact (basisSpan b s).starProjection_apply_mem x
  exact Submodule.finiteDimensional_of_le hrange

/-- Sharp operator-norm tail bound, summing exactly the omitted input columns. -/
theorem operator_tail_bound (b : HilbertBasis ι 𝕜 E) (T : E →L[𝕜] F)
    (h : Summable (fun i => ‖T (b i)‖ ^ 2)) (s : Finset ι) :
    ‖T - T.comp (basisProjection b s)‖ ≤
      Real.sqrt (∑' i : {i // i ∉ s}, ‖T (b i)‖ ^ 2) := by
  classical
  let S := T - T.comp (basisProjection b s)
  have hcol (i : ι) : S (b i) = if i ∈ s then 0 else T (b i) := by
    by_cases hi : i ∈ s <;> simp [S, hi]
  have hS : Summable (fun i => ‖S (b i)‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => by
      by_cases hi : i ∈ s <;> simp [hcol, hi]) h
  have hsupport : Function.support (fun i => ‖S (b i)‖ ^ 2) ⊆ {i | i ∉ s} := by
    intro i hi hmem
    exact hi (by simp [hcol, hmem])
  have htail : (∑' i, ‖S (b i)‖ ^ 2) =
      ∑' i : {i // i ∉ s}, ‖T (b i)‖ ^ 2 := by
    rw [← tsum_subtype_eq_of_support_subset hsupport]
    apply tsum_congr
    intro i
    have hi : (i : ι) ∉ s := i.property
    simp only [hcol, ite_eq_right hi]
  exact (opNorm_le_sqrt_columns b S hS).trans_eq (congrArg Real.sqrt htail)

/-- The finite-column maps converge in operator norm along all finite subsets. -/
theorem finiteColumnApprox_tendsto (b : HilbertBasis ι 𝕜 E) (T : E →L[𝕜] F)
    (h : Summable (fun i => ‖T (b i)‖ ^ 2)) :
    Tendsto (fun s : Finset ι => T.comp (basisProjection b s)) atTop (𝓝 T) := by
  have htail := (tendsto_tsum_compl_atTop_zero (fun i => ‖T (b i)‖ ^ 2)).sqrt
  simp only [Real.sqrt_zero] at htail
  have hnorm : Tendsto (fun s : Finset ι => ‖T - T.comp (basisProjection b s)‖)
      atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero (fun s => norm_nonneg _) (operator_tail_bound b T h) htail
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [norm_sub_rev] using hnorm

/-- Square-summable columns imply compactness of the actual bounded operator. -/
theorem hs_columns_compact [CompleteSpace F] (b : HilbertBasis ι 𝕜 E)
    (T : E →L[𝕜] F) (h : Summable (fun i => ‖T (b i)‖ ^ 2)) :
    IsCompactOperator T := by
  apply isCompactOperator_of_tendsto (finiteColumnApprox_tendsto b T h)
  apply Eventually.of_forall
  intro s
  exact (NlsGge.Atomic.LIB.finiteRank_isCompact (basisProjection b s)
    (basisProjection_finiteRank b s)).clm_comp T

end NlsGge.Atomic.LIB023
