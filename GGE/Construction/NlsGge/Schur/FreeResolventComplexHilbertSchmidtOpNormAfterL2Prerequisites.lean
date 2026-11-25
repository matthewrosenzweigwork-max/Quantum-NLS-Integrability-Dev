import NlsGge.Analysis.ComplexHilbertSchmidtFiniteBasis
import Mathlib.Analysis.Normed.Operator.NormedSpace
import NlsGge.Schur.FreeResolventHilbertSpaceL2AfterRpowIdentity

set_option autoImplicit false
noncomputable section
open scoped ENNReal InnerProduct InnerProductSpace lp

namespace NlsGge.Schur
open NlsGge.Pilot

/-- The actual custom Hilbert--Schmidt norm dominates the operator norm. The
proof expands a vector in an arbitrary Hilbert basis and applies the pinned
`ℓ²` Hölder inequality to the coefficient sequence and the squared-summable
image norms. -/
theorem complexHilbertSchmidt_opNorm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (T : E →L[ℂ] E)
    (hT : IsComplexHilbertSchmidt T) :
    ‖T‖ ≤ complexHilbertSchmidtNorm T := by
  let ι := chosenComplexHilbertBasisIndex (E := E)
  let b : HilbertBasis ι ℂ E := chosenComplexHilbertBasis (E := E)
  have hsum : Summable (fun i => ‖T (b i)‖ ^ 2) :=
    (isComplexHilbertSchmidt_iff_summable_basis T b).mp hT
  have hhs : complexHilbertSchmidtNorm T =
      Real.sqrt (∑' i, ‖T (b i)‖ ^ 2) :=
    complexHilbertSchmidtNorm_eq_basis b hsum
  have hhsnonneg : 0 ≤ complexHilbertSchmidtNorm T := by
    unfold complexHilbertSchmidtNorm
    exact Real.sqrt_nonneg _
  apply ContinuousLinearMap.opNorm_le_bound T
    hhsnonneg
  intro x
  let f : ℓ²(ι, ℂ) := b.repr x
  let g : ℓ²(ι, ℂ) :=
    ⟨fun i => (‖T (b i)‖ : ℂ),
      complex_real_norm_sequence_memLp_two (fun i => T (b i)) hsum⟩
  have hgsq : ‖g‖ ^ 2 = ∑' i, ‖T (b i)‖ ^ 2 := by
    calc
      ‖g‖ ^ 2 = ∑' i, ‖g i‖ ^ 2 := complex_lp_two_norm_sq_eq_tsum g
      _ = ∑' i, ‖T (b i)‖ ^ 2 := by
        apply tsum_congr
        intro i
        simp [g, Complex.norm_real]
  have hgnorm : ‖g‖ = complexHilbertSchmidtNorm T := by
    rw [hhs]
    have hsum_nonneg : 0 ≤ ∑' i, ‖T (b i)‖ ^ 2 :=
      tsum_nonneg fun i => sq_nonneg _
    have hsqrt := Real.sq_sqrt hsum_nonneg
    nlinarith [hgsq, norm_nonneg g]
  have hprod := complex_lp_two_tsum_mul_le f g
  have hterm : Summable (fun i => ‖f i • T (b i)‖) := by
    apply hprod.1.of_norm_bounded
    intro i
    simp [norm_smul, g, Complex.norm_real,
      abs_of_nonneg (norm_nonneg (T (b i)))]
  have hrepr : HasSum (fun i => f i • T (b i)) (T x) := by
    have hm := (b.hasSum_repr x).mapL T
    simpa only [f, map_smul] using hm
  calc
    ‖T x‖ = ‖∑' i, f i • T (b i)‖ := by rw [hrepr.tsum_eq]
    _ ≤ ∑' i, ‖f i‖ * ‖g i‖ := by
      calc
        _ ≤ ∑' i, ‖f i • T (b i)‖ := norm_tsum_le_tsum_norm hterm
        _ = ∑' i, ‖f i‖ * ‖g i‖ := by
          apply tsum_congr
          intro i
          simp [norm_smul, g, Complex.norm_real,
            abs_of_nonneg (norm_nonneg (T (b i)))]
    _ ≤ ‖f‖ * ‖g‖ := hprod.2
    _ = complexHilbertSchmidtNorm T * ‖x‖ := by
      rw [hgnorm]
      dsimp [f]
      rw [(b.repr).norm_map]
      ring

end NlsGge.Schur
