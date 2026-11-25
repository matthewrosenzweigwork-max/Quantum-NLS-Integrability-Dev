import QuantumNLS.TerraMultiRound58ScalarSmooth
import QuantumNLS.TerraMultiRound57Collection

/-! Smooth expansion of the exact free-resolvent scalar. -/
set_option autoImplicit false
noncomputable section
open Complex ComplexConjugate MeasureTheory Finset
namespace QuantumNLS.TerraMultiRound58FreeSmooth
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiPointwiseDisc
open QuantumNLS.RiccatiSobolevE2b
open QuantumNLS.RiccatiODEConverse
open QuantumNLS.RiccatiExpansions QuantumNLS.ClassicalCharges
open QuantumNLS.TerraMultiRound38SignedPicard QuantumNLS.TerraMultiRound39PhysicalBall
open QuantumNLS.TerraMultiRound40ScalarParity QuantumNLS.TerraMultiRound41Coefficients
open QuantumNLS.TerraMultiRound43TwoSidedExpansion QuantumNLS.TerraMultiRound45ScalarBound
open QuantumNLS.TerraMultiRound57Collection QuantumNLS.TerraMultiRound58ScalarSmooth

/-- The free scalar has the same smooth recursive expansion at zero coupling,
with a quantitative error of one further inverse power. -/
theorem free_scalar_smooth_expansion (L : ℝ) [hLf : Fact (0 < L)] (a : ℝ)
    (ha : 1 / 2 < a) (x : Ell2) (f : ℝ → ℂ)
    (hrep : physRep L a x = f) (hf : SmoothPeriodic L f)
    (M : ℕ) (hM : 1 ≤ M) :
    ∃ B C : ℝ, 0 < B ∧ ∀ Y : ℝ, B ≤ Y →
      ‖freeScalar (L := L) a x Y - ∑ n ∈ Finset.Icc 1 M,
        coefficient L 0 f n * ((Y : ℂ)⁻¹) ^ n‖ ≤ C * (Y ^ (M + 1))⁻¹ := by
  obtain ⟨z, hz, _, hp, _⟩ := smooth_two_sided_expansion L ha 0 f hf
  have he : z = x := physRep_injective hLf.out ha (hz.trans hrep.symm)
  subst z
  obtain ⟨B, C, hB, hb⟩ := hp M hM
  refine ⟨B, (L * physK L a ^ 2 * ‖x‖) * C, hB, ?_⟩
  intro Y hYB
  obtain ⟨hY, r, p, _, hr, hpoint, herr⟩ := hb Y hYB
  have hr' : signedCLM L Y (abs_pos.mpr hY.ne') x = r := by
    simpa [physicalT, signedT] using hr
  have hfree : freeScalar (L := L) a x Y = scalar L a x r := by
    simp only [freeScalar, dif_pos (abs_pos.mpr hY.ne')]
    rw [hr']
  rw [hfree, ← scalar_recursive_approximant L a 0 x p f hf hrep M Y hpoint]
  have hc : 0 ≤ L * physK L a ^ 2 * ‖x‖ := by
    have hL : 0 < L := hLf.out
    positivity
  exact (scalar_approximation_bound L hLf.out ha x r p).trans (by
    calc
      (L * physK L a ^ 2 * ‖x‖) * ‖r - p‖ ≤
          (L * physK L a ^ 2 * ‖x‖) * (C * (Y ^ (M + 1))⁻¹) :=
        mul_le_mul_of_nonneg_left herr hc
      _ = _ := by ring)

#print axioms free_scalar_smooth_expansion
end QuantumNLS.TerraMultiRound58FreeSmooth
