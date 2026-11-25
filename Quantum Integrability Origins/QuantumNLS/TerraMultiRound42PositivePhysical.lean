import QuantumNLS.TerraMultiRound42Polynomial
import QuantumNLS.SmoothScalarMomentsPrerequisite

/-! Positive-height all-order expansion in the weighted Fourier norm, with
literal physical recursive coefficients. The negative branch and solution
identification with the independent L∞ construction are separate. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Complex Finset
namespace QuantumNLS.TerraMultiRound42PositivePhysical
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE2b
open QuantumNLS.RiccatiChargeLevels QuantumNLS.RiccatiRemainder
open QuantumNLS.RiccatiExpansions QuantumNLS.RiccatiPointwiseDisc
open QuantumNLS.ComplexifiedSobolevField QuantumNLS.SmoothScalarMomentsPrerequisite
open QuantumNLS.TerraMultiRound39PhysicalBall QuantumNLS.TerraMultiRound41Coefficients
open QuantumNLS.TerraMultiRound42PositiveExpansion QuantumNLS.TerraMultiRound42Polynomial

/-- For any high-order Fourier representation of the field and any finite
order, the positive fixed point has the printed physical polynomial and a
weighted Fourier-norm remainder of order `Y^(-M-1)`. -/
theorem positive_physical_expansion (L : ℝ) [hLf : Fact (0 < L)] {a S : ℝ} {M : ℕ}
    (ha : 1 / 2 < a) (haS : a + (M : ℝ) + 1 ≤ S) (hM : 1 ≤ M)
    (κ : ℝ) (u : Ell2) (f : ℝ → ℂ)
    (hrep : physRep L a (lowT L a S u) = f) :
    ∃ B C : ℝ, 0 < B ∧ ∀ Y : ℝ, B ≤ Y →
      ∃ (hY : 0 < Y) (r p : Ell2),
        ‖r‖ ≤ 2 * ‖lowT L a S u‖ / Y ∧
        physicalT hLf.out ha (abs_pos.mpr hY.ne') κ (lowT L a S u) r = r ∧
        (∀ t : ℝ, physRep L a p t =
          ∑ n ∈ Finset.Icc 1 M, aseq κ f n t * ((Y : ℂ)⁻¹) ^ n) ∧
        ‖r - p‖ ≤ C * (Y ^ (M + 1))⁻¹ := by
  let β : ℝ := ‖u‖ + 1
  have hβ : 0 < β := by dsimp [β]; positivity
  have hu : ‖u‖ ≤ β := by dsimp [β]; linarith
  let D := derivativeExtension L
  have hD : ∀ y : dDom L, D (y : Ell2) = dmulEll L y := derivativeExtension_spec L
  obtain ⟨B₀, hB₀, hfix⟩ := physical_fixed_eventually hLf.out ha κ (lowT L a S u)
  refine ⟨max B₀ (remR L a S M (κ / L) β 1), remC L a S M (κ / L) β 1,
    lt_of_lt_of_le hB₀ (le_max_left _ _), ?_⟩
  intro Y hYB
  have hY : 0 < Y := lt_of_lt_of_le hB₀ ((le_max_left _ _).trans hYB)
  have hYB₀ : B₀ ≤ |Y| := by rw [abs_of_pos hY]; exact (le_max_left _ _).trans hYB
  obtain ⟨_, r, hrn, hr, _⟩ := hfix Y hYB₀
  have hrn' : ‖r‖ ≤ 2 * ‖lowT L a S u‖ / Y := by simpa [abs_of_pos hY] using hrn
  have hrβ : ‖r‖ ≤ 2 * β / Y := hrn'.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left ((norm_lowT_le L a S u).trans hu) (by norm_num)) hY.le)
  let p := rMsum (wAbs (mulLin hLf.out ha) D (jEll (lowT L a S u))
    (lowT L a S u) ((κ / L : ℝ) : ℂ)) (((Y : ℂ) * Complex.I)⁻¹) M
  refine ⟨hY, r, p, hrn', hr, ?_, ?_⟩
  · intro t
    exact positive_polynomial hLf.out ha haS hM κ u D hD f hrep t
  · exact positive_model_expansion hLf.out ha haS hM κ u β hβ hu D hD hY
      ((le_max_right _ _).trans hYB) r hr hrβ

#print axioms positive_physical_expansion
end QuantumNLS.TerraMultiRound42PositivePhysical
