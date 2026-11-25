import QuantumNLS.TerraMultiRound41Cauchy

/-! Removal of the auxiliary high-strip parameters in the positive scalar
identity. The separately constructed L∞ solution is not identified here. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Complex
namespace QuantumNLS.TerraMultiRound41CauchyEventually
open QuantumNLS.PhysicalTensor QuantumNLS.FullMass QuantumNLS.RootMeasureComplex
open QuantumNLS.CauchyUniqueness QuantumNLS.RiccatiSobolevBanach QuantumNLS.ComplexifiedSobolevField
open QuantumNLS.RiccatiSobolevE2b QuantumNLS.RiccatiExpansions
open QuantumNLS.TerraMultiRound39PhysicalBall QuantumNLS.TerraMultiRound40ScalarParity
open QuantumNLS.TerraMultiRound41Cauchy

/-- At all sufficiently large positive heights the actual small signed
fixed point has exactly the selected quantum Cauchy scalar. -/
theorem positive_scalar_cauchy_eventually (L : ℝ) [hLf : Fact (0 < L)]
    {a : ℝ} (ha : 1 / 2 < a) (κ : ℝ) (hκ : 0 < κ) (u : Ell2) :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, C ≤ Y →
      ∃ (hY : 0 < Y) (r : Ell2),
        ‖r‖ ≤ 2 * ‖u‖ / Y ∧
        physicalT hLf.out ha (abs_pos.mpr hY.ne') κ u r = r ∧
        CauchyUniqueness.cauchyTransform
          (Mmeas κ (fieldMap L a (by linarith : (0 : ℝ) ≤ a) u)) ((Y : ℂ) * Complex.I) =
            -Complex.I * scalar L a u r := by
  let β : ℝ := ‖u‖ + 1
  let B : ℝ := 1 + ‖fieldMap L a (by linarith : (0 : ℝ) ≤ a) u‖ ^ 2 +
    2 * L * (physK L a) ^ 2 * β ^ 2
  have hβ : 0 < β := by dsimp [β]; positivity
  have hu : ‖u‖ ≤ β := by dsimp [β]; linarith
  have hL : 0 < L := hLf.out
  have hb0 : 0 ≤ 2 * L * (physK L a) ^ 2 * β ^ 2 := by positivity
  have hB : 0 < B := by dsimp [B]; nlinarith [sq_nonneg ‖fieldMap L a (by linarith : (0 : ℝ) ≤ a) u‖]
  have hm : ‖fieldMap L a (by linarith : (0 : ℝ) ≤ a) u‖ ^ 2 ≤ B := by dsimp [B]; linarith
  have hb : 2 * L * (physK L a) ^ 2 * β ^ 2 ≤ B := by dsimp [B]; nlinarith [sq_nonneg ‖fieldMap L a (by linarith : (0 : ℝ) ≤ a) u‖]
  obtain ⟨C₀, hC₀, hfix⟩ := physical_fixed_eventually hLf.out ha κ u
  refine ⟨max C₀ (max (4 * κ * B) (Real.log 16 / L)),
    lt_of_lt_of_le hC₀ (le_max_left _ _), ?_⟩
  intro Y hYB
  have hY : 0 < Y := lt_of_lt_of_le hC₀ ((le_max_left _ _).trans hYB)
  have hC₀Y : C₀ ≤ |Y| := by rw [abs_of_pos hY]; exact (le_max_left _ _).trans hYB
  obtain ⟨_, r, hrn, hr, _⟩ := hfix Y hC₀Y
  have hrn' : ‖r‖ ≤ 2 * ‖u‖ / Y := by simpa [abs_of_pos hY] using hrn
  have hr' : physicalT hLf.out ha (abs_pos.mpr hY.ne') κ u r = r := hr
  have hhigh : HighHalf L (κ * B) ((Y : ℂ) * Complex.I) := by
    constructor
    · have hh := (le_max_left (4 * κ * B) (Real.log 16 / L)).trans
        ((le_max_right _ _).trans hYB)
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_im,
        Complex.I_re, mul_one, mul_zero, add_zero]
      nlinarith
    · have hy := (le_max_right (4 * κ * B) (Real.log 16 / L)).trans
        ((le_max_right _ _).trans hYB)
      have hy' := (div_le_iff₀ hLf.out).mp hy
      simpa [mul_comm] using hy'
  refine ⟨hY, r, hrn', hr', ?_⟩
  apply positive_scalar_cauchy L ha hY hκ u r β B hβ hu _ hr' hB hm hb hhigh
  exact hrn'.trans (div_le_div_of_nonneg_right (by linarith) hY.le)

#print axioms positive_scalar_cauchy_eventually
end QuantumNLS.TerraMultiRound41CauchyEventually
