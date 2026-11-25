import QuantumNLS.TerraMultiRound59CoefficientPolynomial
import QuantumNLS.TerraMultiRound58SmoothParity
import QuantumNLS.TerraMultiRound57Quartic

/-! Minimal-order polynomial candidates and their smooth recursive identification. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace QuantumNLS.TerraMultiRound59MinimalPolynomial
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiPointwiseDisc
open QuantumNLS.ClassicalCharges QuantumNLS.TranslatedCorrelation
open QuantumNLS.TerraMultiRound49SobolevBridge QuantumNLS.TerraMultiRound57Quartic
open QuantumNLS.TerraMultiRound58Compare QuantumNLS.TerraMultiRound58SmoothParity
open QuantumNLS.TerraMultiRound59CoefficientPolynomial

variable {L : ℝ} [Fact (0 < L)]

def R (j : ℕ) (hj : 2 ≤ j) (κ : ℝ) (x : Ell2) : ℝ :=
  (-1 : ℝ) ^ j * coefficientPolynomial (L := L) (k := j - 1) (by omega) κ j (2 * j + 1) x

theorem R_continuous (j : ℕ) (hj : 2 ≤ j) (κ : ℝ) :
    Continuous (R (L := L) j hj κ) := by
  exact continuous_const.mul (coefficientPolynomial_continuous (L := L) (k := j - 1) (by omega) κ j (2 * j + 1))

theorem R_smooth_recursion (j : ℕ) (hj : 2 ≤ j) (κ : ℝ) (x : Ell2) (f : ℝ → ℂ)
    (hrep : physRep L (j - 1 : ℕ) x = f) (hf : SmoothPeriodic L f) :
    (recursiveDifference L κ f (2 * j + 1)).re = (-1 : ℝ) ^ j * R (L := L) j hj κ x := by
  have hc := coefficientPolynomial_eq (L := L) (k := j - 1) (by omega) κ j (2 * j + 1) (by omega) x
  have ht := tree_coefficient_smooth L j hj κ x f hrep hf (2 * j + 1) le_rfl
  rw [ht] at hc
  have hsign : (-1 : ℝ) ^ j * (-1 : ℝ) ^ j = 1 := by rw [← mul_pow]; norm_num
  unfold R
  rw [hc, ← mul_assoc, hsign, one_mul]

def R1 (κ : ℝ) (x : Ell2) : ℝ :=
  -coefficientPolynomial (L := L) (k := 1) (by omega) κ 2 3 x

theorem R1_continuous (κ : ℝ) : Continuous (R1 (L := L) κ) := by
  exact (coefficientPolynomial_continuous (L := L) (k := 1) (by omega) κ 2 3).neg

theorem R1_quartic (κ : ℝ) (x : Ell2) :
    R1 (L := L) κ x = κ * ∫ y : AddCircle L,
      ‖contRep (by omega) (physicalToHk (L := L) 1 x) y‖ ^ 4 ∂(volume : Measure (AddCircle L)) := by
  unfold R1
  rw [coefficientPolynomial_eq (L := L) (k := 1) (by omega) κ 2 3 (by omega) x,
    tree_coefficient_three_quartic (L := L) (k := 1) (by omega) κ x 2 (by omega),
    integral_complex_ofReal]
  simp [Complex.mul_re]

#print axioms R
#print axioms R_continuous
#print axioms R_smooth_recursion
#print axioms R1
#print axioms R1_continuous
#print axioms R1_quartic
end QuantumNLS.TerraMultiRound59MinimalPolynomial
