import QuantumNLS.TerraMultiRound59MinimalPolynomial
import QuantumNLS.TerraMultiRound59FieldOrder
import QuantumNLS.TerraMultiRound59TreeOrder

/-! Minimal Sobolev polynomials agree with the retained higher-order tree coefficients. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound59RCompatibility
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.TranslatedCorrelation QuantumNLS.Sobolev
open QuantumNLS.TerraMultiRound49SobolevBridge QuantumNLS.TerraMultiRound57CollectedPowers
open QuantumNLS.TerraMultiRound59CoefficientPolynomial QuantumNLS.TerraMultiRound59MinimalPolynomial
open QuantumNLS.TerraMultiRound59SobolevCoordinates QuantumNLS.TerraMultiRound59FieldOrder
open QuantumNLS.TerraMultiRound59TreeOrder

variable {L : ℝ} [Fact (0 < L)]

def Rfield (j : ℕ) (hj : 2 ≤ j) (κ : ℝ) (u : Hk L (j - 1)) : ℝ :=
  R (L := L) j hj κ (coordinates (L := L) (j - 1) u)

def R1field (κ : ℝ) (u : Hk L 1) : ℝ :=
  R1 (L := L) κ (coordinates (L := L) 1 u)

theorem Rfield_continuous (j : ℕ) (hj : 2 ≤ j) (κ : ℝ) :
    Continuous (Rfield (L := L) j hj κ) :=
  (R_continuous (L := L) j hj κ).comp (coordinates (L := L) (j - 1)).continuous

theorem R1field_continuous (κ : ℝ) : Continuous (R1field (L := L) κ) :=
  (R1_continuous (L := L) κ).comp (coordinates (L := L) 1).continuous

#print axioms Rfield
#print axioms R1field
#print axioms Rfield_continuous
#print axioms R1field_continuous
end QuantumNLS.TerraMultiRound59RCompatibility
