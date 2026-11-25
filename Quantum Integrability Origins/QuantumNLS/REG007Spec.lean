import QuantumNLS.TerraMultiRound59REG007
/-! integrator-authored trusted spec for REG-007 CC:G04:scalar-expansion (terra_review r213/r214 PASS): headline statement(s) copied verbatim from TerraMultiRound59REG007 (QuantumNLS.TerraMultiRound59REG007). -/
set_option autoImplicit false
noncomputable section
open Filter Topology Asymptotics MeasureTheory ComplexConjugate
namespace QuantumNLS.REG007Spec
open QuantumNLS.TerraMultiRound59REG007
open QuantumNLS.PhysicalTensor QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.RiccatiSobolevE1 QuantumNLS.RiccatiPointwiseDisc
open QuantumNLS.ComplexifiedSobolevField QuantumNLS.RootH1RatioBounds
open QuantumNLS.ClassicalCharges QuantumNLS.TranslatedCorrelation
open QuantumNLS.TerraMultiRound40ScalarParity QuantumNLS.TerraMultiRound41Coefficients
open QuantumNLS.TerraMultiRound49SobolevBridge QuantumNLS.TerraMultiRound57Collection
open QuantumNLS.TerraMultiRound59SobolevCoordinates QuantumNLS.TerraMultiRound59MinimalPolynomial
open QuantumNLS.TerraMultiRound59RCompatibility QuantumNLS.TerraMultiRound59SignedCharges
open QuantumNLS.TerraMultiRound59SignedExpansion QuantumNLS.TerraMultiRound59SourceRecursion
open QuantumNLS.TerraMultiRound59PolynomialProperty

set_option maxHeartbeats 8000000 in
theorem REG007_spec (L : ℝ) [Fact (0 < L)] (s : ℕ) (hs : 2 ≤ s)
    (κ : ℝ) (hκ : 0 < κ) (u : L2T L)
    (hu : hsq L (s - 1 : ℕ) (fun k => QuantumNLS.Fourier.coeff L u k) ≠ ⊤) :
    (∀ (j : ℕ) (hj : 2 ≤ j), RealPolynomial (Rfield (L := L) j hj κ) ∧
      Continuous (Rfield (L := L) j hj κ)) ∧
    RealPolynomial (R1field (L := L) κ) ∧ Continuous (R1field (L := L) κ) ∧
    (∀ v : Hk L 1, R1field (L := L) κ v = κ * ∫ y : AddCircle L,
      ‖contRep (by omega) v y‖ ^ 4 ∂(volume : Measure (AddCircle L))) ∧
    (∀ (j : ℕ) (hj : 2 ≤ j) (x : Ell2) (f : ℝ → ℂ),
      physRep L (j - 1 : ℕ) x = f → SmoothPeriodic L f →
      ((Rfield (L := L) j hj κ (physicalToHk (L := L) (j - 1) x) : ℝ) : ℂ) =
        (-1 : ℂ) ^ j * ∫ y in (0 : ℝ)..L,
          conj (f y) * (aseq κ f (2 * j + 1) y - iteratedDeriv (2 * j) f y)) ∧
    (∃ (x : Ell2) (ha0 : 0 ≤ ((s - 1 : ℕ) : ℝ)) (r : ℝ → Ell2),
      fieldMap L (s - 1 : ℕ) ha0 x = u ∧
      (physicalToHk (L := L) (s - 1) x).val = u ∧
      (∀ᶠ Y : ℝ in atTop, ∃ (hY : 0 < Y) (hlog : Real.log 3 ≤ Y * L)
        (hsmall : 16 * κ * ‖u‖ ^ 2 ≤ Y),
        fieldMap L (s - 1 : ℕ) ha0 (r Y) = ratioL2 hY hlog hκ.le u hsmall) ∧
      (fun Y : ℝ => (scalar L (s - 1 : ℕ) x (r Y) - freeScalar (L := L) (s - 1 : ℕ) x Y).re -
        ∑ j ∈ Finset.Icc 1 s, (-1 : ℝ) ^ j *
          retainedR (L := L) s hs κ (physicalToHk (L := L) (s - 1) x) j * Y⁻¹ ^ (2 * j + 1))
        =o[atTop] (fun Y : ℝ => Y⁻¹ ^ (2 * s + 1))) := by
  exact QuantumNLS.TerraMultiRound59REG007.REG007 L s hs κ hκ u hu

end QuantumNLS.REG007Spec
#print axioms QuantumNLS.REG007Spec.REG007_spec
