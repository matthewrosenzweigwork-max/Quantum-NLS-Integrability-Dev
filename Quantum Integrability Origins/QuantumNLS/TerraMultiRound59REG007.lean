import QuantumNLS.TerraMultiRound59SignedExpansion
import QuantumNLS.TerraMultiRound59SourceRecursion
import QuantumNLS.TerraMultiRound59PolynomialProperty

/-! REG-007: scalar expansion with minimal Sobolev polynomial coefficients. -/
set_option autoImplicit false
noncomputable section
open Filter Topology Asymptotics MeasureTheory ComplexConjugate
namespace QuantumNLS.TerraMultiRound59REG007
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

theorem physicalToHk_val_eq_fieldMap (L : ℝ) [Fact (0 < L)] (k : ℕ)
    (ha : 0 ≤ (k : ℝ)) (x : Ell2) :
    (physicalToHk (L := L) k x).val = fieldMap L k ha x := by
  apply (QuantumNLS.Fourier.fourierL2 L).injective
  ext n
  rw [physicalToHk_coeff, QuantumNLS.Fourier.fourierL2_apply, coeff_fieldMap]

theorem R1field_quartic (L : ℝ) [Fact (0 < L)] (κ : ℝ) (u : Hk L 1) :
    R1field (L := L) κ u = κ * ∫ y : AddCircle L, ‖contRep (by omega) u y‖ ^ 4 ∂
      (volume : Measure (AddCircle L)) := by
  unfold R1field
  rw [R1_quartic, physical_coordinates]

/-- The fixed-field scalar remainder, minimal-domain polynomial coefficients,
quartic first term, and smooth recursion identification in one statement. -/
theorem REG007 (L : ℝ) [Fact (0 < L)] (s : ℕ) (hs : 2 ≤ s)
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
  refine ⟨fun j hj => ⟨Rfield_polynomial j hj κ, Rfield_continuous j hj κ⟩,
    R1field_polynomial κ, R1field_continuous κ, fun v => R1field_quartic L κ v, ?_, ?_⟩
  · intro j hj x f hrep hf
    change ((R (L := L) j hj κ (coordinates (L := L) (j - 1)
      (physicalToHk (L := L) (j - 1) x)) : ℝ) : ℂ) = _
    rw [coordinates_physical]
    exact R_source_smooth L j hj κ hκ x f hrep hf
  · obtain ⟨x, ha0, r, hx, hr, he⟩ := physical_signed_expansion L s hs κ hκ u hu
    refine ⟨x, ha0, r, hx, ?_, hr, he⟩
    rw [physicalToHk_val_eq_fieldMap L (s - 1) ha0 x, hx]

#print axioms physicalToHk_val_eq_fieldMap
#print axioms R1field_quartic
#print axioms REG007
end QuantumNLS.TerraMultiRound59REG007
