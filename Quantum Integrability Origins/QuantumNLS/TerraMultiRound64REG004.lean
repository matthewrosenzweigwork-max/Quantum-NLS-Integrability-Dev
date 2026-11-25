import QuantumNLS.TerraMultiRound64Equivalences
import QuantumNLS.TerraMultiRound64ExtendedFourier
import QuantumNLS.TerraMultiRound64FirstIdentity
import QuantumNLS.TerraMultiRound59REG007

/-! REG-004: integer even moments, polynomial correction, and smooth recursion. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ComplexConjugate
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.TranslatedCorrelation
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE1 QuantumNLS.RiccatiPointwiseDisc
open QuantumNLS.ComplexifiedSobolevField QuantumNLS.ClassicalCharges
open QuantumNLS.TerraMultiRound41Coefficients QuantumNLS.TerraMultiRound59SobolevCoordinates
open QuantumNLS.TerraMultiRound59RCompatibility QuantumNLS.TerraMultiRound59MinimalPolynomial
open QuantumNLS.TerraMultiRound59PolynomialProperty QuantumNLS.TerraMultiRound59SourceRecursion
open QuantumNLS.TerraMultiRound59REG007 QuantumNLS.TerraMultiRound64Equivalences
open QuantumNLS.TerraMultiRound64FieldIdentity QuantumNLS.TerraMultiRound64ExtendedIdentity
open QuantumNLS.TerraMultiRound64ExtendedMeasure QuantumNLS.TerraMultiRound64ExtendedFourier
open QuantumNLS.TerraMultiRound64FirstIdentity
namespace QuantumNLS.TerraMultiRound64REG004

/-- The three criteria for arbitrary L² fields; the continuous real polynomial and
finite and extended identities on its minimal Sobolev domain; the printed smooth
recursion; and the first quartic correction. -/
theorem REG004 (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) :
    (∀ (s : ℕ), 1 ≤ s → ∀ u : L2T L,
      (hsq L (s : ℕ) (fun k => QuantumNLS.Fourier.coeff L u k) ≠ ⊤ ↔
        (∫⁻ t : ℝ, ENNReal.ofReal (t^(2*s)) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) ≠ ⊤) ∧
      ((∫⁻ t : ℝ, ENNReal.ofReal (t^(2*s)) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) ≠ ⊤ ↔
        (∑' n : ℤ, ENNReal.ofReal (‖QuantumNLS.RootWeightedCellsR26.momentum L n‖^(2*s) *
          (QuantumNLS.RootIndexedMasses.masses hκ u).1 n)) ≠ ⊤)) ∧
    (∀ (s : ℕ) (hs : 2 ≤ s), RealPolynomial (Rfield (L := L) s hs κ) ∧
      Continuous (Rfield (L := L) s hs κ)) ∧
    (∀ (s : ℕ) (hs : 2 ≤ s) (v : Hk L (s-1)),
      hsq L (s : ℕ) (fun k => QuantumNLS.Fourier.coeff L v.val k) ≠ ⊤ →
      (∫ t : ℝ, t^(2*s) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ v.val)) =
        (∑' n : ℤ, (QuantumNLS.RootWeightedCellsR26.momentum L n)^(2*s) *
          ‖QuantumNLS.Fourier.coeff L v.val n‖^2) + Rfield (L := L) s hs κ v) ∧
    (∀ (s : ℕ) (hs : 2 ≤ s) (v : Hk L (s-1)),
      ennrealToWithTop (∫⁻ t : ℝ, ENNReal.ofReal (t^(2*s)) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ v.val)) =
        ennrealToWithTop (∑' n : ℤ, ENNReal.ofReal ((QuantumNLS.RootWeightedCellsR26.momentum L n)^(2*s) *
          ‖QuantumNLS.Fourier.coeff L v.val n‖^2)) + ↑(Rfield (L := L) s hs κ v)) ∧
    (∀ f : ℝ → ℂ, SmoothPeriodic L f →
      aseq κ f 1 = f ∧ ∀ n : ℕ, aseq κ f (n+2) = fun x =>
        -deriv (aseq κ f (n+1)) x - (κ : ℂ) * conj (f x) *
          ∑ j ∈ Finset.Icc 1 n, aseq κ f j x * aseq κ f (n+1-j) x) ∧
    (∀ (s : ℕ) (hs : 2 ≤ s) (v : Hk L (s-1)) (f : ℝ → ℂ),
      physRep L (s-1 : ℕ) (coordinates (L := L) (s-1) v) = f → SmoothPeriodic L f →
      ((Rfield (L := L) s hs κ v : ℝ) : ℂ) = (-1 : ℂ)^s * ∫ y in (0 : ℝ)..L,
        conj (f y) * (aseq κ f (2*s+1) y - iteratedDeriv (2*s) f y)) ∧
    (∀ v : Hk L 1,
      (∫ t : ℝ, t^2 ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ v.val)) =
        (∑' n : ℤ, (QuantumNLS.RootWeightedCellsR26.momentum L n)^2 *
          ‖QuantumNLS.Fourier.coeff L v.val n‖^2) + R1field (L := L) κ v ∧
      R1field (L := L) κ v = κ * ∫ y : AddCircle L, ‖contRep (by omega) v y‖^4 ∂
        (volume : Measure (AddCircle L))) := by
  refine ⟨fun s hs u => integer_even_equivalences L κ hκ s hs u,
    fun s hs => ⟨Rfield_polynomial s hs κ, Rfield_continuous s hs κ⟩,
    fun s hs v hv => finite_field_identity κ hκ s hs v hv, ?_, ?_, ?_, ?_⟩
  · intro s hs v
    have h := extended_field_identity κ hκ s hs v
    rw [extended_moment_eq_lintegral, extended_fourier_eq_series] at h
    exact h
  · intro f hf
    exact ⟨aseq_one κ f, fun n => aseq_succ κ hf n⟩
  · intro s hs v f hrep hf
    change ((R (L := L) s hs κ (coordinates (L := L) (s-1) v) : ℝ) : ℂ) = _
    exact R_source_smooth L s hs κ hκ (coordinates (L := L) (s-1) v) f hrep hf
  · intro v
    exact ⟨first_field_identity κ hκ v, R1field_quartic L κ v⟩

#print axioms REG004
end QuantumNLS.TerraMultiRound64REG004
