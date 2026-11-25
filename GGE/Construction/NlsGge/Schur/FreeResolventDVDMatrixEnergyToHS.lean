import NlsGge.Schur.FreeResolventPotentialOffDiagonalEntries
import NlsGge.Analysis.ComplexHilbertSchmidtFiniteBasis

set_option autoImplicit false
noncomputable section
open scoped ENNReal BigOperators InnerProduct InnerProductSpace

namespace NlsGge.Schur
open NlsGge.Pilot

/-- On the actual paired parity Hilbert space and its actual Fourier basis,
the full matrix-energy estimate gives the operator Hilbert--Schmidt bound.
The continuous-linear-map argument is explicit so concrete operators can use
this bridge without unfolding their construction during type elaboration. -/
theorem freeResolventDVD_isComplexHilbertSchmidt_of_matrix_energy
    (n : ℤ) (T : ParityPair n →L[ℂ] ParityPair n) (R : ℝ)
    (hR : 0 ≤ R)
    (henergy :
      (∑' input : Bool × Sector n, ∑' output : Bool × Sector n,
        ENNReal.ofReal
          (‖inner ℂ (parityPairVector n output)
            (T (parityPairVector n input))‖ ^ 2)) ≤ ENNReal.ofReal (R ^ 2)) :
    IsComplexHilbertSchmidt T ∧ complexHilbertSchmidtNorm T ≤ R := by
  apply complexHilbertSchmidt_of_matrix_bound
    (E := ParityPair n) (F := ParityPair n) (T := T)
    (parityPairFourierBasis n) (parityPairFourierBasis n) hR
  simpa only [parityPairFourierBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]
    using henergy

end NlsGge.Schur
