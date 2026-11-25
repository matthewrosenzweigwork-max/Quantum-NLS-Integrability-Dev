import QuantumNLS.TerraMultiRound47TorusShift
import QuantumNLS.TerraMultiRound39SignedGain

/-! Laplace shifts for the actual weighted-Fourier physical representative. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set AddCircle
namespace QuantumNLS.TerraMultiRound47PhysicalShift
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE2b
open QuantumNLS.RiccatiPointwise QuantumNLS.RiccatiPointwiseCoef QuantumNLS.RiccatiPointwiseDisc
open QuantumNLS.TerraMultiRound38SignedPicard QuantumNLS.TerraMultiRound39SignedGain
open QuantumNLS.TerraMultiRound47TorusShift QuantumNLS.Fourier

/-- The weighted Fourier representative uses exactly the torus normalization. -/
theorem physRep_seriesRep (L : ℝ) [Fact (0 < L)] (a : ℝ) (u : Ell2) (x : ℝ) :
    physRep L a u x = seriesRep L (toField L a u) (x : AddCircle L) := by
  rw [normalized_series_real]
  unfold physRep series
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  have he : ex L k x = Complex.exp (Complex.I * (QuantumNLS.RiccatiSobolevE1.freq L k : ℂ) * x) := by
    unfold ex QuantumNLS.RiccatiSobolevE1.freq
    congr 1
    push_cast
    ring
  rw [he]
  ring

/-- Pointwise Laplace-shift identity for the signed resolvent on the actual
Sobolev model, valid for either sign of nonzero Y and all orders above 1/2. -/
theorem physical_resolvent_laplace (L : ℝ) [hL : Fact (0 < L)] {a Y : ℝ}
    (ha : 1 / 2 < a) (hY : 0 < |Y|) (u : Ell2) (x : ℝ) :
    physRep L a (signedCLM L Y hY u) x = (Y⁻¹ : ℂ) *
      ∫ v : ℝ in Ioi 0, (Real.exp (-v) : ℂ) * physRep L a u (x - v / Y) := by
  have h := torus_series_laplace L Y (abs_pos.mp hY) (toField L a u)
    (summable_norm_toField hL.out ha u) x
  rw [← toField_signedCLM L a Y hY u] at h
  simp_rw [← physRep_seriesRep] at h
  exact h

#print axioms physRep_seriesRep
#print axioms physical_resolvent_laplace
end QuantumNLS.TerraMultiRound47PhysicalShift
