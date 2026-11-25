import QuantumNLS.TerraMultiRound39PhysicalBall

/-! Conjugation covariance of the signed resolvent. This is one ingredient
of the REG-005 parity argument, not the scalar parity identity itself. -/
set_option autoImplicit false
noncomputable section
open Complex ComplexConjugate
namespace QuantumNLS.TerraMultiRound39ConjugateResolvent
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE1
open QuantumNLS.TerraMultiRound38SignedPicard QuantumNLS.ComplexifiedSobolevField

/-- Real-parameter Fourier resolvents commute with physical conjugation. -/
theorem signedCLM_jEll (L Y : ℝ) (hY : 0 < |Y|) (x : Ell2) :
    jEll (signedCLM L Y hY x) = signedCLM L Y hY (jEll x) := by
  apply lp.ext
  funext k
  change conj (x (-k) / ((Y : ℂ) + Complex.I * (freq L (-k) : ℂ))) =
    conj (x (-k)) / ((Y : ℂ) + Complex.I * (freq L k : ℂ))
  rw [map_div₀, map_add, Complex.conj_ofReal, map_mul, Complex.conj_I, Complex.conj_ofReal]
  have hf : freq L (-k) = -freq L k := by simp [freq, neg_div]
  rw [hf]
  push_cast
  congr 2
  ring

end QuantumNLS.TerraMultiRound39ConjugateResolvent
#print axioms QuantumNLS.TerraMultiRound39ConjugateResolvent.signedCLM_jEll
