import Mathlib

set_option autoImplicit false

namespace NlsGge.ThirdConsultation.KSN
noncomputable section

def midpointRatioTail (K : ℕ) (τ : ℤ → ℂ) (μ : ℂ) (n k : ℤ) : ℂ :=
  if K ≤ k.natAbs ∧ k ≠ n then (τ k - (k : ℂ) * Real.pi) / (τ k - μ) else 0

end
end NlsGge.ThirdConsultation.KSN
