import NlsGge.GK38.TauGamma
import NlsGge.GK38.Lib.ParamProducts

/-! P1 data: the infinity-normalized standard root and its symmetric product.
The complex cuts are real affine segments; identities are proved off the cuts. -/

set_option autoImplicit false
open Set Metric SummationFilter
namespace NlsGge.GK38
noncomputable section

def stdRoot38 (τ g2 z : ℂ) : ℂ :=
  (τ - z) * Complex.sqrt (1 - (g2 / 4) / (τ - z)^2)

def gapSegments38 (φ : PotPair) : Set ℂ :=
  ⋃ n : ℤ, segment ℝ (lamMinus φ n) (lamPlus φ n)

def rootDomain38 : Set (PotPair × ℂ) :=
  {p | p.1 ∈ gkW ∧ p.2 ∉ gapSegments38 p.1}

def rootFactor38 (n : ℤ) (p : PotPair × ℂ) : ℂ :=
  stdRoot38 (tauN p.1 n) (gamma2 p.1 n) p.2 / (Lib.piN n : ℂ)

def canonRoot38 (φ : PotPair) (z : ℂ) : ℂ :=
  2 * Complex.I * ∏'[symmetricIcc ℤ] n : ℤ, rootFactor38 n (φ,z)

end
end NlsGge.GK38
