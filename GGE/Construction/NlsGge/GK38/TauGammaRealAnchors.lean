import NlsGge.GK38.TauGammaContourGlue
import NlsGge.GK38.RealTypeSpectrum

/-! Real values follow the actual same-index endpoint matching, without ordering complex numbers. -/
set_option autoImplicit false
open Set
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem tauGamma_real_anchors38 (C : PotPair → ℤ → ℂ) (R : PotPair → ℤ → ℝ)
    (hsel : AdmissibleSelectors38 C R) (u : PhysicalL2) (n : ℤ) :
    tauN38 C R (realSlice u) n =
      (((actualGapLowerAllE02_38 u n + actualGapUpperAllE02_38 u n) / 2 : ℝ) : ℂ) ∧
    gamma2N38 C R (realSlice u) n =
      (((actualGapUpperAllE02_38 u n - actualGapLowerAllE02_38 u n) ^ 2 : ℝ) : ℂ) := by
  rw [tau_pair_mean38 C R hsel (realSlice u) (realSlice_mem_gkW u) n,
    gamma2_pair_gap38 C R hsel (realSlice u) (realSlice_mem_gkW u) n,
    (lamPlus_real u n).1, (lamPlus_real u n).2]
  push_cast
  constructor <;> ring

end
end NlsGge.GK38
