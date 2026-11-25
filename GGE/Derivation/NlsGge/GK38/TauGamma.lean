import NlsGge.GK38.TauGammaCoefficient
import NlsGge.GK38.TauGammaRealAnchors

/-! GK I.12: actual circle moments, analytic symmetric gap data and full multiplicative critical estimate. -/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem tauN_value38 (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    tauN φ n = (lamPlus φ n + lamMinus φ n) / 2 :=
  tau_pair_mean38 discC discR isolating_selectors_admissible38 φ hφ n

theorem gamma2_value38 (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    gamma2 φ n = (lamPlus φ n - lamMinus φ n) ^ 2 :=
  gamma2_pair_gap38 discC discR isolating_selectors_admissible38 φ hφ n

theorem tauN_analytic (n : ℤ) : AnalyticOnNhd ℂ (fun φ => tauN φ n) gkW :=
  tauN_analytic38 discC discR isolating_selectors_admissible38 n

theorem gamma2_analytic (n : ℤ) : AnalyticOnNhd ℂ (fun φ => gamma2 φ n) gkW :=
  (tauGamma_analytic38 discC discR isolating_selectors_admissible38 n).2

theorem tauGamma_real38 (u : PhysicalL2) (n : ℤ) :
    tauN (realSlice u) n =
      (((actualGapLowerAllE02_38 u n + actualGapUpperAllE02_38 u n) / 2 : ℝ) : ℂ) ∧
    gamma2 (realSlice u) n =
      (((actualGapUpperAllE02_38 u n - actualGapLowerAllE02_38 u n) ^ 2 : ℝ) : ℂ) :=
  tauGamma_real_anchors38 discC discR isolating_selectors_admissible38 u n

theorem tauGamma_l2 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) :
    IsLocUnifL2Seq (fun φ n => tauN φ n - (n : ℂ) * (Real.pi : ℂ)) φ₀ ∧
      IsLocUnifL2Seq (fun φ n => (Real.sqrt ‖gamma2 φ n‖ : ℂ)) φ₀ :=
  tauGamma_l2_38 discC discR isolating_selectors_admissible38 φ₀ hφ₀

theorem tauGamma_final38 :
    (∀ n : ℤ, AnalyticOnNhd ℂ (fun φ => tauN φ n) gkW ∧
      AnalyticOnNhd ℂ (fun φ => gamma2 φ n) gkW) ∧
    (∀ φ₀ ∈ gkW,
      IsLocUnifL2Seq (fun φ n => tauN φ n - (n : ℂ) * (Real.pi : ℂ)) φ₀ ∧
      IsLocUnifL2Seq (fun φ n => (Real.sqrt ‖gamma2 φ n‖ : ℂ)) φ₀) ∧
    (∀ φ₀ ∈ gkW, ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ U ⊆ gkW ∧ ∃ a : PotPair → ℤ → ℂ,
      (∀ φ ∈ U, ∀ n : ℤ, lamDot φ n - tauN φ n = gamma2 φ n * a φ n) ∧
      IsLocUnifL2Seq a φ₀) :=
  ⟨fun n => ⟨tauN_analytic n, gamma2_analytic n⟩, tauGamma_l2, lamDot_sub_tau⟩

end
end NlsGge.GK38
