import NlsGge.GK38.GradTauGammaMomentCLM

/-! The actual symmetric spectral mean has the independent quotient contour
as its complex L2 derivative, on any persistent fixed isolating family. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

def k4aTauCLMOnCircle38 (φ : PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ) (n : ℤ) :
    PotPair →L[ℂ] ℂ :=
  -((2 * (Real.pi : ℂ) * Complex.I)⁻¹) •
    circleIntegral (k4aQuotientCLM38 φ) (C n) (R n)

theorem k4aTau_fixed_hasFDeriv38 (V : Set PotPair) (hVo : IsOpen V) (hVW : V ⊆ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : ∀ ψ ∈ V, IsolatingFamily38 ψ C R)
    (φ : PotPair) (hφV : φ ∈ V) (n : ℤ) :
    HasFDerivAt (fun ψ => tauN ψ n) (k4aTauCLMOnCircle38 φ C R n) φ := by
  have hd := (k4aFixedMoment_hasFDeriv38 V hVo C R hf φ hφV n 1).const_mul (1 / 2 : ℂ)
  have he : (fun ψ => tauN ψ n) =ᶠ[nhds φ]
      (fun ψ => (1 / 2 : ℂ) * fixedMoment38 ψ C R n 1) := by
    filter_upwards [hVo.mem_nhds hφV] with ψ hψ
    rw [tauN_value38 ψ (hVW hψ), fixedMoment_pair38 ψ C R (hf ψ hψ) n 1]
    simp only [pow_one]
    ring
  apply (hd.congr_of_eventuallyEq he).congr_fderiv
  apply ContinuousLinearMap.ext
  intro h
  change (1 / 2 : ℂ) * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (circleIntegral (k4aMomentPartial38 φ 1) (C n) (R n)) h) =
    -((2 * (Real.pi : ℂ) * Complex.I)⁻¹) *
      (circleIntegral (k4aQuotientCLM38 φ) (C n) (R n)) h
  rw [k4aCircleIntegral_partial_apply38 φ h C R (hf φ hφV) n 1,
    k4aCircleIntegral_quotient_apply38 φ h C R (hf φ hφV) n]
  simp only [pow_one]
  rw [(k4aDirectionCircleIBP1_38 φ h C R (hf φ hφV) n).2]
  ring

theorem k4aTau_hasFDerivOnAnyCircle38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ) :
    HasFDerivAt (fun ψ => tauN ψ n) (k4aTauCLMOnCircle38 φ C R n) φ := by
  obtain ⟨ρ, hρ, c, N, hg, hs⟩ := fixed_family_persistence38 φ C R hf
  let V : Set PotPair := ball φ ρ ∩ gkW
  have hφV : φ ∈ V := ⟨mem_ball_self hρ, hφ⟩
  exact k4aTau_fixed_hasFDeriv38 V (isOpen_ball.inter isOpen_gkW)
    (fun ψ hψ => hψ.2) C R (fun ψ hψ => ⟨c, N, hg, hs ψ hψ.1⟩) φ hφV n

theorem k4aTauCLM_circle_independent38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C C' : ℤ → ℂ) (R R' : ℤ → ℝ)
    (hf : IsolatingFamily38 φ C R) (hf' : IsolatingFamily38 φ C' R') (n : ℤ) :
    k4aTauCLMOnCircle38 φ C R n = k4aTauCLMOnCircle38 φ C' R' n :=
  (k4aTau_hasFDerivOnAnyCircle38 φ hφ C R hf n).unique
    (k4aTau_hasFDerivOnAnyCircle38 φ hφ C' R' hf' n)

end
end NlsGge.GK38
