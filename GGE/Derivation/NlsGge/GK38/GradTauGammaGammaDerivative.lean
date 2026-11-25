import NlsGge.GK38.GradTauGammaTauDerivative

/-! The squared periodic gap derivative is centered before any estimate.
The coefficient is the full-trace normalization -8/(2πi). -/
set_option autoImplicit false
open Set Metric Filter Topology MeasureTheory
namespace NlsGge.GK38
noncomputable section

def k4aGammaCLMOnCircle38 (φ : PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ) (n : ℤ) :
    PotPair →L[ℂ] ℂ :=
  (-8 * (2 * (Real.pi : ℂ) * Complex.I)⁻¹) •
    circleIntegral (fun z => (z - tauN φ n) • k4aQuotientCLM38 φ z) (C n) (R n)

theorem k4aWeightedQuotient_circleIntegrable38 (φ : PotPair)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ) (a : ℂ) :
    CircleIntegrable (fun z => (z - a) • k4aQuotientCLM38 φ z) (C n) (R n) := by
  have hA : AnalyticOnNhd ℂ (k4aQuotientCLM38 φ) {z : ℂ | perChar φ z ≠ 0} := by
    intro z hz
    exact (k4aQuotientCLM_joint_analytic38 (φ, z) hz).comp
      ((analyticAt_const (v := φ)).prod analyticAt_id)
  exact (((analyticOnNhd_id.sub analyticOnNhd_const).smul hA).continuousOn.mono
    (fun z hz => isolating_periodic_boundary38 hf n z hz)).circleIntegrable
      (isolating_radius_pos38 hf n).le

theorem k4aWeightedQuotient_integral_apply38 (φ h : PotPair)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ) (a : ℂ) :
    (circleIntegral (fun z => (z - a) • k4aQuotientCLM38 φ z) (C n) (R n)) h =
      circleIntegral (fun z => (z - a) * k4aDirectionQuotient38 φ h z) (C n) (R n) := by
  have hi := k4aWeightedQuotient_circleIntegrable38 φ C R hf n a
  unfold circleIntegral
  rw [ContinuousLinearMap.intervalIntegral_apply hi.out h]
  apply intervalIntegral.integral_congr
  intro θ _
  change deriv (circleMap (C n) (R n)) θ *
      ((circleMap (C n) (R n) θ - a) *
        ((discrim φ (circleMap (C n) (R n) θ) / perChar φ (circleMap (C n) (R n) θ)) *
          gradDiscrimCLM φ (circleMap (C n) (R n) θ) h)) =
    deriv (circleMap (C n) (R n)) θ *
      ((circleMap (C n) (R n) θ - a) *
        (discrim φ (circleMap (C n) (R n) θ) *
          gradDiscrimCLM φ (circleMap (C n) (R n) θ) h / perChar φ (circleMap (C n) (R n) θ)))
  ring

theorem k4aCenteredDirection_integral38 (φ h : PotPair)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ) (a : ℂ) :
    circleIntegral (fun z => (z - a) * k4aDirectionQuotient38 φ h z) (C n) (R n) =
      circleIntegral (fun z => z * k4aDirectionQuotient38 φ h z) (C n) (R n) -
        a * circleIntegral (k4aDirectionQuotient38 φ h) (C n) (R n) := by
  have hi := k4aDirectionCircleIntegrable38 φ h C R hf n
  have hzi : CircleIntegrable (fun z => z * k4aDirectionQuotient38 φ h z) (C n) (R n) :=
    ((analyticOnNhd_id.mul (k4aDirectionQuotient_analytic38 φ h)).continuousOn.mono
      (fun z hz => isolating_periodic_boundary38 hf n z hz)).circleIntegrable
        (isolating_radius_pos38 hf n).le
  have he : (fun z => (z - a) * k4aDirectionQuotient38 φ h z) =
      (fun z => z * k4aDirectionQuotient38 φ h z - a * k4aDirectionQuotient38 φ h z) := by
    funext z; ring
  have hai : CircleIntegrable (fun z => a * k4aDirectionQuotient38 φ h z) (C n) (R n) := by
    exact ((analyticOnNhd_const.mul (k4aDirectionQuotient_analytic38 φ h)).continuousOn.mono
      (fun z hz => isolating_periodic_boundary38 hf n z hz)).circleIntegrable
        (isolating_radius_pos38 hf n).le
  rw [he, circleIntegral.integral_sub hzi hai, circleIntegral.integral_const_mul]

theorem k4aGamma_fixed_hasFDeriv38 (V : Set PotPair) (hVo : IsOpen V) (hVW : V ⊆ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : ∀ ψ ∈ V, IsolatingFamily38 ψ C R)
    (φ : PotPair) (hφV : φ ∈ V) (n : ℤ) :
    HasFDerivAt (fun ψ => gamma2 ψ n) (k4aGammaCLMOnCircle38 φ C R n) φ := by
  have hdq₀ := k4aFixedMoment_hasFDeriv38 V hVo C R hf φ hφV n 2
  have heq : (fun ψ => q2 ψ n) =ᶠ[nhds φ] (fun ψ => fixedMoment38 ψ C R n 2) := by
    filter_upwards [hVo.mem_nhds hφV] with ψ hψ
    exact moment_local_selector_glue38 discC discR isolating_selectors_admissible38
      V C R hVW hf ψ hψ n 2
  have hdq := hdq₀.congr_of_eventuallyEq heq
  have hdt := k4aTau_fixed_hasFDeriv38 V hVo hVW C R hf φ hφV n
  have hd := (hdq.const_mul 2).sub ((hdt.pow 2).const_mul 4)
  change HasFDerivAt (fun ψ => gamma2 ψ n) _ φ at hd
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro h
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, nsmul_eq_mul, show (2 - 1 : ℕ) = 1 from rfl, pow_one]
  change 2 * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (circleIntegral (k4aMomentPartial38 φ 2) (C n) (R n)) h) -
    4 * (2 * tauN φ n * k4aTauCLMOnCircle38 φ C R n h) =
      (-8 * (2 * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (circleIntegral (fun z => (z - tauN φ n) • k4aQuotientCLM38 φ z) (C n) (R n)) h
  rw [k4aCircleIntegral_partial_apply38 φ h C R (hf φ hφV) n 2,
    k4aWeightedQuotient_integral_apply38 φ h C R (hf φ hφV) n (tauN φ n),
    k4aCenteredDirection_integral38 φ h C R (hf φ hφV) n (tauN φ n)]
  rw [(k4aDirectionCircleIBP2_38 φ h C R (hf φ hφV) n).2]
  change _ - 4 * (2 * tauN φ n *
    (-((2 * (Real.pi : ℂ) * Complex.I)⁻¹) *
      (circleIntegral (k4aQuotientCLM38 φ) (C n) (R n)) h)) = _
  rw [k4aCircleIntegral_quotient_apply38 φ h C R (hf φ hφV) n]
  ring

theorem k4aGamma_hasFDerivOnAnyCircle38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ) :
    HasFDerivAt (fun ψ => gamma2 ψ n) (k4aGammaCLMOnCircle38 φ C R n) φ := by
  obtain ⟨ρ, hρ, c, N, hg, hs⟩ := fixed_family_persistence38 φ C R hf
  let V : Set PotPair := ball φ ρ ∩ gkW
  exact k4aGamma_fixed_hasFDeriv38 V (isOpen_ball.inter isOpen_gkW)
    (fun ψ hψ => hψ.2) C R (fun ψ hψ => ⟨c, N, hg, hs ψ hψ.1⟩) φ
      ⟨mem_ball_self hρ, hφ⟩ n

theorem k4aGammaCLM_circle_independent38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C C' : ℤ → ℂ) (R R' : ℤ → ℝ)
    (hf : IsolatingFamily38 φ C R) (hf' : IsolatingFamily38 φ C' R') (n : ℤ) :
    k4aGammaCLMOnCircle38 φ C R n = k4aGammaCLMOnCircle38 φ C' R' n :=
  (k4aGamma_hasFDerivOnAnyCircle38 φ hφ C R hf n).unique
    (k4aGamma_hasFDerivOnAnyCircle38 φ hφ C' R' hf' n)

end
end NlsGge.GK38
