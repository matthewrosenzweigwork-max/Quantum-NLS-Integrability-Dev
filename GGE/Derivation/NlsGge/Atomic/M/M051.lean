import Mathlib
import NlsGge.Atomic.M.M007
import NlsGge.Atomic.G2.G2037
import NlsGge.Atomic.M.M051Host
import NlsGge.Atomic.M.M051Accessors

/- M-051 PRODUCTION01 (proof development, AUTHOR; not reviewed).  Pro round 13 section 10 head `finitegap_omega_at_infinity`
   ("Corrected M-051 head: certificates are conclusions, same S throughout"), statement VERBATIM.  All clauses use the landed
   `NlsGge.GKDefinitionDesign.finiteGapDifferential u S` for the S produced by `g2037s1_finite_mem`.
   Route (see M051_ROUTE.md): conjuncts about S, analyticity off the cuts, the rootDomain38 equality: landed G2037 support
   (`g2037s1_finite_mem`, `g2037s1_fgd_analyticOn`, `g2037s2_deriv_eq_fgd`).  Expansion at infinity: landed
   `G2037P5.product_expansion` (Omega z = -I Q(1/z), Q analytic at 0, Q 0 = 1, on |z| > R1): gives AnalyticAtInfinity (Omega + I),
   the limit -I, and the unique-limit certificate.  Zero coefficient: the landed single-valued primitive `f` of Omega on the
   exterior (`g2037_conj5`, built from the zero spectral periods by cycle Cauchy) and FTC on each large circle. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace NlsGge.ThirdConsultation.M
namespace M051Aux
section
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.GKDefinitionDesign

theorem expansion (u : PhysicalL2) (S : Finset ℤ) :
    ∃ Q : ℂ → ℂ, AnalyticAt ℂ Q 0 ∧ Q 0 = 1 ∧ ∃ R1 : ℝ, 0 < R1 ∧
      ∀ z : ℂ, R1 < ‖z‖ → finiteGapDifferential u S z = -Complex.I * Q z⁻¹ := by
  obtain ⟨Q, hQa, hQ0, R1, hR1, hid⟩ := NlsGge.G2037P5.product_expansion S
    (fun n => tauN (realSlice u) n) (fun n => gamma2 (realSlice u) n)
    (fun n => lamDot (realSlice u) n)
  exact ⟨Q, hQa, hQ0, R1, hR1, fun z hz => hid z hz⟩

theorem inf_mem (R1 : ℝ) (hR1 : 0 < R1) :
    {z : ℂ | R1 < ‖z‖} ∈ MPrimitive.infinityFilter := by
  unfold MPrimitive.infinityFilter
  refine Filter.mem_comap.2 ⟨{w : ℂ | w ≠ 0 ∧ ‖w‖ < R1⁻¹}, ?_, ?_⟩
  · have hb : Metric.ball (0 : ℂ) R1⁻¹ ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ (inv_pos.2 hR1)
    refine mem_nhdsWithin.2 ⟨Metric.ball 0 R1⁻¹, Metric.isOpen_ball, by simpa using inv_pos.2 hR1, ?_⟩
    intro w hw
    exact ⟨hw.2, by simpa using hw.1⟩
  · intro z hz
    obtain ⟨hz0, hzn⟩ := hz
    have hz0' : z ≠ 0 := by
      intro h; apply hz0; simp [h]
    rw [norm_inv] at hzn
    show R1 < ‖z‖
    have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0'
    exact (inv_lt_inv₀ hzpos hR1).1 hzn

theorem circle_ftc (f Ω : ℂ → ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hd : ∀ z : ℂ, ‖z‖ = ρ → HasDerivAt f (Ω z) z)
    (hc : ContinuousOn Ω (Metric.sphere (0 : ℂ) ρ)) :
    circleIntegral Ω 0 ρ = 0 := by
  have hci : CircleIntegrable Ω 0 ρ := hc.circleIntegrable hρ
  have hD : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi),
      HasDerivAt (fun s : ℝ => f (circleMap 0 ρ s))
        (deriv (circleMap 0 ρ) θ • Ω (circleMap 0 ρ θ)) θ := by
    intro θ _
    have h1 : HasDerivAt f (Ω (circleMap 0 ρ θ)) (circleMap 0 ρ θ) :=
      hd _ (by simp [abs_of_nonneg hρ])
    have h2 := h1.scomp θ (hasDerivAt_circleMap 0 ρ θ)
    rw [deriv_circleMap]
    exact h2
  unfold circleIntegral
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hD ((circleIntegrable_iff ρ).1 hci)]
  have h := periodic_circleMap (0 : ℂ) ρ 0
  rw [zero_add] at h
  show f (circleMap 0 ρ (2 * Real.pi)) - f (circleMap 0 ρ 0) = 0
  rw [h, sub_self]

end
end M051Aux
end NlsGge.ThirdConsultation.M

set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology BigOperators
open NlsGge.Pilot NlsGge.GK38
open NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.M

theorem finitegap_omega_at_infinity
    (u : PhysicalL2)
    (hfg : NlsGge.ThirdConsultation.finiteGap u) :
  ∃ S : Finset ℤ,
    (∀ n : ℤ, n ∈ S ↔ periodicMinus u n ≠ periodicPlus u n) ∧
    ∃ hExterior : MPrimitive.ExteriorHolomorphic (finiteGapDifferential u S),
    ∃ hLimit : (∃! a : ℂ,
      MPrimitive.HasValueAtInfinity (finiteGapDifferential u S) a),
    AnalyticOnNhd ℂ (finiteGapDifferential u S) (finiteGapCuts u S)ᶜ ∧
    (∀ z : ℂ, (realSlice u, z) ∈ rootDomain38 →
      finiteGapDifferential u S z = omega (realSlice u) z) ∧
    AnalyticAtInfinity
      (fun z : ℂ => finiteGapDifferential u S z + Complex.I) ∧
    MPrimitive.HasLaurentCoefficient (finiteGapDifferential u S) (-1) 0 ∧
    LaurentCoefficient (finiteGapDifferential u S) hExterior (-1) = 0 ∧
    valueAtInfinity (finiteGapDifferential u S) hLimit = -Complex.I ∧
    Tendsto (finiteGapDifferential u S)
      (Filter.comap (fun z : ℂ => z⁻¹) (𝓝[≠] (0 : ℂ)))
      (𝓝 (-Complex.I)) := by
  obtain ⟨S, hS⟩ := g2037s1_finite_mem u hfg
  obtain ⟨Q, hQa, hQ0, R1, hR1, hid⟩ := M051Aux.expansion u S
  -- limit
  have hT : Tendsto (finiteGapDifferential u S) MPrimitive.infinityFilter (𝓝 (-Complex.I)) := by
    have hQt : Tendsto Q (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
      have := hQa.continuousAt.tendsto
      rw [hQ0] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hinv : Tendsto (fun z : ℂ => z⁻¹) MPrimitive.infinityFilter (𝓝[≠] (0 : ℂ)) :=
      Filter.tendsto_comap
    have h2 : Tendsto (fun z : ℂ => -Complex.I * Q z⁻¹) MPrimitive.infinityFilter
        (𝓝 (-Complex.I * 1)) :=
      ((hQt.comp hinv).const_mul (-Complex.I))
    rw [mul_one] at h2
    refine h2.congr' ?_
    filter_upwards [M051Aux.inf_mem R1 hR1] with z hz
    exact (hid z hz).symm
  have hLim : ∃! a : ℂ, MPrimitive.HasValueAtInfinity (finiteGapDifferential u S) a :=
    ⟨-Complex.I, hT, fun b hb =>
      MPrimitive.value_at_infinity_unique _ b (-Complex.I) hb hT⟩
  -- exterior
  obtain ⟨Rc, hRc, hcut⟩ := g2037c5_cuts_bounded u S
  have hExt : MPrimitive.ExteriorHolomorphic (finiteGapDifferential u S) := by
    refine ⟨Rc, hRc, (g2037s1_fgd_analyticOn u S).mono ?_⟩
    intro z hz hzc
    have := hcut hzc
    rw [mem_closedBall_zero_iff] at this
    exact absurd hz (not_lt.2 this)
  have hAn := g2037s1_fgd_analyticOn u S
  -- zero circle integrals for large radii
  obtain ⟨Rf, hRf, hcutf, f, g, hfan, hfd, hga, hfid⟩ := g2037_conj5 u S hS
  have hzero : ∀ ρ : ℝ, max Rf Rc < ρ →
      circleIntegral (finiteGapDifferential u S) 0 ρ = 0 := by
    intro ρ hρ
    have hρf : Rf < ρ := lt_of_le_of_lt (le_max_left _ _) hρ
    have hρc : Rc < ρ := lt_of_le_of_lt (le_max_right _ _) hρ
    have hout : ∀ z : ℂ, ‖z‖ = ρ → z ∉ finiteGapCuts u S := by
      intro z hz hzc
      have := hcutf hzc
      rw [mem_closedBall_zero_iff] at this
      linarith
    refine M051Aux.circle_ftc f _ ρ (hRf.trans hρf).le (fun z hz => hfd z (hout z hz)) ?_
    intro z hz
    have hzn : ‖z‖ = ρ := by simpa using hz
    exact (hAn z (hout z hzn)).continuousAt.continuousWithinAt
  have hLaur : MPrimitive.HasLaurentCoefficient (finiteGapDifferential u S) (-1) 0 := by
    have hp : (-(-1 : ℤ) - 1) = 0 := by norm_num
    refine ⟨⟨Rc, hRc, fun R hR =>
      MPrimitive.exterior_circleIntegrable _ hRc (hAn.mono ?_) (-1) hR⟩, ?_⟩
    · intro z hz hzc
      have := hcut hzc
      rw [mem_closedBall_zero_iff] at this
      exact absurd hz (not_lt.2 this)
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop (max Rf Rc)] with ρ hρ
      simp only [hp, zpow_zero, mul_one]
      rw [hzero ρ hρ, mul_zero]
  refine ⟨S, fun n => (hS n).trans ?_, hExt, hLim, hAn, ?_, ?_, hLaur, ?_, ?_, hT⟩
  · exact Iff.rfl
  · intro z hz
    exact (g2037s2_deriv_eq_fgd u S hS z hz).symm
  · -- analytic at infinity
    have hev : (fun w : ℂ => if w = 0 then 0 else
          (fun z : ℂ => finiteGapDifferential u S z + Complex.I) w⁻¹)
        =ᶠ[𝓝 (0 : ℂ)] fun w : ℂ => -Complex.I * (Q w - 1) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (inv_pos.2 hR1)] with w hw
      by_cases h0 : w = 0
      · subst h0
        simp [hQ0]
      · have hwn : ‖w‖ < R1⁻¹ := by simpa using hw
        have hwp : 0 < ‖w‖ := norm_pos_iff.2 h0
        have hbig : R1 < ‖w⁻¹‖ := by
          rw [norm_inv, lt_inv_comm₀ hR1 hwp]; exact hwn
        simp only [h0, ite_false]
        rw [hid _ hbig, inv_inv]
        ring
    have hA : AnalyticAt ℂ (fun w : ℂ => -Complex.I * (Q w - 1)) 0 :=
      analyticAt_const.mul (hQa.sub analyticAt_const)
    exact hA.congr hev.symm
  · exact ((MPrimitive.laurent_coefficient_characterization _ hExt (-1)).2 0 hLaur).symm
  · exact ((MPrimitive.value_at_infinity_characterization _ hLim).2 (-Complex.I) hT).symm

end NlsGge.ThirdConsultation.M
