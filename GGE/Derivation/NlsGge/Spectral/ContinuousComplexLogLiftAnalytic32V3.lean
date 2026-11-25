import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace NlsGge.SpectralFoundations

/-- A continuous logarithm of an analytic nowhere-zero function on an open
set is analytic. The logarithm is not assumed to be the principal branch.
This local prerequisite does not supply a spectral branch or its normalization. -/
theorem analyticOnNhd_of_continuousComplexLogLift32
    {U : Set ℂ} (hU : IsOpen U) {f ℓ : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hf0 : ∀ z ∈ U, f z ≠ 0)
    (hℓ : ContinuousOn ℓ U) (he : ∀ z ∈ U, Complex.exp (ℓ z) = f z) :
    AnalyticOnNhd ℂ ℓ U := by
  intro x hx
  have hc : ContinuousAt (fun z => ℓ z - ℓ x) x :=
    ((hℓ x hx).continuousAt (hU.mem_nhds hx)).sub continuousAt_const
  have hs : ∀ᶠ z in 𝓝 x, (ℓ z - ℓ x).im ∈ Ioo (-Real.pi) Real.pi := by
    apply (Complex.continuous_im.continuousAt.comp hc).eventually_mem
    apply isOpen_Ioo.mem_nhds
    simpa only [Function.comp_apply, sub_self, Complex.zero_im] using
      (show (0 : ℝ) ∈ Ioo (-Real.pi) Real.pi from
        ⟨neg_lt_zero.mpr Real.pi_pos, Real.pi_pos⟩)
  have ha : AnalyticAt ℂ (fun z => Complex.log (f z / f x) + ℓ x) x := by
    have hq : AnalyticAt ℂ (fun z => f z / f x) x := (hf x hx).div_const
    have hsl : f x / f x ∈ Complex.slitPlane := by
      rw [div_self (hf0 x hx)]
      exact Complex.one_mem_slitPlane
    exact (hq.clog hsl).add analyticAt_const
  apply ha.congr
  filter_upwards [hU.mem_nhds hx, hs] with z hz hzstrip
  rw [← he z hz, ← he x hx, ← Complex.exp_sub,
    Complex.log_exp hzstrip.1 (le_of_lt hzstrip.2)]
  ring

/-- An analytic nowhere-zero function on an open simply connected domain
has an analytic logarithm. The additive integer ambiguity remains explicit
through the existential choice; no asymptotic normalization is asserted. -/
theorem exists_analyticComplexLogLift32
    {U : Set ℂ} (hU : IsOpen U) (hc : IsSimplyConnected U) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hf0 : ∀ z ∈ U, f z ≠ 0) :
    ∃ ℓ : ℂ → ℂ, AnalyticOnNhd ℂ ℓ U ∧ ∀ z ∈ U, Complex.exp (ℓ z) = f z := by
  have hn : (0 : ℂ) ∉ f '' U := by
    rintro ⟨z, hz, he⟩
    exact hf0 z hz he
  obtain ⟨ℓ, hl, he⟩ := Complex.exists_continuousOn_eqOn_exp_comp hc hU
    hf.continuousOn hn
  have he' : ∀ z ∈ U, Complex.exp (ℓ z) = f z := by
    intro z hz
    exact he hz
  exact ⟨ℓ, analyticOnNhd_of_continuousComplexLogLift32 hU hf hf0 hl he', he'⟩

end NlsGge.SpectralFoundations
end
