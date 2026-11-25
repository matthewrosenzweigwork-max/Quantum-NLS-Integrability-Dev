import Mathlib
import NlsGge.Atomic.G5.G5031Host
import NlsGge.Atomic.G5.G5031Sup3
import NlsGge.ThirdConsultation.KO.Basic

/- G5-038 SUPPORT 1 `G5038Sup1` (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G5/G5038Sup1.lean, namespace NlsGge.GKDefinitionDesign.G5038Sup1.
   GK 18.7 (last step): {theta_m,theta_n} is continuous along the real slice at every point with open m-, n-gaps (it locally equals the
   constant-tensor bracket of two analytic primitives, G5031Sup3), the open-gap locus is open (G5031Sup3.eventually_gamma2_ne), and the
   bracket vanishes on finite-gap potentials (G5-037, parameter h37).  Hence it vanishes at every limit of finite-gap potentials.
   Parameters: (hprim) G5035Sup2.angle_local_primitive; (hdense) an L2 sequence of canonical finite-gap potentials converging to u
   (NOT landed in this form: see G5038_STOP.md; source DM-065 at Sobolev level 0); (h37) the G5037 head. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.Atomic.LIB

namespace NlsGge.GKDefinitionDesign
namespace G5038Sup1
noncomputable section

theorem continuousAt_anglePoisson_realSlice (u : PhysicalL2) (m n : ℤ)
    (hm : gamma2 (realSlice u) m ≠ 0) (hn : gamma2 (realSlice u) n ≠ 0)
    (hprim : ∀ (w : PhysicalL2) (j : ℤ), gamma2 (realSlice w) j ≠ 0 →
      ∃ (V : Set PotPair) (θ : PotPair → ℂ), IsOpen V ∧ realSlice w ∈ V ∧
        AnalyticOnNhd ℂ θ V ∧ ∀ ψ ∈ V, fderiv ℂ θ ψ = angleDerivative j ψ) :
    ContinuousAt (fun v : PhysicalL2 => anglePoisson m n (realSlice v)) u := by
  obtain ⟨Vm, θm, hVm, hxm, hanm, hdm⟩ := hprim u m hm
  obtain ⟨Vn, θn, hVn, hxn, hann, hdn⟩ := hprim u n hn
  have hcm : ContDiffAt ℂ 2 θm (realSlice u) := (hanm _ hxm).contDiffAt
  have hcn : ContDiffAt ℂ 2 θn (realSlice u) := (hann _ hxn).contDiffAt
  have hVo : IsOpen (Vm ∩ Vn) := hVm.inter hVn
  have hxV : realSlice u ∈ Vm ∩ Vn := ⟨hxm, hxn⟩
  have hPeq : anglePoisson m n =ᶠ[𝓝 (realSlice u)] constantPoisson G5031Sup3.Jmap θm θn := by
    filter_upwards [hVo.mem_nhds hxV] with ψ hψ
    simp only [anglePoisson, constantPoisson_apply, hdm ψ hψ.1, hdn ψ hψ.2]
    rfl
  have hd : DifferentiableAt ℂ (anglePoisson m n) (realSlice u) :=
    (G5031Sup3.differentiableAt_constantPoisson hcm hcn).congr_of_eventuallyEq hPeq
  exact hd.continuousAt.comp realSlice.continuous.continuousAt

theorem core38 (u : PhysicalL2) (m n : ℤ)
    (hm : gamma2 (realSlice u) m ≠ 0) (hn : gamma2 (realSlice u) n ≠ 0)
    (hprim : ∀ (w : PhysicalL2) (j : ℤ), gamma2 (realSlice w) j ≠ 0 →
      ∃ (V : Set PotPair) (θ : PotPair → ℂ), IsOpen V ∧ realSlice w ∈ V ∧
        AnalyticOnNhd ℂ θ V ∧ ∀ ψ ∈ V, fderiv ℂ θ ψ = angleDerivative j ψ)
    (hdense : ∃ v : ℕ → PhysicalL2, Tendsto v atTop (𝓝 u) ∧
      ∀ j : ℕ, NlsGge.ThirdConsultation.finiteGap (v j))
    (h37 : ∀ (u : PhysicalL2) (m n : ℤ), NlsGge.ThirdConsultation.finiteGap u →
      gamma2 (realSlice u) m ≠ 0 → gamma2 (realSlice u) n ≠ 0 →
      anglePoisson m n (realSlice u) = 0) :
    anglePoisson m n (realSlice u) = 0 := by
  obtain ⟨v, hv, hfg⟩ := hdense
  have hlim : Tendsto (fun j => anglePoisson m n (realSlice (v j))) atTop
      (𝓝 (anglePoisson m n (realSlice u))) :=
    (continuousAt_anglePoisson_realSlice u m n hm hn hprim).tendsto.comp hv
  have hz : (fun j => anglePoisson m n (realSlice (v j))) =ᶠ[atTop] fun _ => (0 : ℂ) := by
    filter_upwards [hv.eventually (G5031Sup3.eventually_gamma2_ne u m hm),
      hv.eventually (G5031Sup3.eventually_gamma2_ne u n hn)] with j h2 h3
    exact h37 (v j) m n (hfg j) h2 h3
  exact tendsto_nhds_unique (hlim.congr' hz) tendsto_const_nhds

end
end G5038Sup1
end NlsGge.GKDefinitionDesign
