import Mathlib
import NlsGge.Atomic.G5.G5019Sup1
import NlsGge.Atomic.G5.G5019Sup2
import NlsGge.Atomic.G5.G5019Sup3
import NlsGge.Atomic.G5.G5001Host
import NlsGge.Atomic.G5.G5024
import NlsGge.Atomic.G5.G5018Host
import NlsGge.GK38.TauGamma

/- G5-019 SUPPORT 5 `G5019Sup5` (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G5/G5019Sup5.lean, namespace NlsGge.GKDefinitionDesign.G5019Sup5.
   `core`: the continuity-extension argument of G5-019, with the three landed inputs taken as explicit parameters so that the
   argument is checkable in the worker lane without the G1/G5018 closure:
     (h18)    the G5018 identity at every w with interior m-th Dirichlet gap and gamma2 n ≠ 0   [instantiated by landed G5018];
     (hdense) density of {w | InteriorRealDirichletGap m w}                                      [instantiated by G5019Sup4];
     (hAID)   continuity at u of w ↦ angleIntegralDerivative m n (realSlice w)                   [instantiated by Sup3 + landed lift].
   The conclusion is the G5019 head. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38
open NlsGge.GKDefinitionDesign

namespace NlsGge.GKDefinitionDesign
namespace G5019Sup5
noncomputable section

theorem core (u : PhysicalL2) (m n : ℤ) (lam : ℂ)
    (hn : gamma2 (realSlice u) n ≠ 0)
    (h18 : ∀ w : PhysicalL2, InteriorRealDirichletGap m w → gamma2 (realSlice w) n ≠ 0 →
      2 * pairPoissonCLM (fderiv ℂ (fun φ => discrim φ lam) (realSlice w))
        (angleIntegralDerivative m n (realSlice w)) =
        psiAt n (muSeq (realSlice w) m) (realSlice w) *
          PoissonMixed38.dirInterpolation38 (realSlice w) (muSeq (realSlice w) m) lam)
    (hdense : Dense {w : PhysicalL2 | InteriorRealDirichletGap m w})
    (hAID : ContinuousAt (fun w : PhysicalL2 => angleIntegralDerivative m n (realSlice w)) u) :
  2 * pairPoissonCLM (fderiv ℂ (fun φ => discrim φ lam) (realSlice u))
    (angleIntegralDerivative m n (realSlice u)) =
    psiAt n (muSeq (realSlice u) m) (realSlice u) *
      PoissonMixed38.dirInterpolation38 (realSlice u) (muSeq (realSlice u) m) lam := by
  let Φ : PhysicalL2 → ℂ := fun w =>
    2 * pairPoissonCLM (fderiv ℂ (fun φ => discrim φ lam) (realSlice w))
      (angleIntegralDerivative m n (realSlice w)) -
    psiAt n (muSeq (realSlice w) m) (realSlice w) *
      PoissonMixed38.dirInterpolation38 (realSlice w) (muSeq (realSlice w) m) lam
  have hdisc : Continuous (fun w : PhysicalL2 => fderiv ℂ (fun φ : PotPair => discrim φ lam) (realSlice w)) :=
    (continuousOn_univ.mp (analyticOnNhd_discrim_phi lam).fderiv.continuousOn).comp
      realSlice.continuous
  have hPP : ContinuousAt (fun w : PhysicalL2 =>
      pairPoissonCLM (fderiv ℂ (fun φ => discrim φ lam) (realSlice w))
        (angleIntegralDerivative m n (realSlice w))) u :=
    (G5019Sup3.continuous_pairPoissonCLM.continuousAt).comp (f := fun w : PhysicalL2 =>
      (fderiv ℂ (fun φ : PotPair => discrim φ lam) (realSlice w), angleIntegralDerivative m n (realSlice w)))
      (hdisc.continuousAt.prodMk hAID)
  have hpsi : Continuous (fun w : PhysicalL2 =>
      psiAt n (muSeq (realSlice w) m) (realSlice w)) :=
    G5019Sup2.continuous_comp_realSlice_muSeq m sourceW (fun p : PotPair × ℂ => psiAt n p.2 p.1)
      (p6PsiNumerator_joint_analytic38 n sourceW (sourceF n) (sourceFamily.F_analytic n)).continuousOn
      (fun w => sourceFamily.W_real (Set.mem_range_self w))
  have hdir := G5019Sup2.continuous_dirInterpolation_mu m lam
  have hΦ : ContinuousAt Φ u :=
    (continuousAt_const.mul hPP).sub (hpsi.mul hdir).continuousAt
  have hg : ContinuousAt (fun w : PhysicalL2 => gamma2 (realSlice w) n) u :=
    ((gamma2_analytic n).continuousOn.continuousAt
      (isOpen_gkW.mem_nhds (realSlice_mem_gkW u))).comp realSlice.continuous.continuousAt
  have hzero : ∀ w : PhysicalL2, InteriorRealDirichletGap m w → gamma2 (realSlice w) n ≠ 0 →
      Φ w = 0 := fun w hw hgw => sub_eq_zero.mpr (h18 w hw hgw)
  have hΦu : Φ u = 0 := by
    by_contra hne
    have h1 : ∀ᶠ w in 𝓝 u, Φ w ≠ 0 := hΦ.eventually_ne hne
    have h2 : ∀ᶠ w in 𝓝 u, gamma2 (realSlice w) n ≠ 0 := hg.eventually_ne hn
    obtain ⟨U, hUsub, hUo, huU⟩ := mem_nhds_iff.mp (h1.and h2)
    obtain ⟨w, hwU, hwD⟩ := hdense.inter_open_nonempty U hUo ⟨u, huU⟩
    exact (hUsub hwU).1 (hzero w hwD (hUsub hwU).2)
  exact sub_eq_zero.mp hΦu

end
end G5019Sup5
end NlsGge.GKDefinitionDesign
