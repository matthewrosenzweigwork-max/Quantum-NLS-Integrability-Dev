import Mathlib
import NlsGge.Atomic.G1.G1082Sup1
import NlsGge.Atomic.G1.G1081Sup6
import NlsGge.GK38.DirichletRealAnalytic
import NlsGge.GK38.DirichletRealBridge
import NlsGge.GK38.GradFundamentalCompact
import NlsGge.GK38.PairRealBridgeProbe

/- G1-082 Sup2 PRODUCTION01 (proof development, AUTHOR; not reviewed). Target NlsGge/Atomic/G1/G1082Sup2.lean.
   CONDITIONAL support for conjunct 3 of G1-082 (second derivative of the moving Dirichlet point).
   Hypothesis `hW : ∃ w, deltaMu w n ≠ 0` (a potential whose n-th Dirichlet point is not a periodic endpoint) is an explicit
   binder and is NOT proved here (see G1082_STOP.md); every other step is proved.
   Route: a(v)^2 = (Re Delta_v(mu))^2 - 4 along the isospectral flow gives a(v)(G(v)-H(v)) = 0 pointwise (G = d a(X), H the head
   expression); G,H continuous and a real-analytic on connected PhysicalL2, so the identity theorem (a not identically 0) gives G = H. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GKDefinitionDesign

namespace NlsGge.Atomic.G1082Sup2
noncomputable section

/-- Head expression for the second derivative, as a function of the potential. -/
def Hfun (n : ℤ) (v : PhysicalL2) : ℝ :=
  -(discrim (realSlice v) (gkMu v n : ℂ) * deriv (discrim (realSlice v)) (gkMu v n : ℂ)).re / 2

/-- Derivative of the antidiscriminant at the Dirichlet point along the single-gap field. -/
def Gfun (n : ℤ) (v : PhysicalL2) : ℝ :=
  fderiv ℝ (fun w : PhysicalL2 => deltaMu w n) v (singleGapField n v)

theorem continuous_Hfun (n : ℤ) : Continuous (Hfun n) := by
  have hmu : Continuous (fun v : PhysicalL2 => gkMu v n) :=
    continuousOn_univ.mp (analyticOnNhd_gkMu38 n).continuousOn
  have h1 : Continuous (fun v : PhysicalL2 => (realSlice v, (gkMu v n : ℂ))) :=
    realSlice.continuous.prodMk
      (Complex.continuous_ofReal.comp hmu)
  have h2 : Continuous (fun v : PhysicalL2 => discrim (realSlice v) (gkMu v n : ℂ)) :=
    Continuous.comp (g := fun p : PhysicalL2 × ℂ => discrim (realSlice p.1) p.2)
      (f := fun v : PhysicalL2 => (v, (gkMu v n : ℂ))) continuous_discrim_realSlice_joint
      (continuous_id.prodMk (Complex.continuous_ofReal.comp hmu))
  have h3 : Continuous (fun v : PhysicalL2 => deriv (discrim (realSlice v)) (gkMu v n : ℂ)) :=
    Continuous.comp (g := fun p : PotPair × ℂ => deriv (discrim p.1) p.2)
      (f := fun v : PhysicalL2 => (realSlice v, (gkMu v n : ℂ)))
      (continuousOn_univ.mp analyticOnNhd_discrimDeriv_joint38.continuousOn) h1
  unfold Hfun
  exact ((Complex.continuous_re.comp (h2.mul h3)).neg).div_const 2

theorem continuous_Gfun (n : ℤ) : Continuous (Gfun n) := by
  have hf : Continuous (fderiv ℝ (fun w : PhysicalL2 => deltaMu w n)) :=
    continuousOn_univ.mp (analyticOnNhd_deltaMu38 n).fderiv.continuousOn
  have hs : Continuous (singleGapField n) :=
    continuousOn_univ.mp (NlsGge.Atomic.G1081Sup1.analyticOnNhd_singleGapField n).continuousOn
  exact hf.clm_apply hs

theorem hasDerivAt_deltaMu_flow (n : ℤ) (v : PhysicalL2) (t : ℝ) :
    HasDerivAt (fun s : ℝ => deltaMu (singleGapFlow n s v) n) (Gfun n (singleGapFlow n t v)) t := by
  have hF := NlsGge.Atomic.G1081Sup5.singleGapFlow_hasDerivAt n v t
  have hm := ((analyticOnNhd_deltaMu38 n) (singleGapFlow n t v) (mem_univ _)).differentiableAt.hasFDerivAt
  exact hm.comp_hasDerivAt t hF

theorem mul_Gfun_sub_Hfun (n : ℤ) (v : PhysicalL2) :
    deltaMu v n * (Gfun n v - Hfun n v) = 0 := by
  set F : ℝ → PhysicalL2 := fun s => singleGapFlow n s v with hFdef
  have hF0 : F 0 = v := NlsGge.Atomic.G1081Sup5.singleGapFlow_zero n v
  have hA : HasDerivAt (fun s : ℝ => deltaMu (F s) n) (Gfun n v) 0 := by
    have := hasDerivAt_deltaMu_flow n v 0
    rwa [NlsGge.Atomic.G1081Sup5.singleGapFlow_zero] at this
  have hA2 : HasDerivAt (fun s : ℝ => deltaMu (F s) n * deltaMu (F s) n)
      (Gfun n v * deltaMu (F 0) n + deltaMu (F 0) n * Gfun n v) 0 := hA.mul hA
  have hg : HasDerivAt (fun s : ℝ => gkMu (F s) n) (-deltaMu v n / 2) 0 := by
    have := NlsGge.Atomic.G1082Sup1.hasDerivAt_gkMu_flow n n v 0
    rw [if_pos rfl, NlsGge.Atomic.G1081Sup5.singleGapFlow_zero] at this
    exact this
  have hD : HasDerivAt (fun x : ℝ => (discrim (realSlice v) (x : ℂ)).re)
      (deriv (discrim (realSlice v)) (gkMu v n : ℂ)).re (gkMu v n) :=
    HasDerivAt.real_of_complex
      ((analyticOnNhd_discrim_z (realSlice v) (gkMu v n : ℂ) (mem_univ _)).differentiableAt.hasDerivAt)
  have hc : HasDerivAt (fun s : ℝ => (discrim (realSlice v) (gkMu (F s) n : ℂ)).re)
      ((deriv (discrim (realSlice v)) (gkMu v n : ℂ)).re * (-deltaMu v n / 2)) 0 :=
    hD.comp_of_eq 0 hg (by rw [hF0])
  have hD' : HasDerivAt (fun s : ℝ => (discrim (realSlice v) (gkMu (F s) n : ℂ)).re *
      (discrim (realSlice v) (gkMu (F s) n : ℂ)).re - 4)
      (((deriv (discrim (realSlice v)) (gkMu v n : ℂ)).re * (-deltaMu v n / 2)) *
        (discrim (realSlice v) (gkMu (F 0) n : ℂ)).re +
      (discrim (realSlice v) (gkMu (F 0) n : ℂ)).re *
        ((deriv (discrim (realSlice v)) (gkMu v n : ℂ)).re * (-deltaMu v n / 2))) 0 :=
    (hc.mul hc).sub_const 4
  have heq : (fun s : ℝ => deltaMu (F s) n * deltaMu (F s) n) =
      fun s : ℝ => ((discrim (realSlice v) (gkMu (F s) n : ℂ)).re) * ((discrim (realSlice v) (gkMu (F s) n : ℂ)).re) - 4 := by
    funext s
    have h := deltaMu_squared38 (F s) n
    have hi : ∀ z : ℂ, discrim (realSlice (F s)) z = discrim (realSlice v) z :=
      NlsGge.Atomic.G1081Sup6.singleGapFlow_isospectral n s v
    rw [hi] at h
    nlinarith [h]
  have hu := hA2.unique (by
    rw [heq]
    exact hD')
  have him := (dirichlet_real_characteristic38 v (gkMu v n)).2.2
  have hre : (discrim (realSlice v) (gkMu v n : ℂ) * deriv (discrim (realSlice v)) (gkMu v n : ℂ)).re =
      (discrim (realSlice v) (gkMu v n : ℂ)).re * (deriv (discrim (realSlice v)) (gkMu v n : ℂ)).re := by
    rw [Complex.mul_re, him, zero_mul, sub_zero]
  unfold Hfun
  rw [hre]
  simp only [hF0] at hu
  nlinarith [hu]

theorem Gfun_eq_Hfun (n : ℤ) (hW : ∃ w : PhysicalL2, deltaMu w n ≠ 0) (v : PhysicalL2) :
    Gfun n v = Hfun n v := by
  by_contra hne
  have hopen : IsOpen {w : PhysicalL2 | Gfun n w - Hfun n w ≠ 0} :=
    isOpen_ne_fun ((continuous_Gfun n).sub (continuous_Hfun n)) continuous_const
  have hev : (fun w : PhysicalL2 => deltaMu w n) =ᶠ[𝓝 v] 0 := by
    filter_upwards [hopen.mem_nhds (sub_ne_zero.mpr hne)] with w hw
    exact (mul_eq_zero.mp (mul_Gfun_sub_Hfun n w)).resolve_right hw
  have hz := (analyticOnNhd_deltaMu38 n).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (mem_univ v) hev
  obtain ⟨w, hw⟩ := hW
  exact hw (hz (mem_univ w))

/-- Conjunct 3 (first part) of G1-082, conditional on the witness `hW`. -/
theorem hasDerivAt_deriv_gkMu_flow (n : ℤ) (hW : ∃ w : PhysicalL2, deltaMu w n ≠ 0)
    (u : PhysicalL2) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => deriv (fun r : ℝ => gkMu (singleGapFlow n r u) n) s)
      ((discrim (realSlice u) (gkMu (singleGapFlow n t u) n : ℂ) *
        deriv (discrim (realSlice u)) (gkMu (singleGapFlow n t u) n : ℂ)).re / 4) t := by
  have hfun : (fun s : ℝ => deriv (fun r : ℝ => gkMu (singleGapFlow n r u) n) s) =
      fun s : ℝ => -(deltaMu (singleGapFlow n s u) n) / 2 := by
    funext s
    exact NlsGge.Atomic.G1082Sup1.deriv_gkMu_flow_self n u s
  rw [hfun]
  have h := (hasDerivAt_deltaMu_flow n u t).neg.div_const 2
  have hGH := Gfun_eq_Hfun n hW (singleGapFlow n t u)
  have hi : discrim (realSlice (singleGapFlow n t u)) = discrim (realSlice u) :=
    funext (NlsGge.Atomic.G1081Sup6.singleGapFlow_isospectral n t u)
  unfold Hfun at hGH
  rw [hi] at hGH
  convert h using 1
  rw [hGH]; ring

end
end NlsGge.Atomic.G1082Sup2
