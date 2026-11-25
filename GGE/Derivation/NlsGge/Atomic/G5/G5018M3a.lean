import Mathlib
import NlsGge.GK38.AbelianHilbert
import NlsGge.GK38.AbelianPeriods
import NlsGge.GK38.Lib.ParamCircleAnalytic
import NlsGge.GK38.StdRootBranchesProducts
import NlsGge.GK38.IsolatingTopology
import NlsGge.GK38.ContourAction
import NlsGge.GK38.PairRealBridge

/- G5-018 M3'a (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G5/G5018M3a.lean,
   namespace NlsGge.GKDefinitionDesign.  Head `g5018_fixedNumerator_period_fderiv_eq_zero` VERBATIM from Pro round 13 section 6 (M3'a).
   Route as Pro: replace discC/discR by a local fixed isolating family (abelianPeriod_fullfamily_realization38), differentiate the
   fixed-contour integral (paramCircle_integral_hasFDerivAt38), root derivative zero from canonRoot^2 = Delta^2 - 4 and hΔ,
   then coordinates via lp.evalCLM and p2Fn_apply38. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
namespace G5018M3aAux
noncomputable section

theorem canonRoot_fderiv_zero (φ v : PotPair) (hφ : φ ∈ gkW) (z : ℂ)
    (hz : z ∉ gapSegments38 φ)
    (hΔ : fderiv ℂ (fun ψ : PotPair => discrim ψ z) φ v = 0) :
    fderiv ℂ (fun ψ : PotPair => canonRoot38 ψ z) φ v = 0 := by
  have hdom : (φ, z) ∈ rootDomain38 := ⟨hφ, hz⟩
  have hA : AnalyticAt ℂ (fun ψ : PotPair => canonRoot38 ψ z) φ :=
    AnalyticAt.comp (g := fun p : PotPair × ℂ => canonRoot38 p.1 p.2)
      (f := fun ψ : PotPair => (ψ, z))
      (canonRoot_analytic38 (φ, z) hdom) (analyticAt_id.prod analyticAt_const)
  have hD : AnalyticAt ℂ (fun ψ : PotPair => discrim ψ z) φ :=
    analyticOnNhd_discrim_phi z φ (mem_univ _)
  have hev : (fun ψ : PotPair => canonRoot38 ψ z * canonRoot38 ψ z) =ᶠ[𝓝 φ]
      fun ψ => discrim ψ z * discrim ψ z - 4 := by
    have hopen : ∀ᶠ ψ in 𝓝 φ, (ψ, z) ∈ rootDomain38 :=
      (isOpen_rootDomain38.preimage (continuous_id.prodMk continuous_const)).mem_nhds hdom
    filter_upwards [hopen] with ψ hψ
    have h := canonRoot_sq38 ψ hψ.1 z hψ.2
    have h2 : perChar ψ z = discrim ψ z ^ 2 - 4 := rfl
    rw [← pow_two, h, h2]; ring
  have h1 := hA.differentiableAt.hasFDerivAt.mul hA.differentiableAt.hasFDerivAt
  have h2 := (hD.differentiableAt.hasFDerivAt.mul hD.differentiableAt.hasFDerivAt).sub_const 4
  have h3 := (hev.hasFDerivAt_iff).mp h1
  have h4 := h3.unique h2
  have h5 := congrArg (fun L : PotPair →L[ℂ] ℂ => L v) h4
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hΔ,
    mul_zero, add_zero] at h5
  have hne : canonRoot38 φ z ≠ 0 := canonRoot_ne_zero38 φ hφ z hz
  have h6 : canonRoot38 φ z * fderiv ℂ (fun ψ : PotPair => canonRoot38 ψ z) φ v = 0 := by
    linear_combination (1 / 2 : ℂ) * h5
  exact (mul_eq_zero.mp h6).resolve_left hne

theorem coord_fderiv_zero (n : ℤ) (s : P2Space38 n) (m : P2Index38 n) (φ v : PotPair)
    (hφ : φ ∈ gkW)
    (hΔ : ∀ z : ℂ, fderiv ℂ (fun ψ : PotPair => discrim ψ z) φ v = 0) :
    fderiv ℂ (fun ψ : PotPair => p2FnCoord38 n (ψ, s) m) φ v = 0 := by
  obtain ⟨V, hV, hVW, hVo, _hVc, C, R, c, N, hgeom, hspec⟩ := local_isolatingFamily_common38 φ hφ
  have hf : ∀ ψ ∈ V, IsolatingFamily38 ψ C R := fun ψ hψ => ⟨c, N, hgeom, hspec ψ hψ⟩
  have hφV : φ ∈ V := mem_of_mem_nhds hV
  let s' : Lib.L2Seq := p2Extend38 n s
  let F : PotPair → ℂ → ℂ := fun ψ z => p2FullNumerator38 n s' z / canonRoot38 ψ z
  have hjoint : AnalyticOnNhd ℂ (Function.uncurry F) (V ×ˢ sphere (C m.1) (R m.1)) := by
    intro q hq
    have hmem : ((q.1, s'), q.2) ∈
        {p : (PotPair × Lib.L2Seq) × ℂ | (p.1.1, p.2) ∈ rootDomain38} :=
      ⟨hVW hq.1, fixed_sphere_subset q.1 C R (hf q.1 hq.1) m.1 hq.2⟩
    exact AnalyticAt.comp
      (g := fun p : (PotPair × Lib.L2Seq) × ℂ => p2FullNumerator38 n p.1.2 p.2 / canonRoot38 p.1.1 p.2)
      (f := fun q : PotPair × ℂ => ((q.1, s'), q.2))
      (p2Quotient_joint_analytic38 n _ hmem)
      ((analyticAt_fst.prod analyticAt_const).prod analyticAt_snd)
  have hr : 0 < R m.1 := isolating_radius_pos38 (hf φ hφV) m.1
  have hD := Lib.paramCircle_integral_hasFDerivAt38 hVo hr hjoint hφV
  have hL : (∫ t in Icc 0 (2 * Real.pi), deriv (circleMap (C m.1) (R m.1)) t •
      Lib.paramCircleDerivative38 F φ (circleMap (C m.1) (R m.1) t)) v = 0 := by
    have hz0 : ∀ t, Lib.paramCircleDerivative38 F φ (circleMap (C m.1) (R m.1) t) v = 0 := by
      intro t
      have hz : circleMap (C m.1) (R m.1) t ∈ sphere (C m.1) (R m.1) :=
        circleMap_mem_sphere _ hr.le t
      have hAn : AnalyticAt ℂ (Function.uncurry F) (φ, circleMap (C m.1) (R m.1) t) :=
        hjoint _ ⟨hφV, hz⟩
      have hzF : circleMap (C m.1) (R m.1) t ∉ gapSegments38 φ :=
        fixed_sphere_subset φ C R (hf φ hφV) m.1 hz
      rw [← (Lib.paramCircle_hasFDerivAt38 hAn).fderiv]
      set z := circleMap (C m.1) (R m.1) t with hzdef
      have hne := canonRoot_ne_zero38 φ hφ z hzF
      have hA : AnalyticAt ℂ (fun ψ : PotPair => canonRoot38 ψ z) φ :=
        AnalyticAt.comp (g := fun p : PotPair × ℂ => canonRoot38 p.1 p.2)
          (f := fun ψ : PotPair => (ψ, z))
          (canonRoot_analytic38 (φ, z) ⟨hφ, hzF⟩) (analyticAt_id.prod analyticAt_const)
      have hDv := canonRoot_fderiv_zero φ v hφ z hzF (hΔ z)
      have h1 := ((hasDerivAt_inv hne).comp_hasFDerivAt φ hA.differentiableAt.hasFDerivAt).const_mul
        (p2FullNumerator38 n s' z)
      have e : (fun ψ : PotPair => F ψ z) =
          fun ψ => p2FullNumerator38 n s' z * (canonRoot38 ψ z)⁻¹ :=
        funext fun ψ => div_eq_mul_inv _ _
      have h1' : HasFDerivAt (fun ψ : PotPair => p2FullNumerator38 n s' z * (canonRoot38 ψ z)⁻¹) _ φ := h1
      rw [e, h1'.fderiv]
      simp [hDv]
    by_cases hI : Integrable (fun t => deriv (circleMap (C m.1) (R m.1)) t •
        Lib.paramCircleDerivative38 F φ (circleMap (C m.1) (R m.1) t)) (volume.restrict (Icc 0 (2 * Real.pi)))
    · rw [ContinuousLinearMap.integral_apply hI]
      simp [hz0]
    · rw [integral_undef hI]; rfl
  have hEq : (fun ψ : PotPair => p2FnCoord38 n (ψ, s) m) =ᶠ[𝓝 φ]
      fun ψ => (((n - m.1 : ℤ) : ℂ)) * circleIntegral (F ψ) (C m.1) (R m.1) := by
    filter_upwards [hV] with ψ hψ
    have hψW := hVW hψ
    have he := abelianPeriod_fullfamily_realization38 ψ hψW (discC ψ) C (discR ψ) R
      (isolating_family38 ψ hψW) (hf ψ hψ) m.1 (p2FullNumerator38 n s')
      (p2FullNumerator_entire38 n s')
    exact congrArg (fun a : ℂ => (((n - m.1 : ℤ) : ℂ)) * a) he.2.2
  rw [hEq.fderiv_eq, (hD.const_mul (((n - m.1 : ℤ) : ℂ))).fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, hL, mul_zero]

end
end G5018M3aAux

noncomputable section

theorem g5018_fixedNumerator_period_fderiv_eq_zero
    (n : ℤ) (s : P2Space38 n) (φ v : PotPair)
    (hφ : φ ∈ gkW)
    (hΔ : ∀ z : ℂ,
      fderiv ℂ (fun ψ : PotPair => discrim ψ z) φ v = 0) :
    fderiv ℂ (fun ψ : PotPair => p2Fn38 n (ψ, s)) φ v = 0 := by
  have hdiff : DifferentiableAt ℂ (fun ψ : PotPair => p2Fn38 n (ψ, s)) φ :=
    (AnalyticAt.comp (g := p2Fn38 n) (f := fun ψ : PotPair => (ψ, s))
      (p2Fn_analytic38 n (φ, s) ⟨hφ, mem_univ _⟩)
      (analyticAt_id.prod analyticAt_const)).differentiableAt
  refine lp.ext (funext fun m => ?_)
  have h1 : HasFDerivAt (fun ψ : PotPair => p2Fn38 n (ψ, s) m)
      ((lp.evalCLM ℂ (fun _ : P2Index38 n => ℂ) 2 m).comp
        (fderiv ℂ (fun ψ : PotPair => p2Fn38 n (ψ, s)) φ)) φ :=
    (lp.evalCLM ℂ (fun _ : P2Index38 n => ℂ) 2 m).hasFDerivAt.comp φ hdiff.hasFDerivAt
  have h2 : (fun ψ : PotPair => p2Fn38 n (ψ, s) m) =ᶠ[𝓝 φ]
      fun ψ : PotPair => p2FnCoord38 n (ψ, s) m := by
    filter_upwards [isOpen_gkW.mem_nhds hφ] with ψ hψ
    exact p2Fn_apply38 n (ψ, s) hψ m
  have h3 := (h2.hasFDerivAt_iff).mp h1
  have h4 := G5018M3aAux.coord_fderiv_zero n s m φ v hφ hΔ
  rw [h3.fderiv] at h4
  exact h4

end
end NlsGge.GKDefinitionDesign
