import Mathlib
import NlsGge.ThirdConsultation.M.M023Host
import NlsGge.ThirdConsultation.M.M023Bridge
import NlsGge.ThirdConsultation.M.M023Kernel1
import NlsGge.ThirdConsultation.M.M023Kernel2
import NlsGge.ThirdConsultation.M.M023Kernel3
import NlsGge.ThirdConsultation.M.M023Tw

   
                                                                  

                                                                                                      
                                                                                                                      
                                                                                                                    
                                                                           
  

set_option autoImplicit false

open scoped ENNReal BigOperators BoundedContinuousFunction Topology

namespace NlsGge.ThirdConsultation.MTwoMode.WeightedInverse
noncomputable section

open NlsGge.ThirdConsultation.MTwoMode

/-- The strip coefficient sequence as an element of the bounded-sequence algebra. -/
def c0n (n : ℤ) (lam : ℂ) (h : lam ∈ NlsGge.Atomic.KST004.spectralStrip n) : ℤ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun l => NlsGge.Atomic.KST004.complementaryResolventCoeff n lam l) 1
    (fun l => (NlsGge.ThirdConsultation.MTwoMode.Comp21.D_facts n lam h).1 l)

theorem gC_expand (n : ℤ) (lam0 : ℂ) (h0 : lam0 ∈ NlsGge.Atomic.KST004.spectralStrip n) (lam : ℂ)
    (hl : ‖lam - lam0‖ < 1) :
    gC n lam = gC n lam0 * Ring.inverse (1 + (lam - lam0) • c0n n lam0 h0) := by
  have hreg0 := strip_mem_region n lam0 h0
  have hreg : |lam.re - (n : ℝ) * Real.pi| ≤ Real.pi / 2 + 1 := by
    have h1 : |lam.re - lam0.re| ≤ ‖lam - lam0‖ := by
      have := Complex.abs_re_le_norm (lam - lam0)
      simpa using this
    have h2 : |lam0.re - (n : ℝ) * Real.pi| ≤ Real.pi / 2 := h0
    calc |lam.re - (n : ℝ) * Real.pi|
        = |(lam.re - lam0.re) + (lam0.re - (n : ℝ) * Real.pi)| := by ring_nf
      _ ≤ |lam.re - lam0.re| + |lam0.re - (n : ℝ) * Real.pi| := abs_add_le _ _
      _ ≤ Real.pi / 2 + 1 := by linarith
  have hc : ∀ l : ℤ, ‖NlsGge.Atomic.KST004.complementaryResolventCoeff n lam0 l‖ ≤ 1 :=
    fun l => (NlsGge.ThirdConsultation.MTwoMode.Comp21.D_facts n lam0 h0).1 l
  set δ : ℝ := ‖lam - lam0‖ with hδ
  set u : ℤ →ᵇ ℂ := 1 + (lam - lam0) • c0n n lam0 h0 with hu
  have hul : ∀ l : ℤ, u l =
      1 + (lam - lam0) * NlsGge.Atomic.KST004.complementaryResolventCoeff n lam0 l := by
    intro l
    simp [hu, c0n]
  have hulb : ∀ l : ℤ, 1 - δ ≤ ‖u l‖ := by
    intro l
    rw [hul l]
    have h1 : ‖(lam - lam0) * NlsGge.Atomic.KST004.complementaryResolventCoeff n lam0 l‖ ≤ δ := by
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hc l)
    have h2 := norm_sub_norm_le (1 : ℂ)
      (-((lam - lam0) * NlsGge.Atomic.KST004.complementaryResolventCoeff n lam0 l))
    rw [sub_neg_eq_add, norm_one, norm_neg] at h2
    linarith
  have hpos : 0 < 1 - δ := by linarith
  have hune : ∀ l : ℤ, u l ≠ 0 := by
    intro l h
    have := hulb l
    rw [h, norm_zero] at this
    linarith
  let v : ℤ →ᵇ ℂ := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun l => (u l)⁻¹) (1 - δ)⁻¹ (fun l => by
      rw [norm_inv]
      exact inv_anti₀ hpos (hulb l))
  have hvl : ∀ l : ℤ, v l = (u l)⁻¹ := fun l => rfl
  have huv : u * v = 1 := by
    ext l
    rw [BoundedContinuousFunction.coe_mul, Pi.mul_apply, hvl, mul_inv_cancel₀ (hune l)]
    rfl
  have hvu : v * u = 1 := by
    ext l
    rw [BoundedContinuousFunction.coe_mul, Pi.mul_apply, hvl, inv_mul_cancel₀ (hune l)]
    rfl
  have hinv : Ring.inverse u = v := Ring.inverse_unit (⟨u, v, huv, hvu⟩ : (ℤ →ᵇ ℂ)ˣ)
  rw [hinv]
  ext l
  rw [BoundedContinuousFunction.coe_mul, Pi.mul_apply, gC_apply n lam hreg, gC_apply n lam0 hreg0, hvl]
  by_cases hln : l = n
  · simp [gFun, NlsGge.Atomic.KST004.complementaryResolventCoeff, hln]
  · have hA : lam0 - (l : ℂ) * (Real.pi : ℂ) ≠ 0 :=
      NlsGge.Atomic.KST004.complementary_denominator_ne_zero n l lam0 h0 hln
    have hu2 := hune l
    rw [hul l] at hu2 ⊢
    simp only [gFun, NlsGge.Atomic.KST004.complementaryResolventCoeff, if_neg hln] at hu2 ⊢
    have e : 1 + (lam - lam0) * (lam0 - (l : ℂ) * (Real.pi : ℂ))⁻¹ =
        (lam - (l : ℂ) * (Real.pi : ℂ)) * (lam0 - (l : ℂ) * (Real.pi : ℂ))⁻¹ := by
      field_simp
      ring
    rw [e] at hu2 ⊢
    have hB : lam - (l : ℂ) * (Real.pi : ℂ) ≠ 0 := left_ne_zero_of_mul hu2
    field_simp

local instance : Nontrivial (ℤ →ᵇ ℂ) :=
  ⟨⟨0, 1, fun h => by
    have := congrArg (fun f : ℤ →ᵇ ℂ => f 0) h
    simp at this⟩⟩

theorem analyticAt_gC (n : ℤ) (lam0 : ℂ) (h0 : lam0 ∈ NlsGge.Atomic.KST004.spectralStrip n) :
    AnalyticAt ℂ (gC n) lam0 := by
  have hsm : AnalyticAt ℂ (fun h : ℂ => h • c0n n lam0 h0) 0 :=
    analyticAt_id.smul analyticAt_const
  have hF : AnalyticAt ℂ (fun h : ℂ => Ring.inverse (1 + h • c0n n lam0 h0)) 0 := by
    have h1 : AnalyticAt ℂ (fun x : ℤ →ᵇ ℂ => Ring.inverse (1 + x))
        ((fun h : ℂ => h • c0n n lam0 h0) 0) := by
      show AnalyticAt ℂ (fun x : ℤ →ᵇ ℂ => Ring.inverse (1 + x)) ((0 : ℂ) • c0n n lam0 h0)
      rw [zero_smul]
      exact analyticAt_inverse_one_add ℂ (ℤ →ᵇ ℂ)
    exact AnalyticAt.comp (g := fun x : ℤ →ᵇ ℂ => Ring.inverse (1 + x))
      (f := fun h : ℂ => h • c0n n lam0 h0) h1 hsm
  have hshift : AnalyticAt ℂ (fun lam : ℂ => lam - lam0) lam0 := analyticAt_id.sub analyticAt_const
  have hG : AnalyticAt ℂ (fun lam : ℂ => gC n lam0 * Ring.inverse (1 + (lam - lam0) • c0n n lam0 h0)) lam0 := by
    have h3 : AnalyticAt ℂ (fun h : ℂ => Ring.inverse (1 + h • c0n n lam0 h0))
        ((fun lam : ℂ => lam - lam0) lam0) := by
      show AnalyticAt ℂ (fun h : ℂ => Ring.inverse (1 + h • c0n n lam0 h0)) (lam0 - lam0)
      rw [sub_self]; exact hF
    have h2 := AnalyticAt.comp (g := fun h : ℂ => Ring.inverse (1 + h • c0n n lam0 h0))
      (f := fun lam : ℂ => lam - lam0) h3 hshift
    exact analyticAt_const.mul h2
  refine hG.congr ?_
  filter_upwards [Metric.ball_mem_nhds lam0 one_pos] with lam hlam
  rw [Metric.mem_ball, dist_eq_norm] at hlam
  exact (gC_expand n lam0 h0 lam hlam).symm

theorem analyticAt_Tw (w : ℤ → ℝ) (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w) (n : ℤ)
    (p : ℂ × PotentialCode w) (hp : p.1 ∈ NlsGge.Atomic.KST004.spectralStrip n) :
    AnalyticAt ℂ (Tw w hw n) p := by
  have hB := ContinuousLinearMap.analyticAt_bilinear
    (Bop w hw (w_submul_of_oneDerivative w hw) n) (p.2, gC n p.1)
  have hg : AnalyticAt ℂ (fun q : ℂ × PotentialCode w => gC n q.1) p :=
    (analyticAt_gC n p.1 hp).comp analyticAt_fst
  have := AnalyticAt.comp₂ (h := fun q : PotentialCode w × (ℤ →ᵇ ℂ) =>
      Bop w hw (w_submul_of_oneDerivative w hw) n q.1 q.2)
    (f := fun q : ℂ × PotentialCode w => q.2) (g := fun q : ℂ × PotentialCode w => gC n q.1)
    hB analyticAt_snd hg
  exact this

theorem analyticAt_evenNeumann (w : ℤ → ℝ) (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w)
    (n : ℤ) (p : ℂ × PotentialCode w) (hp : p.1 ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hth : 8 * ‖p.2‖ ^ 2 ≤ NlsGge.Atomic.M.M054.indexWeight n) :
    AnalyticAt ℂ (fun q : ℂ × PotentialCode w => evenNeumann (Tw w hw n q)) p ∧
    AnalyticAt ℂ (fun q : ℂ × PotentialCode w => fullNeumann (Tw w hw n q)) p := by
  have hT := analyticAt_Tw w hw n p hp
  have hS : AnalyticAt ℂ (fun q : ℂ × PotentialCode w => Tw w hw n q * Tw w hw n q) p := hT.mul hT
  have h1 : ‖Tw w hw n p * Tw w hw n p‖ < 1 :=
    lt_of_le_of_lt (Tw_sq_bound w hw n p hp hth) (by norm_num)
  have hcont : ContinuousAt (fun q : ℂ × PotentialCode w => Tw w hw n q * Tw w hw n q) p := hS.continuousAt
  have hev : ∀ᶠ q in 𝓝 p, ‖Tw w hw n q * Tw w hw n q‖ < 1 :=
    hcont.norm.eventually (gt_mem_nhds h1)
  have hE : AnalyticAt ℂ (fun q : ℂ × PotentialCode w => evenNeumann (Tw w hw n q)) p := by
    have hu : IsUnit (1 - Tw w hw n p * Tw w hw n p) := isUnit_one_sub_of_norm_lt_one h1
    have hinv : AnalyticAt ℂ (Ring.inverse : (SourceCode w n →L[ℂ] SourceCode w n) → _)
        (1 - Tw w hw n p * Tw w hw n p) := analyticOnNhd_inverse (𝕜 := ℂ) _ hu
    have hc : AnalyticAt ℂ (fun q : ℂ × PotentialCode w => 1 - Tw w hw n q * Tw w hw n q) p :=
      analyticAt_const.sub hS
    have hinv' : AnalyticAt ℂ (Ring.inverse : (SourceCode w n →L[ℂ] SourceCode w n) → _)
        ((fun q : ℂ × PotentialCode w => 1 - Tw w hw n q * Tw w hw n q) p) := hinv
    have hcomp := AnalyticAt.comp (g := (Ring.inverse : (SourceCode w n →L[ℂ] SourceCode w n) → _))
      (f := fun q : ℂ × PotentialCode w => 1 - Tw w hw n q * Tw w hw n q) hinv' hc
    refine hcomp.congr ?_
    filter_upwards [hev] with q hq
    simp only [Function.comp_apply]
    unfold evenNeumann
    exact (NormedRing.inverse_one_sub _ hq)
  refine ⟨hE, ?_⟩
  exact (analyticAt_const.add hT).mul hE

end
end NlsGge.ThirdConsultation.MTwoMode.WeightedInverse
