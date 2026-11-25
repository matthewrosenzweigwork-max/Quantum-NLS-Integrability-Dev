import Mathlib
import NlsGge.ThirdConsultation.G2.G2037P5A
import NlsGge.Atomic.M.M051Host

                                                                                                    
                                                                                                                        
                                                                                                           
                                                                                                               
                                                                                                                   
                                                                                                                  
                                                                                                                          
                                                                                                                       

set_option autoImplicit false
open Set Filter Topology Metric

namespace NlsGge.ThirdConsultation.M016ChartAux

/-- Removable singularity at an isolated point (Mathlib `RemovableSingularity`). -/
theorem differentiableOn_of_punctured {F : ℂ → ℂ} {U : Set ℂ} {c : ℂ} (hU : IsOpen U) (hc : c ∈ U)
    (hd : DifferentiableOn ℂ F (U \ {c})) (hcont : ContinuousAt F c) : DifferentiableOn ℂ F U :=
  (Complex.differentiableOn_compl_singleton_and_continuousAt_iff (hU.mem_nhds hc)).mp ⟨hd, hcont⟩

/-- A derivative formula valid on a punctured neighbourhood extends to the centre. -/
theorem hasDerivAt_of_punctured {F h : ℂ → ℂ} {U : Set ℂ} {c : ℂ} (hU : IsOpen U) (hc : c ∈ U)
    (hF : DifferentiableOn ℂ F U) (hh : ContinuousAt h c)
    (hd : ∀ w ∈ U, w ≠ c → HasDerivAt F (h w) w) : HasDerivAt F (h c) c := by
  have hFc : DifferentiableAt ℂ F c := hF.differentiableAt (hU.mem_nhds hc)
  have hcont : ContinuousAt (deriv F) c := ((hF.analyticOnNhd hU) c hc).deriv.continuousAt
  have h1 : Tendsto (deriv F) (𝓝[≠] c) (𝓝 (deriv F c)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (deriv F) (𝓝[≠] c) (𝓝 (h c)) := by
    refine (hh.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hU.mem_nhds hc)] with w hw hwU
    exact ((hd w hwU hw).deriv).symm
  have heq : deriv F c = h c := tendsto_nhds_unique h1 h2
  rw [← heq]
  exact hFc.hasDerivAt

/-- The exterior expansion of a primitive of `-i Q(1/z)` (wrapper of the landed
`G2037P5.primitive_expansion_core`, which retains the same `F`). -/
theorem expansion_of_deriv (F Q : ℂ → ℂ) {R0 : ℝ} (hR0 : 0 < R0) (hQ : AnalyticAt ℂ Q 0)
    (hQ0 : Q 0 = 1) (hF : ∀ z : ℂ, R0 < ‖z‖ → HasDerivAt F (-Complex.I * Q z⁻¹) z) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧ ∃ R : ℝ, 0 < R ∧
      ∀ z : ℂ, R < ‖z‖ → F z + Complex.I * z = G z⁻¹ := by
  obtain ⟨r0, hr0, hball⟩ := hQ.exists_ball_analyticOnNhd
  obtain ⟨g, hg, hgF⟩ := NlsGge.G2037P5.primitive_expansion_core F Q hR0 hr0
    hball.differentiableOn hQ0 hF
  refine ⟨g, hg, 1 / min r0 (1 / R0), one_div_pos.mpr (lt_min hr0 (one_div_pos.mpr hR0)),
    fun z hz => ?_⟩
  rw [hgF z hz]
  ring

/-- `G(0) = 0` gives analyticity and the value `0` at infinity. -/
theorem infinity_of_G (F G : ℂ → ℂ) {R : ℝ} (hR : 0 < R) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (hFG : ∀ z : ℂ, R < ‖z‖ → F z + Complex.I * z = G z⁻¹) :
    NlsGge.ThirdConsultation.M.AnalyticAtInfinity (fun z : ℂ => F z + Complex.I * z) ∧
      NlsGge.ThirdConsultation.MPrimitive.HasValueAtInfinity
        (fun z : ℂ => F z + Complex.I * z) 0 := by
  have hnorm : ∀ w : ℂ, w ≠ 0 → ‖w‖ < 1 / R → R < ‖w⁻¹‖ := by
    intro w hw hwR
    rw [norm_inv, lt_inv_comm₀ hR (norm_pos_iff.mpr hw), ← one_div]
    exact hwR
  have hev : ∀ w : ℂ, w ≠ 0 → ‖w‖ < 1 / R → F w⁻¹ + Complex.I * w⁻¹ = G w := by
    intro w hw hwR
    rw [hFG _ (hnorm w hw hwR), inv_inv]
  refine ⟨?_, ?_⟩
  · unfold NlsGge.ThirdConsultation.M.AnalyticAtInfinity
    refine hG.congr ?_
    filter_upwards [ball_mem_nhds (0 : ℂ) (one_div_pos.mpr hR)] with w hw
    rw [mem_ball, dist_zero_right] at hw
    by_cases h0 : w = 0
    · simp [h0, hG0]
    · simp only [h0, ↓reduceIte]; exact (hev w h0 hw).symm
  · unfold NlsGge.ThirdConsultation.MPrimitive.HasValueAtInfinity
      NlsGge.ThirdConsultation.MPrimitive.infinityFilter
    have hGt : Tendsto G (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
      have := hG.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := ({0} : Set ℂ)ᶜ))
      rwa [hG0] at this
    have hcomp : Tendsto (fun z : ℂ => G z⁻¹)
        (Filter.comap (fun z : ℂ => z⁻¹) (𝓝[≠] (0 : ℂ))) (𝓝 0) :=
      hGt.comp tendsto_comap
    have hmem : {z : ℂ | R < ‖z‖} ∈ Filter.comap (fun z : ℂ => z⁻¹) (𝓝[≠] (0 : ℂ)) := by
      refine Filter.mem_comap.mpr ⟨({0} : Set ℂ)ᶜ ∩ ball 0 (1 / R),
        inter_mem_nhdsWithin _ (ball_mem_nhds _ (one_div_pos.mpr hR)), fun z hz => ?_⟩
      obtain ⟨hz0, hzb⟩ := hz
      have hz0' : z⁻¹ ≠ 0 := hz0
      rw [mem_ball, dist_zero_right] at hzb
      have := hnorm z⁻¹ hz0' hzb
      rwa [inv_inv] at this
    exact hcomp.congr' (Filter.mem_of_superset hmem fun z hz => (hFG z hz).symm)

/-- The ray calibration `F(it) - t → 0` forces `G(0) = 0`. -/
theorem G0_of_ray (F G : ℂ → ℂ) {R : ℝ} (hG : ContinuousAt G 0)
    (hFG : ∀ z : ℂ, R < ‖z‖ → F z + Complex.I * z = G z⁻¹)
    (hray : Tendsto (fun t : ℝ => F (Complex.I * t) - t) atTop (𝓝 0)) : G 0 = 0 := by
  have hinv : Tendsto (fun t : ℝ => (Complex.I * (t : ℂ))⁻¹) atTop (𝓝 0) := by
    have : Tendsto (fun t : ℝ => ‖(Complex.I * (t : ℂ))⁻¹‖) atTop (𝓝 0) := by
      refine (tendsto_inv_atTop_zero (𝕜 := ℝ)).congr' ((eventually_gt_atTop 0).mono fun t ht => ?_)
      show t⁻¹ = ‖(Complex.I * (t : ℂ))⁻¹‖
      rw [norm_inv, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg ht.le]
    exact tendsto_zero_iff_norm_tendsto_zero.mpr this
  have h1 : Tendsto (fun t : ℝ => G (Complex.I * (t : ℂ))⁻¹) atTop (𝓝 (G 0)) := hG.tendsto.comp hinv
  have h2 : Tendsto (fun t : ℝ => G (Complex.I * (t : ℂ))⁻¹) atTop (𝓝 0) := by
    refine hray.congr' ((eventually_gt_atTop (max R 0)).mono fun t ht => ?_)
    have hn : R < ‖Complex.I * (t : ℂ)‖ := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg
        (le_of_lt (lt_of_le_of_lt (le_max_right _ _) ht))]
      exact lt_of_le_of_lt (le_max_left _ _) ht
    show F (Complex.I * t) - t = G (Complex.I * (t : ℂ))⁻¹
    rw [← hFG _ hn]
    have : Complex.I * (Complex.I * (t : ℂ)) = -(t : ℂ) := by
      rw [← mul_assoc, Complex.I_mul_I]; ring
    rw [this]; ring
  exact tendsto_nhds_unique h1 h2

end NlsGge.ThirdConsultation.M016ChartAux

namespace NlsGge.ThirdConsultation.M016ChartAux

/-- **Generic exterior chart.** `F = L - k0` on `E`, `L` the boundary continuation of a holomorphic `P` on the open set
`C ⊆ E` with derivative `ω`; every exterior point is in `C` or an isolated point of `E` with a punctured neighbourhood in
`C`; `ω = -i Q(1/z)` far out. Then `F` is holomorphic far out and `F(z) + iz = G(1/z)` with `G` analytic at `0`. -/
theorem exterior_chart_generic (C E : Set ℂ) (hC : IsOpen C) (hCE : C ⊆ E)
    (P L ω F : ℂ → ℂ) (k0 : ℂ)
    (hP : ∀ z ∈ C, HasDerivAt P (ω z) z)
    (hPL : ∀ z ∈ E, Tendsto P (𝓝[C] z) (𝓝 (L z)))
    (hFL : ∀ z ∈ E, F z = L z - k0)
    {B : ℝ} (hB0 : 0 < B)
    (hpt : ∀ z : ℂ, B < ‖z‖ → z ∈ C ∨
      (z ∈ E ∧ ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ U \ {z} ⊆ C))
    (Q : ℂ → ℂ) (hQa : AnalyticAt ℂ Q 0) (hQ0 : Q 0 = 1) {R1 : ℝ}
    (hω : ∀ z ∈ C, R1 < ‖z‖ → ω z = -Complex.I * Q z⁻¹) :
    ∃ R' : ℝ, 0 < R' ∧ (∀ z : ℂ, R' < ‖z‖ → AnalyticAt ℂ F z) ∧
      ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧ ∃ R'' : ℝ, 0 < R'' ∧
        ∀ z : ℂ, R'' < ‖z‖ → F z + Complex.I * z = G z⁻¹ := by
  have hLP : ∀ z ∈ C, L z = P z := fun z hz => by
    have h1 := hPL z (hCE hz)
    rw [nhdsWithin_eq_nhds.mpr (hC.mem_nhds hz)] at h1
    exact tendsto_nhds_unique h1 (hP z hz).continuousAt.tendsto
  have hFP : ∀ z ∈ C, F =ᶠ[𝓝 z] fun w => P w - k0 := fun z hz => by
    filter_upwards [hC.mem_nhds hz] with w hw
    rw [hFL w (hCE hw), hLP w hw]
  have hderiv : ∀ z ∈ C, HasDerivAt F (ω z) z := fun z hz =>
    ((hP z hz).sub_const k0).congr_of_eventuallyEq (hFP z hz)
  obtain ⟨r0, hr0, hQball⟩ := hQa.exists_ball_analyticOnNhd
  set R' : ℝ := max (max B R1) (2 / r0) with hR'def
  have hR'B : B ≤ R' := le_trans (le_max_left _ _) (le_max_left _ _)
  have hR'1 : R1 ≤ R' := le_trans (le_max_right _ _) (le_max_left _ _)
  have hR'r : 2 / r0 ≤ R' := le_max_right _ _
  have hR'0 : 0 < R' := lt_of_lt_of_le hB0 hR'B
  have hQcont : ∀ z : ℂ, R' < ‖z‖ → ContinuousAt (fun w : ℂ => -Complex.I * Q w⁻¹) z := by
    intro z hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_trans hR'0 hz)
    have hzr : z⁻¹ ∈ ball (0 : ℂ) r0 := by
      rw [mem_ball, dist_zero_right, norm_inv]
      have h2 : 2 / r0 < ‖z‖ := lt_of_le_of_lt hR'r hz
      rw [inv_lt_comm₀ (norm_pos_iff.mpr hz0) hr0]
      calc r0⁻¹ < 2 / r0 := by
            rw [inv_eq_one_div]; exact div_lt_div_of_pos_right one_lt_two hr0
        _ < ‖z‖ := h2
    exact continuousAt_const.mul ((hQball _ hzr).continuousAt.comp (continuousAt_inv₀ hz0))
  have hderivQ : ∀ z ∈ C, R' < ‖z‖ → HasDerivAt F (-Complex.I * Q z⁻¹) z := fun z hz hzR => by
    rw [← hω z hz (lt_of_le_of_lt hR'1 hzR)]; exact hderiv z hz
  have hdiffC : DifferentiableOn ℂ F C := fun w hw => (hderiv w hw).differentiableAt.differentiableWithinAt
  have hext : ∀ z : ℂ, R' < ‖z‖ → AnalyticAt ℂ F z ∧ HasDerivAt F (-Complex.I * Q z⁻¹) z := by
    intro z hz
    rcases hpt z (lt_of_le_of_lt hR'B hz) with hc | ⟨hzE, U, hUo, hzU, hUC⟩
    · exact ⟨hdiffC.analyticAt (hC.mem_nhds hc), hderivQ z hc hz⟩
    · have hdiffU : DifferentiableOn ℂ F (U \ {z}) := hdiffC.mono hUC
      have hcont : ContinuousAt F z := by
        rw [← continuousWithinAt_compl_self, ContinuousWithinAt, hFL z hzE]
        have hlim : Tendsto P (𝓝[{z}ᶜ] z) (𝓝 (L z)) := by
          refine (hPL z hzE).mono_left ?_
          rw [← nhdsWithin_inter_of_mem (s := U) (t := {z}ᶜ)
            (mem_nhdsWithin_of_mem_nhds (hUo.mem_nhds hzU))]
          exact nhdsWithin_mono _ fun w hw => hUC ⟨hw.1, hw.2⟩
        refine (hlim.sub_const k0).congr' ?_
        filter_upwards [mem_nhdsWithin_of_mem_nhds (hUo.mem_nhds hzU), self_mem_nhdsWithin]
          with w hwU hwz
        have hwC : w ∈ C := hUC ⟨hwU, hwz⟩
        rw [hFL w (hCE hwC), hLP w hwC]
      have hdU : DifferentiableOn ℂ F U := differentiableOn_of_punctured hUo hzU hdiffU hcont
      refine ⟨hdU.analyticAt (hUo.mem_nhds hzU), ?_⟩
      have hU' : IsOpen (U ∩ {w : ℂ | R' < ‖w‖}) :=
        hUo.inter (isOpen_lt continuous_const continuous_norm)
      exact hasDerivAt_of_punctured hU' ⟨hzU, hz⟩ (hdU.mono inter_subset_left) (hQcont z hz)
        fun w hw hwz => hderivQ w (hUC ⟨hw.1, hwz⟩) hw.2
  obtain ⟨G, hG, R'', hR'', hFG⟩ := expansion_of_deriv F Q hR'0 hQa hQ0 fun z hz => (hext z hz).2
  exact ⟨R', hR'0, fun z hz => (hext z hz).1, G, hG, R'', hR'', hFG⟩

end NlsGge.ThirdConsultation.M016ChartAux
