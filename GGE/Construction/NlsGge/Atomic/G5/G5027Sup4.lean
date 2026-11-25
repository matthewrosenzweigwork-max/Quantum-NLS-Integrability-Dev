import Mathlib
import NlsGge.Atomic.G5.G5027Sup1
import NlsGge.Atomic.G5.G5027Sup2
import NlsGge.Atomic.G5.G5018M5Ep

                                                                                       
                                                                                        
                                                                                                                                   
                                                      
                                                                                                           
                                                                                                                                   
                                                                                                          
                                                                                                                    
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
namespace G5027Aux
noncomputable section
open G3024Endpoint

theorem tip_package (k : ℤ) (u0 : PhysicalL2) (hk : gamma2 (realSlice u0) k ≠ 0)
    (hβ : AnalyticOnNhd ℂ (betaSum k) sourceBetaW) :
    ∃ (V : Set PotPair) (a b : PotPair → ℂ) (c : ℂ), c ≠ 0 ∧ IsOpen V ∧ realSlice u0 ∈ V ∧
      V ⊆ sourceW \ collapsedSet k ∧ AnalyticOnNhd ℂ a V ∧ AnalyticOnNhd ℂ b V ∧
      AnalyticOnNhd ℂ (tipRoot k b c) V ∧
      (∀ φ ∈ V, ({a φ, b φ} : Set ℂ) = {lamMinus φ k, lamPlus φ k} ∧
        tipRoot k b c φ ^ 2 = muSeq φ k - a φ ∧
        ∀ t ∈ Icc (0 : ℝ) 1,
          ‖gap φ k‖ / 3 ≤ ‖a φ + (t : ℂ) * (muSeq φ k - a φ) - b φ‖ ∧
          c * (a φ + (t : ℂ) * (muSeq φ k - a φ) - b φ) ∈ Complex.slitPlane) ∧
      ∀ φ ∈ V, angleDerivative k φ - fderiv ℂ (betaSum k) φ =
        fderiv ℂ (fun ψ => tipRoot k b c ψ * segK (tipG k k b c) a (fun ψ => muSeq ψ k) ψ) φ := by
  have hW0 : realSlice u0 ∈ sourceW := sourceFamily.W_real (Set.mem_range_self u0)
  have hB0 : realSlice u0 ∈ sourceBetaW := sourceFamily.V_real (Set.mem_range_self u0)
  have hgk0 : realSlice u0 ∈ gkW := sourceFamily.W_gk hW0
  have hφ0 : realSlice u0 ∈ sourceW \ collapsedSet k := ⟨hW0, fun h => hk h.2⟩
  obtain ⟨V1, a, b, hV1o, hφV1, hV1sub, haA, hbA, hVp⟩ := labels_any k (realSlice u0) hφ0
  obtain ⟨U, c, hc, hUo, hφU, hUV, hrωA, hUall⟩ :=
    roots_explicit k V1 a b hV1o hV1sub haA hbA hVp (realSlice u0) hφV1
  have hUsub : U ⊆ sourceW \ collapsedSet k := fun φ hφ => hV1sub (hUV hφ)
  have hgapU : ∀ φ ∈ U, gap φ k ≠ 0 := fun φ hφ => gap_ne k φ (hUsub hφ)
  have hzb : ∀ φ ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, a φ + (t : ℂ) * (muSeq φ k - a φ) - b φ ≠ 0 := by
    intro φ hφ t ht h
    have hb := (hVp φ (hUV hφ)).2 t ht
    rw [h, norm_zero] at hb
    have : 0 < ‖gap φ k‖ := norm_pos_iff.2 (hgapU φ hφ)
    linarith
  have hμA : ∀ φ ∈ U, AnalyticAt ℂ (fun ψ : PotPair => muSeq ψ k) φ := fun φ hφ =>
    analyticOnNhd_muSeq_complex38 k φ (sourceFamily.W_gk (hUsub hφ).1)
  set rseg : PotPair → ℝ → ℂ := fun φ t =>
    G3014Aux.sqrtB c (a φ + (t : ℂ) * (muSeq φ k - a φ) - b φ) with hrseg
  have hrsegA : ∀ t ∈ Icc (0 : ℝ) 1, AnalyticOnNhd ℂ (fun φ => rseg φ t) U := by
    intro t ht φ hφ
    have hφV := hUV hφ
    exact G3014Aux.sqrtB_analyticAt
      (h := fun ψ : PotPair => a ψ + (t : ℂ) * (muSeq ψ k - a ψ) - b ψ)
      (((haA φ hφV).add (analyticAt_const.mul ((hμA φ hφ).sub (haA φ hφV)))).sub (hbA φ hφV))
      ((hUall φ hφ).2 t ht)
  have hrsegC : ContinuousOn (fun p : PotPair × ℝ => rseg p.1 p.2) (U ×ˢ Icc (0 : ℝ) 1) := by
    have hGc : ContinuousOn (fun p : PotPair × ℝ =>
        c * (a p.1 + ((p.2 : ℝ) : ℂ) * (muSeq p.1 k - a p.1) - b p.1)) (U ×ˢ Icc (0 : ℝ) 1) := by
      intro p hp
      apply ContinuousAt.continuousWithinAt
      have hpV : p.1 ∈ V1 := hUV hp.1
      have h1 : ContinuousAt (fun q : PotPair × ℝ => a q.1) p :=
        (haA p.1 hpV).continuousAt.comp continuousAt_fst
      have h2 : ContinuousAt (fun q : PotPair × ℝ => b q.1) p :=
        (hbA p.1 hpV).continuousAt.comp continuousAt_fst
      have h3 : ContinuousAt (fun q : PotPair × ℝ => muSeq q.1 k) p :=
        (hμA p.1 hp.1).continuousAt.comp continuousAt_fst
      have h4 : ContinuousAt (fun q : PotPair × ℝ => ((q.2 : ℝ) : ℂ)) p :=
        Complex.continuous_ofReal.continuousAt.comp continuousAt_snd
      exact continuousAt_const.mul ((h1.add (h4.mul (h3.sub h1))).sub h2)
    have hcp : ContinuousOn (fun p : PotPair × ℝ =>
        (c * (a p.1 + ((p.2 : ℝ) : ℂ) * (muSeq p.1 k - a p.1) - b p.1)) ^ (2⁻¹ : ℂ))
        (U ×ˢ Icc (0 : ℝ) 1) :=
      ContinuousOn.cpow hGc continuousOn_const (fun p hp => (hUall p.1 hp.1).2 p.2 hp.2)
    simp only [hrseg, G3014Aux.sqrtB]
    exact continuousOn_const.mul hcp
  have hall : ∀ φ ∈ U, tipRoot k b c φ ^ 2 = muSeq φ k - a φ ∧
      (∀ t ∈ Icc (0 : ℝ) 1, rseg φ t ≠ 0 ∧
        rseg φ t ^ 2 = a φ + (t : ℂ) * (muSeq φ k - a φ) - b φ) ∧
      2 * Complex.I * rootProduct k (φ, muSeq φ k) * tipRoot k b c φ * rseg φ 1 =
        antiDiscrim φ (muSeq φ k) := by
    intro φ hφ
    have hgk : φ ∈ gkW := sourceFamily.W_gk (hUsub hφ).1
    have hrP0 : rootProduct k (φ, muSeq φ k) ≠ 0 :=
      (G2_021 k).2.2 _ ⟨hgk, G3014Aux.avoids_other φ hgk k⟩
    have hS1 : G3014Aux.sqrtB c (muSeq φ k - b φ) ≠ 0 := by
      have h := hzb φ hφ 1 ⟨zero_le_one, le_rfl⟩
      refine G3014Aux.sqrtB_ne hc ?_
      intro h'
      apply h
      push_cast
      linear_combination h'
    have hrs1 : rseg φ 1 = G3014Aux.sqrtB c (muSeq φ k - b φ) := by
      simp only [hrseg]
      congr 1
      push_cast
      ring
    refine ⟨(hUall φ hφ).1, fun t ht => ⟨G3014Aux.sqrtB_ne hc (hzb φ hφ t ht),
      G3014Aux.sqrtB_sq hc _⟩, ?_⟩
    rw [hrs1, tipRoot]
    field_simp
  obtain ⟨V, C, hVo, hφV, hVU, hC, hHan, hHφ⟩ :=
    param_data k (realSlice u0) U a b (tipRoot k b c) rseg hUo hφU hUsub (haA.mono hUV) (hbA.mono hUV)
      (fun φ hφ => (hVp φ (hUV hφ)).1) hrωA hrsegA hrsegC hall
  obtain ⟨Gf, hGf⟩ : ∃ Gf : PotPair → ℝ → ℂ, Gf = fun (φ : PotPair) (t : ℝ) =>
      psi k φ (a φ + (t : ℂ) * (muSeq φ k - a φ)) * tipRoot k b c φ /
        (2 * Complex.I * rootProduct k (φ, a φ + (t : ℂ) * (muSeq φ k - a φ)) * rseg φ t) :=
    ⟨_, rfl⟩
  have hHan' : ∀ t ∈ Ioo (0 : ℝ) 1, AnalyticOnNhd ℂ (fun φ => Gf φ t) V := by
    subst hGf; exact hHan
  have hHφ' : ∀ φ ∈ V, ContinuousOn (Gf φ) (Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ‖Gf φ t‖ ≤ C) ∧
      IntervalIntegrable (fun t => Gf φ t / (Real.sqrt t : ℂ)) volume 0 1 ∧
      gk16ActualScalarZPlus38 sourceF k φ = (b φ - a φ) *
        Complex.exp (Complex.I * ∫ t in (0 : ℝ)..1, Gf φ t / (Real.sqrt t : ℂ)) := by
    subst hGf; exact hHφ
  -- the explicit lift equals tipRoot * segK everywhere
  have hEq : ∀ φ : PotPair, (∫ t in (0 : ℝ)..1, Gf φ t / (Real.sqrt t : ℂ)) =
      tipRoot k b c φ * segK (tipG k k b c) a (fun ψ => muSeq ψ k) φ := by
    intro φ
    simp only [segK]
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    subst hGf
    simp only [tipG, hrseg]
    ring
  have hmain := NlsGge.Atomic.G4.analyticOn_integral_of_rpow_half_locally_dominated
    (E := PotPair) (F := ℂ) (U := V)
    (a := fun (t : ℝ) (φ : PotPair) => Gf φ t / (Real.sqrt t : ℂ)) C hC.le hVo
    ((ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun t ht φ hφ =>
      (hHan' t ht φ hφ).div analyticAt_const
        (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 ht.1).ne')))
    (fun φ hφ => by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
      refine ((hHφ' φ hφ).1.mono Ioo_subset_Icc_self).div
        (Complex.continuous_ofReal.comp_continuousOn Real.continuous_sqrt.continuousOn) ?_
      intro t ht
      exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 ht.1).ne')
    (fun φ hφ => by
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hVo φ hφ
      refine ⟨r, hr, hball, fun v hv => ?_⟩
      refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun t ht => ?_)
      have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht.1
      have hb := (hHφ' v (hball hv)).2.1 t ⟨ht.1.le, ht.2.le⟩
      have hr' : Real.rpow t (-1 / 2) = (Real.sqrt t)⁻¹ := by
        rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num]
        exact (inv_sqrt_eq_rpow ht.1).symm
      rw [hr', norm_div, Complex.norm_real, Real.norm_of_nonneg hs.le, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right hb hs.le)
  have hAn : AnalyticOnNhd ℂ
      (fun ψ => tipRoot k b c ψ * segK (tipG k k b c) a (fun ψ => muSeq ψ k) ψ) V := by
    intro φ hφ
    refine (hmain φ hφ).congr ?_
    filter_upwards [hVo.mem_nhds hφ] with ψ hψ
    show _ = tipRoot k b c ψ * segK (tipG k k b c) a (fun ψ => muSeq ψ k) ψ
    rw [← hEq ψ, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  -- xi analytic and nonzero near the real point
  have hslit : xiSq38 k (realSlice u0) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    exact Or.inl (lt_of_lt_of_le one_pos (xiSq38_real_ge_one u0 k).2)
  have hξ : AnalyticAt ℂ (xiN38 k) (realSlice u0) := xiN38_analytic k _ ⟨hgk0, hslit⟩
  have hξ0 : xiN38 k (realSlice u0) ≠ 0 := by
    intro h
    have := (xiN38_real_ge_one u0 k).2
    rw [h] at this
    simp at this
    linarith
  have hxev : ∀ᶠ φ in 𝓝 (realSlice u0), AnalyticAt ℂ (xiN38 k) φ ∧ xiN38 k φ ≠ 0 :=
    hξ.eventually_analyticAt.and (hξ.continuousAt.eventually_ne hξ0)
  obtain ⟨Wx, hWxsub, hWxo, hφWx⟩ := _root_.mem_nhds_iff.1 hxev
  set V' : Set PotPair := V ∩ sourceBetaW ∩ Wx with hV'def
  have hV'o : IsOpen V' := (hVo.inter sourceFamily.V_open).inter hWxo
  have hV'V : V' ⊆ V := fun φ hφ => hφ.1.1
  have hV'U : V' ⊆ U := fun φ hφ => hVU (hV'V hφ)
  refine ⟨V', a, b, c, hc, hV'o, ⟨⟨hφV, hB0⟩, hφWx⟩, fun φ hφ => hUsub (hV'U hφ),
    fun φ hφ => haA φ (hUV (hV'U hφ)), fun φ hφ => hbA φ (hUV (hV'U hφ)),
    fun φ hφ => hrωA φ (hV'U hφ), fun φ hφ => ⟨(hVp φ (hUV (hV'U hφ))).1, (hUall φ (hV'U hφ)).1,
      fun t ht => ⟨(hVp φ (hUV (hV'U hφ))).2 t ht, (hUall φ (hV'U hφ)).2 t ht⟩⟩, ?_⟩
  intro φ hφ
  exact G5018M5Aux.angle_diff_eq k φ V' hV'o hφ (fun ψ hψ => hUsub (hV'U hψ)) a b
    (fun ψ => tipRoot k b c ψ * segK (tipG k k b c) a (fun ψ => muSeq ψ k) ψ)
    (haA φ (hUV (hV'U hφ))).differentiableAt (hbA φ (hUV (hV'U hφ))).differentiableAt
    (hAn φ (hV'V hφ)).differentiableAt
    (fun ψ hψ => (hVp ψ (hUV (hV'U hψ))).1)
    (fun ψ hψ => by rw [(hHφ' ψ (hV'V hψ)).2.2.2, hEq ψ])
    (hWxsub hφ.2).1.differentiableAt (hWxsub hφ.2).2
    (hβ φ hφ.1.2).differentiableAt

end
end G5027Aux
end NlsGge.GKDefinitionDesign
