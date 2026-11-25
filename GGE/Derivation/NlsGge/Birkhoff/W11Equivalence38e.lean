import NlsGge.Birkhoff.W11Equivalence38d

/-! # W11 (`D:thm:equivalence`), part e: boundedness in probability implies `Z_N → Z_W` (W11.04, W11.05)
and the headline `W11_38`

Source: `paper/v2.tex` l.1686-1690:
"Conversely, assume `eq:remainingtight`. For any `ε > 0`, choose `R` with `liminf_N ν_{W,N}(χ_R) ≥ 1 - ε`.
Theorem `D:thm:localized`, with `F = 1`, gives `Z_N ν_{W,N}(χ_R) → Z_W μ_W(χ_R) ≤ Z_W`. Hence
`limsup Z_N ≤ Z_W/(1-ε)`. Let `ε ↓ 0` and use `liminf Z_N ≥ Z_W`."
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.Weights NlsGge.HierarchyRiccati.Core NlsGge.Ramer Filter Topology
open scoped ENNReal Real

/-- If `ρ` is a probability measure with `ρ(‖u‖_{H²} > R) ≤ ε`, then `∫ χ_R dρ ≥ 1 - ε`. -/
theorem one_sub_le_integral_chiR_W11 {χ : ℝ → ℝ} (hχ : CutoffProfile38 χ) {R : ℝ} (hR : 0 < R)
    {ρ : Measure PhysicalL2} [IsProbabilityMeasure ρ] (hint : Integrable (chiR38 χ R) ρ)
    {ε : ℝ} (hε : 0 ≤ ε) (h : ρ (h2Tail38 R) ≤ ENNReal.ofReal ε) :
    1 - ε ≤ ∫ u, chiR38 χ R u ∂ρ := by
  have hS := measurableSet_h2Tail38 R
  have hI : Integrable ((h2Tail38 R).indicator (1 : PhysicalL2 → ℝ)) ρ :=
    (integrable_const (1 : ℝ)).indicator hS
  have hmono : ∫ u, (1 - (h2Tail38 R).indicator (1 : PhysicalL2 → ℝ) u) ∂ρ ≤
      ∫ u, chiR38 χ R u ∂ρ := by
    refine integral_mono ((integrable_const (1 : ℝ)).sub hI) hint (fun u => ?_)
    by_cases hu : u ∈ h2Tail38 R
    · rw [Set.indicator_of_mem hu]
      have := chiR38_mem_Icc hχ hR u
      simp only [Pi.one_apply, sub_self]; exact this.1
    · rw [Set.indicator_of_notMem hu, chiR38_eq_one_of_not_tail hχ hR hu]; simp
  rw [integral_sub (integrable_const (1 : ℝ)) hI, integral_indicator_one hS] at hmono
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at hmono
  have : ρ.real (h2Tail38 R) ≤ ε := ENNReal.toReal_le_of_le_ofReal hε h
  linarith

namespace BirkhoffInput38

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B) {lower upper : ℝ}
  (c : BoundedCoefficients lower upper) {s : ℝ}

include B O in
/-- Upper bound step (W11.04 + W11.05): if `ν_{W,N}(‖u‖_{H²} > R) < ε` eventually for some `R`, then
eventually `(1 - ε) Z_N ≤ Z_W + η`. -/
theorem upper_W11 (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) (htight : W11Tight38 c)
    {ε : ℝ} (hε : 0 < ε) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, (1 - ε) * relativePartition38 c N ≤ B.ZW38 c.val + η := by
  obtain ⟨χ, hχ⟩ := exists_cutoffProfile38
  unfold W11Tight38 at htight
  have hev := htight.eventually (eventually_lt_nhds (ENNReal.ofReal_pos.2 hε))
  obtain ⟨R, hRg, hR⟩ := (hev.and (eventually_gt_atTop (0 : ℝ))).exists
  have hN : ∀ᶠ N : ℕ in atTop, nuWN38 c N (h2Tail38 R) < ENNReal.ofReal ε :=
    eventually_lt_of_limsup_lt hRg
  have h10 := (B.W10_38 O c hs hs' hχ hR).1 (fun _ => 1) continuous_const ⟨1, fun _ => by simp⟩
  simp only [one_mul] at h10
  have hprob := B.isProbabilityMeasure_muW38 lower upper c.val c.property.1 (coef_bound38 c)
    (coef_upper38 c)
  have hZpos := B.ZW_pos_W11 c
  have hchiint : Integrable (chiR38 χ R) (B.muW38 c.val) :=
    Integrable.of_bound (B.aestronglyMeasurable_muW38 O c hs hs' _
      (continuous_chiR38_physOfE38 c s hχ hR)) 1 (Eventually.of_forall fun u => by
        have := chiR38_mem_Icc hχ hR u
        rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2)
  have hA : B.ZW38 c.val * ∫ u, chiR38 χ R u ∂(B.muW38 c.val) ≤ B.ZW38 c.val := by
    have : ∫ u, chiR38 χ R u ∂(B.muW38 c.val) ≤ 1 := by
      calc ∫ u, chiR38 χ R u ∂(B.muW38 c.val) ≤ ∫ u, (1 : ℝ) ∂(B.muW38 c.val) :=
            integral_mono hchiint (integrable_const _) fun u => (chiR38_mem_Icc hχ hR u).2
        _ = 1 := by simp
    nlinarith
  have hev2 := h10.eventually (eventually_lt_nhds (lt_of_le_of_lt hA (by linarith :
    B.ZW38 c.val < B.ZW38 c.val + η)))
  filter_upwards [hN, hev2] with N hN1 hN2
  have hZN := relativePartition38_pos c N
  have := isProbabilityMeasure_nuWN38 c N
  have hcint : Integrable (chiR38 χ R) (nuWN38 c N) :=
    integrable_nuWN38_W11 c s hs N _ (continuous_chiR38_physOfE38 c s hχ hR) 1 (fun y => by
      have := chiR38_mem_Icc hχ hR (physOfE38 c s y)
      rw [abs_of_nonneg this.1]; exact this.2)
  have h1 := one_sub_le_integral_chiR_W11 hχ hR hcint hε.le hN1.le
  have h2 := integral_nuWN38 c s hs N (chiR38 χ R) (continuous_chiR38_physOfE38 c s hχ hR)
  have h3 : ∫ x, chiR38 χ R (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
      ∂(fullWeightedSequenceGaussian c s) =
      relativePartition38 c N * ∫ u, chiR38 χ R u ∂(nuWN38 c N) := by
    rw [h2]; field_simp
  rw [h3] at hN2
  nlinarith

include B O in
/-- **W11.04-.05.** Boundedness in probability implies `Z_N → Z_W`. -/
theorem normalizer_of_tight_W11 (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) {f : FullWeightedHilbert c s → ℝ}
    (hW : W11Weight38 B c s f) (htight : W11Tight38 c) : W11Normalizer38 B c := by
  have hZpos := B.ZW_pos_W11 c
  have hg : ∫⁻ x, ENNReal.ofReal (f x) ∂(fullWeightedSequenceGaussian c s) =
      ENNReal.ofReal (B.ZW38 c.val) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hW.integrable hW.nonneg, hW.integral_eq]
  have hlow := fatou_liminf_W07 (μ := fullWeightedSequenceGaussian c s)
    (fun N x => fN38 c s N x) f (fun N => measurable_fN38 c s N) hW.inMeasure
    (fun N => relativePartition38 c N) (fun N => lintegral_fN38 c s hs N) hZpos hg
  refine tendsto_order.2 ⟨fun a ha => hlow a ha, fun b hb => ?_⟩
  have hcont : ContinuousAt (fun ε : ℝ => (B.ZW38 c.val + ε) / (1 - ε)) 0 :=
    (continuous_const.add continuous_id).continuousAt.div
      (continuous_const.sub continuous_id).continuousAt (by norm_num)
  have hev : ∀ᶠ ε : ℝ in 𝓝 0, (B.ZW38 c.val + ε) / (1 - ε) < b :=
    hcont.eventually (eventually_lt_nhds (by simpa using hb))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  set ε : ℝ := min (δ / 2) (1 / 2) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by norm_num)
  have hε1 : ε ≤ 1 / 2 := min_le_right _ _
  have hlt : (B.ZW38 c.val + ε) / (1 - ε) < b := by
    refine hball ?_
    rw [Real.dist_eq, sub_zero, abs_of_pos hε0]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  filter_upwards [B.upper_W11 O c hs hs' htight hε0 hε0] with N hN
  have h1 : relativePartition38 c N ≤ (B.ZW38 c.val + ε) / (1 - ε) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  exact lt_of_le_of_lt h1 hlt

end BirkhoffInput38

end NlsGge.Birkhoff
end
