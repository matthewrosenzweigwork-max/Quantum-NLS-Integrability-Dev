import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB3Hm1Duhamel

/-! # Track B, step B3: crude continuity of the `H⁻¹` Duhamel integral in the forcing

For forcings `F, G ∈ L¹([a,b] × 𝕋)` and times `s, s' ∈ [a,b]`, the actual `H⁻¹`-valued Bochner
Duhamel integrals satisfy, for every `t`,
`‖∫ₛ^{s'} e^{i(t-r)∂ₓ²}(-iF(r)) dr - ∫ₛ^{s'} e^{i(t-r)∂ₓ²}(-iG(r)) dr‖_{H⁻¹} ≤ C_{-1} ‖F - G‖_{L¹([a,b]×𝕋)}`
(`norm_duhamel_sub_le`), with `C_{-1} = hm1Const` (the `L¹(𝕋) → H⁻¹` constant). This is the crude
continuity `L¹_{t,x} → C_t H⁻¹_x` used to identify limits in the density argument for
(eq:L4duhamel) (`L^{4/3} ⊂ L¹` on the finite slab).
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

open MeasureTheory Filter Topology NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38

attribute [local instance] isProbabilityMeasure_spatialMeasure

theorem fnToHm1_sub {f g : PhysicalCircle → ℂ} (hf : Integrable f spatialMeasure)
    (hg : Integrable g spatialMeasure) : fnToHm1 (f - g) = fnToHm1 f - fnToHm1 g := by
  simp only [fnToHm1, hf, hg, hf.sub hg, ↓reduceDIte]
  rw [Integrable.toL1_sub, map_sub]

/-- **Crude continuity of the actual `H⁻¹` Duhamel integral in the forcing.** -/
theorem norm_duhamel_sub_le {F G : ℝ × PhysicalCircle → ℂ} {a b : ℝ}
    (hF : Integrable F (((volume : Measure ℝ).restrict (Set.Icc a b)).prod spatialMeasure))
    (hG : Integrable G (((volume : Measure ℝ).restrict (Set.Icc a b)).prod spatialMeasure))
    (t : ℝ) {s s' : ℝ} (hs : s ∈ Set.Icc a b) (hs' : s' ∈ Set.Icc a b) :
    ‖(∫ r in s..s', freeProp (-1) (t - r) (negIMul (-1) (fnToHm1 (fun x => F (r, x))))) -
        ∫ r in s..s', freeProp (-1) (t - r) (negIMul (-1) (fnToHm1 (fun x => G (r, x))))‖ ≤
      hm1Const * ∫ p, ‖F p - G p‖ ∂(((volume : Measure ℝ).restrict (Set.Icc a b)).prod
        spatialMeasure) := by
  have hsub : Set.uIoc s s' ⊆ Set.Icc a b :=
    Set.uIoc_subset_uIcc.trans (Set.uIcc_subset_Icc hs hs')
  have iF := integrable_duhamel_slab hF t
  have iG := integrable_duhamel_slab hG t
  have hsub' : Set.uIcc s s' ⊆ Set.Icc a b := Set.uIcc_subset_Icc hs hs'
  have iF' : IntervalIntegrable (fun r => freeProp (-1) (t - r)
      (negIMul (-1) (fnToHm1 (fun x => F (r, x))))) volume s s' :=
    (IntegrableOn.mono_set iF hsub').intervalIntegrable
  have iG' : IntervalIntegrable (fun r => freeProp (-1) (t - r)
      (negIMul (-1) (fnToHm1 (fun x => G (r, x))))) volume s s' :=
    (IntegrableOn.mono_set iG hsub').intervalIntegrable
  have hFG : Integrable (fun p => ‖F p - G p‖)
      (((volume : Measure ℝ).restrict (Set.Icc a b)).prod spatialMeasure) := (hF.sub hG).norm
  have hR : Integrable (fun r => hm1Const * ∫ x, ‖F (r, x) - G (r, x)‖ ∂spatialMeasure)
      ((volume : Measure ℝ).restrict (Set.Icc a b)) :=
    (hF.sub hG).integral_norm_prod_left.const_mul hm1Const
  rw [← intervalIntegral.integral_sub iF' iG']
  calc ‖∫ r in s..s', (freeProp (-1) (t - r) (negIMul (-1) (fnToHm1 (fun x => F (r, x)))) -
          freeProp (-1) (t - r) (negIMul (-1) (fnToHm1 (fun x => G (r, x)))))‖
      ≤ ∫ r in Set.uIoc s s', ‖freeProp (-1) (t - r) (negIMul (-1) (fnToHm1 (fun x => F (r, x)))) -
          freeProp (-1) (t - r) (negIMul (-1) (fnToHm1 (fun x => G (r, x))))‖ :=
        intervalIntegral.norm_integral_le_integral_norm_uIoc
    _ ≤ ∫ r in Set.Icc a b, ‖freeProp (-1) (t - r) (negIMul (-1) (fnToHm1 (fun x => F (r, x)))) -
          freeProp (-1) (t - r) (negIMul (-1) (fnToHm1 (fun x => G (r, x))))‖ :=
        setIntegral_mono_set (iF.sub iG).norm (ae_of_all _ fun _ => norm_nonneg _)
          hsub.eventuallyLE
    _ ≤ ∫ r in Set.Icc a b, hm1Const * ∫ x, ‖F (r, x) - G (r, x)‖ ∂spatialMeasure := by
        refine integral_mono_ae (iF.sub iG).norm hR ?_
        filter_upwards [hF.prod_right_ae, hG.prod_right_ae] with r hFr hGr
        rw [← map_sub, ← map_sub, norm_duhamel_term, ← fnToHm1_sub hFr hGr]
        exact norm_fnToHm1_le _
    _ = hm1Const * ∫ p, ‖F p - G p‖ ∂(((volume : Measure ℝ).restrict (Set.Icc a b)).prod
          spatialMeasure) := by
        rw [integral_const_mul, integral_prod _ hFG]

end LiebLiniger.FixedPeriod.ALLS.PdeB
