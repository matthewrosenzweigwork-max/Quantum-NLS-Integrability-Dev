import NlsGge.Birkhoff.W10Localized38f

/-! # W10b, file 3 (W10.07 and the remaining assertions of `D:thm:localized`)

Source: `paper/v2.tex` l.1635-1643, 1662-1663. Conditional on `B : BirkhoffInput38`,
`O : OneSmoothingInput38 B`, for `1/2 < s < 3/4`.

* `muW_chiR_pos38` (W10.07): `μ_W(χ_R) = ∫ χ_R dμ_W > 0`. Proof: `χ_R = 1` on the open `E_s`-neighbourhood
  `{‖x‖_{h²} < R}` of `0`, `γ_W` has full support (W06.01), and `f_W > 0`.
* `W10_localized_Sobolev38`: the same convergence for `F` bounded and continuous on a fixed ordinary
  Sobolev space `H^r` (`r ≥ 0`): `F∘𝓕⁻¹|_{E_s}` is continuous on `E_s` by the continuous embedding `E_s ↪ h^r`.
* `W10_normalized_Es38`: the normalized full-energy Fourier laws with the fixed factor `χ_R` converge
  to `χ_R μ_W / μ_W(χ_R)` (tested against every bounded `F`, continuous on `E_s` or on `H^r`);
  `locLimitLaw38` is this probability measure.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.Weights NlsGge.Ramer Filter Topology
open scoped ENNReal Real

section Sobolev

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

/-- `𝓕⁻¹ : h^r → L²` for `r ≥ 0` (the ordinary Sobolev space `H^r`, through the reflected Fourier
isometry). -/
def physOfCarrier38 (r : ℝ) (hr : 0 ≤ r) (y : SobolevCarrier38 r) : PhysicalL2 :=
  physInv38 (carrierCoe38 r y) (seqSobolev38_mono hr (carrierCoe38_mem r y))

theorem physOfE38_eq_physOfCarrier38 (r : ℝ) (hr : 0 ≤ r) (x : ECarrier38 c s) :
    physOfE38 c s x = physOfCarrier38 r hr (eToSob38 c s r x) := by
  apply fourierSeq38_injective
  unfold physOfCarrier38
  rw [fourierSeq38_physOfE38, fourierSeq38_physInv38, carrierCoe_eToSob38]

theorem eToSob38_zero (r : ℝ) : eToSob38 c s r 0 = 0 := by
  apply carrierExt38
  funext n
  rw [carrierCoe_eToSob38]
  rfl

end Sobolev

namespace BirkhoffInput38

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B) {lower upper : ℝ}
  (c : BoundedCoefficients lower upper) {s : ℝ}

include B O in
/-- `μ_W` as a measure: `μ_W = Z_W⁻¹ (𝓕⁻¹)_#(f_W γ_W)` with `f_W = e^{-R_W} J_T` (W06). -/
theorem muW_measure_formula38 (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    ∃ J : FullWeightedHilbert c s → ℝ,
      (∀ x, 0 < J x) ∧ Integrable J (fullWeightedSequenceGaussian c s) ∧
      B.muW38 c.val = ENNReal.ofReal (1 / B.ZW38 c.val) •
        ((fullWeightedSequenceGaussian c s).withDensity
          (fun x => ENNReal.ofReal (Real.exp (-(remainder38 c.val (physOfE38 c s x))) * J x))).map
          (physFW06_38 c s) := by
  have hs1 : s ≤ 1 := by linarith
  obtain ⟨δK, -, hmap, hpos, hint, -⟩ := ramer_W06_38 B O c s hs hs1
  refine ⟨_, hpos, hint, ?_⟩
  exact muW38_eq_map_W06 B c s O hs hs'.le _ hmap hint.aemeasurable.ennreal_ofReal

include B O in
/-- A function on `L²` whose restriction to `𝓕⁻¹ E_s` is continuous is `μ_W`-a.e. strongly measurable. -/
theorem aestronglyMeasurable_muW38 (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) (G : PhysicalL2 → ℝ)
    (hG : Continuous (fun y : ECarrier38 c s => G (physOfE38 c s y))) :
    AEStronglyMeasurable G (B.muW38 c.val) := by
  obtain ⟨J, -, -, hmu⟩ := B.muW_measure_formula38 O c hs hs'
  rw [hmu]
  refine AEStronglyMeasurable.smul_measure ?_ _
  rw [(measurableEmbedding_physFW06_38 c s).aestronglyMeasurable_map_iff]
  have hG' : Continuous (fun y : FullWeightedHilbert c s => G (physOfE38 c s y)) := hG
  exact (hG'.aestronglyMeasurable).mono_ac (withDensity_absolutelyContinuous _ _)

include B O in
/-- **W10.07.** The localized normalizer is positive: `∫ χ_R dμ_W > 0`. -/
theorem muW_chiR_pos38 (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) {χ : ℝ → ℝ} {R : ℝ}
    (hχ : CutoffProfile38 χ) (hR : 0 < R) : 0 < ∫ u, chiR38 χ R u ∂(B.muW38 c.val) := by
  obtain ⟨J, hmap, hpos, hint, hmu⟩ := B.muW_integral_formula38 O c hs hs'
  set γ := fullWeightedSequenceGaussian c s with hγ
  have hZ := (B.ZW38_pos_le_one lower upper c.val c.property.1 (coef_bound38 c)
    (coef_upper38 c)).1
  rw [hmu (fun u => chiR38 χ R u)]
  refine mul_pos (one_div_pos.2 hZ) ?_
  have hrc : Continuous (fun x : FullWeightedHilbert c s =>
      remainder38 c.val (physOfE38 c s x)) := B.continuous_remainder_physOfE38 c s O hs'
  have hchic : Continuous (fun x : FullWeightedHilbert c s => chiR38 χ R (physOfE38 c s x)) :=
    continuous_chiR38_physOfE38 c s hχ hR
  set h : FullWeightedHilbert c s → ℝ := fun x =>
    (Real.exp (-(remainder38 c.val (physOfE38 c s x))) * J x) * chiR38 χ R (physOfE38 c s x) with hh
  have hnn : ∀ x, 0 ≤ h x := fun x =>
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (hpos x).le) (chiR38_mem_Icc hχ hR _).1
  have hint' : Integrable h γ := by
    refine Integrable.mono' hint
      (((hrc.neg.rexp).aestronglyMeasurable.mul hint.aestronglyMeasurable).mul
        hchic.aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn x)]
    have hrem : 0 ≤ remainder38 c.val (physOfE38 c s x) :=
      (B.finiteGap_approximation_PM_W05_38 c s O hs' x).2.2.2
    have h1 : Real.exp (-(remainder38 c.val (physOfE38 c s x))) ≤ 1 :=
      Real.exp_le_one_iff.2 (by linarith)
    have h2 := (chiR38_mem_Icc hχ hR (physOfE38 c s x)).2
    have hJx := (hpos x).le
    calc h x = (Real.exp (-(remainder38 c.val (physOfE38 c s x))) * J x) *
          chiR38 χ R (physOfE38 c s x) := rfl
      _ ≤ (1 * J x) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_right h1 hJx) h2 (chiR38_mem_Icc hχ hR _).1
          (by positivity)
      _ = J x := by ring
  rw [integral_pos_iff_support_of_nonneg hnn hint']
  set U0 : Set (FullWeightedHilbert c s) :=
    {x | ‖eToSob38 c s (((1 + 1 : ℕ)) : ℝ) x‖ < R} with hU0
  have hU0o : IsOpen U0 :=
    isOpen_lt ((continuous_eToSob38 c s _).norm) continuous_const
  have hU0n : U0.Nonempty := ⟨0, by
    show ‖eToSob38 c s (((1 + 1 : ℕ)) : ℝ) 0‖ < R
    rw [eToSob38_zero, norm_zero]; exact hR⟩
  have hsub : U0 ⊆ Function.support h := by
    intro x hx
    have hx' : ‖eToSob38 c s (((1 + 1 : ℕ)) : ℝ) x‖ < R := hx
    have hchi1 : chiR38 χ R (physOfE38 c s x) = 1 := by
      refine (chiR38_physOfE38 c s χ R x).trans ?_
      exact hχ.eq_one _ (div_nonneg (norm_nonneg _) hR.le)
        ((div_le_one hR).2 hx'.le)
    show h x ≠ 0
    simp only [hh, hchi1, mul_one]
    exact (mul_pos (Real.exp_pos _) (hpos x)).ne'
  exact lt_of_lt_of_le ((W06_01_38 c s hs).2.2 U0 hU0o hU0n) (measure_mono hsub)

/-- The normalized limit law `χ_R μ_W / μ_W(χ_R)` on `L²`. -/
def locLimitLaw38 (χ : ℝ → ℝ) (R : ℝ) : Measure PhysicalL2 :=
  ENNReal.ofReal (1 / ∫ u, chiR38 χ R u ∂(B.muW38 c.val)) •
    (B.muW38 c.val).withDensity (fun u => ENNReal.ofReal (chiR38 χ R u))

include B O in
/-- Integral against the normalized limit law: `∫ F dν = ∫ F χ_R dμ_W / ∫ χ_R dμ_W`. -/
theorem integral_locLimitLaw38 (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) {χ : ℝ → ℝ} {R : ℝ}
    (hχ : CutoffProfile38 χ) (hR : 0 < R) (F : PhysicalL2 → ℝ) :
    ∫ u, F u ∂(B.locLimitLaw38 c χ R) =
      (∫ u, F u * chiR38 χ R u ∂(B.muW38 c.val)) / ∫ u, chiR38 χ R u ∂(B.muW38 c.val) := by
  have hpos := B.muW_chiR_pos38 O c hs hs' hχ hR
  have hchi : AEStronglyMeasurable (fun u => chiR38 χ R u) (B.muW38 c.val) :=
    B.aestronglyMeasurable_muW38 O c hs hs' _ (continuous_chiR38_physOfE38 c s hχ hR)
  unfold locLimitLaw38
  rw [integral_smul_measure, ENNReal.toReal_ofReal (one_div_pos.2 hpos).le,
    integral_withDensity_eq_integral_toReal_smul₀ hchi.aemeasurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have : ∫ u, (ENNReal.ofReal (chiR38 χ R u)).toReal • F u ∂(B.muW38 c.val) =
      ∫ u, F u * chiR38 χ R u ∂(B.muW38 c.val) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [ENNReal.toReal_ofReal (chiR38_mem_Icc hχ hR u).1, smul_eq_mul]
    ring
  rw [this, smul_eq_mul, one_div, inv_mul_eq_div]

include B O in
/-- **`D:thm:localized`, ordinary Sobolev assertion.** The same convergence for `F` bounded and
continuous on a fixed ordinary Sobolev space `H^r`, `r ≥ 0`. -/
theorem W10_localized_Sobolev38 (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) {χ : ℝ → ℝ} {R : ℝ}
    (hχ : CutoffProfile38 χ) (hR : 0 < R) (r : ℝ) (hr : 0 ≤ r) (F : PhysicalL2 → ℝ)
    (hF : Continuous (fun y : SobolevCarrier38 r => F (physOfCarrier38 r hr y)))
    (hFb : ∃ M, ∀ y : SobolevCarrier38 r, |F (physOfCarrier38 r hr y)| ≤ M) :
    Tendsto (fun N : ℕ => ∫ x, F (physOfE38 c s (projE38 c s N x)) *
        chiR38 χ R (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
        ∂(fullWeightedSequenceGaussian c s))
      atTop (𝓝 (B.ZW38 c.val * ∫ u, F u * chiR38 χ R u ∂(B.muW38 c.val))) := by
  obtain ⟨M, hM⟩ := hFb
  have hEq : (fun y : ECarrier38 c s => F (physOfE38 c s y)) =
      (fun y : SobolevCarrier38 r => F (physOfCarrier38 r hr y)) ∘ (eToSob38 c s r) :=
    funext fun y => by simp only [Function.comp, physOfE38_eq_physOfCarrier38 c s r hr y]
  refine B.W10_localized_Es38 O c hs hs' hχ hR F ?_ ⟨M, fun y => ?_⟩
  · rw [hEq]; exact hF.comp (continuous_eToSob38 c s r)
  · rw [physOfE38_eq_physOfCarrier38 c s r hr y]; exact hM _

include B O in
/-- **The normalized-law corollary.** For `F` bounded and continuous on `𝓕⁻¹E_s`: `μ_W(χ_R) > 0` and
`∫ F χ_R(𝓕⁻¹P_N x) f_N dγ_W / ∫ χ_R(𝓕⁻¹P_N x) f_N dγ_W → ∫ F χ_R dμ_W / ∫ χ_R dμ_W`, which is
`∫ F d(χ_R μ_W/μ_W(χ_R))`. -/
theorem W10_normalized_Es38 (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) {χ : ℝ → ℝ} {R : ℝ}
    (hχ : CutoffProfile38 χ) (hR : 0 < R) (F : PhysicalL2 → ℝ)
    (hF : Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y)))
    (hFb : ∃ M, ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M) :
    0 < ∫ u, chiR38 χ R u ∂(B.muW38 c.val) ∧
    Tendsto (fun N : ℕ =>
        (∫ x, F (physOfE38 c s (projE38 c s N x)) * chiR38 χ R (physOfE38 c s (projE38 c s N x)) *
          fN38 c s N x ∂(fullWeightedSequenceGaussian c s)) /
        ∫ x, chiR38 χ R (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
          ∂(fullWeightedSequenceGaussian c s)) atTop
      (𝓝 (∫ u, F u ∂(B.locLimitLaw38 c χ R))) := by
  have hpos := B.muW_chiR_pos38 O c hs hs' hχ hR
  have hZ := (B.ZW38_pos_le_one lower upper c.val c.property.1 (coef_bound38 c)
    (coef_upper38 c)).1
  refine ⟨hpos, ?_⟩
  have hnum := B.W10_localized_Es38 O c hs hs' hχ hR F hF hFb
  have hden := B.W10_localized_Es38 O c hs hs' hχ hR (fun _ => 1) continuous_const
    ⟨1, fun _ => by simp⟩
  simp only [one_mul] at hden
  have hq := hnum.div hden (mul_pos hZ hpos).ne'
  rw [B.integral_locLimitLaw38 O c hs hs' hχ hR F]
  convert hq using 2
  field_simp

end BirkhoffInput38

end NlsGge.Birkhoff
end
