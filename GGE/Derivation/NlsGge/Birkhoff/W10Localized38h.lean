import NlsGge.Birkhoff.W10Localized38g

/-! # W10b, file 4: the headline `D:thm:localized` (conditional on `B`, `O`)

Source: `paper/v2.tex` l.1635-1643 (statement) and l.1644-1663 (proof). Conditional on
`B : BirkhoffInput38` (E01) and `O : OneSmoothingInput38 B` (E04), for `1/2 < s < 3/4`.

`W10_38` states, for every cutoff profile `χ` (continuous, nonincreasing, `1` on `[0,1]`, `0` on
`[2,∞)`), every `R > 0`, with `γ_W = fullWeightedSequenceGaussian c s` on `E_s`,
`f_N = fN38 c s N` (`D:eq:fN`), `μ_W = B.muW38 c`, `Z_W = B.ZW38 c`, `χ_R = chiR38 χ R`:

1. `E_s`-continuous `F`: `∫ F(𝓕⁻¹P_Nx) χ_R(𝓕⁻¹P_Nx) f_N(x) dγ_W → Z_W ∫ F χ_R dμ_W`;
2. the same for `F` bounded and continuous on a fixed ordinary Sobolev space `H^r` (`r ≥ 0`);
3. the normalized-law corollary: `μ_W(χ_R) > 0`, `ν := χ_Rμ_W/μ_W(χ_R)` is a probability measure, and the
   normalized expectations `∫ F χ_R f_N dγ_W / ∫ χ_R f_N dγ_W → ∫ F dν` for the same two classes of `F`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.Weights NlsGge.Ramer Filter Topology
open scoped ENNReal Real

namespace BirkhoffInput38

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B) {lower upper : ℝ}
  (c : BoundedCoefficients lower upper) {s : ℝ}

include B O in
/-- `ν = χ_R μ_W / μ_W(χ_R)` is a probability measure on `L²`. -/
theorem isProbabilityMeasure_locLimitLaw38 (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4)
    {χ : ℝ → ℝ} {R : ℝ} (hχ : CutoffProfile38 χ) (hR : 0 < R) :
    IsProbabilityMeasure (B.locLimitLaw38 c χ R) := by
  have hpos := B.muW_chiR_pos38 O c hs hs' hχ hR
  have hprob := B.isProbabilityMeasure_muW38 lower upper c.val c.property.1 (coef_bound38 c)
    (coef_upper38 c)
  have hchi : AEStronglyMeasurable (fun u => chiR38 χ R u) (B.muW38 c.val) :=
    B.aestronglyMeasurable_muW38 O c hs hs' _ (continuous_chiR38_physOfE38 c s hχ hR)
  have hint : Integrable (fun u => chiR38 χ R u) (B.muW38 c.val) :=
    Integrable.of_bound hchi 1 (Filter.Eventually.of_forall fun u => by
      have h := chiR38_mem_Icc hχ hR u
      rw [Real.norm_eq_abs, abs_of_nonneg h.1]; exact h.2)
  refine ⟨?_⟩
  unfold locLimitLaw38
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun u => (chiR38_mem_Icc hχ hR u).1),
    smul_eq_mul, ← ENNReal.ofReal_mul (one_div_pos.2 hpos).le, one_div, inv_mul_cancel₀ hpos.ne',
    ENNReal.ofReal_one]

include B O in
/-- The normalized-law corollary for `F` bounded and continuous on a fixed ordinary Sobolev space. -/
theorem W10_normalized_Sobolev38 (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) {χ : ℝ → ℝ} {R : ℝ}
    (hχ : CutoffProfile38 χ) (hR : 0 < R) (r : ℝ) (hr : 0 ≤ r) (F : PhysicalL2 → ℝ)
    (hF : Continuous (fun y : SobolevCarrier38 r => F (physOfCarrier38 r hr y)))
    (hFb : ∃ M, ∀ y : SobolevCarrier38 r, |F (physOfCarrier38 r hr y)| ≤ M) :
    Tendsto (fun N : ℕ =>
        (∫ x, F (physOfE38 c s (projE38 c s N x)) * chiR38 χ R (physOfE38 c s (projE38 c s N x)) *
          fN38 c s N x ∂(fullWeightedSequenceGaussian c s)) /
        ∫ x, chiR38 χ R (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
          ∂(fullWeightedSequenceGaussian c s)) atTop
      (𝓝 (∫ u, F u ∂(B.locLimitLaw38 c χ R))) := by
  obtain ⟨M, hM⟩ := hFb
  have hEq : (fun y : ECarrier38 c s => F (physOfE38 c s y)) =
      (fun y : SobolevCarrier38 r => F (physOfCarrier38 r hr y)) ∘ (eToSob38 c s r) :=
    funext fun y => by simp only [Function.comp, physOfE38_eq_physOfCarrier38 c s r hr y]
  refine (B.W10_normalized_Es38 O c hs hs' hχ hR F ?_ ⟨M, fun y => ?_⟩).2
  · rw [hEq]; exact hF.comp (continuous_eToSob38 c s r)
  · rw [physOfE38_eq_physOfCarrier38 c s r hr y]; exact hM _

include B O in
/-- **`D:thm:localized` (v2 l.1635-1643), conditional on `B : BirkhoffInput38`, `O : OneSmoothingInput38 B`.**
See the file docstring for the reading of every symbol. -/
theorem W10_38 (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) {χ : ℝ → ℝ} {R : ℝ}
    (hχ : CutoffProfile38 χ) (hR : 0 < R) :
    (∀ F : PhysicalL2 → ℝ, Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y)) →
      (∃ M, ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M) →
      Tendsto (fun N : ℕ => ∫ x, F (physOfE38 c s (projE38 c s N x)) *
          chiR38 χ R (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
          ∂(fullWeightedSequenceGaussian c s))
        atTop (𝓝 (B.ZW38 c.val * ∫ u, F u * chiR38 χ R u ∂(B.muW38 c.val)))) ∧
    (∀ (r : ℝ) (hr : 0 ≤ r) (F : PhysicalL2 → ℝ),
      Continuous (fun y : SobolevCarrier38 r => F (physOfCarrier38 r hr y)) →
      (∃ M, ∀ y : SobolevCarrier38 r, |F (physOfCarrier38 r hr y)| ≤ M) →
      Tendsto (fun N : ℕ => ∫ x, F (physOfE38 c s (projE38 c s N x)) *
          chiR38 χ R (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
          ∂(fullWeightedSequenceGaussian c s))
        atTop (𝓝 (B.ZW38 c.val * ∫ u, F u * chiR38 χ R u ∂(B.muW38 c.val)))) ∧
    (0 < ∫ u, chiR38 χ R u ∂(B.muW38 c.val) ∧
      IsProbabilityMeasure (B.locLimitLaw38 c χ R) ∧
      (∀ F : PhysicalL2 → ℝ, Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y)) →
        (∃ M, ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M) →
        Tendsto (fun N : ℕ =>
          (∫ x, F (physOfE38 c s (projE38 c s N x)) *
            chiR38 χ R (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
            ∂(fullWeightedSequenceGaussian c s)) /
          ∫ x, chiR38 χ R (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
            ∂(fullWeightedSequenceGaussian c s)) atTop
          (𝓝 (∫ u, F u ∂(B.locLimitLaw38 c χ R)))) ∧
      (∀ (r : ℝ) (hr : 0 ≤ r) (F : PhysicalL2 → ℝ),
        Continuous (fun y : SobolevCarrier38 r => F (physOfCarrier38 r hr y)) →
        (∃ M, ∀ y : SobolevCarrier38 r, |F (physOfCarrier38 r hr y)| ≤ M) →
        Tendsto (fun N : ℕ =>
          (∫ x, F (physOfE38 c s (projE38 c s N x)) *
            chiR38 χ R (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
            ∂(fullWeightedSequenceGaussian c s)) /
          ∫ x, chiR38 χ R (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
            ∂(fullWeightedSequenceGaussian c s)) atTop
          (𝓝 (∫ u, F u ∂(B.locLimitLaw38 c χ R))))) :=
  ⟨fun F hF hFb => B.W10_localized_Es38 O c hs hs' hχ hR F hF hFb,
    fun r hr F hF hFb => B.W10_localized_Sobolev38 O c hs hs' hχ hR r hr F hF hFb,
    B.muW_chiR_pos38 O c hs hs' hχ hR, B.isProbabilityMeasure_locLimitLaw38 O c hs hs' hχ hR,
    fun F hF hFb => (B.W10_normalized_Es38 O c hs hs' hχ hR F hF hFb).2,
    fun r hr F hF hFb => B.W10_normalized_Sobolev38 O c hs hs' hχ hR r hr F hF hFb⟩

end BirkhoffInput38

end NlsGge.Birkhoff
end
