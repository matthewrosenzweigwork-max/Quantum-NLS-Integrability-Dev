import NlsGge.Birkhoff.W11Equivalence38e

/-! # W11 (`D:thm:equivalence`, v2 l.1671-1691): the headline `W11_38` (conditional on `B`, `O`)

Setting. `B : BirkhoffInput38` (E01), `O : OneSmoothingInput38 B` (E04), `c : BoundedCoefficients lower upper`
(`0 < lower ≤ c_j ≤ upper`), `1/2 < s < 3/4`. `γ_W = fullWeightedSequenceGaussian c s` on `E_s`,
`f_N = fN38 c s N` (`D:eq:fN`), `Z_N = relativePartition38 c N` (`F:eq:relativeZ`),
`f_W = fW06_38 c s hs K δK` with `K = B.KW06_38 O c _` and `δK` any Gaussian divergence
(`RamerDivergence38`; the weight is a.e. independent of the choice and such `δK` exist),
`Z_W = B.ZW38 c.val`, `μ_W = B.muW38 c.val`, `ν_{W,N} = nuWN38 c N` (`eq:fullbare`).

The five statements (all equivalent):
1. `W11Normalizer38`: `Z_N → Z_W`.
2. `Tendsto (∫ |f_N - f_W| dγ_W) → 0` (`f_N → f_W` in `L¹(γ_W)`).
2'. `UniformIntegrable (f_N) 1 γ_W` (Mathlib: `UnifIntegrable` + bounded `L¹` norm; `f_N ≥ 0`).
3. `W11Weak38`: `ν_{W,N} ⇀ μ_W` on `𝓕⁻¹E_s`.
4. `W11Tight38`: `lim_{R→∞} limsup_N ν_{W,N}(‖u‖_{H²} > R) = 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.Weights NlsGge.HierarchyRiccati.Core NlsGge.Ramer Filter Topology
open scoped ENNReal Real

namespace BirkhoffInput38

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B) {lower upper : ℝ}
  (c : BoundedCoefficients lower upper) {s : ℝ}

include B O in
/-- **`D:thm:localized` with `F = 1`** (the form W11 consumes): `∫ χ_R(𝓕⁻¹P_Nx) f_N dγ_W → Z_W ∫ χ_R dμ_W`, with
positive limit, so the denominator of the normalized laws is eventually positive. -/
theorem W10_F1_W11 (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) {χ : ℝ → ℝ} {R : ℝ}
    (hχ : CutoffProfile38 χ) (hR : 0 < R) :
    Tendsto (fun N : ℕ => ∫ x, chiR38 χ R (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
        ∂(fullWeightedSequenceGaussian c s)) atTop
      (𝓝 (B.ZW38 c.val * ∫ u, chiR38 χ R u ∂(B.muW38 c.val))) ∧
    0 < B.ZW38 c.val * ∫ u, chiR38 χ R u ∂(B.muW38 c.val) ∧
    ∀ᶠ N : ℕ in atTop, 0 < ∫ x, chiR38 χ R (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
        ∂(fullWeightedSequenceGaussian c s) := by
  have h10 := (B.W10_38 O c hs hs' hχ hR).1 (fun _ => 1) continuous_const ⟨1, fun _ => by simp⟩
  simp only [one_mul] at h10
  have hpos : 0 < B.ZW38 c.val * ∫ u, chiR38 χ R u ∂(B.muW38 c.val) :=
    mul_pos (B.ZW_pos_W11 c) (B.muW_chiR_pos38 O c hs hs' hχ hR)
  exact ⟨h10, hpos, h10.eventually (lt_mem_nhds hpos)⟩

/-- `1 - χ_R ≤ 1_{‖u‖_{H²} > R}` (and `0 ≤ 1 - χ_R`). -/
theorem one_sub_chiR_le_indicator_W11 {χ : ℝ → ℝ} (hχ : CutoffProfile38 χ) {R : ℝ} (hR : 0 < R)
    (u : PhysicalL2) :
    0 ≤ 1 - chiR38 χ R u ∧ 1 - chiR38 χ R u ≤ (h2Tail38 R).indicator 1 u := by
  have := chiR38_mem_Icc hχ hR u
  refine ⟨by linarith [this.2], ?_⟩
  by_cases hu : u ∈ h2Tail38 R
  · rw [Set.indicator_of_mem hu]; simp only [Pi.one_apply]; linarith [this.1]
  · rw [Set.indicator_of_notMem hu, chiR38_eq_one_of_not_tail hχ hR hu]; simp

include B O in
/-- **W11 (`D:thm:equivalence`), conditional on `B`, `O`, for `1/2 < s < 3/4`.**
For every Gaussian divergence `δK` (`RamerDivergence38`; one exists), the five statements in the file
docstring are equivalent. -/
theorem W11_38 (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    (∃ δK : (ℤ → ℂ) → ℝ,
      RamerDivergence38 c s (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK) ∧
    ∀ δK : (ℤ → ℂ) → ℝ,
      RamerDivergence38 c s (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK →
      List.TFAE
        [ W11Normalizer38 B c,
          Tendsto (fun N : ℕ => ∫ x, |fN38 c s N x -
              fW06_38 c s hs (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK x|
            ∂(fullWeightedSequenceGaussian c s)) atTop (𝓝 0),
          UniformIntegrable (fun N x => fN38 c s N x) 1 (fullWeightedSequenceGaussian c s),
          W11Weak38 B c s,
          W11Tight38 c ] := by
  refine ⟨?_, fun δ hδ => ?_⟩
  · obtain ⟨δ, hδ, -⟩ := B.exists_weight_W11 O c hs hs'
    exact ⟨δ, hδ⟩
  · have hW := B.weight_W11 O c hs hs' δ hδ
    tfae_have 1 ↔ 2 := B.tendsto_Z_iff_l1_W11 c hs hW
    tfae_have 2 ↔ 3 := B.l1_iff_uniformIntegrable_W11' c hs hW
    tfae_have 2 → 4 := fun h F hF hFb => B.weak_of_l1_W11 c hs hW h F hF hFb
    tfae_have 4 → 5 := fun h => B.tight_of_weak_W11 O c hs hs' h
    tfae_have 5 → 1 := fun h => B.normalizer_of_tight_W11 O c hs hs' hW h
    tfae_finish

end BirkhoffInput38

end NlsGge.Birkhoff
end
