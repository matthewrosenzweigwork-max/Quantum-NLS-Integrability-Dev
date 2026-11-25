import NlsGge.Birkhoff.F09Limit38f

/-! # NEW-F09 (`F:cor:limit`, v2 l.1702-1722): the headline (conditional on `B`, `O`)

Source: `paper/v2.tex` l.1702-1722 (statement), l.1774-1794 (proof). Conditional on
`B : BirkhoffInput38` (E01) and `O : OneSmoothingInput38 B` (E04), for `1/2 < s < 3/4`, `c` an allowed
coefficient sequence `0 < c₋ ≤ c_j ≤ c₊` (`BoundedCoefficients lower upper`).

Notation. `γ_W = fullWeightedSequenceGaussian c s` on `E_s`; `f_N = fN38 c s N` (`D:eq:fN`, `f_N^F(U) = f_N(𝓕U)`);
`Z_N = relativePartition38 c N`; `Z_W = B.ZW38 c.val`; `μ_W = B.muW38 c.val`; `ν_{W,N} = nuWN38 c N`
(`eq:fullbare`, a genuine probability measure on `L²`); `g_N(x) = 𝓕⁻¹P_N x = physOfE38 c s (projE38 c s N x)`.
"Weak convergence on `𝓕⁻¹E_s`" means convergence of `∫ F d·` for every `F : L² → ℝ` with `F ∘ physOfE38` bounded
and continuous on `E_s`; "on a fixed ordinary Sobolev space `H^r`" for every `F` with
`F ∘ physOfCarrier38 r` bounded and continuous on `h^r` (the same form as `W10_38`).

`F09_38` conjuncts:
1. `Z_N → Z_W`, `Z_W > 0`, `∃ δ > 0, ∀ N, δ ≤ Z_N`.
2. `F:eq:fullunnorm`: `∫ F(g_N) f_N dγ_W → Z_W ∫ F dμ_W` (both classes of `F`).
3. every `ν_{W,N}` is a probability measure; `∫ F dν_{W,N} → ∫ F dμ_W` (both classes of `F`).
4. `F:eq:expH2`: `∃ η > 0, C, ∀ N`, `ν_{W,N}`-a.e. `u ∈ H²`, `e^{η‖u‖²_{H²}}` is `ν_{W,N}`-integrable with integral `≤ C`.
5. `F:eq:L1`: `f_N → f_W` in `L¹(γ_W)`, also on the physical space `γ_W^F = (𝓕⁻¹)_# γ_W` with `f ∘ 𝓕`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.Weights NlsGge.HierarchyRiccati.Core NlsGge.Ramer Filter Topology
open scoped ENNReal Real

section Sobolev

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

/-- A test function continuous and bounded on `h^r` is continuous and bounded on `E_s`. -/
theorem esClass_of_sobolev38 (r : ℝ) (hr : 0 ≤ r) (F : PhysicalL2 → ℝ)
    (hF : Continuous (fun y : SobolevCarrier38 r => F (physOfCarrier38 r hr y)))
    (hFb : ∃ M, ∀ y : SobolevCarrier38 r, |F (physOfCarrier38 r hr y)| ≤ M) :
    Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y)) ∧
      ∃ M, ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M := by
  obtain ⟨M, hM⟩ := hFb
  have hEq : (fun y : ECarrier38 c s => F (physOfE38 c s y)) =
      (fun y : SobolevCarrier38 r => F (physOfCarrier38 r hr y)) ∘ (eToSob38 c s r) :=
    funext fun y => by simp only [Function.comp, physOfE38_eq_physOfCarrier38 c s r hr y]
  refine ⟨?_, M, fun y => ?_⟩
  · rw [hEq]; exact hF.comp (continuous_eToSob38 c s r)
  · rw [physOfE38_eq_physOfCarrier38 c s r hr y]; exact hM _

end Sobolev

namespace BirkhoffInput38

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B) {lower upper : ℝ}
  (c : BoundedCoefficients lower upper) {s : ℝ}

include B O in
theorem fullunnorm_Sobolev38 (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) (r : ℝ) (hr : 0 ≤ r)
    (F : PhysicalL2 → ℝ)
    (hF : Continuous (fun y : SobolevCarrier38 r => F (physOfCarrier38 r hr y)))
    (hFb : ∃ M, ∀ y : SobolevCarrier38 r, |F (physOfCarrier38 r hr y)| ≤ M) :
    Tendsto (fun N : ℕ => ∫ x, F (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
        ∂(fullWeightedSequenceGaussian c s)) atTop
      (𝓝 (B.ZW38 c.val * ∫ u, F u ∂(B.muW38 c.val))) := by
  obtain ⟨h1, h2⟩ := esClass_of_sobolev38 c s r hr F hF hFb
  exact B.fullunnorm_Es38 O c hs hs' F h1 h2

include B O in
/-- `inf_N Z_N(W) > 0` (v2 l.1786). -/
theorem inf_Z_pos38 (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, δ ≤ relativePartition38 c N := by
  obtain ⟨h, hpos⟩ := B.Z_tendsto_38 O c hs hs'
  exact exists_pos_lower_of_tendsto38 _ _ hpos (relativePartition38_pos c) h

include B O in
theorem weak_Es38 (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) (F : PhysicalL2 → ℝ)
    (hF : Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y)))
    (hFb : ∃ M, ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M) :
    Tendsto (fun N : ℕ => ∫ u, F u ∂(nuWN38 c N)) atTop (𝓝 (∫ u, F u ∂(B.muW38 c.val))) := by
  obtain ⟨hZ, hpos⟩ := B.Z_tendsto_38 O c hs hs'
  have h1 := B.fullunnorm_Es38 O c hs hs' F hF hFb
  have h2 := (hZ.inv₀ hpos.ne').mul h1
  have e : (B.ZW38 c.val)⁻¹ * (B.ZW38 c.val * ∫ u, F u ∂(B.muW38 c.val)) =
      ∫ u, F u ∂(B.muW38 c.val) := by field_simp
  rw [e] at h2
  refine h2.congr fun N => ?_
  rw [integral_nuWN38_Es c s hs N F (continuous_comp_planeL2_of_cont38 c s F hF N).measurable]
  simp [one_div]

include B O in
theorem weak_Sobolev38 (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) (r : ℝ) (hr : 0 ≤ r)
    (F : PhysicalL2 → ℝ)
    (hF : Continuous (fun y : SobolevCarrier38 r => F (physOfCarrier38 r hr y)))
    (hFb : ∃ M, ∀ y : SobolevCarrier38 r, |F (physOfCarrier38 r hr y)| ≤ M) :
    Tendsto (fun N : ℕ => ∫ u, F u ∂(nuWN38 c N)) atTop (𝓝 (∫ u, F u ∂(B.muW38 c.val))) := by
  obtain ⟨h1, h2⟩ := esClass_of_sobolev38 c s r hr F hF hFb
  exact B.weak_Es38 O c hs hs' F h1 h2

include B O in
/-- **`F:eq:expH2`.** -/
theorem expH2_38 (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    ∃ η C : ℝ, 0 < η ∧ ∀ N : ℕ,
      (∀ᵐ u ∂(nuWN38 c N), fourierSeq38 u ∈ seqSobolev38 (((2 : ℕ)) : ℝ)) ∧
      Integrable (fun u => Real.exp (η * ‖physH38 2 u‖ ^ 2)) (nuWN38 c N) ∧
      ∫ u, Real.exp (η * ‖physH38 2 u‖ ^ 2) ∂(nuWN38 c N) ≤ C := by
  obtain ⟨δ, hδ, hZ⟩ := B.inf_Z_pos38 O c hs hs'
  exact expMoment_nuWN38 c c.property.2.1 δ hδ hZ

include B O in
/-- **`F:eq:L1`.** -/
theorem L1_38 (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    ∃ δK : (ℤ → ℂ) → ℝ,
      RamerDivergence38 c s (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK ∧
      Integrable (fW06_38 c s hs (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK)
        (fullWeightedSequenceGaussian c s) ∧
      ∫ x, fW06_38 c s hs (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK x
        ∂(fullWeightedSequenceGaussian c s) = B.ZW38 c.val ∧
      (∀ N : ℕ, Integrable (fun x => fN38 c s N x -
        fW06_38 c s hs (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK x)
        (fullWeightedSequenceGaussian c s)) ∧
      Tendsto (fun N : ℕ => ∫ x, |fN38 c s N x -
        fW06_38 c s hs (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK x|
        ∂(fullWeightedSequenceGaussian c s)) atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => ∫ u, |physFun38 c s (fN38 c s N) u -
        physFun38 c s (fW06_38 c s hs (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK) u|
        ∂((fullWeightedSequenceGaussian c s).map (physFW06_38 c s))) atTop (𝓝 0) := by
  obtain ⟨δK, hdiv, -, hfi, hfint, hprob, -, -, -⟩ := W07_38 B O c s hs hs'
  obtain ⟨hZ, -⟩ := B.Z_tendsto_38 O c hs hs'
  have hN : ∀ N, Integrable (fN38 c s N) (fullWeightedSequenceGaussian c s) :=
    fun N => integrable_fN38 c hs N
  have hf0 : ∀ x, 0 ≤ fW06_38 c s hs (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK x :=
    fun x => mul_nonneg (Real.exp_pos _).le (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
  have hmain := tendsto_integral_abs_sub_of_inMeasure38 (μ := fullWeightedSequenceGaussian c s)
    (fun N x => fN38 c s N x)
    (fW06_38 c s hs (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK) hN hfi
    (fun N x => (fN38_pos c s N x).le) hf0 hprob (by
      rw [hfint]
      exact hZ.congr fun N => (integral_fN38 c s hs N).symm)
  refine ⟨δK, hdiv, hfi, hfint, fun N => (hN N).sub hfi, hmain, ?_⟩
  refine hmain.congr fun N => ?_
  rw [(measurableEmbedding_physFW06_38 c s).integral_map]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [physFun38_physOfE38]

include B O in
/-- **`F:cor:limit` (v2 l.1702-1722), conditional on `B : BirkhoffInput38`, `O : OneSmoothingInput38 B`.**
See the file docstring for the reading of every symbol. -/
theorem F09_38 (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    (Tendsto (fun N : ℕ => relativePartition38 c N) atTop (𝓝 (B.ZW38 c.val)) ∧
      0 < B.ZW38 c.val ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, δ ≤ relativePartition38 c N) ∧
    ((∀ F : PhysicalL2 → ℝ, Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y)) →
        (∃ M, ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M) →
        Tendsto (fun N : ℕ => ∫ x, F (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
          ∂(fullWeightedSequenceGaussian c s)) atTop
          (𝓝 (B.ZW38 c.val * ∫ u, F u ∂(B.muW38 c.val)))) ∧
      (∀ (r : ℝ) (hr : 0 ≤ r) (F : PhysicalL2 → ℝ),
        Continuous (fun y : SobolevCarrier38 r => F (physOfCarrier38 r hr y)) →
        (∃ M, ∀ y : SobolevCarrier38 r, |F (physOfCarrier38 r hr y)| ≤ M) →
        Tendsto (fun N : ℕ => ∫ x, F (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
          ∂(fullWeightedSequenceGaussian c s)) atTop
          (𝓝 (B.ZW38 c.val * ∫ u, F u ∂(B.muW38 c.val))))) ∧
    ((∀ N : ℕ, IsProbabilityMeasure (nuWN38 c N)) ∧
      (∀ F : PhysicalL2 → ℝ, Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y)) →
        (∃ M, ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M) →
        Tendsto (fun N : ℕ => ∫ u, F u ∂(nuWN38 c N)) atTop
          (𝓝 (∫ u, F u ∂(B.muW38 c.val)))) ∧
      (∀ (r : ℝ) (hr : 0 ≤ r) (F : PhysicalL2 → ℝ),
        Continuous (fun y : SobolevCarrier38 r => F (physOfCarrier38 r hr y)) →
        (∃ M, ∀ y : SobolevCarrier38 r, |F (physOfCarrier38 r hr y)| ≤ M) →
        Tendsto (fun N : ℕ => ∫ u, F u ∂(nuWN38 c N)) atTop
          (𝓝 (∫ u, F u ∂(B.muW38 c.val))))) ∧
    (∃ η C : ℝ, 0 < η ∧ ∀ N : ℕ,
      (∀ᵐ u ∂(nuWN38 c N), fourierSeq38 u ∈ seqSobolev38 (((2 : ℕ)) : ℝ)) ∧
      Integrable (fun u => Real.exp (η * ‖physH38 2 u‖ ^ 2)) (nuWN38 c N) ∧
      ∫ u, Real.exp (η * ‖physH38 2 u‖ ^ 2) ∂(nuWN38 c N) ≤ C) ∧
    (∃ δK : (ℤ → ℂ) → ℝ,
      RamerDivergence38 c s (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK ∧
      Integrable (fW06_38 c s hs (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK)
        (fullWeightedSequenceGaussian c s) ∧
      ∫ x, fW06_38 c s hs (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK x
        ∂(fullWeightedSequenceGaussian c s) = B.ZW38 c.val ∧
      (∀ N : ℕ, Integrable (fun x => fN38 c s N x -
        fW06_38 c s hs (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK x)
        (fullWeightedSequenceGaussian c s)) ∧
      Tendsto (fun N : ℕ => ∫ x, |fN38 c s N x -
        fW06_38 c s hs (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK x|
        ∂(fullWeightedSequenceGaussian c s)) atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => ∫ u, |physFun38 c s (fN38 c s N) u -
        physFun38 c s (fW06_38 c s hs (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK) u|
        ∂((fullWeightedSequenceGaussian c s).map (physFW06_38 c s))) atTop (𝓝 0)) :=
  ⟨⟨(B.Z_tendsto_38 O c hs hs').1, (B.Z_tendsto_38 O c hs hs').2, B.inf_Z_pos38 O c hs hs'⟩,
    ⟨fun F hF hFb => B.fullunnorm_Es38 O c hs hs' F hF hFb,
      fun r hr F hF hFb => B.fullunnorm_Sobolev38 O c hs hs' r hr F hF hFb⟩,
    ⟨fun N => isProbabilityMeasure_nuWN38 c N,
      fun F hF hFb => B.weak_Es38 O c hs hs' F hF hFb,
      fun r hr F hF hFb => B.weak_Sobolev38 O c hs hs' r hr F hF hFb⟩,
    B.expH2_38 O c hs hs', B.L1_38 O c hs hs'⟩

end BirkhoffInput38

end NlsGge.Birkhoff
end
