import NlsGge.Birkhoff.F09Limit38e
import NlsGge.Birkhoff.W07Probability38e
import NlsGge.Birkhoff.W06Jacobian38b

/-! # NEW-F10 (`F:eq:L1`, v2 l.1717-1721, proof l.1788-1794): `L¹` convergence of the common-space
weights (conditional on `B : BirkhoffInput38`, `O : OneSmoothingInput38 B`)

Source: `paper/v2.tex` l.1717-1721 (statement), l.1788-1794 (proof), l.1796-1798 (remark).

Reading. `γ_W = fullWeightedSequenceGaussian c s` on `E_s`, `1/2 < s < 3/4`, `c` a coefficient sequence
`0 < c₋ ≤ c_j ≤ c₊` (`BoundedCoefficients lower upper`). `f_N = fN38 c s N`
(`f_N(x) = exp[-E_W(𝓕⁻¹ x_N) + A(x_N)]`, v2 `D:eq:fN`, i.e. the physical weights `f_N^F(U) = f_N(𝓕U)`),
`f_W = fW06_38 ...` the W06 density `e^{-R_W(𝓕⁻¹x)} J_T(x)` for a Gaussian divergence `δK`
(`RamerDivergence38`), `Z_N = relativePartition38 c N`, `Z_W = B.ZW38 c.val`.

Sub-claims.
* NEW-F10.01 (`W07_38` conjuncts: `f_N → f_W` in probability; W06 inside it: `∫ f_W dγ_W = Z_W`).
* NEW-F10.02 (`Z_tendsto_38`: `Z_N → Z_W`, with `∫ f_N dγ_W = Z_N` from `W07_38`).
* NEW-F10.03-.06 are proof steps; they are the `B`-free lemma `tendsto_integral_abs_sub_F10_38`
  (subsequence / a.e. subsequence; dominated convergence for `min(f_N,f)`; the identity
  `∫|f_N-f| = ∫f_N + ∫f - 2∫min(f_N,f)` (`integral_abs_sub_eq_F10_38`); the subsequence criterion).
* The statement sub-claim is `L1_F10_38`: `∫ |f_N - f_W| dγ_W → 0` on `E_s`, and on the physical space
  `γ_W^F = (𝓕⁻¹)_# γ_W` (`Measure.map physFW06_38`) for `f ∘ 𝓕` (`physFun38`).

This is `L¹` of densities on a common Gaussian space, not total variation of finite-plane field laws.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.Weights NlsGge.HierarchyRiccati.Core NlsGge.Ramer Filter Topology
open scoped ENNReal Real

/-- NEW-F10.05: `|g - f| = g + f - 2 min(g,f)` pointwise. -/
theorem abs_sub_eq_F10_38 (a b : ℝ) : |a - b| = a + b - 2 * min a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
  · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring

/-- NEW-F10.05: `∫|g - f| = ∫ g + ∫ f - 2 ∫ min(g,f)` for integrable `g`, `f`. -/
theorem integral_abs_sub_eq_F10_38 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g f : α → ℝ} (hg : Integrable g μ) (hf : Integrable f μ) :
    ∫ x, |g x - f x| ∂μ = ∫ x, g x ∂μ + ∫ x, f x ∂μ - 2 * ∫ x, min (g x) (f x) ∂μ := by
  have hm : Integrable (fun x => min (g x) (f x)) μ := hg.inf hf
  have : (fun x => |g x - f x|) = fun x => g x + f x - 2 * min (g x) (f x) :=
    funext fun x => abs_sub_eq_F10_38 _ _
  rw [this, integral_sub (f := fun x => g x + f x) (g := fun x => 2 * min (g x) (f x))
    (hg.add hf) (hm.const_mul 2), integral_add hg hf, integral_const_mul]

/-- NEW-F10.03-.06 (`B`-free). If `f_n ≥ 0` are integrable, `f ≥ 0` is integrable, `f_n → f` in
measure and `∫ f_n → ∫ f`, then `∫ |f_n - f| → 0`. -/
theorem tendsto_integral_abs_sub_F10_38 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (fN : ℕ → α → ℝ) (f : α → ℝ) (hN : ∀ n, Integrable (fN n) μ) (hf : Integrable f μ)
    (hN0 : ∀ n x, 0 ≤ fN n x) (hf0 : ∀ x, 0 ≤ f x)
    (hmeas : TendstoInMeasure μ fN atTop f)
    (hint : Tendsto (fun n => ∫ x, fN n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ))) :
    Tendsto (fun n => ∫ x, |fN n x - f x| ∂μ) atTop (𝓝 0) := by
  -- NEW-F10.06: the subsequence criterion
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  -- NEW-F10.03: a further subsequence converging almost everywhere
  have hm' : TendstoInMeasure μ (fun k => fN (ns k)) atTop f :=
    fun ε hε => (hmeas ε hε).comp hns
  obtain ⟨ms, hms, hae⟩ := hm'.exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  have hmin : Tendsto (fun k => ∫ x, min (fN (ns (ms k)) x) (f x) ∂μ) atTop
      (𝓝 (∫ x, f x ∂μ)) := by
    -- NEW-F10.04: dominated convergence for `min(f_N, f)`, dominated by `f`
    refine tendsto_integral_of_dominated_convergence f
      (fun k => ((hN _).inf hf).aestronglyMeasurable) hf (fun k => Eventually.of_forall fun x => ?_) ?_
    · rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hN0 _ x) (hf0 x))]
      exact min_le_right _ _
    · filter_upwards [hae] with x hx
      simpa using hx.min (tendsto_const_nhds (x := f x))
  have hgint : Tendsto (fun k => ∫ x, fN (ns (ms k)) x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) :=
    hint.comp (hns.comp hms.tendsto_atTop)
  have := (hgint.add_const (∫ x, f x ∂μ)).sub (hmin.const_mul 2)
  rw [show (0 : ℝ) = ∫ x, f x ∂μ + ∫ x, f x ∂μ - 2 * ∫ x, f x ∂μ by ring]
  refine this.congr fun k => ?_
  exact (integral_abs_sub_eq_F10_38 (hN _) hf).symm

namespace BirkhoffInput38

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B) {lower upper : ℝ}
  (c : BoundedCoefficients lower upper) {s : ℝ}

include B O in
/-- **NEW-F10 (`F:eq:L1`, v2 l.1717-1721), conditional on `B`, `O`.** There is a Gaussian divergence
`δK` of the W06 map such that the W06 density `f_W` is `γ_W`-integrable with `∫ f_W dγ_W = Z_W`,
each `f_N - f_W` is `γ_W`-integrable, and
`∫ |f_N - f_W| dγ_W → 0` (`L¹(γ_W)`), and likewise on the physical space
`γ_W^F = (𝓕⁻¹)_# γ_W` for `f ∘ 𝓕` (`physFun38`). -/
theorem L1_F10_38 (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
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
  -- NEW-F10.01: W07 (probability) and W06 (limit integral)
  obtain ⟨δK, hdiv, hZN, hfi, hfint, hprob, -, -, -⟩ := W07_38 B O c s hs hs'
  -- NEW-F10.02: NEW-F09 identifies the limit of the integrals
  obtain ⟨hZ, -⟩ := B.Z_tendsto_38 O c hs hs'
  have hN : ∀ N, Integrable (fN38 c s N) (fullWeightedSequenceGaussian c s) :=
    fun N => integrable_fN38 c hs N
  have hf0 : ∀ x, 0 ≤
      fW06_38 c s hs (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK x :=
    fun x => mul_nonneg (Real.exp_pos _).le (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
  have hmain := tendsto_integral_abs_sub_F10_38 (μ := fullWeightedSequenceGaussian c s)
    (fun N x => fN38 c s N x)
    (fW06_38 c s hs (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK) hN hfi
    (fun N x => (fN38_pos c s N x).le) hf0 hprob (by
      rw [hfint]
      exact hZ.congr fun N => (hZN N).symm)
  refine ⟨δK, hdiv, hfi, hfint, fun N => (hN N).sub hfi, hmain, ?_⟩
  refine hmain.congr fun N => ?_
  rw [(measurableEmbedding_physFW06_38 c s).integral_map]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [physFun38_physOfE38]

end BirkhoffInput38

end NlsGge.Birkhoff
end
