import NlsGge.Birkhoff.W07Probability38d

/-! # W07, part e: `liminf Z_N ≥ Z_W > 0` (Fatou) and the headline (v2 `D:prop:probability`)

Source: `paper/v2.tex` l.1554-1574 and `blueprint/claims/W07.md` (W07.05-W07.06).

* `fatou_liminf_W07`: abstract Fatou step. A probability measure, nonnegative measurable `f_N → g`
  in probability, `∫ f_N = Z_N`, `∫ g = Z > 0` give `∀ a < Z, ∀ᶠ N, a < Z_N`. (Take a subsequence with
  `Z_{N_k} ≤ a`, then an almost surely convergent further subsequence, and apply Fatou's lemma.)
* `W07_38`: the headline, conditional on `B`, `O`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.Weights NlsGge.HierarchyRiccati.Core NlsGge.Ramer NlsGge.Analysis.RegularizedDeterminant
  Filter Topology
open scoped ENNReal Real

/-- **The Fatou step of `D:prop:probability`** (no uniform upper bound on `Z_N` is assumed or
claimed): if nonnegative measurable `f_N → g` in probability, `∫ f_N = Z_N` and `∫ g = Z`, then
every `a < Z` is eventually below `Z_N`. -/
theorem fatou_liminf_W07 {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    (f : ℕ → α → ℝ) (g : α → ℝ) (hf : ∀ n, Measurable (f n))
    (hconv : TendstoInMeasure μ f atTop g) (Zn : ℕ → ℝ)
    (hZn : ∀ n, ∫⁻ x, ENNReal.ofReal (f n x) ∂μ = ENNReal.ofReal (Zn n)) {Z : ℝ} (hZ : 0 < Z)
    (hg : ∫⁻ x, ENNReal.ofReal (g x) ∂μ = ENNReal.ofReal Z) :
    ∀ a : ℝ, a < Z → ∀ᶠ n in atTop, a < Zn n := by
  intro a ha
  by_contra hcon
  have hfreq : ∃ᶠ n in atTop, Zn n ≤ a := by
    simpa [Filter.Eventually, Filter.Frequently, not_lt] using hcon
  obtain ⟨ns, hns, hle⟩ := Filter.extraction_of_frequently_atTop hfreq
  obtain ⟨ns', hns', hae⟩ := (hconv.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  set F : ℕ → α → ℝ≥0∞ := fun k x => ENNReal.ofReal (f (ns (ns' k)) x) with hF
  have hFm : ∀ k, Measurable (F k) := fun k => (hf _).ennreal_ofReal
  have h1 := lintegral_liminf_le (u := (atTop : Filter ℕ)) (μ := μ) hFm
  have h2 : ∫⁻ x, liminf (fun k => F k x) atTop ∂μ = ENNReal.ofReal Z := by
    rw [← hg]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    have : Tendsto (fun k => F k x) atTop (𝓝 (ENNReal.ofReal (g x))) :=
      (ENNReal.tendsto_ofReal hx)
    exact this.liminf_eq
  have h3 : liminf (fun k => ∫⁻ x, F k x ∂μ) atTop ≤ ENNReal.ofReal a := by
    have : ∀ k, ∫⁻ x, F k x ∂μ ≤ ENNReal.ofReal a := fun k => by
      simp only [hF]
      rw [hZn]
      exact ENNReal.ofReal_le_ofReal (hle _)
    calc liminf (fun k => ∫⁻ x, F k x ∂μ) atTop ≤ liminf (fun _ => ENNReal.ofReal a) atTop :=
          liminf_le_liminf (Eventually.of_forall this)
      _ = ENNReal.ofReal a := liminf_const _
  have h4 : ENNReal.ofReal Z ≤ ENNReal.ofReal a := by
    rw [← h2]; exact h1.trans h3
  rw [ENNReal.ofReal_le_ofReal_iff'] at h4
  rcases h4 with h | h <;> linarith

section Headline

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

theorem measurable_fN38 (N : ℕ) : Measurable (fun x : FullWeightedHilbert c s => fN38 c s N x) := by
  have : (fun x : FullWeightedHilbert c s => fN38 c s N x) = fun x => fNseq38 c N (coordE c s x) :=
    funext (fN38_eq_fNseq c s N)
  rw [this]
  exact (measurable_fNseq38 c N).comp (measurable_coordE c s)

/-- `Z_N = ∫ f_N dγ_W` as a lower integral. -/
theorem lintegral_fN38 (hs : (1 : ℝ) / 2 < s) (N : ℕ) :
    ∫⁻ x, ENNReal.ofReal (fN38 c s N x) ∂(fullWeightedSequenceGaussian c s) =
      ENNReal.ofReal (relativePartition38 c N) := by
  have : (fun x => ENNReal.ofReal (fN38 c s N x)) =
      fun x => ENNReal.ofReal (fNseq38 c N (coordE c s x)) :=
    funext fun x => by rw [fN38_eq_fNseq]
  rw [this, lintegral_comp_coordE c s hs
    (f := fun z => ENNReal.ofReal (fNseq38 c N z))
    ((measurable_fNseq38 c N).ennreal_ofReal.aemeasurable)]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_fNseq38 c N)
    (Eventually.of_forall fun z => (Real.exp_pos _).le), integral_fNseq38]

/-- Independence of the weight from the choice of the Gaussian divergence: two divergences
satisfying v2's local clauses give `γ_W`-a.e. equal `f_W`. -/
theorem fW06_ae_unique_W07 (B : BirkhoffInput38) (O : OneSmoothingInput38 B)
    (hs : (1 : ℝ) / 2 < s) (hs1 : s ≤ 1) (δ₁ δ₂ : (ℤ → ℂ) → ℝ)
    (h₁ : RamerDivergence38 c s (B.KW06_38 O c hs1) δ₁)
    (h₂ : RamerDivergence38 c s (B.KW06_38 O c hs1) δ₂) :
    fW06_38 c s hs (B.KW06_38 O c hs1) δ₁ =ᵐ[fullWeightedSequenceGaussian c s]
      fW06_38 c s hs (B.KW06_38 O c hs1) δ₂ := by
  have h := v2_divergence_unique c s hs (B.KW06_38 O c hs1) δ₁ δ₂ h₁.1 h₁.2 h₂.2
  filter_upwards [ae_of_ae_coordE c s hs (P := fun z => δ₁ z = δ₂ z) h] with x hx
  unfold fW06_38 JW06_38
  rw [hx]

end Headline

/-- **W07 (v2 `D:prop:probability`, l.1554-1574), conditional on `B : BirkhoffInput38` and
`O : OneSmoothingInput38 B`, for `1/2 < s < 3/4`.**

`γ_W = fullWeightedSequenceGaussian c s` is the full-weight Gaussian on `E_s`; `f_N = fN38 c s N`
is `x ↦ exp[-E_W(𝓕⁻¹ x_N) + A(x_N)]` (`x_N = P_N x`, `E_W` the spectral energy, `A(x_N) = ∑_{|n|≤N} a_n|x_n|²`),
`Z_N = relativePartition38 c N = ∫ f_N dγ_W`, `f_W = e^{-R_W(𝓕⁻¹ x)} J_T(x)` is the W06 density
(for a Gaussian divergence `δK` in the sense of `RamerDivergence38`; the weight does not depend on
that choice up to `γ_W`-null sets, `fW06_ae_unique_W07`) and `Z_W = ZW38 c.val = ∫ f_W dγ_W` (W06).
Conclusions:
* `f_N → f_W` in probability under `γ_W`;
* `Z_W > 0` and `liminf Z_N ≥ Z_W`, stated both as `∀ a < Z_W, ∀ᶠ N, a < Z_N` and as
  `ofReal Z_W ≤ liminf ofReal Z_N` in `[0,∞]` (no upper bound on `Z_N` is assumed or claimed). -/
theorem W07_38 (B : BirkhoffInput38) (O : OneSmoothingInput38 B) {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    ∃ δK : (ℤ → ℂ) → ℝ,
      RamerDivergence38 c s (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK ∧
      (∀ N : ℕ, ∫ x, fN38 c s N x ∂(fullWeightedSequenceGaussian c s) = relativePartition38 c N) ∧
      Integrable (fW06_38 c s hs (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK)
        (fullWeightedSequenceGaussian c s) ∧
      ∫ x, fW06_38 c s hs (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK x
        ∂(fullWeightedSequenceGaussian c s) = B.ZW38 c.val ∧
      TendstoInMeasure (fullWeightedSequenceGaussian c s) (fun N x => fN38 c s N x) atTop
        (fW06_38 c s hs (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK) ∧
      0 < B.ZW38 c.val ∧
      (∀ a : ℝ, a < B.ZW38 c.val → ∀ᶠ N : ℕ in atTop, a < relativePartition38 c N) ∧
      ENNReal.ofReal (B.ZW38 c.val) ≤
        liminf (fun N : ℕ => ENNReal.ofReal (relativePartition38 c N)) atTop := by
  have hs1 := le_one_of_lt_three_quarters_W06_38 hs'
  obtain ⟨δK, hdiv, hmap, hpos, hint, hone, hconv⟩ := B.ramer_W06_cyl_38 O c hs hs1
  have hJ : AEMeasurable (fun x => ENNReal.ofReal (JW06_38 c s hs (B.KW06_38 O c hs1) δK x))
      (fullWeightedSequenceGaussian c s) := hint.aemeasurable.ennreal_ofReal
  obtain ⟨-, hfi, hfint, -⟩ := density_W06_38 B c s O hs hs' _ hmap hint hpos
  have hprob := B.tendstoInMeasure_fN_W07 O c hs hs' hs1 δK hconv
  have hZ := (B.ZW38_pos_le_one lower upper c.val c.property.1 (coef_bound38 c)
    (coef_upper38 c)).1
  have hg : ∫⁻ x, ENNReal.ofReal (fW06_38 c s hs (B.KW06_38 O c hs1) δK x)
      ∂(fullWeightedSequenceGaussian c s) = ENNReal.ofReal (B.ZW38 c.val) :=
    ofReal_lintegral_eq_W06 B c s O hs hs' _ hmap hJ
  have hEv := fatou_liminf_W07 (μ := fullWeightedSequenceGaussian c s)
    (fun N x => fN38 c s N x) (fW06_38 c s hs (B.KW06_38 O c hs1) δK)
    (fun N => measurable_fN38 c s N) hprob (fun N => relativePartition38 c N)
    (fun N => lintegral_fN38 c s hs N) hZ hg
  refine ⟨δK, hdiv, fun N => integral_fN38 c s hs N, hfi, hfint, hprob, hZ, hEv, ?_⟩
  refine le_of_forall_lt (fun b hb => ?_)
  obtain ⟨b', hb1, hb2⟩ := exists_between hb
  have hb'top : b' ≠ ⊤ := ne_top_of_lt hb2
  have hlt : b'.toReal < B.ZW38 c.val := (ENNReal.lt_ofReal_iff_toReal_lt hb'top).1 hb2
  have hle : b' ≤ liminf (fun N : ℕ => ENNReal.ofReal (relativePartition38 c N)) atTop := by
    refine le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [hEv _ hlt] with N hN
    calc b' = ENNReal.ofReal b'.toReal := (ENNReal.ofReal_toReal hb'top).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hN.le
  exact lt_of_lt_of_le hb1 hle

end NlsGge.Birkhoff
