import NlsGge.Hierarchy.ALQ4Gaussian38
import NlsGge.Hierarchy.ALQ4Ensemble38
import NlsGge.Hierarchy.ALSampling38
import NlsGge.Hierarchy.ALSamplingV2Formula38
import NlsGge.Hierarchy.ALFreeFields38
import Mathlib

/-! # L06b: the limit half of `C:thm:AL` (paper/v2.tex l.2195-2218; measures l.2093-2141, `ρ₂` l.2027-2039)

Positive `β₀, β₁, β₂`, `W(r) = β₀ + β₁r² + β₂r⁴`, `L = 2N+1`, `h = 1/L`.  The coupling space is
`(ℤ → ℂ, alFreeLaw38)`: independent standard complex Gaussians `g_k` (`E|g_k|² = 1`, i.e.
`complexGaussian 1`, whose real components have variance `1/2`).  Because `complexGaussian a` has
real-component variance `1/(2a)`, `a^{-1/2} g_k ~ complexGaussian a`
(`complexGaussian_scale38`), so `Û_N = (a_{h,k}^{-1/2} g_k)_k` has exactly the law
`alQ4Gauss38` (`alQ4Hat_law38`) and `U = (a_k^{-1/2} g_k)_k` has law `γ₂ = gammaM38 2 β`
(`alQ4UCoef_law38`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace NlsGge.AblowitzLadik
open MeasureTheory Filter Topology NlsGge.Pilot NlsGge.HierarchyRiccati.Core

theorem sobolevModeWeight_eq_rpow38 (s : ℝ) (k : ℤ) :
    sobolevModeWeight s k = (1 + (k : ℝ) ^ 2) ^ s := by
  unfold sobolevModeWeight japaneseBracket
  show Real.sqrt (1 + (k : ℝ) ^ 2) ^ (2 * s) = _
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  congr 1; ring

/-- `Σ_k ⟨k⟩^{2s}/(1+k⁴) < ∞` iff `s < 3/2` (the "if" direction). -/
theorem summable_sobolev_div_quartic38 (s : ℝ) (hs : s < 3 / 2) :
    Summable (fun k : ℤ => sobolevModeWeight s k / (1 + (k : ℝ) ^ 4)) := by
  have hb : (1 : ℝ) < 4 - 2 * s := by linarith
  have hg := (Real.summable_abs_int_rpow hb).mul_left 2
  refine Summable.of_norm_bounded_eventually hg ?_
  have hz : ∀ k : ℤ, k ≠ 0 → ‖sobolevModeWeight s k / (1 + (k : ℝ) ^ 4)‖ ≤
      2 * |(k : ℝ)| ^ (-(4 - 2 * s)) := by
    intro k hk
    have hk0 : (0 : ℝ) < |(k : ℝ)| := by
      rw [abs_pos]; exact_mod_cast hk
    have hk2 : (k : ℝ) ^ 2 = |(k : ℝ)| ^ 2 := (sq_abs _).symm
    set x : ℝ := (1 + (k : ℝ) ^ 2) with hx
    have hxpos : 0 < x := by positivity
    rw [sobolevModeWeight_eq_rpow38, ← hx, Real.norm_of_nonneg (by positivity)]
    have h4 : x ^ 2 ≤ 2 * (1 + (k : ℝ) ^ 4) := by
      rw [hx]; nlinarith [sq_nonneg ((k : ℝ) ^ 2 - 1)]
    have hpos4 : 0 < 1 + (k : ℝ) ^ 4 := by positivity
    have e1 : x ^ s / (1 + (k : ℝ) ^ 4) ≤ 2 * x ^ (s - 2) := by
      rw [div_le_iff₀ hpos4, Real.rpow_sub hxpos, Real.rpow_two]
      have : 2 * (x ^ s / x ^ 2) * (1 + (k : ℝ) ^ 4) = x ^ s * (2 * (1 + (k : ℝ) ^ 4)) / x ^ 2 := by ring
      rw [this, le_div_iff₀ (by positivity)]
      exact mul_le_mul_of_nonneg_left h4 (by positivity)
    have e2 : x ^ (s - 2) ≤ (|(k : ℝ)| ^ 2) ^ (s - 2) := by
      apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
      rw [hx, hk2]; linarith
    have e3 : (|(k : ℝ)| ^ 2) ^ (s - 2) = |(k : ℝ)| ^ (-(4 - 2 * s)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hk0.le]
      congr 1; push_cast; ring
    linarith
  have : ∀ᶠ k : ℤ in cofinite, k ≠ 0 := by
    simpa using (Set.finite_singleton (0 : ℤ)).compl_mem_cofinite
  filter_upwards [this] with k hk using hz k hk


section Conv

/-- Truncated coefficients `a_{h,k}^{-1/2} g_k 1_{|k|≤N}` for a generic rate family. -/
def alUhGen38 (Ah : ℕ → ℤ → ℝ) (N : ℕ) (g : ℤ → ℂ) (k : ℤ) : ℂ :=
  if |k| ≤ (N : ℤ) then (((Real.sqrt (Ah N k))⁻¹ : ℝ) : ℂ) * g k else 0

def alUGen38 (A : ℤ → ℝ) (g : ℤ → ℂ) (k : ℤ) : ℂ := (((Real.sqrt (A k))⁻¹ : ℝ) : ℂ) * g k

theorem norm_sq_coef38 (c : ℝ) (z : ℂ) : ‖((c : ℝ) : ℂ) * z‖ ^ 2 = c ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_mul, Complex.norm_real, mul_pow, Real.norm_eq_abs, sq_abs]

/-- Deterministic dominated convergence: `U_h → U` in `H^s` whenever `Σ ⟨k⟩^{2s}|g_k|²/B_k < ∞`,
`0 < B ≤ A`, eventually `B_k ≤ a_{h,k}` for `|k| ≤ N`, and `a_{h,k} → A_k`. -/
theorem alSobolev_tendsto_gen38 (s : ℝ) (Ah : ℕ → ℤ → ℝ) (A B : ℤ → ℝ) (g : ℤ → ℂ)
    (hB : ∀ k, 0 < B k) (hBA : ∀ k, B k ≤ A k)
    (hBh : ∀ᶠ N : ℕ in atTop, ∀ k : ℤ, |k| ≤ (N : ℤ) → B k ≤ Ah N k)
    (hlim : ∀ k, Tendsto (fun N : ℕ => Ah N k) atTop (𝓝 (A k)))
    (hg : Summable (fun k : ℤ => sobolevModeWeight s k * ‖g k‖ ^ 2 / B k)) :
    Tendsto (fun N : ℕ => (seqRealization38 (sobolevModeWeight s) (alUhGen38 Ah N g) : SobolevHilbert s))
      atTop (𝓝 (seqRealization38 (sobolevModeWeight s) (alUGen38 A g) : SobolevHilbert s)) := by
  set w := sobolevModeWeight s with hwdef
  have hwpos : ∀ k, 0 < w k := (inferInstance : Fact (∀ n : ℤ, 0 < sobolevModeWeight s n)).out
  have hApos : ∀ k, 0 < A k := fun k => (hB k).trans_le (hBA k)
  have hsumU : Summable (fun k => w k * ‖alUGen38 A g k‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg (hwpos k).le (sq_nonneg _)) (fun k => ?_) hg
    unfold alUGen38
    rw [norm_sq_coef38, inv_pow, Real.sq_sqrt (hApos k).le]
    have : w k * ((A k)⁻¹ * ‖g k‖ ^ 2) = w k * ‖g k‖ ^ 2 / A k := by ring
    rw [this]
    exact div_le_div_of_nonneg_left (by have := hwpos k; positivity) (hB k) (hBA k)
  have hsumUh : ∀ N, Summable (fun k => w k * ‖alUhGen38 Ah N g k‖ ^ 2) := by
    intro N
    apply summable_of_ne_finset_zero (s := Finset.Icc (-(N : ℤ)) N)
    intro k hk
    have : ¬ |k| ≤ (N : ℤ) := by
      intro h; apply hk; rw [Finset.mem_Icc]; exact abs_le.mp h
    simp [alUhGen38, this]
  set F : ℕ → ℤ → ℝ := fun N k => w k * ‖alUhGen38 Ah N g k - alUGen38 A g k‖ ^ 2 with hF
  have hdom : ∀ᶠ N : ℕ in atTop, ∀ k, ‖F N k‖ ≤ 2 * (w k * ‖g k‖ ^ 2 / B k) := by
    filter_upwards [hBh] with N hN k
    have hwk := hwpos k
    have hq : (Real.sqrt (A k))⁻¹ ^ 2 ≤ (B k)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt (hApos k).le]
      exact inv_anti₀ (hB k) (hBA k)
    rw [Real.norm_of_nonneg (by positivity)]
    by_cases hk : |k| ≤ (N : ℤ)
    · have hah := hN k hk
      have hahpos : 0 < Ah N k := lt_of_lt_of_le (hB k) hah
      have hp : (Real.sqrt (Ah N k))⁻¹ ^ 2 ≤ (B k)⁻¹ := by
        rw [inv_pow, Real.sq_sqrt hahpos.le]
        exact inv_anti₀ (hB k) hah
      simp only [hF, alUhGen38, alUGen38, hk, ↓reduceIte]
      rw [← sub_mul, ← Complex.ofReal_sub, norm_sq_coef38]
      have hp0 : 0 ≤ (Real.sqrt (Ah N k))⁻¹ := by positivity
      have hq0 : 0 ≤ (Real.sqrt (A k))⁻¹ := by positivity
      have hsq : ((Real.sqrt (Ah N k))⁻¹ - (Real.sqrt (A k))⁻¹) ^ 2 ≤ 2 * (B k)⁻¹ := by
        nlinarith [mul_nonneg hp0 hq0]
      calc w k * (((Real.sqrt (Ah N k))⁻¹ - (Real.sqrt (A k))⁻¹) ^ 2 * ‖g k‖ ^ 2)
          ≤ w k * ((2 * (B k)⁻¹) * ‖g k‖ ^ 2) := by gcongr
        _ = 2 * (w k * ‖g k‖ ^ 2 / B k) := by field_simp
    · simp only [hF, alUhGen38, alUGen38, hk, ↓reduceIte, zero_sub, norm_neg]
      rw [norm_sq_coef38]
      have : w k * ((Real.sqrt (A k))⁻¹ ^ 2 * ‖g k‖ ^ 2) ≤ w k * ‖g k‖ ^ 2 / B k := by
        calc w k * ((Real.sqrt (A k))⁻¹ ^ 2 * ‖g k‖ ^ 2) ≤ w k * ((B k)⁻¹ * ‖g k‖ ^ 2) := by gcongr
          _ = _ := by field_simp
      have h0 : 0 ≤ w k * ‖g k‖ ^ 2 / B k := by have := hB k; positivity
      linarith
  have hpt : ∀ k, Tendsto (fun N => F N k) atTop (𝓝 0) := by
    intro k
    have hlim' : Tendsto (fun N : ℕ => (Real.sqrt (Ah N k))⁻¹) atTop (𝓝 ((Real.sqrt (A k))⁻¹)) :=
      ((hlim k).sqrt).inv₀ (Real.sqrt_pos.2 (hApos k)).ne'
    have h2 : Tendsto (fun N : ℕ => w k * (((Real.sqrt (Ah N k))⁻¹ - (Real.sqrt (A k))⁻¹) ^ 2 *
        ‖g k‖ ^ 2)) atTop (𝓝 (w k * (((Real.sqrt (A k))⁻¹ - (Real.sqrt (A k))⁻¹) ^ 2 * ‖g k‖ ^ 2))) :=
      ((((hlim'.sub_const _).pow 2).mul_const _).const_mul _)
    rw [sub_self] at h2
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, mul_zero] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop k.natAbs] with N hN
    have hk : |k| ≤ (N : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast hN
    simp only [hF, alUhGen38, alUGen38, hk, ↓reduceIte]
    rw [← sub_mul, ← Complex.ofReal_sub, norm_sq_coef38]
  have hT : Tendsto (fun N => ∑' k, F N k) atTop (𝓝 0) := by
    have := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (f := F) (g := fun _ => (0 : ℝ))
      (hg.mul_left 2) hpt hdom
    simpa using this
  rw [tendsto_iff_dist_tendsto_zero]
  have hd : ∀ N, dist (seqRealization38 (sobolevModeWeight s) (alUhGen38 Ah N g) : SobolevHilbert s)
      (seqRealization38 (sobolevModeWeight s) (alUGen38 A g)) =
      Real.sqrt (∑' k, F N k) := by
    intro N
    rw [dist_eq_norm, ← Real.sqrt_sq (norm_nonneg _)]
    rw [seqRealization_dist_sq38 w _ _ (hsumUh N) hsumU]
  simp_rw [hd]
  simpa using hT.sqrt

end Conv

section Rates

/-- Comparison rate `B_k = m (1 + k⁴)`, `m = min(β₀/2, 256 β₂)`. -/
def alQ4B38 (β₀ β₂ : ℝ) (k : ℤ) : ℝ := min (β₀ / 2) (256 * β₂) * (1 + (k : ℝ) ^ 4)

theorem alQ4B_pos38 {β₀ β₂ : ℝ} (h0 : 0 < β₀) (h2 : 0 < β₂) (k : ℤ) : 0 < alQ4B38 β₀ β₂ k := by
  unfold alQ4B38
  have : 0 < min (β₀ / 2) (256 * β₂) := lt_min (by linarith) (by linarith)
  positivity

theorem alQ4B_le_symbol38 {β₀ β₁ β₂ : ℝ} (h0 : 0 < β₀) (h1 : 0 ≤ β₁) (h2 : 0 ≤ β₂) {N : ℕ}
    (hh : alh38 N ≤ β₀ / 2) {k : ℤ} (hk : |k| ≤ (N : ℤ)) :
    alQ4B38 β₀ β₂ k ≤ alSymbol38 β₀ β₁ β₂ N k := by
  obtain ⟨hb, -⟩ := alOmega_abs_bounds38 N k hk
  have hw : alomega38 N k = alOmegaFree38 N k := rfl
  unfold alSymbol38 alQ4B38
  rw [hw]
  set ω := alOmegaFree38 N k
  have h4 : (4 * |(k : ℝ)|) ^ 4 ≤ ω ^ 4 := by
    have := pow_le_pow_left₀ (by positivity) hb 4
    rwa [Even.pow_abs (by decide)] at this
  have h5 : (4 * |(k : ℝ)|) ^ 4 = 256 * (k : ℝ) ^ 4 := by
    rw [mul_pow, Even.pow_abs (by decide)]; norm_num
  rw [h5] at h4
  have hm1 : min (β₀ / 2) (256 * β₂) ≤ β₀ / 2 := min_le_left _ _
  have hm2 : min (β₀ / 2) (256 * β₂) ≤ 256 * β₂ := min_le_right _ _
  have hk4 : 0 ≤ (k : ℝ) ^ 4 := by positivity
  have hm0 : 0 ≤ min (β₀ / 2) (256 * β₂) := le_min (by linarith) (by linarith)
  have h6 : β₂ * (256 * (k : ℝ) ^ 4) ≤ β₂ * ω ^ 4 := mul_le_mul_of_nonneg_left h4 h2
  have h7 : 0 ≤ β₁ * ω ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hm2 hk4]

theorem alQ4B_le_rateC38 {β₀ β₁ β₂ : ℝ} (h0 : 0 < β₀) (h1 : 0 ≤ β₁) (h2 : 0 ≤ β₂) (k : ℤ) :
    alQ4B38 β₀ β₂ k ≤ alQ4RateC38 β₀ β₁ β₂ k := by
  unfold alQ4RateC38 alQ4B38
  have hm1 : min (β₀ / 2) (256 * β₂) ≤ β₀ / 2 := min_le_left _ _
  have hm2 : min (β₀ / 2) (256 * β₂) ≤ 256 * β₂ := min_le_right _ _
  have hk4 : 0 ≤ (k : ℝ) ^ 4 := by positivity
  have hpi : (6 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have h4 : 256 * (k : ℝ) ^ 4 ≤ (2 * Real.pi * (k : ℝ)) ^ 4 := by
    rw [mul_pow]
    have : (256 : ℝ) ≤ (2 * Real.pi) ^ 4 := by nlinarith [pow_le_pow_left₀ (by norm_num) hpi 4]
    exact mul_le_mul_of_nonneg_right this hk4
  have h7 : 0 ≤ β₁ * (2 * Real.pi * (k : ℝ)) ^ 2 := by positivity
  have h6 : β₂ * (256 * (k : ℝ) ^ 4) ≤ β₂ * (2 * Real.pi * (k : ℝ)) ^ 4 :=
    mul_le_mul_of_nonneg_left h4 h2
  nlinarith [mul_le_mul_of_nonneg_right hm2 hk4]

theorem alQ4RateC_pos38 {β₀ β₁ β₂ : ℝ} (h0 : 0 < β₀) (h1 : 0 ≤ β₁) (h2 : 0 < β₂) (k : ℤ) :
    0 < alQ4RateC38 β₀ β₁ β₂ k :=
  (alQ4B_pos38 h0 h2 k).trans_le (alQ4B_le_rateC38 h0 h1 h2.le k)

theorem alQ4Symbol_tendsto38 (β₀ β₁ β₂ : ℝ) (k : ℤ) :
    Tendsto (fun N : ℕ => alSymbol38 β₀ β₁ β₂ N k) atTop (𝓝 (alQ4RateC38 β₀ β₁ β₂ k)) := by
  have hω : Tendsto (fun N : ℕ => alomega38 N k) atTop (𝓝 (2 * Real.pi * (k : ℝ))) :=
    alOmega_tendsto38 k
  have hh : Tendsto (fun N : ℕ => alh38 N) atTop (𝓝 0) := alMeshStep_tendsto38
  have := ((tendsto_const_nhds (x := β₀)).sub hh).add ((hω.pow 2).const_mul β₁) |>.add
    ((hω.pow 4).const_mul β₂)
  simpa [alSymbol38, alQ4RateC38] using this

theorem alh_eventually_le38 {β₀ : ℝ} (h0 : 0 < β₀) : ∀ᶠ N : ℕ in atTop, alh38 N ≤ β₀ / 2 :=
  (alMeshStep_tendsto38.eventually (ge_mem_nhds (by linarith : (0 : ℝ) < β₀ / 2)))

theorem alQ4B_summable38 {β₀ β₂ : ℝ} (h0 : 0 < β₀) (h2 : 0 < β₂) (s : ℝ) (hs : s < 3 / 2) :
    Summable (fun k : ℤ => sobolevModeWeight s k / alQ4B38 β₀ β₂ k) := by
  have hm : 0 < min (β₀ / 2) (256 * β₂) := lt_min (by linarith) (by linarith)
  have := (summable_sobolev_div_quartic38 s hs).mul_left (min (β₀ / 2) (256 * β₂))⁻¹
  refine this.congr (fun k => ?_)
  unfold alQ4B38
  field_simp

end Rates

section Sample

theorem alSample_eq_alQ4V38 {N : ℕ} (x : SobolevHilbert 1) (hx : alInF38 N x)
    (û : ZMod (2 * N + 1) → ℂ)
    (hc : ∀ k : ℤ, |k| ≤ (N : ℤ) → alCoefH1_38 x k = û ((k : ℤ) : ZMod (2 * N + 1))) :
    alSample38 N x = alQ4V38 N û := by
  have hh : ((alh38 N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (alh38_pos N).ne'
  set α : ZMod (2 * N + 1) → ℂ := fun j => ((alh38 N : ℝ) : ℂ) * alSample38 N x j with hα
  have hdft : ZMod.dft α = û := by
    funext k
    have e := alDFT_eq_dft38 N α k
    have hfun : (fun j => ((alh38 N : ℝ) : ℂ)⁻¹ * α j) = alSample38 N x := by
      funext j; rw [hα]; field_simp
    rw [hfun] at e
    rw [← e]
    obtain ⟨i, hi⟩ := modeIndex_covers N k.valMinAbs
      (by have := valMinAbs_mem_Icc38 N k; rw [Finset.mem_Icc] at this; exact this.1)
      (by have := valMinAbs_mem_Icc38 N k; rw [Finset.mem_Icc] at this; exact this.2)
    rw [← hi, alSample_plane38 hx, alDFT_plane38 N _ i]
    have := hc (modeIndex N i) (by rw [hi]; have := valMinAbs_mem_Icc38 N k
                                   rw [Finset.mem_Icc] at this; rw [abs_le]; exact this)
    have h2 : alCoefH1_38 x (modeIndex N i) = physicalH1FiniteProjectionPlane N x i := rfl
    rw [← h2, this, hi, ZMod.coe_valMinAbs]
  have hα' : α = ZMod.dft.symm û := by rw [← hdft]; simp
  funext j
  unfold alQ4V38
  rw [← hα', hα]
  field_simp

end Sample

section Realization

/-- `U_h = Σ_{|k|≤N} g_k a_{h,k}^{-1/2} e_k` realized in `H^s` (`a_{h,k} = alSymbol38`). -/
def alQ4UhReal38 (s : ℝ) (β₀ β₁ β₂ : ℝ) (N : ℕ) (g : ℤ → ℂ) : SobolevHilbert s :=
  seqRealization38 (sobolevModeWeight s) (alUhGen38 (alSymbol38 β₀ β₁ β₂) N g)

/-- `U = Σ_k g_k a_k^{-1/2} e_k` realized in `H^s` (totalized: `0` off the summability event). -/
def alQ4UReal38 (s : ℝ) (β₀ β₁ β₂ : ℝ) (g : ℤ → ℂ) : SobolevHilbert s :=
  seqRealization38 (sobolevModeWeight s) (alQ4UCoef38 β₀ β₁ β₂ g)

theorem alQ4_sobolev_ae38 {β₀ β₁ β₂ : ℝ} (h0 : 0 < β₀) (h1 : 0 ≤ β₁) (h2 : 0 < β₂) (s : ℝ)
    (hs : s < 3 / 2) :
    ∀ᵐ g ∂alFreeLaw38, Tendsto (fun N : ℕ => alQ4UhReal38 s β₀ β₁ β₂ N g) atTop
      (𝓝 (alQ4UReal38 s β₀ β₁ β₂ g)) := by
  have hae : ∀ᵐ g ∂alFreeLaw38,
      Summable (fun k : ℤ => (sobolevModeWeight s k / alQ4B38 β₀ β₂ k) * ‖g k‖ ^ 2) := by
    apply NlsGge.Measure.ae_sequenceSummable (fun _ => (1 : ℝ)) _ (fun _ => one_pos)
    · intro k
      have : 0 < sobolevModeWeight s k :=
        (inferInstance : Fact (∀ n : ℤ, 0 < sobolevModeWeight s n)).out k
      have := alQ4B_pos38 h0 h2 k
      positivity
    · simpa using alQ4B_summable38 h0 h2 s hs
  filter_upwards [hae] with g hg
  refine alSobolev_tendsto_gen38 s (alSymbol38 β₀ β₁ β₂) (alQ4RateC38 β₀ β₁ β₂) (alQ4B38 β₀ β₂) g
    (alQ4B_pos38 h0 h2) (alQ4B_le_rateC38 h0 h1 h2.le) ?_ (alQ4Symbol_tendsto38 β₀ β₁ β₂) ?_
  · filter_upwards [alh_eventually_le38 h0] with N hN k hk
    exact alQ4B_le_symbol38 h0 h1 h2.le hN hk
  · refine hg.congr (fun k => ?_)
    ring

theorem alQ4UhReal_coef38 (s β₀ β₁ β₂ : ℝ) (N : ℕ) (g : ℤ → ℂ) (n : ℤ) :
    (show WeightedHilbert (sobolevModeWeight s) from alQ4UhReal38 s β₀ β₁ β₂ N g) n =
      alUhGen38 (alSymbol38 β₀ β₁ β₂) N g n := by
  have hsum : Summable (fun k : ℤ => sobolevModeWeight s k *
      ‖alUhGen38 (alSymbol38 β₀ β₁ β₂) N g k‖ ^ 2) := by
    apply summable_of_ne_finset_zero (s := Finset.Icc (-(N : ℤ)) N)
    intro k hk
    have : ¬ |k| ≤ (N : ℤ) := by
      intro h; apply hk; rw [Finset.mem_Icc]; exact abs_le.mp h
    simp [alUhGen38, this]
  exact seqRealization_apply38 _ _ hsum n

theorem alQ4UhReal_inF38 (β₀ β₁ β₂ : ℝ) (N : ℕ) (g : ℤ → ℂ) :
    alInF38 N (alQ4UhReal38 1 β₀ β₁ β₂ N g) := by
  intro n hn
  have h := alQ4UhReal_coef38 1 β₀ β₁ β₂ N g n
  have hk : ¬ |n| ≤ (N : ℤ) := by
    intro h'; apply hn
    simp only [symmetricModes, Finset.mem_Icc]; exact abs_le.mp h'
  change (show WeightedHilbert (sobolevModeWeight 1) from alQ4UhReal38 1 β₀ β₁ β₂ N g) n = 0
  rw [h]; simp [alUhGen38, hk]

theorem alQ4Hat_coef38 (β₀ β₁ β₂ : ℝ) (N : ℕ) (g : ℤ → ℂ) (k : ℤ) (hk : |k| ≤ (N : ℤ)) :
    alUhGen38 (alSymbol38 β₀ β₁ β₂) N g k =
      alQ4Hat38 β₀ β₁ β₂ N g ((k : ℤ) : ZMod (2 * N + 1)) := by
  have hk' := abs_le.mp hk
  unfold alUhGen38 alQ4Hat38
  simp only [hk, ↓reduceIte]
  rw [valMinAbs_intCast38 N k hk'.1 hk'.2]

theorem alQ4F_limit_ae38 {β₀ β₁ β₂ : ℝ} (h0 : 0 < β₀) (h1 : 0 ≤ β₁) (h2 : 0 < β₂) :
    ∀ᵐ g ∂alFreeLaw38, Tendsto
      (fun N : ℕ => alQ4F38 β₀ β₁ β₂ N (alQ4V38 N (alQ4Hat38 β₀ β₁ β₂ N g))) atTop
      (𝓝 (Real.exp (-alV2_38 β₁ β₂ (alQ4UReal38 1 β₀ β₁ β₂ g)))) := by
  filter_upwards [alQ4_sobolev_ae38 h0 h1 h2 1 (by norm_num)] with g hg
  obtain ⟨hdisk, hR⟩ := alSampling38 β₀ β₁ β₂ (fun N => alQ4UhReal38 1 β₀ β₁ β₂ N g)
    (alQ4UReal38 1 β₀ β₁ β₂ g) (fun N => alQ4UhReal_inF38 β₀ β₁ β₂ N g) hg
  have hS : ∀ N, alSample38 N (alQ4UhReal38 1 β₀ β₁ β₂ N g) =
      alQ4V38 N (alQ4Hat38 β₀ β₁ β₂ N g) := by
    intro N
    refine alSample_eq_alQ4V38 _ (alQ4UhReal_inF38 β₀ β₁ β₂ N g) _ (fun k hk => ?_)
    exact (alQ4UhReal_coef38 1 β₀ β₁ β₂ N g k).trans (alQ4Hat_coef38 β₀ β₁ β₂ N g k hk)
  simp only [hS] at hdisk hR
  have hE := (Real.continuous_exp.tendsto _).comp hR.neg
  refine hE.congr' ?_
  filter_upwards [hdisk] with N hN
  simp only [Function.comp]
  simp [alQ4F38, hN]

end Realization

section V2

theorem continuous_alV2_38 (β₁ β₂ : ℝ) : Continuous (alV2_38 β₁ β₂) := by
  unfold alV2_38
  exact (continuous_const.mul
    (continuous_physicalH1QuarticIntegralAfterScalarL1Prerequisites.comp
      (physicalH1CanonicalContinuousRepresentativeCLM).continuous)).add
    (continuous_const.mul continuous_physicalH1Q4LowerOrderRemainderAfterCanonicalComponents)

/-- `V₂ ≥ 0` for `β₁, β₂ ≥ 0` (every integrand in `C:eq:V2positive` is nonnegative). -/
theorem alV2_nonneg38 {β₁ β₂ : ℝ} (h1 : 0 ≤ β₁) (h2 : 0 ≤ β₂) (u : SobolevHilbert 1) :
    0 ≤ alV2_38 β₁ β₂ u := by
  obtain ⟨-, -, e⟩ := alV2_eq_integral38 β₁ β₂ u
  rw [e]
  have a1 : 0 ≤ ∫ t in (0 : ℝ)..1, ‖alCanon38 u t‖ ^ 4 :=
    intervalIntegral.integral_nonneg zero_le_one (fun t _ => by positivity)
  have a2 : 0 ≤ ∫ t in (0 : ℝ)..1, (2 * ‖alCanon38 u t‖ ^ 6
        + 6 * ‖alCanon38 u t‖ ^ 2 * ‖alDeriv38 u t‖ ^ 2
        + (2 * ((starRingEnd ℂ) (alCanon38 u t) * alDeriv38 u t).re) ^ 2) :=
    intervalIntegral.integral_nonneg zero_le_one (fun t _ => by positivity)
  positivity

end V2

section Interp

/-- Fourier coefficients (indexed by `ℤ`) of the interpolant: `û(k)` for `|k| ≤ N`, `0` otherwise. -/
def alQ4Ext38 (N : ℕ) (û : ZMod (2 * N + 1) → ℂ) : ℤ → ℂ :=
  fun k => if |k| ≤ (N : ℤ) then û ((k : ℤ) : ZMod (2 * N + 1)) else 0

/-- The interpolant `I_h(α/h) = Σ_{|k|≤N} û(k) e_k` of a lattice configuration with Fourier
coordinates `û`, realized in `H^s` (a trigonometric polynomial, so in every `H^s`). -/
def alQ4Interp38 (s : ℝ) (N : ℕ) (û : ZMod (2 * N + 1) → ℂ) : SobolevHilbert s :=
  seqRealization38 (sobolevModeWeight s) (alQ4Ext38 N û)

theorem measurable_alQ4Ext38 (N : ℕ) : Measurable (alQ4Ext38 N) := by
  refine measurable_pi_iff.2 fun k => ?_
  by_cases hk : |k| ≤ (N : ℤ)
  · simp only [alQ4Ext38, hk, ↓reduceIte]
    exact measurable_pi_apply _
  · simp only [alQ4Ext38, hk, ↓reduceIte]
    exact measurable_const

theorem measurable_alQ4Interp38 (s : ℝ) (N : ℕ) : Measurable (alQ4Interp38 s N) :=
  (measurable_seqRealization38 (sobolevModeWeight s)).comp (measurable_alQ4Ext38 N)

theorem measurable_dft38 {L : ℕ} [NeZero L] :
    Measurable (fun α : ZMod L → ℂ => ZMod.dft α) := by
  refine measurable_pi_iff.2 fun k => ?_
  simp only [ZMod.dft_apply]
  refine Finset.measurable_sum _ fun j _ => ?_
  simp only [smul_eq_mul]
  exact measurable_const.mul (measurable_pi_apply j)

theorem measurable_alQ4Hat38 (β₀ β₁ β₂ : ℝ) (N : ℕ) : Measurable (alQ4Hat38 β₀ β₁ β₂ N) := by
  refine measurable_pi_iff.2 fun k => ?_
  exact measurable_const.mul (measurable_pi_apply _)

theorem alQ4Interp_Hat38 (s β₀ β₁ β₂ : ℝ) (N : ℕ) (g : ℤ → ℂ) :
    alQ4Interp38 s N (alQ4Hat38 β₀ β₁ β₂ N g) = alQ4UhReal38 s β₀ β₁ β₂ N g := by
  unfold alQ4Interp38 alQ4UhReal38
  congr 1
  funext k
  by_cases hk : |k| ≤ (N : ℤ)
  · simp only [alQ4Ext38, hk, ↓reduceIte]
    exact (alQ4Hat_coef38 β₀ β₁ β₂ N g k hk).symm
  · simp [alQ4Ext38, alUhGen38, hk]

end Interp

section Rho

/-- `V₂` evaluated on a Fourier coefficient sequence through its `H¹` realization. -/
def alQ4V2Seq38 (β₁ β₂ : ℝ) (z : ℤ → ℂ) : ℝ :=
  alV2_38 β₁ β₂ (seqRealization38 (sobolevModeWeight 1) z)

theorem measurable_alQ4V2Seq38 (β₁ β₂ : ℝ) : Measurable (alQ4V2Seq38 β₁ β₂) :=
  (continuous_alV2_38 β₁ β₂).measurable.comp (measurable_seqRealization38 _)

/-- The order-two Gaussian `γ₂ = γ_2^F` (`B:eq:finitehierarchy`, `m = 2`, rates `a_k = W₂(2πk)`). -/
abbrev alQ4Gamma2_38 (β₀ β₁ β₂ : ℝ) : Measure (ℤ → ℂ) := gammaM38 2 (alQ4Beta38 β₀ β₁ β₂)

/-- `Z₂ = E_{γ₂} e^{-V₂}` (`C:eq:rho2`). -/
def alQ4Z2_38 (β₀ β₁ β₂ : ℝ) : ℝ :=
  ∫ z, Real.exp (-alQ4V2Seq38 β₁ β₂ z) ∂(alQ4Gamma2_38 β₀ β₁ β₂)

/-- **`ρ₂ = Z₂⁻¹ e^{-V₂} γ₂^F`** on `H^s` (paper/v2.tex l.2027-2039): the Gaussian `γ₂` on coefficient
sequences, reweighted by `e^{-V₂}` (with `V₂` of the `H¹` realization of the sequence, `V₂ ≥ 0`
continuous on `H¹`), normalised by `Z₂`, and transported to `H^s` by the realization map. -/
def alQ4Rho38 (s : ℝ) (β₀ β₁ β₂ : ℝ) : Measure (SobolevHilbert s) :=
  ENNReal.ofReal (alQ4Z2_38 β₀ β₁ β₂)⁻¹ •
    (((alQ4Gamma2_38 β₀ β₁ β₂).withDensity
      fun z => ENNReal.ofReal (Real.exp (-alQ4V2Seq38 β₁ β₂ z))).map
        (seqRealization38 (sobolevModeWeight s)))

variable {β₀ β₁ β₂ : ℝ}

theorem alQ4_coupling_integral38 (h0 : 0 < β₀) (h1 : 0 ≤ β₁) (h2 : 0 < β₂)
    (F : (ℤ → ℂ) → ℝ) (hF : Measurable F) :
    ∫ z, F z ∂(alQ4Gamma2_38 β₀ β₁ β₂) = ∫ g, F (alQ4UCoef38 β₀ β₁ β₂ g) ∂alFreeLaw38 := by
  show ∫ z, F z ∂(gammaM38 2 (alQ4Beta38 β₀ β₁ β₂)) = _
  rw [← alQ4UCoef_law38 β₀ β₁ β₂ (alQ4RateC_pos38 h0 h1 h2)]
  have hm : Measurable (alQ4UCoef38 β₀ β₁ β₂) := by
    refine measurable_pi_iff.2 fun k => ?_
    exact measurable_const.mul (measurable_pi_apply _)
  exact integral_map hm.aemeasurable hF.aestronglyMeasurable

theorem alQ4Z2_eq38 (h0 : 0 < β₀) (h1 : 0 ≤ β₁) (h2 : 0 < β₂) :
    alQ4Z2_38 β₀ β₁ β₂ =
      ∫ g, Real.exp (-alV2_38 β₁ β₂ (alQ4UReal38 1 β₀ β₁ β₂ g)) ∂alFreeLaw38 := by
  unfold alQ4Z2_38
  exact alQ4_coupling_integral38 h0 h1 h2 _ (measurable_alQ4V2Seq38 β₁ β₂).neg.exp

theorem alQ4Z2_pos38 (h0 : 0 < β₀) (h1 : 0 ≤ β₁) (h2 : 0 < β₂) : 0 < alQ4Z2_38 β₀ β₁ β₂ := by
  unfold alQ4Z2_38
  refine integral_exp_pos (f := fun z => -alQ4V2Seq38 β₁ β₂ z) ?_
  refine Integrable.of_bound (measurable_alQ4V2Seq38 β₁ β₂).neg.exp.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
  have := alV2_nonneg38 h1 h2.le (seqRealization38 (sobolevModeWeight 1) z)
  unfold alQ4V2Seq38; linarith

theorem alQ4Rho_integral38 (h0 : 0 < β₀) (h1 : 0 ≤ β₁) (h2 : 0 < β₂) (s : ℝ)
    (φ : SobolevHilbert s → ℝ) (hφ : Measurable φ) :
    ∫ x, φ x ∂(alQ4Rho38 s β₀ β₁ β₂) =
      (alQ4Z2_38 β₀ β₁ β₂)⁻¹ * ∫ g, φ (alQ4UReal38 s β₀ β₁ β₂ g) *
        Real.exp (-alV2_38 β₁ β₂ (alQ4UReal38 1 β₀ β₁ β₂ g)) ∂alFreeLaw38 := by
  have hZ := alQ4Z2_pos38 h0 h1 h2
  have hm : Measurable (fun z : ℤ → ℂ => ENNReal.ofReal (Real.exp (-alQ4V2Seq38 β₁ β₂ z))) :=
    ENNReal.measurable_ofReal.comp (measurable_alQ4V2Seq38 β₁ β₂).neg.exp
  unfold alQ4Rho38
  rw [integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.2 hZ.le), smul_eq_mul]
  congr 1
  rw [integral_map (measurable_seqRealization38 _).aemeasurable hφ.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hm
      (Filter.Eventually.of_forall fun z => ENNReal.ofReal_lt_top)]
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  have := alQ4_coupling_integral38 h0 h1 h2
    (fun z => Real.exp (-alQ4V2Seq38 β₁ β₂ z) * φ (seqRealization38 (sobolevModeWeight s) z))
    (((measurable_alQ4V2Seq38 β₁ β₂).neg.exp).mul
      (hφ.comp (measurable_seqRealization38 _)))
  rw [this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [alQ4V2Seq38, alQ4UReal38]
  ring

theorem isProbabilityMeasure_alQ4Rho38 (h0 : 0 < β₀) (h1 : 0 ≤ β₁) (h2 : 0 < β₂) (s : ℝ) :
    IsProbabilityMeasure (alQ4Rho38 s β₀ β₁ β₂) := by
  refine ⟨?_⟩
  have hZ := alQ4Z2_pos38 h0 h1 h2
  have hint : Integrable (fun z => Real.exp (-alQ4V2Seq38 β₁ β₂ z)) (alQ4Gamma2_38 β₀ β₁ β₂) := by
    refine Integrable.of_bound (measurable_alQ4V2Seq38 β₁ β₂).neg.exp.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
    have := alV2_nonneg38 h1 h2.le (seqRealization38 (sobolevModeWeight 1) z)
    unfold alQ4V2Seq38; linarith
  unfold alQ4Rho38
  rw [Measure.smul_apply, Measure.map_apply (measurable_seqRealization38 _) MeasurableSet.univ,
    Set.preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun z => (Real.exp_pos _).le)]
  change ENNReal.ofReal (alQ4Z2_38 β₀ β₁ β₂)⁻¹ • ENNReal.ofReal (alQ4Z2_38 β₀ β₁ β₂) = 1
  rw [smul_eq_mul, ← ENNReal.ofReal_mul (inv_nonneg.2 hZ.le), inv_mul_cancel₀ hZ.ne',
    ENNReal.ofReal_one]

end Rho

section Finite

variable {β₀ β₁ β₂ : ℝ}

/-- Law of the interpolant of `η_h` in `H^s`: the pushforward of `η_h` under
`α ↦ I_h(α/h) = Σ_{|k|≤N} (𝓕α)(k) e_k`. -/
def alQ4Mu38 (s : ℝ) (β₀ β₁ β₂ : ℝ) (N : ℕ) : Measure (SobolevHilbert s) :=
  (alQ4Eta38 β₀ β₁ β₂ N).map (fun α => alQ4Interp38 s N (ZMod.dft α))

theorem measurable_alQ4InterpDft38 (s : ℝ) (N : ℕ) :
    Measurable (fun α : ZMod (2 * N + 1) → ℂ => alQ4Interp38 s N (ZMod.dft α)) :=
  (measurable_alQ4Interp38 s N).comp measurable_dft38

theorem isProbabilityMeasure_alQ4Mu38 (h0 : 0 < β₀) (h1 : 0 ≤ β₁) (h2 : 0 ≤ β₂) (s : ℝ) (N : ℕ) :
    IsProbabilityMeasure (alQ4Mu38 s β₀ β₁ β₂ N) := by
  have := isProbabilityMeasure_alQ4Eta38 h0 h1 h2 N
  unfold alQ4Mu38
  infer_instance

theorem alQ4Gauss_eq_map38 (h1 : 0 ≤ β₁) (h2 : 0 ≤ β₂) {N : ℕ} (hh : alh38 N < β₀) :
    (alFreeLaw38).map (alQ4Hat38 β₀ β₁ β₂ N) = alQ4Gauss38 β₀ β₁ β₂ N :=
  alQ4Hat_law38 β₀ β₁ β₂ N (fun k _ => alSymbol38_pos h1 h2 N hh k)

/-- `Z_h = E_P f_h(V Û_N)` on the coupling space. -/
theorem alQ4Z_coupling38 (h1 : 0 ≤ β₁) (h2 : 0 ≤ β₂) {N : ℕ} (hh : alh38 N < β₀) :
    alQ4Z38 β₀ β₁ β₂ N =
      ∫ g, alQ4F38 β₀ β₁ β₂ N (alQ4V38 N (alQ4Hat38 β₀ β₁ β₂ N g)) ∂alFreeLaw38 := by
  unfold alQ4Z38
  rw [← alQ4Gauss_eq_map38 h1 h2 hh]
  exact integral_map (measurable_alQ4Hat38 β₀ β₁ β₂ N).aemeasurable
    (meas_alQ4F_V38 β₀ β₁ β₂ N).aestronglyMeasurable

/-- **Law of the interpolant via the coupling**: for `φ` measurable on `H^s`,
`E_{μ_h} φ = Z_h⁻¹ E_P[φ(U_h) f_h(V Û_N)]`. -/
theorem alQ4Mu_integral38 (h1 : 0 ≤ β₁) (h2 : 0 ≤ β₂) {N : ℕ} (hN : 1 ≤ N) (hh : alh38 N < β₀)
    (s : ℝ) (φ : SobolevHilbert s → ℝ) (hφ : Measurable φ) :
    ∫ x, φ x ∂(alQ4Mu38 s β₀ β₁ β₂ N) =
      (alQ4Z38 β₀ β₁ β₂ N)⁻¹ * ∫ g, φ (alQ4UhReal38 s β₀ β₁ β₂ N g) *
        alQ4F38 β₀ β₁ β₂ N (alQ4V38 N (alQ4Hat38 β₀ β₁ β₂ N g)) ∂alFreeLaw38 := by
  unfold alQ4Mu38
  rw [integral_map (measurable_alQ4InterpDft38 s N).aemeasurable hφ.aestronglyMeasurable]
  have := alQ4Eta_integral38 (β₀ := β₀) h1 h2 hN hh (fun û => φ (alQ4Interp38 s N û))
  rw [this]
  congr 1
  rw [← alQ4Gauss_eq_map38 h1 h2 hh]
  have hmeas : Measurable (fun û : ZMod (2 * N + 1) → ℂ => φ (alQ4Interp38 s N û) *
      alQ4F38 β₀ β₁ β₂ N (alQ4V38 N û)) :=
    (hφ.comp (measurable_alQ4Interp38 s N)).mul (meas_alQ4F_V38 β₀ β₁ β₂ N)
  rw [integral_map (measurable_alQ4Hat38 β₀ β₁ β₂ N).aemeasurable hmeas.aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [alQ4Interp_Hat38]

end Finite

section Main

variable {β₀ β₁ β₂ : ℝ}

theorem alQ4_eventually_good38 (h0 : 0 < β₀) : ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ alh38 N < β₀ := by
  have h1 : ∀ᶠ N : ℕ in atTop, alh38 N ≤ β₀ / 2 := alh_eventually_le38 h0
  filter_upwards [h1, eventually_ge_atTop 1] with N hN hN1
  exact ⟨hN1, by linarith⟩

/-- **`Z_h → Z₂ > 0`** (`C:thm:AL`, normalizer claim). -/
theorem alQ4Z_tendsto38 (h0 : 0 < β₀) (h1 : 0 ≤ β₁) (h2 : 0 < β₂) :
    Tendsto (alQ4Z38 β₀ β₁ β₂) atTop (𝓝 (alQ4Z2_38 β₀ β₁ β₂)) := by
  rw [alQ4Z2_eq38 h0 h1 h2]
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := alFreeLaw38) (l := atTop)
    (F := fun N g => alQ4F38 β₀ β₁ β₂ N (alQ4V38 N (alQ4Hat38 β₀ β₁ β₂ N g)))
    (f := fun g => Real.exp (-alV2_38 β₁ β₂ (alQ4UReal38 1 β₀ β₁ β₂ g))) (fun _ => (1 : ℝ))
    (Filter.Eventually.of_forall fun N =>
      ((meas_alQ4F_V38 β₀ β₁ β₂ N).comp (measurable_alQ4Hat38 β₀ β₁ β₂ N)).aestronglyMeasurable)
    ?_ (integrable_const _) (alQ4F_limit_ae38 h0 h1 h2)
  · refine hlim.congr' ?_
    filter_upwards [alQ4_eventually_good38 h0] with N hN
    exact (alQ4Z_coupling38 h1 h2.le hN.2).symm
  · filter_upwards [alQ4_eventually_good38 h0] with N hN
    refine Filter.Eventually.of_forall fun g => ?_
    rw [Real.norm_of_nonneg (alQ4F_nonneg38 _ _ _ _ _)]
    exact alQ4F_le_one38 h1 h2.le hN.1 hN.2 _

/-- **Weak convergence of the interpolated laws** on `H^s`, `s < 3/2`, tested against bounded
continuous functions: `E_{η_h} φ(I_h) → E_{ρ₂} φ`. -/
theorem alQ4_weak_tendsto38 (h0 : 0 < β₀) (h1 : 0 ≤ β₁) (h2 : 0 < β₂) (s : ℝ) (hs : s < 3 / 2)
    (φ : BoundedContinuousFunction (SobolevHilbert s) ℝ) :
    Tendsto (fun N : ℕ => ∫ x, φ x ∂(alQ4Mu38 s β₀ β₁ β₂ N)) atTop
      (𝓝 (∫ x, φ x ∂(alQ4Rho38 s β₀ β₁ β₂))) := by
  have hφm : Measurable φ := φ.continuous.measurable
  rw [alQ4Rho_integral38 h0 h1 h2 s φ hφm]
  have hZ := alQ4Z_tendsto38 h0 h1 h2
  have hZpos := alQ4Z2_pos38 h0 h1 h2
  have hI := tendsto_integral_filter_of_dominated_convergence (μ := alFreeLaw38) (l := atTop)
    (F := fun N g => φ (alQ4UhReal38 s β₀ β₁ β₂ N g) *
      alQ4F38 β₀ β₁ β₂ N (alQ4V38 N (alQ4Hat38 β₀ β₁ β₂ N g)))
    (f := fun g => φ (alQ4UReal38 s β₀ β₁ β₂ g) *
      Real.exp (-alV2_38 β₁ β₂ (alQ4UReal38 1 β₀ β₁ β₂ g))) (fun _ => ‖φ‖)
    (Filter.Eventually.of_forall fun N => by
      have : Measurable (fun g => φ (alQ4UhReal38 s β₀ β₁ β₂ N g) *
          alQ4F38 β₀ β₁ β₂ N (alQ4V38 N (alQ4Hat38 β₀ β₁ β₂ N g))) := by
        have hm1 : Measurable (fun g => φ (alQ4UhReal38 s β₀ β₁ β₂ N g)) := by
          have e : (fun g => φ (alQ4UhReal38 s β₀ β₁ β₂ N g)) =
              fun g => φ (alQ4Interp38 s N (alQ4Hat38 β₀ β₁ β₂ N g)) := by
            funext g; rw [alQ4Interp_Hat38]
          rw [e]
          exact hφm.comp ((measurable_alQ4Interp38 s N).comp (measurable_alQ4Hat38 β₀ β₁ β₂ N))
        exact hm1.mul ((meas_alQ4F_V38 β₀ β₁ β₂ N).comp (measurable_alQ4Hat38 β₀ β₁ β₂ N))
      exact this.aestronglyMeasurable)
    ?_ (integrable_const _) ?_
  · have hfin := (hZ.inv₀ hZpos.ne').mul hI
    refine hfin.congr' ?_
    filter_upwards [alQ4_eventually_good38 h0] with N hN
    exact (alQ4Mu_integral38 h1 h2.le hN.1 hN.2 s φ hφm).symm
  · filter_upwards [alQ4_eventually_good38 h0] with N hN
    refine Filter.Eventually.of_forall fun g => ?_
    rw [norm_mul, Real.norm_of_nonneg (alQ4F_nonneg38 _ _ _ _ _)]
    calc _ ≤ ‖φ‖ * 1 := mul_le_mul (φ.norm_coe_le_norm _)
          (alQ4F_le_one38 h1 h2.le hN.1 hN.2 _) (alQ4F_nonneg38 _ _ _ _ _) (norm_nonneg _)
      _ = ‖φ‖ := mul_one _
  · filter_upwards [alQ4_sobolev_ae38 h0 h1 h2 s hs, alQ4F_limit_ae38 h0 h1 h2] with g hg hF
    exact ((φ.continuous.tendsto _).comp hg).mul hF

end Main

section Final

variable {β₀ β₁ β₂ : ℝ}

/-- `μ_h` as a `ProbabilityMeasure` on `H^s`. -/
def alQ4MuPM38 (h0 : 0 < β₀) (h1 : 0 ≤ β₁) (h2 : 0 ≤ β₂) (s : ℝ) (N : ℕ) :
    ProbabilityMeasure (SobolevHilbert s) :=
  ⟨alQ4Mu38 s β₀ β₁ β₂ N, isProbabilityMeasure_alQ4Mu38 h0 h1 h2 s N⟩

/-- `ρ₂` as a `ProbabilityMeasure` on `H^s`. -/
def alQ4RhoPM38 (h0 : 0 < β₀) (h1 : 0 ≤ β₁) (h2 : 0 < β₂) (s : ℝ) :
    ProbabilityMeasure (SobolevHilbert s) :=
  ⟨alQ4Rho38 s β₀ β₁ β₂, isProbabilityMeasure_alQ4Rho38 h0 h1 h2 s⟩

/-- Weak convergence of probability measures on `H^s`: `μ_h → ρ₂` in the topology of
`ProbabilityMeasure (SobolevHilbert s)`. -/
theorem alQ4_probMeasure_tendsto38 (h0 : 0 < β₀) (h1 : 0 ≤ β₁) (h2 : 0 < β₂) (s : ℝ)
    (hs : s < 3 / 2) :
    Tendsto (fun N : ℕ => alQ4MuPM38 h0 h1 h2.le s N) atTop (𝓝 (alQ4RhoPM38 h0 h1 h2 s)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro φ
  exact alQ4_weak_tendsto38 h0 h1 h2 s hs φ

/-- **`C:thm:AL` (limit half; paper/v2.tex l.2195-2218).**  For `β₀, β₁, β₂ > 0`, with `h = 1/(2N+1)`:

* `Z_h → Z₂ > 0`, where `Z_h = E_{γ_h} f_h` (`alQ4Z38`) and `Z₂ = E_{γ₂} e^{-V₂}` (`alQ4Z2_38`);
* for every `s < 3/2` the laws `μ_h` of the interpolants `I_h(α/h) = Σ_{|k|≤N} (𝓕α)(k) e_k`
  under `η_h` (`alQ4Mu38`, a probability measure on `H^s`) converge weakly to the probability
  measure `ρ₂ = Z₂⁻¹ e^{-V₂} γ₂^F` (`alQ4Rho38`).

The identification of `ρ₂` with the Fourier limit `μ₂` (`B:cor:identity`) is a separate claim (F05)
and is NOT proved here. -/
theorem alQ4Limit38 (h0 : 0 < β₀) (h1 : 0 < β₁) (h2 : 0 < β₂) :
    (Tendsto (alQ4Z38 β₀ β₁ β₂) atTop (𝓝 (alQ4Z2_38 β₀ β₁ β₂)) ∧ 0 < alQ4Z2_38 β₀ β₁ β₂) ∧
    ∀ s : ℝ, s < 3 / 2 →
      IsProbabilityMeasure (alQ4Rho38 s β₀ β₁ β₂) ∧
      (∀ N : ℕ, IsProbabilityMeasure (alQ4Mu38 s β₀ β₁ β₂ N)) ∧
      (∀ φ : BoundedContinuousFunction (SobolevHilbert s) ℝ,
        Tendsto (fun N : ℕ => ∫ x, φ x ∂(alQ4Mu38 s β₀ β₁ β₂ N)) atTop
          (𝓝 (∫ x, φ x ∂(alQ4Rho38 s β₀ β₁ β₂)))) ∧
      Tendsto (fun N : ℕ => alQ4MuPM38 h0 h1.le h2.le s N) atTop
        (𝓝 (alQ4RhoPM38 h0 h1.le h2 s)) :=
  ⟨⟨alQ4Z_tendsto38 h0 h1.le h2, alQ4Z2_pos38 h0 h1.le h2⟩, fun s hs =>
    ⟨isProbabilityMeasure_alQ4Rho38 h0 h1.le h2 s,
     fun N => isProbabilityMeasure_alQ4Mu38 h0 h1.le h2.le s N,
     fun φ => alQ4_weak_tendsto38 h0 h1.le h2 s hs φ,
     alQ4_probMeasure_tendsto38 h0 h1.le h2 s hs⟩⟩

end Final

end NlsGge.AblowitzLadik

#check @NlsGge.AblowitzLadik.alQ4Limit38
#check @NlsGge.AblowitzLadik.alQ4Z_tendsto38
#check @NlsGge.AblowitzLadik.alQ4_weak_tendsto38
#check @NlsGge.AblowitzLadik.alQ4_probMeasure_tendsto38
#check @NlsGge.AblowitzLadik.alQ4Rho_integral38
#check @NlsGge.AblowitzLadik.alQ4Mu_integral38
#check @NlsGge.AblowitzLadik.alQ4_sobolev_ae38
#check @NlsGge.AblowitzLadik.alQ4F_limit_ae38
#check @NlsGge.AblowitzLadik.alSobolev_tendsto_gen38
#check @NlsGge.AblowitzLadik.alSample_eq_alQ4V38
#check @NlsGge.AblowitzLadik.alQ4Rho38
#check @NlsGge.AblowitzLadik.alQ4Mu38
#check @NlsGge.AblowitzLadik.alQ4Z2_38
#print axioms NlsGge.AblowitzLadik.alQ4Limit38
#print axioms NlsGge.AblowitzLadik.alQ4Z_tendsto38
#print axioms NlsGge.AblowitzLadik.alQ4_weak_tendsto38
#print axioms NlsGge.AblowitzLadik.alQ4_probMeasure_tendsto38
#print axioms NlsGge.AblowitzLadik.alQ4Mu_integral38
#print axioms NlsGge.AblowitzLadik.alQ4F_limit_ae38
#print axioms NlsGge.AblowitzLadik.alSample_eq_alQ4V38
#print axioms NlsGge.AblowitzLadik.alQ4Rho_integral38
