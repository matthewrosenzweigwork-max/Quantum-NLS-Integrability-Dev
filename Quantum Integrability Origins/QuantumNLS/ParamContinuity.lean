import Mathlib
import QuantumNLS.FreeLimit
import QuantumNLS.RootMeasureContinuity

/-!
# R-043AB9AA `prop:root-full-mass`: joint continuity of `(lam, v) ↦ μ_{lam,v}` for `lam ≥ 0`

Source: `ROOT_measure_extensions.tex`, proof of `prop:root-full-mass` ("We spell out the parameter continuity used here ... Thus `(lam,v) ↦ μ_{lam,v}`
is jointly continuous for `lam > 0`. Continuity at `lam = 0` with varying unit input follows from the free-limit expansion and its uniform geometric
bounds on a bounded coupling interval, together with the same mass-one argument.").

* `fz_lam_sub_le`: `‖f_{lam,z}(w) − f_{lam',z}(w)‖ ≤ 2|lam−lam'|/η` on `|w| ≤ η⁻¹`, `lam,lam' ≤ η/4`, `‖e^{izL}‖ ≤ 1/16`;
* `tendsto_productSymbol`: `s_{lam_j}(z; v_j) → s_lam(z; v)` (dominated convergence for the series with the common geometric bound, termwise convergence from
  `RootMeasureContinuity.norm_kps_sub_le`), including `lam = 0` where `s_0 = 1 + e^{izL}`;
* `gFull` (`g_{lam,v}(z)` = `gStar` for `lam > 0`, `G_free` for `lam = 0`), `Gfree_sub_le` and `gFull_tendsto`: pointwise joint continuity of the limiting Cauchy transform;
* `tendsto_muKappa_joint`: if `lam_j → lam ≥ 0` and unit `v_j → v` then `μ_{lam_j,v_j} → μ_{lam,v}` weakly (`muKappa` of `FreeLimit`), via the frozen
  `CauchyLimitCriterion.tendsto_of_cauchy`.
Routing: the scope lists `FIN-EXT025-GP-10` for this node; here compactness is mathlib's Prokhorov theorem for the tight sequences produced by the
mass-one tail inequality (see `CauchyLimitCriterion`); no EXT-025 contract is used or assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace QuantumNLS.ParamContinuity

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.CauchyUniqueness (cauchyTransform)
open QuantumNLS.RootMeasureComplex (fz HighHalf norm_exp_izL_le norm_exp_le_four_thirds norm_exp_sub_one_le')
open QuantumNLS.RootMeasureConcentration (gStar gStar_spec)
open QuantumNLS.NormalizedTransfer (productSymbol symbolTerm orderedKernel)
open QuantumNLS.KernelDefinition (kernelProductSymbol)
open QuantumNLS.FreeLimit (freeMeasure freeProb muKappa muKappa_spec)
open QuantumNLS.BulkResponseActual (IsLimitingRapidityMeasure)

variable {L : ℝ} [Fact (0 < L)]

/-! ### Lipschitz dependence of `f_{lam,z}` on `lam` -/

theorem exp_sub_exp_le (a a' : ℂ) (h1 : ‖a'‖ ≤ 1 / 4) (h2 : ‖a - a'‖ ≤ 1 / 4) :
    ‖Complex.exp a - Complex.exp a'‖ ≤ 16 / 9 * ‖a - a'‖ := by
  have h : Complex.exp a - Complex.exp a' = Complex.exp a' * (Complex.exp (a - a') - 1) := by
    rw [mul_sub, ← Complex.exp_add]; ring_nf
  rw [h, norm_mul]
  calc ‖Complex.exp a'‖ * ‖Complex.exp (a - a') - 1‖ ≤ 4 / 3 * (4 / 3 * ‖a - a'‖) :=
        mul_le_mul (norm_exp_le_four_thirds h1) (norm_exp_sub_one_le' h2) (norm_nonneg _) (by norm_num)
    _ = 16 / 9 * ‖a - a'‖ := by ring

theorem fz_lam_sub_le {lam lam' : ℝ} (hlam : 0 ≤ lam) (hlam' : 0 ≤ lam') {z : ℂ} (hη : 0 < z.im)
    (hE : ‖Complex.exp (Complex.I * z * L)‖ ≤ 1 / 16) (h1 : lam ≤ z.im / 4) (h2 : lam' ≤ z.im / 4)
    {w : ℂ} (hw : ‖w‖ ≤ (z.im)⁻¹) :
    ‖fz L lam z w - fz L lam' z w‖ ≤ 2 * |lam - lam'| / z.im := by
  have hn : ∀ μ : ℝ, 0 ≤ μ → μ ≤ z.im / 4 → ‖Complex.I * (μ : ℂ) * w‖ ≤ 1 / 4 := by
    intro μ h0 h4
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
    calc μ * ‖w‖ ≤ (z.im / 4) * (z.im)⁻¹ := mul_le_mul h4 hw (norm_nonneg _) (by positivity)
      _ = 1 / 4 := by field_simp
  have hd : ‖Complex.I * (lam : ℂ) * w - Complex.I * (lam' : ℂ) * w‖ = |lam - lam'| * ‖w‖ := by
    rw [← sub_mul, ← mul_sub, ← Complex.ofReal_sub, norm_mul, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs]
  have hd4 : ‖Complex.I * (lam : ℂ) * w - Complex.I * (lam' : ℂ) * w‖ ≤ 1 / 4 := by
    rw [hd]
    have : |lam - lam'| ≤ z.im / 4 := by
      rw [abs_le]; constructor <;> linarith
    calc |lam - lam'| * ‖w‖ ≤ (z.im / 4) * (z.im)⁻¹ := mul_le_mul this hw (norm_nonneg _) (by positivity)
      _ = 1 / 4 := by field_simp
  have e1 := exp_sub_exp_le _ _ (hn lam' hlam' h2) hd4
  have e2 := exp_sub_exp_le (-(Complex.I * (lam : ℂ) * w)) (-(Complex.I * (lam' : ℂ) * w))
    (by rw [norm_neg]; exact hn lam' hlam' h2)
    (by rw [show -(Complex.I * (lam : ℂ) * w) - -(Complex.I * (lam' : ℂ) * w) =
        -(Complex.I * (lam : ℂ) * w - Complex.I * (lam' : ℂ) * w) by ring, norm_neg]; exact hd4)
  rw [show -(Complex.I * (lam : ℂ) * w) - -(Complex.I * (lam' : ℂ) * w) =
        -(Complex.I * (lam : ℂ) * w - Complex.I * (lam' : ℂ) * w) by ring, norm_neg] at e2
  unfold fz
  set E := Complex.exp (Complex.I * z * L) with hEdef
  have : Complex.exp (Complex.I * (lam : ℂ) * w) + E * Complex.exp (-(Complex.I * (lam : ℂ) * w)) -
      (Complex.exp (Complex.I * (lam' : ℂ) * w) + E * Complex.exp (-(Complex.I * (lam' : ℂ) * w))) =
      (Complex.exp (Complex.I * (lam : ℂ) * w) - Complex.exp (Complex.I * (lam' : ℂ) * w)) +
        E * (Complex.exp (-(Complex.I * (lam : ℂ) * w)) - Complex.exp (-(Complex.I * (lam' : ℂ) * w))) := by ring
  rw [this]
  have hwd : |lam - lam'| * ‖w‖ ≤ |lam - lam'| / z.im := by
    rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left hw (abs_nonneg _)
  rw [hd] at e1 e2
  calc _ ≤ ‖Complex.exp (Complex.I * (lam : ℂ) * w) - Complex.exp (Complex.I * (lam' : ℂ) * w)‖ +
        ‖E‖ * ‖Complex.exp (-(Complex.I * (lam : ℂ) * w)) - Complex.exp (-(Complex.I * (lam' : ℂ) * w))‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_mul]
    _ ≤ 16 / 9 * (|lam - lam'| * ‖w‖) + 1 / 16 * (16 / 9 * (|lam - lam'| * ‖w‖)) := by
        gcongr
    _ ≤ 2 * (|lam - lam'| / z.im) := by
        have : 0 ≤ |lam - lam'| * ‖w‖ := by positivity
        nlinarith
    _ = 2 * |lam - lam'| / z.im := by ring

/-! ### Continuity of the product symbol in `(lam, v)` -/

theorem symbolTerm_le' {κ : ℝ} (hκ : 0 ≤ κ) (u : L2T L) (hu : ‖u‖ = 1) {z : ℂ} (hz : 0 < z.im) (r : ℕ)
    (hr : 1 ≤ r) : ‖symbolTerm L κ u z r‖ ≤ 2 * (κ / z.im) ^ r := by
  rcases hκ.eq_or_lt with h | h
  · subst h
    have : symbolTerm L 0 u z r = 0 := by
      unfold symbolTerm
      rw [zero_pow (by omega)]; simp
    rw [this, norm_zero]
    positivity
  · exact QuantumNLS.RootMeasureNoLoss.symbolTerm_le h u hu hz r hr

theorem tendsto_symbolTerm {lams : ℕ → ℝ} {lam : ℝ} (hlim : Tendsto lams atTop (𝓝 lam)) (vs : ℕ → L2T L)
    (hvs : ∀ j, ‖vs j‖ = 1) {v : L2T L} (hv : ‖v‖ = 1) (hvl : Tendsto vs atTop (𝓝 v)) (z : ℂ) (r : ℕ) :
    Tendsto (fun j => symbolTerm L (lams j) (vs j) z r) atTop (𝓝 (symbolTerm L lam v z r)) := by
  unfold symbolTerm
  have h1 : Tendsto (fun j => (((lams j) ^ r : ℝ) : ℂ)) atTop (𝓝 (((lam ^ r : ℝ) : ℂ))) :=
    (Complex.continuous_ofReal.tendsto _).comp (hlim.pow r)
  have h2 : Tendsto (fun j => kernelProductSymbol (orderedKernel L r z) (vs j)) atTop
      (𝓝 (kernelProductSymbol (orderedKernel L r z) v)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : Tendsto (fun j => 2 * ‖orderedKernel L r z‖ * (r * ‖vs j - v‖)) atTop (𝓝 0) := by
      have := (tendsto_iff_norm_sub_tendsto_zero.1 hvl)
      simpa using (this.const_mul (r : ℝ)).const_mul (2 * ‖orderedKernel L r z‖)
    exact squeeze_zero (fun _ => norm_nonneg _)
      (fun j => QuantumNLS.RootMeasureContinuity.norm_kps_sub_le r (orderedKernel L r z) (vs j) v (hvs j) hv) hb
  exact h1.mul h2

theorem tendsto_productSymbol {lams : ℕ → ℝ} {lam : ℝ} (hlim : Tendsto lams atTop (𝓝 lam)) (hlams : ∀ j, 0 ≤ lams j)
    (vs : ℕ → L2T L) (hvs : ∀ j, ‖vs j‖ = 1) {v : L2T L} (hv : ‖v‖ = 1) (hvl : Tendsto vs atTop (𝓝 v))
    {z : ℂ} (hz : 0 < z.im) (hbd : ∀ j, lams j ≤ z.im / 4) :
    Tendsto (fun j => productSymbol L (lams j) (vs j) z) atTop (𝓝 (productSymbol L lam v z)) := by
  unfold productSymbol
  refine tendsto_const_nhds.add ?_
  have hx : ∀ j, lams j / z.im ≤ 1 / 4 := fun j => by rw [div_le_iff₀ hz]; linarith [hbd j]
  refine tendsto_tsum_of_dominated_convergence (bound := fun j : ℕ => 2 * (1 / 4 : ℝ) ^ (j + 1)) ?_ ?_ ?_
  · exact ((summable_geometric_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num)).mul_left (2 * (1 / 4))).congr
      (fun j => by rw [pow_succ]; ring)
  · intro j
    exact tendsto_symbolTerm hlim vs hvs hv hvl z (j + 1)
  · refine Eventually.of_forall fun k j => ?_
    refine (symbolTerm_le' (hlams k) (vs k) (hvs k) hz (j + 1) (by omega)).trans ?_
    have h0 : 0 ≤ lams k / z.im := div_nonneg (hlams k) hz.le
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (hx k) _) (by norm_num)

/-! ### The limiting Cauchy transform as a function of `(lam, v)` -/

/-- `g_{lam,v}(z)`: the unique solution of `f_{lam,z}(w) = s_lam(z;v)` in `|w| ≤ (Im z)⁻¹` for `lam > 0` (`gStar`), and the Cauchy transform of the free measure for `lam = 0`. -/
def gFull (v : L2T L) (hv : ‖v‖ = 1) (lam : ℝ) (z : ℂ) : ℂ :=
  if h : 0 < lam then gStar L lam h v hv z else cauchyTransform (freeMeasure L v) z

/-- The Cauchy transform of `μ_{lam,v}` is `gFull` (high half-plane for `lam > 0`; any `Im z > 0` for `lam = 0`). -/
theorem cauchy_muKappa_eq (v : L2T L) (hv : ‖v‖ = 1) {lam : ℝ} {z : ℂ} (hz : 0 < z.im)
    (hH : 0 < lam → HighHalf L lam z) :
    cauchyTransform (muKappa v hv lam : Measure ℝ) z = gFull v hv lam z := by
  by_cases h : 0 < lam
  · unfold gFull
    rw [dif_pos h]
    exact QuantumNLS.RootMeasureExistence.cauchy_limiting_measure h v hv (muKappa_spec v hv h) (hH h)
  · unfold gFull muKappa
    rw [dif_neg h, dif_neg h]
    rfl

theorem Gfree_sub_le (v v' : L2T L) (hv : ‖v‖ = 1) (hv' : ‖v'‖ = 1) {z : ℂ} (hz : 0 < z.im)
    (hlog : Real.log 16 ≤ L * z.im) :
    ‖cauchyTransform (freeMeasure L v) z - cauchyTransform (freeMeasure L v') z‖ ≤ 5 / z.im * ‖v - v'‖ := by
  have hH : HighHalf L 0 z := ⟨by linarith, hlog⟩
  have hE : ‖Complex.exp (Complex.I * z * L)‖ ≤ 1 / 16 := norm_exp_izL_le hH
  set E := Complex.exp (Complex.I * z * L) with hEdef
  have h1E : 15 / 16 ≤ ‖1 - E‖ := by
    have := norm_sub_norm_le (1 : ℂ) E
    rw [norm_one] at this
    linarith
  have ha := QuantumNLS.FreeLimit.a1_eq (κ := 1) one_pos v hv hz
  have ha' := QuantumNLS.FreeLimit.a1_eq (κ := 1) one_pos v' hv' hz
  have hk := QuantumNLS.RootMeasureContinuity.norm_kps_sub_le 1 (orderedKernel L 1 z) v v' hv hv'
  have hK : ‖orderedKernel L 1 z‖ ≤ 2 * (z.im)⁻¹ ^ 1 :=
    (QuantumNLS.RootPlacementBound.lem_root_placement v hv (N := 1) le_rfl le_rfl z hz).1
  rw [ha, ha'] at hk
  have hid : Complex.I * (1 - E) * cauchyTransform (freeMeasure L v) z -
      Complex.I * (1 - E) * cauchyTransform (freeMeasure L v') z =
      Complex.I * (1 - E) * (cauchyTransform (freeMeasure L v) z - cauchyTransform (freeMeasure L v') z) := by ring
  rw [hid, norm_mul, norm_mul, Complex.norm_I, one_mul] at hk
  have hD : 0 ≤ ‖cauchyTransform (freeMeasure L v) z - cauchyTransform (freeMeasure L v') z‖ := norm_nonneg _
  have hη : (0 : ℝ) < (z.im)⁻¹ := inv_pos.2 hz
  have hk2 : 2 * ‖orderedKernel L 1 z‖ * (((1 : ℕ) : ℝ) * ‖v - v'‖) ≤ 4 * (z.im)⁻¹ * ‖v - v'‖ := by
    rw [pow_one] at hK
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK (by norm_num : (0:ℝ) ≤ 2))
      (by positivity : 0 ≤ ((1 : ℕ) : ℝ) * ‖v - v'‖)
    nlinarith [this]
  have h3 : 15 / 16 * ‖cauchyTransform (freeMeasure L v) z - cauchyTransform (freeMeasure L v') z‖ ≤
      4 * (z.im)⁻¹ * ‖v - v'‖ := by
    calc _ ≤ ‖1 - E‖ * ‖cauchyTransform (freeMeasure L v) z - cauchyTransform (freeMeasure L v') z‖ :=
          mul_le_mul_of_nonneg_right h1E hD
      _ ≤ _ := hk.trans hk2
  have h64 : ‖cauchyTransform (freeMeasure L v) z - cauchyTransform (freeMeasure L v') z‖ ≤
      64 / 15 * ((z.im)⁻¹ * ‖v - v'‖) := by nlinarith
  have hn : 0 ≤ (z.im)⁻¹ * ‖v - v'‖ := by positivity
  have h5 : 64 / 15 * ((z.im)⁻¹ * ‖v - v'‖) ≤ 5 * ((z.im)⁻¹ * ‖v - v'‖) :=
    mul_le_mul_of_nonneg_right (by norm_num) hn
  calc _ ≤ 64 / 15 * ((z.im)⁻¹ * ‖v - v'‖) := h64
    _ ≤ 5 * ((z.im)⁻¹ * ‖v - v'‖) := h5
    _ = 5 / z.im * ‖v - v'‖ := by rw [div_eq_mul_inv]; ring

theorem gFull_tendsto {lams : ℕ → ℝ} {lam : ℝ} (hlim : Tendsto lams atTop (𝓝 lam)) (hlams : ∀ j, 0 ≤ lams j) (hlam : 0 ≤ lam)
    (vs : ℕ → L2T L) (hvs : ∀ j, ‖vs j‖ = 1) {v : L2T L} (hv : ‖v‖ = 1) (hvl : Tendsto vs atTop (𝓝 v))
    {z : ℂ} (hz : 0 < z.im) (hlog : Real.log 16 ≤ L * z.im) (hbd : ∀ j, 4 * lams j ≤ z.im)
    (hbd0 : 4 * lam ≤ z.im) :
    Tendsto (fun j => gFull (vs j) (hvs j) (lams j) z) atTop (𝓝 (gFull v hv lam z)) := by
  have hbd' : ∀ j, lams j ≤ z.im / 4 := fun j => by linarith [hbd j]
  have hE : ‖Complex.exp (Complex.I * z * L)‖ ≤ 1 / 16 := norm_exp_izL_le (⟨by linarith, hlog⟩ : HighHalf L 0 z)
  rcases hlam.eq_or_lt with h0 | hpos
  · -- lam = 0
    subst h0
    have hg0 : gFull v hv 0 z = cauchyTransform (freeMeasure L v) z := by
      unfold gFull; rw [dif_neg (lt_irrefl 0)]
    rw [hg0, tendsto_iff_norm_sub_tendsto_zero]
    have hb : Tendsto (fun j => 5 * lams j / z.im ^ 2 + 5 / z.im * ‖vs j - v‖) atTop (𝓝 0) := by
      have h1 := (hlim.const_mul 5).div_const (z.im ^ 2)
      have h2 := ((tendsto_iff_norm_sub_tendsto_zero.1 hvl).const_mul (5 / z.im))
      simpa using h1.add h2
    refine squeeze_zero (fun _ => norm_nonneg _) (fun j => ?_) hb
    have hj : ‖gFull (vs j) (hvs j) (lams j) z - cauchyTransform (freeMeasure L (vs j)) z‖ ≤ 5 * lams j / z.im ^ 2 := by
      by_cases hp : 0 < lams j
      · unfold gFull; rw [dif_pos hp]
        exact QuantumNLS.FreeLimit.gStar_free_dist hp (vs j) (hvs j) ⟨hbd j, by
          have : Real.log 16 ≤ L * z.im := hlog
          exact this⟩
      · have : lams j = 0 := le_antisymm (not_lt.1 hp) (hlams j)
        unfold gFull; rw [dif_neg hp, this]; simp
    have hG := Gfree_sub_le (vs j) v (hvs j) hv hz hlog
    calc _ ≤ ‖gFull (vs j) (hvs j) (lams j) z - cauchyTransform (freeMeasure L (vs j)) z‖ +
          ‖cauchyTransform (freeMeasure L (vs j)) z - cauchyTransform (freeMeasure L v) z‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := add_le_add hj hG
  · -- lam > 0
    have hH : HighHalf L lam z := ⟨hbd0, hlog⟩
    have hηpos : 0 < z.im := hz
    have hev : ∀ᶠ j in atTop, 0 < lams j := hlim.eventually (lt_mem_nhds hpos)
    obtain ⟨hg1, hg2⟩ := gStar_spec hpos v hv hH
    have hg : gFull v hv lam z = gStar L lam hpos v hv z := by unfold gFull; rw [dif_pos hpos]
    rw [hg, tendsto_iff_norm_sub_tendsto_zero]
    have hsym := tendsto_productSymbol hlim hlams vs hvs hv hvl hz hbd'
    have hs0 : Tendsto (fun j => ‖productSymbol L (lams j) (vs j) z - productSymbol L lam v z‖) atTop (𝓝 0) := by
      rw [← tendsto_iff_norm_sub_tendsto_zero]; exact hsym
    have hl0 : Tendsto (fun j => |lams j - lam|) atTop (𝓝 0) := by
      have := (tendsto_iff_norm_sub_tendsto_zero.1 hlim)
      simpa [Real.norm_eq_abs] using this
    have hb : Tendsto (fun j => (2 / lam) * (2 * |lam - lams j| / z.im +
        ‖productSymbol L (lams j) (vs j) z - productSymbol L lam v z‖)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun j => 2 * |lam - lams j| / z.im) atTop (𝓝 0) := by
        have := (hl0.const_mul 2).div_const z.im
        simpa [abs_sub_comm] using this
      simpa using (h1.add hs0).const_mul (2 / lam)
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hb
    filter_upwards [hev] with j hj
    have hHj : HighHalf L (lams j) z := ⟨hbd j, hlog⟩
    obtain ⟨hj1, hj2⟩ := gStar_spec hj (vs j) (hvs j) hHj
    have hgj : gFull (vs j) (hvs j) (lams j) z = gStar L (lams j) hj (vs j) (hvs j) z := by
      unfold gFull; rw [dif_pos hj]
    rw [hgj]
    have hinj := QuantumNLS.RootMeasureComplex.fz_lower hpos hH hj1 hg1
    have hLip := fz_lam_sub_le (L := L) hpos.le (hlams j) hz hE (by linarith [hbd0]) (hbd' j) hj1
    have hmid : ‖fz L lam z (gStar L (lams j) hj (vs j) (hvs j) z) - productSymbol L lam v z‖ ≤
        2 * |lam - lams j| / z.im + ‖productSymbol L (lams j) (vs j) z - productSymbol L lam v z‖ := by
      have : fz L lam z (gStar L (lams j) hj (vs j) (hvs j) z) - productSymbol L lam v z =
          (fz L lam z (gStar L (lams j) hj (vs j) (hvs j) z) - fz L (lams j) z (gStar L (lams j) hj (vs j) (hvs j) z)) +
          (productSymbol L (lams j) (vs j) z - productSymbol L lam v z) := by
        rw [hj2]; ring
      rw [this]
      exact (norm_add_le _ _).trans (add_le_add hLip le_rfl)
    rw [hg2] at hinj
    have hκ2 : 0 < lam / 2 := by positivity
    calc ‖gStar L (lams j) hj (vs j) (hvs j) z - gStar L lam hpos v hv z‖
        = (2 / lam) * (lam / 2 * ‖gStar L (lams j) hj (vs j) (hvs j) z - gStar L lam hpos v hv z‖) := by
          field_simp
      _ ≤ (2 / lam) * (2 * |lam - lams j| / z.im + ‖productSymbol L (lams j) (vs j) z - productSymbol L lam v z‖) :=
          mul_le_mul_of_nonneg_left (hinj.trans hmid) (by positivity)

/-! ### Joint continuity of `μ_{lam,v}` -/

theorem tendsto_muKappa_joint {lams : ℕ → ℝ} {lam : ℝ} (hlim : Tendsto lams atTop (𝓝 lam)) (hlams : ∀ j, 0 ≤ lams j)
    (hlam : 0 ≤ lam) (vs : ℕ → L2T L) (hvs : ∀ j, ‖vs j‖ = 1) {v : L2T L} (hv : ‖v‖ = 1)
    (hvl : Tendsto vs atTop (𝓝 v)) :
    Tendsto (fun j => muKappa (vs j) (hvs j) (lams j)) atTop (𝓝 (muKappa v hv lam)) := by
  have hL : 0 < L := Fact.out
  set η₀ : ℝ := max (4 * (lam + 1)) (Real.log 16 / L) with hη₀
  have hη0 : 0 < η₀ := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  let q : ℕ → ℝ := TopologicalSpace.denseSeq ℝ
  let Y : ℕ → ℝ := fun j => η₀ + j
  have hYge : ∀ j, η₀ ≤ Y j := fun j => by
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    simp only [Y]; linarith
  have hYpos : ∀ j, 0 < Y j := fun j => lt_of_lt_of_le hη0 (hYge j)
  have hsmall : ∀ᶠ j in atTop, lams j ≤ lam + 1 := hlim.eventually (ge_mem_nhds (by linarith))
  -- every point with `Im z ≥ η₀` is good for `lam` and (eventually) for `lam_j`
  have hgoodlog : ∀ z : ℂ, η₀ ≤ z.im → Real.log 16 ≤ L * z.im := by
    intro z hz
    have : Real.log 16 / L ≤ z.im := (le_max_right _ _).trans hz
    rwa [div_le_iff₀ hL, mul_comm] at this
  have hR1 : ∀ y : ℝ, η₀ ≤ y → 4 * lam ≤ y := fun y hy => by
    have := (le_max_left (4 * (lam + 1)) (Real.log 16 / L)).trans hy
    linarith
  have hR2 : ∀ y : ℝ, η₀ ≤ y → Real.log 16 ≤ L * y := fun y hy => by
    have : Real.log 16 / L ≤ y := (le_max_right _ _).trans hy
    rwa [div_le_iff₀ hL, mul_comm] at this
  have hgoodlam : ∀ z : ℂ, η₀ ≤ z.im → 4 * lam ≤ z.im := by
    intro z hz
    have := (le_max_left (4 * (lam + 1)) (Real.log 16 / L)).trans hz
    linarith
  have hconv : ∀ z : ℂ, η₀ ≤ z.im →
      Tendsto (fun j => cauchyTransform (muKappa (vs j) (hvs j) (lams j) : Measure ℝ) z) atTop
        (𝓝 (gFull v hv lam z)) := by
    intro z hz
    have hzpos : 0 < z.im := lt_of_lt_of_le hη0 hz
    have hbd : ∀ᶠ j in atTop, 4 * lams j ≤ z.im := by
      filter_upwards [hsmall] with j hj
      have := (le_max_left (4 * (lam + 1)) (Real.log 16 / L)).trans hz
      linarith
    -- the sequence of values `gFull`, along the whole sequence, converges (use a modified bounded sequence)
    have hmod : Tendsto (fun j => gFull (vs j) (hvs j) (if 4 * lams j ≤ z.im then lams j else 0) z) atTop
        (𝓝 (gFull v hv lam z)) := by
      refine gFull_tendsto (lams := fun j => if 4 * lams j ≤ z.im then lams j else 0) ?_ ?_ hlam vs hvs hv hvl hzpos
        (hgoodlog z hz) ?_ (hgoodlam z hz)
      · refine hlim.congr' ?_
        filter_upwards [hbd] with j hj
        simp [hj]
      · intro j; split_ifs <;> [exact hlams j; exact le_rfl]
      · intro j; split_ifs with h
        · exact h
        · linarith
    refine hmod.congr' ?_
    filter_upwards [hbd] with j hj
    rw [if_pos hj]
    have hH : 0 < lams j → HighHalf L (lams j) z := fun _ => ⟨hj, hgoodlog z hz⟩
    exact (cauchy_muKappa_eq (vs j) (hvs j) hzpos hH).symm
  have hmassY : Tendsto (fun j : ℕ => 1 + Y j * (gFull v hv lam (Complex.I * (Y j : ℂ))).im) atTop (𝓝 0) := by
    have h := (QuantumNLS.FreeLimit.one_add_mul_im_tendsto_prob (muKappa v hv lam : Measure ℝ)).comp
      (tendsto_atTop_add_const_left _ _ (tendsto_natCast_atTop_atTop (R := ℝ)) : Tendsto Y atTop atTop)
    refine h.congr (fun j => ?_)
    simp only [Function.comp_apply]
    have hzim : (Complex.I * (Y j : ℂ)).im = Y j := by simp
    have hH : 0 < lam → HighHalf L lam (Complex.I * (Y j : ℂ)) := fun _ =>
      ⟨by rw [hzim]; exact hR1 _ (hYge j), by rw [hzim]; exact hR2 _ (hYge j)⟩
    rw [cauchy_muKappa_eq v hv (by rw [hzim]; exact hYpos j) hH]
  exact QuantumNLS.CauchyLimitCriterion.tendsto_of_cauchy (η₀ := η₀) (q := q) (g := gFull v hv lam) (Y := Y) hη0
    (TopologicalSpace.denseRange_denseSeq ℝ) (fun j => muKappa (vs j) (hvs j) (lams j)) hYpos (muKappa v hv lam)
    (fun k => by
      have hzim : (((q k : ℝ) : ℂ) + η₀ * Complex.I).im = η₀ := by simp
      exact cauchy_muKappa_eq v hv (by rw [hzim]; exact hη0) (fun _ => ⟨by rw [hzim]; exact hR1 _ le_rfl,
        by rw [hzim]; exact hR2 _ le_rfl⟩))
    hmassY
    (fun j => hconv _ (by simpa using hYge j))
    (fun k => hconv _ (by simp))

end QuantumNLS.ParamContinuity

#print axioms QuantumNLS.ParamContinuity.fz_lam_sub_le
#print axioms QuantumNLS.ParamContinuity.tendsto_productSymbol
#print axioms QuantumNLS.ParamContinuity.Gfree_sub_le
#print axioms QuantumNLS.ParamContinuity.gFull_tendsto
#print axioms QuantumNLS.ParamContinuity.tendsto_muKappa_joint
