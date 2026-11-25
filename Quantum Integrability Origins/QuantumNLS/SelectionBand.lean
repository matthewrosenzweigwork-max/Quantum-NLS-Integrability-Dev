import Mathlib
import QuantumNLS.LocalHeight

/-!
# CC:F04:selection (R-F4C3E5BE), step S3: the whole-band cluster comparison

Source: `source-text/chapters/root_response/F04.tex`, Proposition `CC:F04:selection` (line 202) and its proof, from "We now exclude the endpoints and select the interior point without ignoring a microscopic cluster" to
the end of the proof of (CC:F04:selected-root).

Setting (same conventions as `LocalHeight`, read-only): `RealBethe L κ N (q N) (ν N)` (`CC:F04:real-bethe`, arrays of `N + 1` roots, `c = κ/(N+1)`), `EmpiricalWeakConv q μ`, `LocalHeight.theta`.
`r < l` are the support edges `r_j < l_ℓ` of the proof, and the band `(r, l)` carries no `μ`-mass (`hband`); `μ` is atomless (`hna`, the printed atomlessness). The cluster `U_h = (r − h, l + h)` is realized as the closed interval `[r − h, l + h]`
(its boundary is `μ`-null by atomlessness; recorded as in `LocalHeight`).

Interface (exact S3 statement, for sonnet_fourier's S1/S2): `selection_core`. Hypotheses:
* `hloc`: for every `h > 0`, eventually `q_{i_N,N} ∈ (r − h, l + h)` (the printed rank bracketing "the selected root lies in `U_h` for all large `N`", i.e. every limit point of the selected root lies in `[r_j, l_ℓ]`);
* `hlab`: `ν_{i_N,N} → λ` (the selected root has real label `λ`, `CC:F04:parameter`);
* `xs ∈ (r, l)` with `θ(xs) = πλ` (`CC:F04:phase-inverse`: the point `x(λ)` in the open band);
conclusion: `q_{i_N,N} → xs` (`CC:F04:selected-root`).

Parts (all proved here, no hypothesis beyond the above):
* `theta_mono`: `θ` has slope at least `L/2` on the band (`CC:F04:phase`: `θ' = L/2 + κ ∫ dμ/(x−y)² > 0`), so `x_- < xs < x_+` with `θ(x_-) < πλ < θ(x_+)` exist arbitrarily close to `xs`;
* `M_tendsto`: `μ(U_h) → 0` as `h ↓ 0` (atomlessness and the empty band);
* `force_approx_band`: the whole-band version of the deterministic `CC:F04:external-limit` estimate (the printed `H^{U_h}(x_±) → 2θ(x_±)` up to the cluster mass): at a point `x` with `[x − 2ε, x + 2ε]` inside the cluster interval,
  `|force(x) − (Lx − 2c Σ_j g_x(q_j))| ≤ 2(n(c/ε)³ + c K/ε)`, `K` the cluster size; with `K_N/N ≲ μ(U_h)` the limit is `2θ(x)` within `2κμ(U_h)/ε`;
* the cluster comparison `LocalHeight.cluster_bound` (R-52E511D4) gives `|q_{i_N,N} − p_N| ≤ 4√(κ K_N/(LN))`, `p_N` the inverse of the extended external force at `2πν_{i_N,N}`, and the monotone force places `p_N` in `(x_-, x_+)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section
open scoped BigOperators Topology BoundedContinuousFunction
open Finset Filter MeasureTheory

namespace QuantumNLS.SelectionBand

open QuantumNLS.LocalHeight

/-! ## 1. The phase on the band -/

section Theta

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

theorem integrable_inv {r l : ℝ} (hband : μ (Set.Ioo r l) = 0) {x : ℝ} (hx : x ∈ Set.Ioo r l) :
    Integrable (fun y => 1 / (x - y)) μ := by
  have hae := measure_eq_zero_iff_ae_notMem.1 hband
  set d := min (x - r) (l - x) with hd
  have hd0 : 0 < d := lt_min (by linarith [hx.1]) (by linarith [hx.2])
  refine Integrable.of_bound (C := 1 / d)
    ((measurable_const.div (measurable_const.sub measurable_id)).aestronglyMeasurable) ?_
  filter_upwards [hae] with y hy
  have h1 : d ≤ |x - y| := by
    by_contra h
    push Not at h
    apply hy
    have := abs_lt.1 h
    have e1 := min_le_left (x - r) (l - x)
    have e2 := min_le_right (x - r) (l - x)
    constructor <;> linarith
  rw [Real.norm_eq_abs, abs_div, abs_one]
  exact div_le_div_of_nonneg_left zero_le_one hd0 h1

theorem theta_mono {L κ : ℝ} {r l : ℝ} (hband : μ (Set.Ioo r l) = 0) {x x' : ℝ}
    (hx : x ∈ Set.Ioo r l) (hx' : x' ∈ Set.Ioo r l) (hxx : x ≤ x') (hκ : 0 ≤ κ) :
    L * (x' - x) / 2 ≤ theta L κ μ x' - theta L κ μ x := by
  have i1 := integrable_inv hband hx
  have i2 := integrable_inv hband hx'
  have hae := measure_eq_zero_iff_ae_notMem.1 hband
  have hnn : 0 ≤ ∫ y, (1 / (x - y) - 1 / (x' - y)) ∂μ := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hae] with y hy
    have hy' : y ≤ r ∨ l ≤ y := by
      by_contra h
      push Not at h
      exact hy ⟨h.1, h.2⟩
    have hprod : 0 < (x - y) * (x' - y) := by
      rcases hy' with h | h
      · exact mul_pos (by linarith [hx.1]) (by linarith [hx'.1])
      · exact mul_pos_of_neg_of_neg (by linarith [hx.2]) (by linarith [hx'.2])
    have hx0 : x - y ≠ 0 := by intro h0; rw [h0] at hprod; simp at hprod
    have hx0' : x' - y ≠ 0 := by intro h0; rw [h0] at hprod; simp at hprod
    have e : 1 / (x - y) - 1 / (x' - y) = (x' - x) / ((x - y) * (x' - y)) := by
      field_simp; ring
    simp only [Pi.zero_apply]
    rw [e]
    exact div_nonneg (by linarith) hprod.le
  rw [integral_sub i1 i2] at hnn
  unfold theta
  nlinarith

end Theta

/-! ## 2. The cluster interval shrinks to the empty band -/

theorem M_tendsto {μ : Measure ℝ} [IsProbabilityMeasure μ] (hna : ∀ y, μ {y} = 0) {r l : ℝ}
    (hband : μ (Set.Ioo r l) = 0) :
    Tendsto (fun h : ℝ => μ.real (Set.Icc (r - h) (l + h))) (𝓝[>] 0) (𝓝 0) := by
  have hIcc : μ (Set.Icc r l) = 0 := by
    have hsub : Set.Icc r l ⊆ Set.Ioo r l ∪ {r} ∪ {l} := by
      intro y hy
      rcases eq_or_lt_of_le hy.1 with h | h
      · simp [← h]
      · rcases eq_or_lt_of_le hy.2 with h' | h'
        · simp [h']
        · exact Or.inl (Or.inl ⟨h, h'⟩)
    exact measure_mono_null hsub (measure_union_null (measure_union_null hband (hna r)) (hna l))
  have h := tendsto_measure_biInter_gt (μ := μ) (s := fun h : ℝ => Set.Icc (r - h) (l + h)) (a := (0 : ℝ))
    (fun h _ => measurableSet_Icc.nullMeasurableSet)
    (fun i j _ hij => Set.Icc_subset_Icc (by linarith) (by linarith))
    ⟨1, one_pos, measure_ne_top _ _⟩
  have hint : (⋂ h > (0 : ℝ), Set.Icc (r - h) (l + h)) = Set.Icc r l := by
    ext y
    simp only [Set.mem_iInter, Set.mem_Icc]
    constructor
    · intro hy
      constructor
      · refine le_of_forall_pos_le_add fun ε hε => ?_
        have := (hy ε hε).1; linarith
      · refine le_of_forall_pos_le_add fun ε hε => ?_
        have := (hy ε hε).2; linarith
    · intro hy ε hε
      constructor <;> linarith [hy.1, hy.2]
  rw [hint, hIcc] at h
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simpa [Measure.real, Function.comp_def] using this

/-! ## 3. The whole-band deterministic force estimate -/

lemma force_approx_band {n : ℕ} {L c x ε a b : ℝ} (hc : 0 ≤ c) (hε : 0 < ε)
    (ha : a ≤ x - 2 * ε) (hb : x + 2 * ε ≤ b) (q : Fin n → ℝ) :
    |force L c a b q x - (L * x - 2 * c * ∑ j, gK x ε (q j))| ≤
      2 * (n * (c / ε) ^ 3 + c * ((cluster a b q).card * (1 / ε))) := by
  set S := cluster a b q
  set T := univ.filter (fun j => q j ∉ Set.Icc a b)
  have hsplit : ∑ j, gK x ε (q j) = ∑ j ∈ S, gK x ε (q j) + ∑ j ∈ T, gK x ε (q j) :=
    (Finset.sum_filter_add_sum_filter_not univ (fun j => q j ∈ Set.Icc a b) _).symm
  have hTx : ∀ j ∈ T, ε ≤ |x - q j| := by
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    by_contra h
    push Not at h
    apply hj'
    have := abs_lt.1 h
    constructor <;> linarith [this.1, this.2]
  have hT' : ∑ j ∈ T, gK x ε (q j) = ∑ j ∈ T, 1 / (x - q j) :=
    Finset.sum_congr rfl fun j hj => gK_eq hε (hTx j hj)
  have hF : force L c a b q x = L * x - 2 * ∑ j ∈ T, Real.arctan (c / (x - q j)) := rfl
  have hG : c * ∑ j, gK x ε (q j) = c * ∑ j ∈ S, gK x ε (q j) + ∑ j ∈ T, c / (x - q j) := by
    rw [hsplit, mul_add, hT']
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hdec : force L c a b q x - (L * x - 2 * c * ∑ j, gK x ε (q j)) =
      -2 * (∑ j ∈ T, (Real.arctan (c / (x - q j)) - c / (x - q j)) - c * ∑ j ∈ S, gK x ε (q j)) := by
    rw [hF, Finset.sum_sub_distrib]
    linarith [hG]
  rw [hdec, abs_mul, show |(-2 : ℝ)| = 2 by norm_num]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hcardT : (T.card : ℝ) ≤ n := by
    have := Finset.card_le_univ T; simp only [Fintype.card_fin] at this; exact_mod_cast this
  have b1 : |∑ j ∈ T, (Real.arctan (c / (x - q j)) - c / (x - q j))| ≤ n * (c / ε) ^ 3 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ ((c / ε) ^ 3) fun j hj => ?_).trans ?_
    · refine (arctan_sub_self_le _).trans (pow_le_pow_left₀ (abs_nonneg _) ?_ 3)
      rw [abs_div, abs_of_nonneg hc]
      exact div_le_div_of_nonneg_left hc hε (hTx j hj)
    · rw [nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right hcardT (by positivity)
  have b3 : |c * ∑ j ∈ S, gK x ε (q j)| ≤ c * (S.card * (1 / ε)) := by
    rw [abs_mul, abs_of_nonneg hc]
    apply mul_le_mul_of_nonneg_left _ hc
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ (1 / ε) fun j _ => gK_abs_le hε _).trans ?_
    rw [nsmul_eq_mul]
  have h3 := abs_sub (∑ j ∈ T, (Real.arctan (c / (x - q j)) - c / (x - q j))) (c * ∑ j ∈ S, gK x ε (q j))
  linarith


/-! ## 4. The cluster fraction and the main limit -/

lemma cluster_frac {μ : Measure ℝ} [IsProbabilityMeasure μ] {q : (N : ℕ) → Fin (N + 1) → ℝ}
    (hw : EmpiricalWeakConv q μ) {r l h : ℝ} (hh : 0 < h) (hrl : r ≤ l) {τ : ℝ}
    (hτ : μ.real (Set.Icc (r - 2 * h) (l + 2 * h)) < τ) :
    ∀ᶠ N : ℕ in atTop, ((cluster (r - h) (l + h) (q N)).card : ℝ) / ((N : ℝ) + 1) < τ := by
  set m : ℝ := (r + l) / 2 with hm
  set w : ℝ := (l - r) / 2 + h with hw'
  set f : ℝ → ℝ := fun y => max 0 (min 1 (1 + (w - |y - m|) / h)) with hf
  have hfc : Continuous f :=
    continuous_const.max (continuous_const.min (continuous_const.add
      ((continuous_const.sub (continuous_id.sub continuous_const).abs).div_const h)))
  have hfb : ∀ y, ‖f y‖ ≤ 1 := by
    intro y
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
    exact max_le zero_le_one (min_le_left _ _)
  have hf0 : ∀ y, 0 ≤ f y := fun y => le_max_left _ _
  have hfin : ∀ y, y ∈ Set.Icc (r - h) (l + h) → f y = 1 := by
    intro y hy
    have h1 : |y - m| ≤ w := by
      rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
    have h2 : 1 ≤ 1 + (w - |y - m|) / h := by
      have : 0 ≤ (w - |y - m|) / h := div_nonneg (by linarith) hh.le
      linarith
    simp only [hf]
    rw [min_eq_left h2, max_eq_right zero_le_one]
  have hfind : ∀ y, f y ≤ (Set.Icc (r - 2 * h) (l + 2 * h)).indicator (fun _ => (1 : ℝ)) y := by
    intro y
    by_cases hy : y ∈ Set.Icc (r - 2 * h) (l + 2 * h)
    · rw [Set.indicator_of_mem hy]
      exact (le_abs_self _).trans (hfb y)
    · rw [Set.indicator_of_notMem hy]
      have h1 : w + h < |y - m| := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hy
        rcases hy with h | h
        · rw [abs_sub_comm]; refine lt_of_lt_of_le ?_ (le_abs_self _); linarith
        · refine lt_of_lt_of_le ?_ (le_abs_self _); linarith
      have h2 : 1 + (w - |y - m|) / h < 0 := by
        have : (w - |y - m|) / h < -1 := by
          rw [div_lt_iff₀ hh]; linarith
        linarith
      simp only [hf]
      rw [min_eq_right (by linarith), max_eq_left h2.le]
  set F : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup f hfc 1 hfb with hF
  have hconv := hw F
  have hint : ∫ y, F y ∂μ ≤ μ.real (Set.Icc (r - 2 * h) (l + 2 * h)) := by
    have hI : Integrable (fun y => F y) μ := F.integrable μ
    have hI2 : Integrable ((Set.Icc (r - 2 * h) (l + 2 * h)).indicator (fun _ => (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ)).indicator measurableSet_Icc
    calc ∫ y, F y ∂μ ≤ ∫ y, (Set.Icc (r - 2 * h) (l + 2 * h)).indicator (fun _ => (1 : ℝ)) y ∂μ :=
          integral_mono hI hI2 fun y => hfind y
      _ = μ.real (Set.Icc (r - 2 * h) (l + 2 * h)) := by
          rw [integral_indicator_const _ measurableSet_Icc]; simp
  have hev := hconv.eventually_lt_const (lt_of_le_of_lt hint hτ)
  filter_upwards [hev] with N hN
  refine lt_of_le_of_lt ?_ hN
  rw [div_eq_mul_inv, mul_comm, one_div]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h1 : ((cluster (r - h) (l + h) (q N)).card : ℝ) =
      ∑ j ∈ cluster (r - h) (l + h) (q N), f (q N j) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    exact Finset.sum_congr rfl fun j hj => (hfin _ (Finset.mem_filter.mp hj).2).symm
  rw [h1]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hf0 _)

lemma main_conv {μ : Measure ℝ} [IsProbabilityMeasure μ] {q : (N : ℕ) → Fin (N + 1) → ℝ}
    (hw : EmpiricalWeakConv q μ) {L κ x ε : ℝ} (hε : 0 < ε)
    (hnull : μ (Set.Icc (x - 4 * ε) (x + 4 * ε)) = 0) :
    Tendsto (fun N : ℕ => L * x - 2 * κ * ((1 / ((N : ℝ) + 1)) * ∑ j, gK x ε (q N j))) atTop
      (𝓝 (2 * theta L κ μ x)) := by
  have hae : ∀ᵐ y ∂μ, 4 * ε < |y - x| := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with y hy
    by_contra h
    push Not at h
    exact hy ⟨by linarith [(abs_le.mp h).1], by linarith [(abs_le.mp h).2]⟩
  have hgint : ∫ y, (gBCF x ε hε) y ∂μ = ∫ y, 1 / (x - y) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with y hy
    show gK x ε y = 1 / (x - y)
    exact gK_eq hε (by rw [abs_sub_comm]; linarith)
  have hA : Tendsto (fun N : ℕ => (1 / ((N : ℝ) + 1)) * ∑ j, gK x ε (q N j)) atTop
      (𝓝 (∫ y, 1 / (x - y) ∂μ)) := by
    rw [← hgint]; exact hw (gBCF x ε hε)
  have := (tendsto_const_nhds (x := L * x)).sub (hA.const_mul (2 * κ))
  unfold theta
  convert this using 2
  ring

/-- **S3 of `CC:F04:selection`** (whole-band cluster comparison): `q_{i_N,N} → x(λ)`. -/
theorem selection_core {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hna : ∀ y, μ {y} = 0) {r l : ℝ} (hrl : r < l) (hband : μ (Set.Ioo r l) = 0)
    {q ν : (N : ℕ) → Fin (N + 1) → ℝ} (hB : ∀ N, RealBethe L κ N (q N) (ν N))
    (hw : EmpiricalWeakConv q μ) (i : (N : ℕ) → Fin (N + 1)) {lam : ℝ}
    (hloc : ∀ h : ℝ, 0 < h → ∀ᶠ N : ℕ in atTop, q N (i N) ∈ Set.Ioo (r - h) (l + h))
    (hlab : Tendsto (fun N => ν N (i N)) atTop (𝓝 lam))
    {xs : ℝ} (hxs : xs ∈ Set.Ioo r l) (hθ : theta L κ μ xs = Real.pi * lam) :
    Tendsto (fun N => q N (i N)) atTop (𝓝 xs) := by
  have hIcc : μ (Set.Icc r l) = 0 := by
    have hsub : Set.Icc r l ⊆ Set.Ioo r l ∪ {r} ∪ {l} := by
      intro y hy
      rcases eq_or_lt_of_le hy.1 with h | h
      · simp [← h]
      · rcases eq_or_lt_of_le hy.2 with h' | h'
        · simp [h']
        · exact Or.inl (Or.inl ⟨h, h'⟩)
    exact measure_mono_null hsub (measure_union_null (measure_union_null hband (hna r)) (hna l))
  rw [Metric.tendsto_nhds]
  intro δ hδ
  -- (1) the points `x_- < xs < x_+` with `θ(x_-) < πλ < θ(x_+)`
  have hm1 : 0 < min (xs - r) (l - xs) := lt_min (sub_pos.2 hxs.1) (sub_pos.2 hxs.2)
  set δ' : ℝ := min (δ / 4) (min (xs - r) (l - xs) / 2) with hδ'
  have hδ'pos : 0 < δ' := lt_min (by linarith) (by linarith)
  have hδ'1 : δ' ≤ δ / 4 := min_le_left _ _
  have hδ'2 : δ' ≤ min (xs - r) (l - xs) / 2 := min_le_right _ _
  have hmr : min (xs - r) (l - xs) ≤ xs - r := min_le_left _ _
  have hml : min (xs - r) (l - xs) ≤ l - xs := min_le_right _ _
  set xm : ℝ := xs - δ' with hxm
  set xp : ℝ := xs + δ' with hxp
  have hxm_mem : xm ∈ Set.Ioo r l := ⟨by linarith, by linarith [hxs.2]⟩
  have hxp_mem : xp ∈ Set.Ioo r l := ⟨by linarith [hxs.1], by linarith⟩
  have hθm : theta L κ μ xm ≤ theta L κ μ xs - L * δ' / 2 := by
    have := theta_mono (L := L) (κ := κ) hband hxm_mem hxs (by linarith) hκ.le
    have e : xs - xm = δ' := by rw [hxm]; ring
    rw [e] at this
    linarith
  have hθp : theta L κ μ xs + L * δ' / 2 ≤ theta L κ μ xp := by
    have := theta_mono (L := L) (κ := κ) hband hxs hxp_mem (by linarith) hκ.le
    have e : xp - xs = δ' := by rw [hxp]; ring
    rw [e] at this
    linarith
  -- (2) the scale `ε`
  set d : ℝ := min (xm - r) (l - xp) with hd
  have hd0 : 0 < d := lt_min (by linarith [hxm_mem.1]) (by linarith [hxp_mem.2])
  have hdm : d ≤ xm - r := min_le_left _ _
  have hdp : d ≤ l - xp := min_le_right _ _
  set ε : ℝ := d / 4 with hεdef
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hnullm : μ (Set.Icc (xm - 4 * ε) (xm + 4 * ε)) = 0 :=
    measure_mono_null (Set.Icc_subset_Icc (by rw [hεdef]; linarith) (by rw [hεdef]; linarith)) hIcc
  have hnullp : μ (Set.Icc (xp - 4 * ε) (xp + 4 * ε)) = 0 :=
    measure_mono_null (Set.Icc_subset_Icc (by rw [hεdef]; linarith) (by rw [hεdef]; linarith)) hIcc
  have hmainm := main_conv (L := L) (κ := κ) hw hε hnullm
  have hmainp := main_conv (L := L) (κ := κ) hw hε hnullp
  -- (3) the tolerances
  set ρ : ℝ := L * δ' / 4 with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  set τ0 : ℝ := min (ρ * ε / (4 * κ)) (L * δ ^ 2 / (64 * κ)) with hτ0
  have hτ0pos : 0 < τ0 := lt_min (by positivity) (by positivity)
  have hτ1 : 2 * κ * τ0 / ε ≤ ρ / 2 := by
    have : τ0 ≤ ρ * ε / (4 * κ) := min_le_left _ _
    rw [div_le_iff₀ hε]
    have h4 : 4 * κ * τ0 ≤ ρ * ε := by
      have := (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * κ)).1 this
      linarith
    nlinarith
  have hτ2 : κ * τ0 / L ≤ (δ / 8) ^ 2 := by
    have : τ0 ≤ L * δ ^ 2 / (64 * κ) := min_le_right _ _
    rw [div_le_iff₀ hL]
    have h4 := (le_div_iff₀ (by positivity : (0 : ℝ) < 64 * κ)).1 this
    nlinarith
  -- (4) the cluster interval `[r - h, l + h]` with small mass
  obtain ⟨h', hh'0, hh'⟩ : ∃ h' : ℝ, 0 < h' ∧ μ.real (Set.Icc (r - h') (l + h')) < τ0 := by
    have hM := (M_tendsto hna hband).eventually (eventually_lt_nhds hτ0pos)
    obtain ⟨h', h1, h2⟩ := (hM.and self_mem_nhdsWithin).exists
    exact ⟨h', h2, h1⟩
  set h : ℝ := h' / 2 with hhdef
  have hh0 : 0 < h := by rw [hhdef]; positivity
  have hh2 : μ.real (Set.Icc (r - 2 * h) (l + 2 * h)) < τ0 := by
    have : 2 * h = h' := by rw [hhdef]; ring
    rw [this]; exact hh'
  have hab : r - h ≤ l + h := by linarith
  have hKfrac := cluster_frac hw hh0 hrl.le hh2
  -- (5) eventual inequalities
  have hcN : ∀ N : ℕ, 0 < κ / ((N : ℝ) + 1) := fun N => by positivity
  have h1N : Tendsto (fun N : ℕ => (κ ^ 3 / ε ^ 3) * (1 / ((N : ℝ) + 1)) ^ 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => (1 / ((N : ℝ) + 1)) ^ 2) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
      simpa using this
    simpa using h1.const_mul (κ ^ 3 / ε ^ 3)
  have hev1 : ∀ᶠ N : ℕ in atTop, (κ ^ 3 / ε ^ 3) * (1 / ((N : ℝ) + 1)) ^ 2 < ρ / 4 :=
    h1N.eventually (gt_mem_nhds (by positivity))
  have hevm : ∀ᶠ N : ℕ in atTop,
      L * xm - 2 * κ * ((1 / ((N : ℝ) + 1)) * ∑ j, gK xm ε (q N j)) < 2 * theta L κ μ xm + ρ :=
    hmainm.eventually (gt_mem_nhds (by linarith))
  have hevp : ∀ᶠ N : ℕ in atTop,
      2 * theta L κ μ xp - ρ < L * xp - 2 * κ * ((1 / ((N : ℝ) + 1)) * ∑ j, gK xp ε (q N j)) :=
    hmainp.eventually (lt_mem_nhds (by linarith))
  have hevlab : ∀ᶠ N : ℕ in atTop, |2 * Real.pi * ν N (i N) - 2 * Real.pi * lam| < ρ := by
    have hl := (hlab.const_mul (2 * Real.pi))
    have := (Metric.tendsto_nhds.mp hl) ρ hρ0
    filter_upwards [this] with N hN
    rwa [Real.dist_eq] at hN
  have hevloc := hloc h hh0
  -- (6) assemble
  filter_upwards [hKfrac, hev1, hevm, hevp, hevlab, hevloc] with N hK he1 hem hep hel hloc'
  set c : ℝ := κ / ((N : ℝ) + 1) with hcdef
  have hc : 0 < c := hcN N
  set a : ℝ := r - h
  set b : ℝ := l + h
  have hxmab : xm ∈ Set.Icc a b := ⟨by linarith [hxm_mem.1], by linarith [hxm_mem.2]⟩
  have hxpab : xp ∈ Set.Icc a b := ⟨by linarith [hxp_mem.1], by linarith [hxp_mem.2]⟩
  set Kc : ℝ := ((cluster a b (q N)).card : ℝ) with hKc
  have hKfracN : Kc / ((N : ℝ) + 1) < τ0 := hK
  have hKnn : 0 ≤ Kc := by positivity
  -- the force estimate at `x_±`
  have hbound : ∀ x : ℝ, a ≤ x - 2 * ε → x + 2 * ε ≤ b →
      |force L c a b (q N) x - (L * x - 2 * c * ∑ j, gK x ε (q N j))| ≤ ρ := by
    intro x hxa hxb
    have := force_approx_band (L := L) (c := c) hc.le hε hxa hxb (q N)
    refine this.trans ?_
    have e1 : ((N + 1 : ℕ) : ℝ) * (c / ε) ^ 3 = (κ ^ 3 / ε ^ 3) * (1 / ((N : ℝ) + 1)) ^ 2 := by
      rw [hcdef]; push_cast; field_simp
    have e2 : c * (Kc * (1 / ε)) = κ * (Kc / ((N : ℝ) + 1)) / ε := by
      rw [hcdef]; field_simp
    have hn : ((Fin (N + 1)) → ℝ) = ((Fin (N + 1)) → ℝ) := rfl
    have hcard : ((Fintype.card (Fin (N + 1)) : ℕ) : ℝ) = ((N + 1 : ℕ) : ℝ) := by simp
    calc 2 * (((N + 1 : ℕ) : ℝ) * (c / ε) ^ 3 + c * ((cluster a b (q N)).card * (1 / ε)))
        = 2 * ((κ ^ 3 / ε ^ 3) * (1 / ((N : ℝ) + 1)) ^ 2 + κ * (Kc / ((N : ℝ) + 1)) / ε) := by
          rw [e1]; congr 2
      _ ≤ ρ := by
          have h3 : κ * (Kc / ((N : ℝ) + 1)) / ε ≤ κ * τ0 / ε := by
            gcongr
          have h4 : κ * τ0 / ε ≤ ρ / 4 := by
            have := hτ1
            have e : 2 * κ * τ0 / ε = 2 * (κ * τ0 / ε) := by ring
            linarith
          linarith
  have hfm : force L c a b (q N) xm ≤ 2 * Real.pi * lam - 2 * ρ := by
    have hb1 := hbound xm (by linarith [hdm]) (by linarith [hdm, hdp, hxm_mem.2, hxp_mem.2])
    rw [abs_le] at hb1
    have e : 2 * κ * ((1 / ((N : ℝ) + 1)) * ∑ j, gK xm ε (q N j)) =
        2 * c * ∑ j, gK xm ε (q N j) := by rw [hcdef]; field_simp
    rw [e] at hem
    have : 2 * theta L κ μ xm ≤ 2 * Real.pi * lam - 4 * ρ := by
      have : theta L κ μ xm ≤ Real.pi * lam - L * δ' / 2 := by rw [← hθ]; exact hθm
      rw [hρ]; linarith
    linarith [hb1.2]
  have hfp : 2 * Real.pi * lam + 2 * ρ ≤ force L c a b (q N) xp := by
    have hb1 := hbound xp (by linarith [hdm, hdp, hxm_mem.1, hxp_mem.1]) (by linarith [hdp])
    rw [abs_le] at hb1
    have e : 2 * κ * ((1 / ((N : ℝ) + 1)) * ∑ j, gK xp ε (q N j)) =
        2 * c * ∑ j, gK xp ε (q N j) := by rw [hcdef]; field_simp
    rw [e] at hep
    have : 2 * Real.pi * lam + 4 * ρ ≤ 2 * theta L κ μ xp := by
      have : Real.pi * lam + L * δ' / 2 ≤ theta L κ μ xp := by rw [← hθ]; exact hθp
      rw [hρ]; linarith
    linarith [hb1.1]
  have hlabs := abs_lt.1 hel
  -- the inverse `p` of the extended external force
  have hsurj : Function.Surjective (extForce L c a b (q N)) :=
    ExternalConfinement.H_surjective hL (extForce_continuous hab _) (extForce_slope hc.le hab _)
  set p : ℝ := Function.surjInv hsurj (2 * Real.pi * ν N (i N)) with hpdef
  have hp : extForce L c a b (q N) p = 2 * Real.pi * ν N (i N) := Function.surjInv_eq hsurj _
  have hxmf : extForce L c a b (q N) xm = force L c a b (q N) xm := extForce_of_mem hxmab
  have hxpf : extForce L c a b (q N) xp = force L c a b (q N) xp := extForce_of_mem hxpab
  have hpm : xm < p := by
    by_contra hle
    push Not at hle
    have := extForce_slope (L := L) hc.le hab (q N) p xm hle
    nlinarith [hlabs.1, hlabs.2]
  have hpp : p < xp := by
    by_contra hle
    push Not at hle
    have := extForce_slope (L := L) hc.le hab (q N) xp p hle
    nlinarith [hlabs.1, hlabs.2]
  have hi : i N ∈ cluster a b (q N) :=
    Finset.mem_filter.mpr ⟨mem_univ _, ⟨hloc'.1.le, hloc'.2.le⟩⟩
  have hcb := cluster_bound hL hc hab (hB N).sorted (hB N).labels (hB N).eqn hi hp
  have hsq : 4 * Real.sqrt (c * (cluster a b (q N)).card / L) ≤ δ / 2 := by
    have h1 : c * (cluster a b (q N)).card / L ≤ (δ / 8) ^ 2 := by
      have e : c * (cluster a b (q N)).card / L = (κ / L) * (Kc / ((N : ℝ) + 1)) := by
        rw [hcdef, hKc]; field_simp
      rw [e]
      calc (κ / L) * (Kc / ((N : ℝ) + 1)) ≤ (κ / L) * τ0 := by gcongr
        _ = κ * τ0 / L := by ring
        _ ≤ (δ / 8) ^ 2 := hτ2
    have h2 : Real.sqrt (c * (cluster a b (q N)).card / L) ≤ δ / 8 := by
      calc Real.sqrt (c * (cluster a b (q N)).card / L) ≤ Real.sqrt ((δ / 8) ^ 2) :=
            Real.sqrt_le_sqrt h1
        _ = δ / 8 := Real.sqrt_sq (by positivity)
    linarith
  rw [Real.dist_eq]
  have h3 : |q N (i N) - p| ≤ δ / 2 := hcb.trans hsq
  have h4 : |p - xs| < δ' := by
    rw [abs_lt]; constructor <;> linarith
  calc |q N (i N) - xs| = |(q N (i N) - p) + (p - xs)| := by ring_nf
    _ ≤ |q N (i N) - p| + |p - xs| := abs_add_le _ _
    _ < δ := by linarith

end QuantumNLS.SelectionBand

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.SelectionBand.theta_mono
#print axioms QuantumNLS.SelectionBand.M_tendsto
#print axioms QuantumNLS.SelectionBand.force_approx_band
#print axioms QuantumNLS.SelectionBand.cluster_frac
#print axioms QuantumNLS.SelectionBand.selection_core
