import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB3DenseJ

/-! # Track B, step B3: the short-time Duhamel estimate for general `L^{4/3}` forcings

`duhamel_L43` : there is `K < ∞` such that for every `0 < δ ≤ 1` and every
`F ∈ L^{4/3}(ℝ × 𝕋)` there are `v : ℝ → L²(𝕋)` (continuous) and a spacetime function
`w : ℝ × 𝕋 → ℂ` (a.e. strongly measurable) with

* `l2ToHm1 (v t) = ∫₀ᵗ e^{i(t-r)∂ₓ²}(-iF(r)) dr` (the actual `H⁻¹` Bochner integral) for `t ∈ [0,δ]`;
* `‖v t‖_{L²} ≤ K δ^{1/16} ‖F‖_{L^{4/3}(ℝ×𝕋)}` for every `t`;
* `‖w‖_{L⁴(ℝ×𝕋)} ≤ K δ^{1/16} ‖F‖_{L^{4/3}(ℝ×𝕋)}`;
* for a.e. `t`, `w(t,·) = v t` a.e. on `𝕋`.

Proof (completeness route, replacing Pro's Fatou step): dense forcings `G_n` with
`‖F - G_n‖_{L^{4/3}} ≤ 2⁻ⁿ` (`dense_forcing_approx`); by linearity (`dField_sub`, `wOut_sub`) and the
dense estimates (`dField_trace`, `wOut_L4`) the dense outputs are geometrically Cauchy uniformly in
`t` in `L²` and in `L⁴(ℝ × 𝕋)`; the `L²` limits are continuous (uniform limit), the `L⁴` sequence
converges a.e. (`ae_tendsto_of_cauchy_eLpNorm`); the bounds pass to the limit (Fatou for `eLpNorm`);
the identification with the Bochner integral passes to the limit through the crude continuity
`norm_duhamel_sub_le` and `L^{4/3} ⊂ L¹` on the finite slab `[0,δ] × 𝕋`.
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

open MeasureTheory Filter Topology NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38
open SchwartzMap
open scoped ENNReal

attribute [local instance] isProbabilityMeasure_spatialMeasure

/-- The slab measure on `[0,δ] × 𝕋`. -/
abbrev slabMeasure (δ : ℝ) : Measure (ℝ × PhysicalCircle) :=
  ((volume : Measure ℝ).restrict (Set.Icc 0 δ)).prod spatialMeasure

theorem slabMeasure_le (δ : ℝ) : slabMeasure δ ≤ stMeasure := by
  have h := Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := spatialMeasure)
    (Set.Icc 0 δ) Set.univ
  rw [Measure.restrict_univ] at h
  rw [slabMeasure, h]
  exact Measure.restrict_le_self

theorem emL {a b c : ℝ≥0∞} (h : b ≤ c) : a * b ≤ a * c := by gcongr

theorem emR {a b c : ℝ≥0∞} (h : b ≤ c) : b * a ≤ c * a := by gcongr

theorem one_le_four_thirds : (1 : ℝ≥0∞) ≤ 4 / 3 := by
  rw [four_thirds_eq]; exact ENNReal.one_le_ofReal.2 (by norm_num)

theorem four_thirds_ne_top : (4 / 3 : ℝ≥0∞) ≠ ⊤ := by
  rw [four_thirds_eq]; exact ENNReal.ofReal_ne_top

/-- `L^{4/3}(ℝ × 𝕋) ⊂ L¹([0,δ] × 𝕋)`, quantitatively. -/
theorem integral_norm_slab_le (δ : ℝ) {f : ℝ × PhysicalCircle → ℂ}
    (hf : AEStronglyMeasurable f stMeasure) (hfin : eLpNorm f (4 / 3) stMeasure ≠ ⊤) :
    ∫ p, ‖f p‖ ∂slabMeasure δ ≤
      (eLpNorm f (4 / 3) stMeasure * slabMeasure δ Set.univ ^ (1 / (1 : ℝ≥0∞).toReal -
        1 / (4 / 3 : ℝ≥0∞).toReal)).toReal := by
  have hfs : AEStronglyMeasurable f (slabMeasure δ) := hf.mono_measure (slabMeasure_le δ)
  have hne : slabMeasure δ Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (4 / 3 : ℝ≥0∞).toReal) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by rw [four_thirds_eq, ENNReal.toReal_ofReal (by norm_num)]; norm_num)
      (measure_ne_top _ _)
  rw [integral_norm_eq_lintegral_enorm hfs, ← eLpNorm_one_eq_lintegral_enorm]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top hfin hne) ?_
  refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ one_le_four_thirds hfs).trans ?_
  exact emR (eLpNorm_mono_measure _ (slabMeasure_le δ))
  exact hfs

theorem geom_tendsto {A : ℝ≥0∞} (hA : A ≠ ⊤) :
    Tendsto (fun n : ℕ => A * 2⁻¹ ^ n) atTop (𝓝 0) := by
  have h := ENNReal.Tendsto.const_mul
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (ENNReal.inv_lt_one.2 (by norm_num : (1 : ℝ≥0∞) < 2))) (Or.inr hA)
  rwa [mul_zero] at h

theorem bound_tendsto {A : ℝ≥0∞} (hA : A ≠ ⊤) (E : ℝ≥0∞) :
    Tendsto (fun n : ℕ => A * (E + 2⁻¹ ^ n)) atTop (𝓝 (A * E)) := by
  have h := ENNReal.Tendsto.const_mul (tendsto_const_nhds (x := E).add
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (ENNReal.inv_lt_one.2 (by norm_num : (1 : ℝ≥0∞) < 2)))) (Or.inr hA)
  rwa [add_zero] at h

theorem two_inv_pow_succ_le (n : ℕ) : (2⁻¹ : ℝ≥0∞) ^ (n + 1) ≤ 2⁻¹ ^ n := by
  rw [pow_succ]
  exact mul_le_of_le_one_right' (ENNReal.inv_le_one.2 one_le_two)

theorem two_inv_pow_anti {N n : ℕ} (h : N ≤ n) : (2⁻¹ : ℝ≥0∞) ^ n ≤ 2⁻¹ ^ N :=
  pow_le_pow_right_of_le_one' (ENNReal.inv_le_one.2 one_le_two) h

/-- **Short-time Duhamel estimate for general `L^{4/3}(ℝ × 𝕋)` forcings**, with identification
with the actual `H⁻¹` Bochner Duhamel integral on `[0,δ]`. -/
theorem duhamel_L43 : ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
    ∀ F : ℝ × PhysicalCircle → ℂ, MemLp F (4 / 3) stMeasure →
    ∃ (v : ℝ → PhysicalL2) (w : ℝ × PhysicalCircle → ℂ),
      Continuous v ∧
      (∀ t ∈ Set.Icc 0 δ, l2ToHm1 (v t) = duhH F t) ∧
      (∀ t, ‖v t‖ₑ ≤ K * ENNReal.ofReal (δ ^ (1 / 16 : ℝ)) * eLpNorm F (4 / 3) stMeasure) ∧
      AEStronglyMeasurable w stMeasure ∧
      eLpNorm w 4 stMeasure ≤ K * ENNReal.ofReal (δ ^ (1 / 16 : ℝ)) * eLpNorm F (4 / 3) stMeasure ∧
      (∀ᵐ t ∂(volume : Measure ℝ),
        (fun x => w (t, x)) =ᵐ[spatialMeasure] (v t : PhysicalCircle → ℂ)) := by
  obtain ⟨K1, hK1, htr⟩ := dField_trace
  obtain ⟨K2, hK2, hL4⟩ := wOut_L4
  refine ⟨K1 + K2, ENNReal.add_ne_top.2 ⟨hK1, hK2⟩, fun δ hδ hδ1 F hF => ?_⟩
  set b : ℝ≥0∞ := ENNReal.ofReal (δ ^ (1 / 16 : ℝ)) with hb_def
  have hb : b ≠ ⊤ := ENNReal.ofReal_ne_top
  set E : ℝ≥0∞ := eLpNorm F (4 / 3) stMeasure with hE
  have hEt : E ≠ ⊤ := hF.eLpNorm_ne_top
  have h2 : (2⁻¹ : ℝ≥0∞) ≠ 0 := ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top
  choose S G hGS hG using fun n : ℕ =>
    dense_forcing_approx one_le_four_thirds four_thirds_ne_top hF (ε := 2⁻¹ ^ n) (pow_ne_zero _ h2)
  -- dense differences and dense norms
  have hdiff : ∀ n m, eLpNorm (denseSp (S n ∪ S m) (G n - G m)) (4 / 3) stMeasure ≤
      2⁻¹ ^ n + 2⁻¹ ^ m := by
    intro n m
    rw [denseSp_sub_union (hGS n) (hGS m), add_comm]
    calc eLpNorm (denseSp (S n) (G n) - denseSp (S m) (G m)) (4 / 3) stMeasure
        = eLpNorm ((F - denseSp (S m) (G m)) - (F - denseSp (S n) (G n))) (4 / 3) stMeasure := by
          congr 1; abel
      _ ≤ _ := eLpNorm_sub_le one_le_four_thirds
      _ ≤ _ := add_le_add (hG m) (hG n)
  have hnorm : ∀ n, eLpNorm (denseSp (S n) (G n)) (4 / 3) stMeasure ≤ E + 2⁻¹ ^ n := by
    intro n
    calc eLpNorm (denseSp (S n) (G n)) (4 / 3) stMeasure
        = eLpNorm (F - (F - denseSp (S n) (G n))) (4 / 3) stMeasure := by rw [sub_sub_cancel]
      _ ≤ _ := eLpNorm_sub_le one_le_four_thirds
      _ ≤ _ := add_le_add le_rfl (hG n)
  have hsum_le : ∀ N n m : ℕ, N ≤ n → N ≤ m → (2⁻¹ : ℝ≥0∞) ^ n + 2⁻¹ ^ m ≤ 2 * 2⁻¹ ^ N :=
    fun N n m hn hm => by rw [two_mul]; exact add_le_add (two_inv_pow_anti hn) (two_inv_pow_anti hm)
  -- the `L²` part
  set y : ℕ → ℝ → PhysicalL2 := fun n => dField δ (S n) (G n) with hy
  have hy_diff : ∀ n m t, edist (y n t) (y m t) ≤ K1 * b * (2⁻¹ ^ n + 2⁻¹ ^ m) := by
    intro n m t
    rw [edist_eq_enorm_sub, hy, ← dField_sub δ (hGS n) (hGS m)]
    exact (htr δ hδ _ _ (sub_zero_off (hGS n) (hGS m)) t).trans (emL (hdiff n m))
  have hCg : K1 * b * 2 ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top hK1 hb) ENNReal.ofNat_ne_top
  have hgeo : ∀ t n, edist (y n t) (y (n + 1) t) ≤ K1 * b * 2 / 2 ^ n := by
    intro t n
    rw [div_eq_mul_inv, ENNReal.inv_pow, mul_assoc]
    exact (hy_diff n (n + 1) t).trans (emL (hsum_le n n (n + 1) le_rfl n.le_succ))
  have hcs : ∀ t, CauchySeq fun n => y n t := fun t =>
    cauchySeq_of_edist_le_geometric_two _ hCg (hgeo t)
  set v : ℝ → PhysicalL2 := fun t => limUnder atTop fun n => y n t with hv_def
  have hv : ∀ t, Tendsto (fun n => y n t) atTop (𝓝 (v t)) := fun t => (hcs t).tendsto_limUnder
  have hunif : ∀ t n, edist (y n t) (v t) ≤ 2 * (K1 * b * 2) * 2⁻¹ ^ n := fun t n => by
    have := edist_le_of_edist_le_geometric_two_of_tendsto _ (hgeo t) (hv t) n
    rwa [div_eq_mul_inv, ENNReal.inv_pow] at this
  have hv_cont : Continuous v := by
    have hTU : TendstoUniformly y v atTop := by
      rw [EMetric.tendstoUniformly_iff]
      intro ε hε
      filter_upwards [(geom_tendsto (ENNReal.mul_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hCg)).eventually
        (gt_mem_nhds hε)] with n hn t
      rw [edist_comm]
      exact (hunif t n).trans_lt hn
    exact hTU.continuous (Frequently.of_forall fun n => continuous_dField δ (S n) (G n))
  -- the identification on `[0, δ]`
  have hident : ∀ t ∈ Set.Icc 0 δ, l2ToHm1 (v t) = duhH F t := by
    intro t ht
    have hA : Tendsto (fun n => l2ToHm1 (y n t)) atTop (𝓝 (l2ToHm1 (v t))) :=
      (l2ToHm1.continuous.tendsto _).comp (hv t)
    have hB : Tendsto (fun n => duhH (denseSp (S n) (G n)) t) atTop (𝓝 (duhH F t)) := by
      have hFs : Integrable F (slabMeasure δ) :=
        memLp_one_iff_integrable.1 ((hF.mono_measure (slabMeasure_le δ)).mono_exponent
          one_le_four_thirds)
      set c : ℝ≥0∞ := slabMeasure δ Set.univ ^ (1 / (1 : ℝ≥0∞).toReal -
        1 / (4 / 3 : ℝ≥0∞).toReal) with hc
      have hct : c ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg
        (by rw [four_thirds_eq, ENNReal.toReal_ofReal (by norm_num)]; norm_num) (measure_ne_top _ _)
      have hbd : ∀ n, ‖duhH F t - duhH (denseSp (S n) (G n)) t‖ ≤
          hm1Const * (c * 2⁻¹ ^ n).toReal := by
        intro n
        have hmeas : AEStronglyMeasurable (F - denseSp (S n) (G n)) stMeasure :=
          hF.aestronglyMeasurable.sub (continuous_denseSp _ _).aestronglyMeasurable
        have hfin : eLpNorm (F - denseSp (S n) (G n)) (4 / 3) stMeasure ≠ ⊤ :=
          ne_top_of_le_ne_top (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 two_ne_zero)) (hG n)
        refine (norm_duhamel_sub_le hFs (integrable_denseSp_slab _ _ 0 δ) t ⟨le_rfl, hδ.le⟩ ht).trans
          (mul_le_mul_of_nonneg_left ?_ hm1Const_nonneg)
        refine (integral_norm_slab_le δ hmeas hfin).trans (ENNReal.toReal_mono
          (ENNReal.mul_ne_top hct (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 two_ne_zero))) ?_)
        rw [mul_comm c]
        exact emR (hG n)
      have hlim : Tendsto (fun n : ℕ => hm1Const * (c * 2⁻¹ ^ n).toReal) atTop (𝓝 0) := by
        have h := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (geom_tendsto hct)).const_mul
          hm1Const
        simpa using h
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
      rw [norm_sub_rev]
      exact hbd n
    have hAB : (fun n => l2ToHm1 (y n t)) = fun n => duhH (denseSp (S n) (G n)) t :=
      funext fun n => dField_ident hδ hδ1 (S n) (G n) (hGS n) ht
    rw [hAB] at hA
    exact tendsto_nhds_unique hA hB
  -- the trace bound
  have hvb : ∀ t, ‖v t‖ₑ ≤ (K1 + K2) * b * E := by
    intro t
    have hlhs : Tendsto (fun n => ‖y n t‖ₑ) atTop (𝓝 ‖v t‖ₑ) :=
      (continuous_enorm.tendsto _).comp (hv t)
    have hle : ∀ n, ‖y n t‖ₑ ≤ K1 * b * (E + 2⁻¹ ^ n) := fun n =>
      (htr δ hδ _ _ (hGS n) t).trans (emL (hnorm n))
    refine (le_of_tendsto_of_tendsto' hlhs (bound_tendsto (ENNReal.mul_ne_top hK1 hb) E) hle).trans ?_
    exact emR (emR le_self_add)
  -- the `L⁴` part
  set w : ℕ → ℝ × PhysicalCircle → ℂ := fun n => wOut δ (S n) (G n) with hw
  have hwm : ∀ n, AEStronglyMeasurable (w n) stMeasure := fun n =>
    (continuous_wOut δ (S n) (G n)).aestronglyMeasurable
  have hw_diff : ∀ n m, eLpNorm (w n - w m) 4 stMeasure ≤ K2 * b * (2⁻¹ ^ n + 2⁻¹ ^ m) := by
    intro n m
    rw [hw, ← wOut_sub δ (hGS n) (hGS m)]
    exact (hL4 δ hδ _ _ (sub_zero_off (hGS n) (hGS m))).trans (emL (hdiff n m))
  have hA2 : K2 * b * 2 ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top hK2 hb) ENNReal.ofNat_ne_top
  have hae : ∀ᵐ p ∂stMeasure, ∃ l : ℂ, Tendsto (fun n => w n p) atTop (𝓝 l) := by
    refine Lp.ae_tendsto_of_cauchy_eLpNorm hwm (by norm_num : (1 : ℝ≥0∞) ≤ 4) (B := fun N => (K2 * b * 2 + 1) * 2⁻¹ ^ N)
      ?_ ?_
    · rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
      exact ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨hA2, ENNReal.one_ne_top⟩) ENNReal.ofNat_ne_top
    · intro N n m hn hm
      refine (hw_diff n m).trans_lt ?_
      calc K2 * b * (2⁻¹ ^ n + 2⁻¹ ^ m) ≤ K2 * b * (2 * 2⁻¹ ^ N) :=
            emL (hsum_le N n m hn hm)
        _ = K2 * b * 2 * 2⁻¹ ^ N := by ring
        _ < (K2 * b * 2 + 1) * 2⁻¹ ^ N := by
          rw [mul_comm _ (2⁻¹ ^ N), mul_comm _ (2⁻¹ ^ N)]
          exact ENNReal.mul_lt_mul_right (pow_ne_zero _ h2) (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 two_ne_zero))
              (ENNReal.lt_add_right hA2 one_ne_zero)
  set W : ℝ × PhysicalCircle → ℂ := fun p => limUnder atTop fun n => w n p with hW_def
  have hWlim : ∀ᵐ p ∂stMeasure, Tendsto (fun n => w n p) atTop (𝓝 (W p)) := by
    filter_upwards [hae] with p hp
    exact tendsto_nhds_limUnder hp
  have hWm : AEStronglyMeasurable W stMeasure := aestronglyMeasurable_of_tendsto_ae atTop hwm hWlim
  have hWb : eLpNorm W 4 stMeasure ≤ (K1 + K2) * b * E := by
    refine (Lp.eLpNorm_lim_le_liminf_eLpNorm hwm W hWm hWlim).trans ?_
    have hle : ∀ n, eLpNorm (w n) 4 stMeasure ≤ K2 * b * (E + 2⁻¹ ^ n) := fun n =>
      (hL4 δ hδ _ _ (hGS n)).trans (emL (hnorm n))
    refine (Filter.liminf_le_liminf (Eventually.of_forall hle)).trans ?_
    rw [(bound_tendsto (ENNReal.mul_ne_top hK2 hb) E).liminf_eq]
    exact emR (emR le_add_self)
  -- slices of `W` are the `L²` limits
  have hslice : ∀ᵐ t ∂(volume : Measure ℝ),
      (fun x => W (t, x)) =ᵐ[spatialMeasure] (v t : PhysicalCircle → ℂ) := by
    filter_upwards [Measure.ae_ae_of_ae_prod hWlim] with t ht
    set f : ℕ → PhysicalCircle → ℂ := fun n x => w n (t, x) - (v t : PhysicalCircle → ℂ) x
    have hfm : ∀ n, AEStronglyMeasurable (f n) spatialMeasure := fun n =>
      ((continuous_wOut δ (S n) (G n)).comp (Continuous.prodMk_right t)).aestronglyMeasurable.sub
        (Lp.aestronglyMeasurable _)
    have hglim : ∀ᵐ x ∂spatialMeasure,
        Tendsto (fun n => f n x) atTop (𝓝 (W (t, x) - (v t : PhysicalCircle → ℂ) x)) := by
      filter_upwards [ht] with x hx
      exact hx.sub tendsto_const_nhds
    have hgm := aestronglyMeasurable_of_tendsto_ae atTop hfm hglim
    have hfn : ∀ n, eLpNorm (f n) 2 spatialMeasure = edist (y n t) (v t) := by
      intro n
      rw [edist_eq_enorm_sub, Lp.enorm_def]
      refine eLpNorm_congr_ae ?_
      filter_upwards [dField_ae δ (S n) (G n) t, Lp.coeFn_sub (y n t) (v t)] with x h1 h2
      rw [h2, Pi.sub_apply, hy]
      simp only [f, hw, h1]
    have h0 : eLpNorm (fun x => W (t, x) - (v t : PhysicalCircle → ℂ) x) 2 spatialMeasure = 0 := by
      refine le_antisymm ((Lp.eLpNorm_lim_le_liminf_eLpNorm hfm _ hgm hglim).trans ?_) bot_le
      simp only [hfn]
      rw [((tendsto_iff_edist_tendsto_0.1 (hv t))).liminf_eq]
    rw [eLpNorm_eq_zero_iff two_ne_zero] at h0
    filter_upwards [h0] with x hx
    exact sub_eq_zero.1 hx
  exact ⟨v, W, hv_cont, hident, hvb, hWm, hWb, hslice⟩

theorem slabMeasure_eq (δ : ℝ) :
    slabMeasure δ = stMeasure.restrict (Set.Icc 0 δ ×ˢ Set.univ) := by
  have h := Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := spatialMeasure)
    (Set.Icc 0 δ) Set.univ
  rw [Measure.restrict_univ] at h
  exact h

/-- **Forcing given on the slab `J × 𝕋`, `J = [0,δ]`**: the same estimate with the norm
`‖F‖_{L^{4/3}(J×𝕋)}` (apply `duhamel_L43` to `1_{J×𝕋} F`, whose `L^{4/3}(ℝ×𝕋)` norm is
`‖F‖_{L^{4/3}(J×𝕋)}` and whose Duhamel integral agrees with that of `F` on `J`). -/
theorem duhamel_L43_slab : ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
    ∀ F : ℝ × PhysicalCircle → ℂ, MemLp F (4 / 3) (slabMeasure δ) →
    ∃ (v : ℝ → PhysicalL2) (w : ℝ × PhysicalCircle → ℂ),
      Continuous v ∧
      (∀ t ∈ Set.Icc 0 δ, l2ToHm1 (v t) = duhH F t) ∧
      (∀ t, ‖v t‖ₑ ≤ K * ENNReal.ofReal (δ ^ (1 / 16 : ℝ)) * eLpNorm F (4 / 3) (slabMeasure δ)) ∧
      AEStronglyMeasurable w stMeasure ∧
      eLpNorm w 4 stMeasure ≤
        K * ENNReal.ofReal (δ ^ (1 / 16 : ℝ)) * eLpNorm F (4 / 3) (slabMeasure δ) ∧
      (∀ᵐ t ∂(volume : Measure ℝ),
        (fun x => w (t, x)) =ᵐ[spatialMeasure] (v t : PhysicalCircle → ℂ)) := by
  obtain ⟨K, hK, h⟩ := duhamel_L43
  refine ⟨K, hK, fun δ hδ hδ1 F hF => ?_⟩
  have hs : MeasurableSet (Set.Icc (0 : ℝ) δ ×ˢ (Set.univ : Set PhysicalCircle)) :=
    measurableSet_Icc.prod MeasurableSet.univ
  have hF' : MemLp ((Set.Icc 0 δ ×ˢ Set.univ).indicator F) (4 / 3) stMeasure := by
    rw [memLp_indicator_iff_restrict hs, ← slabMeasure_eq]; exact hF
  have hn : eLpNorm ((Set.Icc 0 δ ×ˢ Set.univ).indicator F) (4 / 3) stMeasure =
      eLpNorm F (4 / 3) (slabMeasure δ) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hs, ← slabMeasure_eq]
  obtain ⟨v, w, h1, h2, h3, h4, h5, h6⟩ := h δ hδ hδ1 _ hF'
  refine ⟨v, w, h1, fun t ht => ?_, fun t => hn ▸ h3 t, h4, hn ▸ h5, h6⟩
  rw [h2 t ht]
  unfold duhH
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [Set.uIcc_of_le ht.1] at hr
  have hx : ∀ x, (Set.Icc 0 δ ×ˢ Set.univ).indicator F (r, x) = F (r, x) := fun x =>
    Set.indicator_of_mem (show (r, x) ∈ Set.Icc 0 δ ×ˢ (Set.univ : Set PhysicalCircle) from
      ⟨⟨hr.1, hr.2.trans ht.2⟩, Set.mem_univ x⟩) F
  simp only [hx]

end LiebLiniger.FixedPeriod.ALLS.PdeB
