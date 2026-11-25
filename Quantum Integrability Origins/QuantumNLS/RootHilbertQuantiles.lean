import QuantumNLS.RootHilbertL2

/-!
# R-409128A9 `lem:root-Hilbert-quantiles` (ROOT_scalar_uniqueness.tex:69-134)

Source statement. Let `μ = ρ dx` and `ν = σ dx` have the same finite positive mass `m`, with bounded,
nonnegative, locally Hölder densities. Let `q, q̃ : (0,m) → ℝ` be their increasing quantile
functions. If `q − q̃ ∈ L²(0,m)`, then
`∫_0^m (q − q̃)(s) [Hρ(q(s)) − Hσ(q̃(s))] ds ≤ 0`. Every term is integrable. Neither measure is
required to have a finite second moment.

Realization. The density hypotheses are R-064239ED's `HilbertHyp` (`ρ ≥ 0`, `ρ ∈ L¹ ∩ L^∞`, locally
Hölder; "bounded with finite mass" is exactly `L¹ ∩ L^∞` for a nonnegative density), the mass is
`∫ ρ = ∫ σ = m > 0`, `Hρ = hilbertPV ρ`, `H_ε ρ = hilbertTrunc ρ ε` (sonnet_fourier's
`RootHilbertTruncations` `a8bc2895…` and `RootHilbertL2` `53ddff94…`, read-only; through them
`RootHilbertConv` `0ece6138…`, `RootHilbertEnergy` `66903e82…`). The quantile is the printed
`q(s) = inf {x : F(x) ≥ s}`, `F(x) = ∫_{-∞}^x ρ` (`cdf`, `qtl`), on `(0,m)` with Lebesgue measure
`volume.restrict (Ioo 0 m)`. No second-moment hypothesis occurs.

Printed proof followed:
* quantile facts: `cdf_qtl` (`F(q(s)) = s`), `qtl_le_iff`, `qtl_strictMonoOn`, `qtl_separation`
  (`|s − t| ≤ B|q(s) − q(t)|`, eq:root-quantile-separation), `map_qtl` (`q` pushes Lebesgue measure on
  `(0,m)` to `ρ dx`);
* `hilbertTrunc_qtl`: `H_ε ρ(x) = ∫_0^m k_ε(x − q(t)) dt`, `k_ε(a) = 1_{|a|>ε}/a` (`kt`);
* `trunc_pairing_le`: symmetrization (eq:root-quantile-symmetrization) and the region analysis give
  `L_ε ≤ m(B + B̃)ε` (the printed bound is `2m(B+B̃)ε`; the sharper constant is what the same
  argument yields);
* `root_Hilbert_quantiles`: `L²(0,m)` convergence of the pulled-back truncations (R-064239ED in
  `L²(ρ dx)` and the push-forward), Cauchy–Schwarz, and `ε ↓ 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace QuantumNLS.RootHilbertQuantiles

open QuantumNLS.RootHilbert

/-! ## 1. Distribution function and quantile -/

/-- `F(x) = ∫_{-∞}^x ρ`. -/
def cdf (ρ : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y in Iic x, ρ y

/-- The quantile `q(s) = inf {x : F(x) ≥ s}`. -/
def qtl (ρ : ℝ → ℝ) (s : ℝ) : ℝ := sInf {x | s ≤ cdf ρ x}

section Quantile

variable {ρ : ℝ → ℝ} (hnn : ∀ x, 0 ≤ ρ x) (hi : Integrable ρ) {B : ℝ} (hB : ∀ x, ρ x ≤ B)
include hnn hi

lemma cdf_nonneg (x : ℝ) : 0 ≤ cdf ρ x := setIntegral_nonneg measurableSet_Iic fun y _ => hnn y

lemma cdf_le (x : ℝ) : cdf ρ x ≤ ∫ y, ρ y :=
  setIntegral_le_integral hi (Eventually.of_forall hnn)

lemma cdf_sub (x y : ℝ) : cdf ρ y - cdf ρ x = ∫ t in x..y, ρ t :=
  intervalIntegral.integral_Iic_sub_Iic hi.integrableOn hi.integrableOn

include hB in
lemma abs_cdf_sub_le (x y : ℝ) : |cdf ρ y - cdf ρ x| ≤ B * |y - x| := by
  rw [cdf_sub hnn hi, ← Real.norm_eq_abs]
  exact intervalIntegral.norm_integral_le_of_norm_le_const fun t _ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn t)]; exact hB t

include hB in
lemma continuous_cdf : Continuous (cdf ρ) := by
  have hB0 : 0 ≤ B := (hnn 0).trans (hB 0)
  refine (LipschitzWith.of_dist_le_mul (K := B.toNNReal) fun x y => ?_).continuous
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hB0]
  exact abs_cdf_sub_le hnn hi hB y x

lemma cdf_mono : Monotone (cdf ρ) := fun _ _ hxy =>
  setIntegral_mono_set hi.integrableOn (Eventually.of_forall fun t => hnn t)
    (Eventually.of_forall (Iic_subset_Iic.2 hxy))

lemma tendsto_cdf_atTop : Tendsto (cdf ρ) atTop (𝓝 (∫ y, ρ y)) := by
  have := tendsto_setIntegral_of_monotone (μ := volume) (f := ρ) (s := fun x : ℝ => Iic x)
    (fun x => measurableSet_Iic) (fun a b h => Iic_subset_Iic.2 h)
    (by rw [iUnion_Iic]; exact hi.integrableOn)
  rwa [iUnion_Iic, setIntegral_univ] at this

lemma tendsto_cdf_atBot : Tendsto (cdf ρ) atBot (𝓝 0) := by
  have := tendsto_setIntegral_of_antitone (μ := volume) (f := ρ) (s := fun x : ℝ => Iic (-x))
    (fun x => measurableSet_Iic) (fun a b h => Iic_subset_Iic.2 (neg_le_neg h))
    ⟨0, hi.integrableOn⟩
  have he : (⋂ n : ℝ, Iic (-n)) = ∅ := by
    ext x
    simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false, not_forall, not_le]
    exact ⟨-x + 1, by linarith⟩
  rw [he, Measure.restrict_empty, integral_zero_measure] at this
  refine (this.comp tendsto_neg_atBot_atTop).congr fun x => ?_
  simp [cdf]

lemma qset_nonempty {s : ℝ} (hs : s < ∫ y, ρ y) : {x | s ≤ cdf ρ x}.Nonempty := by
  obtain ⟨x, hx⟩ := ((tendsto_cdf_atTop hnn hi).eventually (lt_mem_nhds hs)).exists
  exact ⟨x, hx.le⟩

lemma qset_bddBelow {s : ℝ} (hs : 0 < s) : BddBelow {x | s ≤ cdf ρ x} := by
  obtain ⟨x0, hx0⟩ := ((tendsto_cdf_atBot hnn hi).eventually (gt_mem_nhds hs)).exists
  refine ⟨x0, fun x hx => ?_⟩
  by_contra h
  push Not at h
  have := cdf_mono hnn hi h.le
  have hx' : s ≤ cdf ρ x := hx
  linarith

include hB in
/-- `F(q(s)) = s` for `0 < s < m`. -/
lemma cdf_qtl {s : ℝ} (hs0 : 0 < s) (hs : s < ∫ y, ρ y) : cdf ρ (qtl ρ s) = s := by
  have hne := qset_nonempty hnn hi hs
  have hbdd := qset_bddBelow hnn hi hs0
  have hcont := continuous_cdf hnn hi hB
  have hclosed : IsClosed {x | s ≤ cdf ρ x} := isClosed_le continuous_const hcont
  have hmem : s ≤ cdf ρ (qtl ρ s) := hclosed.csInf_mem hne hbdd
  refine le_antisymm ?_ hmem
  by_contra h
  push Not at h
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 (hcont.continuousAt (x := qtl ρ s))
    (cdf ρ (qtl ρ s) - s) (by linarith)
  have h1 : s ≤ cdf ρ (qtl ρ s - δ / 2) := by
    have := hδ' (x := qtl ρ s - δ / 2) (by
      rw [Real.dist_eq, show qtl ρ s - δ / 2 - qtl ρ s = -(δ / 2) by ring, abs_neg,
        abs_of_pos (by linarith)]; linarith)
    rw [Real.dist_eq] at this
    linarith [neg_abs_le (cdf ρ (qtl ρ s - δ / 2) - cdf ρ (qtl ρ s))]
  have := csInf_le hbdd h1
  unfold qtl at this
  linarith

include hB in
/-- `q(s) ≤ x ↔ s ≤ F(x)`. -/
lemma qtl_le_iff {s : ℝ} (hs0 : 0 < s) (hs : s < ∫ y, ρ y) (x : ℝ) :
    qtl ρ s ≤ x ↔ s ≤ cdf ρ x := by
  constructor
  · intro h; rw [← cdf_qtl hnn hi hB hs0 hs]; exact cdf_mono hnn hi h
  · intro h; exact csInf_le (qset_bddBelow hnn hi hs0) h

include hB in
lemma qtl_strictMonoOn : StrictMonoOn (qtl ρ) (Ioo 0 (∫ y, ρ y)) := by
  intro s hs t ht hst
  have hle : qtl ρ s ≤ qtl ρ t := (qtl_le_iff hnn hi hB hs.1 hs.2 _).2
    (by rw [cdf_qtl hnn hi hB ht.1 ht.2]; exact hst.le)
  refine lt_of_le_of_ne hle fun heq => ?_
  have := congrArg (cdf ρ) heq
  rw [cdf_qtl hnn hi hB hs.1 hs.2, cdf_qtl hnn hi hB ht.1 ht.2] at this
  linarith

include hB in
/-- eq:root-quantile-separation: `|s − t| ≤ B |q(s) − q(t)|`. -/
lemma qtl_separation {s t : ℝ} (hs : s ∈ Ioo 0 (∫ y, ρ y)) (ht : t ∈ Ioo 0 (∫ y, ρ y)) :
    |s - t| ≤ B * |qtl ρ s - qtl ρ t| := by
  have := abs_cdf_sub_le hnn hi hB (qtl ρ t) (qtl ρ s)
  rwa [cdf_qtl hnn hi hB hs.1 hs.2, cdf_qtl hnn hi hB ht.1 ht.2] at this

include hB in
lemma aemeasurable_qtl :
    AEMeasurable (qtl ρ) (volume.restrict (Ioo 0 (∫ y, ρ y))) :=
  aemeasurable_restrict_of_monotoneOn measurableSet_Ioo (qtl_strictMonoOn hnn hi hB).monotoneOn

include hB in
/-- **The quantile pushes Lebesgue measure on `(0,m)` to `ρ dx`.** -/
lemma map_qtl (_hm : 0 < ∫ y, ρ y) :
    (volume.restrict (Ioo 0 (∫ y, ρ y))).map (qtl ρ) = rhoMeasure ρ := by
  set m := ∫ y, ρ y with hmdef
  have hq := aemeasurable_qtl hnn hi hB
  have : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) m)) := isFiniteMeasure_restrict.2 (by simp)
  refine Measure.ext_of_Iic _ _ fun a => ?_
  rw [Measure.map_apply_of_aemeasurable hq measurableSet_Iic,
    Measure.restrict_apply' measurableSet_Ioo]
  have hset : qtl ρ ⁻¹' Iic a ∩ Ioo 0 m = Ioo 0 m ∩ Iic (cdf ρ a) := by
    ext s
    simp only [mem_inter_iff, mem_preimage, mem_Iic]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, (qtl_le_iff hnn hi hB h2.1 h2.2 a).1 h1⟩
    · rintro ⟨h2, h1⟩; exact ⟨(qtl_le_iff hnn hi hB h2.1 h2.2 a).2 h1, h2⟩
  rw [hset]
  have hc0 := cdf_nonneg hnn hi a
  have hcm : cdf ρ a ≤ m := cdf_le hnn hi a
  have hvol : volume (Ioo 0 m ∩ Iic (cdf ρ a)) = ENNReal.ofReal (cdf ρ a) := by
    apply le_antisymm
    · calc volume (Ioo 0 m ∩ Iic (cdf ρ a)) ≤ volume (Ioc 0 (cdf ρ a)) :=
            measure_mono fun s hs => ⟨hs.1.1, hs.2⟩
        _ = _ := by rw [Real.volume_Ioc, sub_zero]
    · calc ENNReal.ofReal (cdf ρ a) = volume (Ioo 0 (cdf ρ a)) := by
            rw [Real.volume_Ioo, sub_zero]
        _ ≤ volume (Ioo 0 m ∩ Iic (cdf ρ a)) :=
            measure_mono fun s hs => ⟨⟨hs.1, lt_of_lt_of_le hs.2 hcm⟩, hs.2.le⟩
  rw [hvol, rhoMeasure, withDensity_apply _ measurableSet_Iic,
    ← ofReal_integral_eq_lintegral_ofReal hi.integrableOn (ae_of_all _ hnn)]
  rfl

end Quantile

/-- A locally Hölder `L^∞` density is bounded everywhere. -/
lemma hilbertHyp_exists_bound {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ρ x ≤ B := by
  obtain ⟨M, hM⟩ := hρ.ae_le
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  by_contra h
  push Not at h
  have hopen : IsOpen {y | max M 0 < ρ y} := isOpen_lt continuous_const hρ.continuous
  have hpos := hopen.measure_pos volume ⟨x, h⟩
  have h0 : volume {y | max M 0 < ρ y} = 0 := by
    refine measure_mono_null (fun y hy => ?_) (ae_iff.1 hM)
    have hy' : max M 0 < ρ y := hy
    show ¬ ρ y ≤ M
    exact not_le.2 ((le_max_left _ _).trans_lt hy')
  rw [h0] at hpos
  exact lt_irrefl _ hpos

/-! ## 2. The truncated kernel -/

/-- `k_ε(a) = 1_{|a| > ε} / a`. -/
def kt (ε a : ℝ) : ℝ := if ε < |a| then a⁻¹ else 0

lemma kt_neg (ε a : ℝ) : kt ε (-a) = -kt ε a := by
  unfold kt; rw [abs_neg]; split_ifs <;> simp [inv_neg]

lemma measurable_kt (ε : ℝ) : Measurable (kt ε) :=
  Measurable.ite (measurableSet_lt measurable_const continuous_abs.measurable) measurable_inv
    measurable_const

lemma abs_kt_le {ε : ℝ} (hε : 0 < ε) (a : ℝ) : |kt ε a| ≤ 1 / ε := by
  unfold kt
  split_ifs with h
  · rw [abs_inv, one_div]; exact inv_anti₀ hε h.le
  · simp only [abs_zero]; positivity

/-- `H_ε ρ(x) = ∫_0^m k_ε(x − q(t)) dt`. -/
lemma hilbertTrunc_qtl {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) (hm : 0 < ∫ y, ρ y) (ε x : ℝ) :
    hilbertTrunc ρ ε x = ∫ t in Ioo 0 (∫ y, ρ y), kt ε (x - qtl ρ t) := by
  obtain ⟨B, -, hB⟩ := hilbertHyp_exists_bound hρ
  have hq := aemeasurable_qtl hρ.nonneg hρ.integrable hB
  have hk : Measurable fun y => kt ε (x - y) := (measurable_kt ε).comp (measurable_const.sub measurable_id)
  rw [← integral_map hq (f := fun y => kt ε (x - y)) (by
      rw [map_qtl hρ.nonneg hρ.integrable hB hm]; exact hk.aestronglyMeasurable),
    map_qtl hρ.nonneg hρ.integrable hB hm, integral_rhoMeasure hρ, hilbertTrunc,
    ← integral_indicator (measurableSet_lt measurable_const (by fun_prop))]
  congr 1
  funext y
  simp only [indicator, kt, Set.mem_ofPred_eq]
  split_ifs <;> simp [div_eq_mul_inv]

/-! ## 3. Symmetrization and the region estimate -/

lemma scalar_le {ε a b : ℝ} (hε : 0 < ε) (hab : 0 ≤ a * b) :
    (a - b) * (kt ε a - kt ε b) ≤
      (if |a| ≤ ε then 1 else 0) + (if |b| ≤ ε then 1 else 0) := by
  unfold kt
  by_cases ha : ε < |a| <;> by_cases hb : ε < |b|
  · have ha0 : a ≠ 0 := by intro h; rw [h, abs_zero] at ha; linarith
    have hb0 : b ≠ 0 := by intro h; rw [h, abs_zero] at hb; linarith
    have hpos : 0 < a * b := lt_of_le_of_ne hab (mul_ne_zero ha0 hb0).symm
    simp only [ha, hb, ↓reduceIte, not_le.2 ha, not_le.2 hb, add_zero]
    have e : (a - b) * (a⁻¹ - b⁻¹) = -((a - b) ^ 2 / (a * b)) := by field_simp; ring
    rw [e, neg_nonpos]; positivity
  · have ha0 : a ≠ 0 := by intro h; rw [h, abs_zero] at ha; linarith
    simp only [ha, hb, ↓reduceIte, not_le.2 ha, not_lt.1 hb, sub_zero, zero_add]
    have e : (a - b) * a⁻¹ = 1 - a * b / a ^ 2 := by field_simp
    rw [e]; have : 0 ≤ a * b / a ^ 2 := by positivity
    linarith
  · have hb0 : b ≠ 0 := by intro h; rw [h, abs_zero] at hb; linarith
    simp only [ha, hb, ↓reduceIte, not_lt.1 ha, not_le.2 hb, zero_sub, add_zero]
    have e : (a - b) * -b⁻¹ = 1 - a * b / b ^ 2 := by field_simp; ring
    rw [e]; have : 0 ≤ a * b / b ^ 2 := by positivity
    linarith
  · simp only [ha, hb, ↓reduceIte, not_lt.1 ha, not_lt.1 hb, sub_zero, mul_zero]
    norm_num

/-- The strip `|s − t| ≤ δ` in `(0,m)²` has measure at most `2δm`. -/
lemma strip_le {m δ : ℝ} (hm : 0 ≤ m) (hδ : 0 ≤ δ) :
    ((volume.restrict (Ioo 0 m)).prod (volume.restrict (Ioo 0 m))).real
      {p : ℝ × ℝ | |p.1 - p.2| ≤ δ} ≤ 2 * δ * m := by
  set μ0 := volume.restrict (Ioo (0 : ℝ) m)
  have hS : MeasurableSet {p : ℝ × ℝ | |p.1 - p.2| ≤ δ} :=
    measurableSet_le (by fun_prop) measurable_const
  have h1 : (μ0.prod μ0) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ} ≤
      ENNReal.ofReal (2 * δ) * ENNReal.ofReal m := by
    rw [Measure.prod_apply hS]
    calc ∫⁻ s, μ0 (Prod.mk s ⁻¹' {p : ℝ × ℝ | |p.1 - p.2| ≤ δ}) ∂μ0
        ≤ ∫⁻ _s, ENNReal.ofReal (2 * δ) ∂μ0 := by
          refine lintegral_mono fun s => ?_
          calc μ0 (Prod.mk s ⁻¹' {p : ℝ × ℝ | |p.1 - p.2| ≤ δ})
              ≤ volume (Prod.mk s ⁻¹' {p : ℝ × ℝ | |p.1 - p.2| ≤ δ}) :=
                Measure.restrict_le_self _
            _ ≤ volume (Icc (s - δ) (s + δ)) := measure_mono fun t ht => by
                simp only [mem_preimage, Set.mem_ofPred_eq] at ht
                rw [abs_le] at ht
                exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
            _ = ENNReal.ofReal (2 * δ) := by rw [Real.volume_Icc]; ring_nf
      _ = ENNReal.ofReal (2 * δ) * ENNReal.ofReal m := by
          rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
            Real.volume_Ioo, sub_zero]
  rw [measureReal_def]
  calc ((μ0.prod μ0) _).toReal ≤ (ENNReal.ofReal (2 * δ) * ENNReal.ofReal m).toReal :=
        ENNReal.toReal_mono (by finiteness) h1
    _ = 2 * δ * m := by
        rw [← ENNReal.ofReal_mul (by positivity), ENNReal.toReal_ofReal (by positivity)]

/-- **Symmetrization and the region estimate**: `L_ε ≤ m(B + B̃)ε` for two monotone functions on
`(0,m)` with the separation property. -/
theorem trunc_pairing_le {m : ℝ} (hm : 0 < m) {q q' : ℝ → ℝ}
    (hq : AEMeasurable q (volume.restrict (Ioo 0 m)))
    (hq' : AEMeasurable q' (volume.restrict (Ioo 0 m)))
    (hmo : MonotoneOn q (Ioo 0 m)) (hmo' : MonotoneOn q' (Ioo 0 m))
    {B B' : ℝ} (hB : 0 ≤ B) (hB' : 0 ≤ B')
    (hsep : ∀ s ∈ Ioo 0 m, ∀ t ∈ Ioo 0 m, |s - t| ≤ B * |q s - q t|)
    (hsep' : ∀ s ∈ Ioo 0 m, ∀ t ∈ Ioo 0 m, |s - t| ≤ B' * |q' s - q' t|)
    (hd : Integrable (fun s => q s - q' s) (volume.restrict (Ioo 0 m))) {ε : ℝ} (hε : 0 < ε) :
    ∫ s in Ioo 0 m, (q s - q' s) *
        ((∫ t in Ioo 0 m, kt ε (q s - q t)) - ∫ t in Ioo 0 m, kt ε (q' s - q' t))
      ≤ m * (B + B') * ε := by
  set μ0 := volume.restrict (Ioo (0 : ℝ) m) with hμ0
  have : IsFiniteMeasure μ0 := isFiniteMeasure_restrict.2 (by simp)
  set P := μ0.prod μ0 with hP
  set d : ℝ → ℝ := fun s => q s - q' s with hddef
  set K : ℝ × ℝ → ℝ := fun p => kt ε (q p.1 - q p.2) - kt ε (q' p.1 - q' p.2) with hKdef
  have hKm : AEStronglyMeasurable K P := by
    have h1 := (measurable_kt ε).comp_aemeasurable
      ((AEMeasurable.comp_fst hq).sub (AEMeasurable.comp_snd hq))
    have h2 := (measurable_kt ε).comp_aemeasurable
      ((AEMeasurable.comp_fst hq').sub (AEMeasurable.comp_snd hq'))
    exact (h1.sub h2).aestronglyMeasurable
  have hKb : ∀ p, |K p| ≤ 2 / ε := fun p => (abs_sub _ _).trans (by
    have h1 := abs_kt_le hε (q p.1 - q p.2)
    have h2 := abs_kt_le hε (q' p.1 - q' p.2)
    have e : (2 : ℝ) / ε = 1 / ε + 1 / ε := by ring
    rw [e]; linarith)
  have hdm1 : AEStronglyMeasurable (fun p : ℝ × ℝ => d p.1) P :=
    (AEMeasurable.comp_fst hd.aemeasurable).aestronglyMeasurable
  have hdm2 : AEStronglyMeasurable (fun p : ℝ × ℝ => d p.2) P :=
    (AEMeasurable.comp_snd hd.aemeasurable).aestronglyMeasurable
  have hF : Integrable (fun p => d p.1 * K p) P :=
    Integrable.mono' ((hd.norm.comp_fst μ0).mul_const (2 / ε)) (hdm1.mul hKm)
      (ae_of_all _ fun p => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (by rw [Real.norm_eq_abs]; exact hKb p) (norm_nonneg _))
  have hF' : Integrable (fun p => d p.2 * K p) P :=
    Integrable.mono' ((hd.norm.comp_snd μ0).mul_const (2 / ε)) (hdm2.mul hKm)
      (ae_of_all _ fun p => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (by rw [Real.norm_eq_abs]; exact hKb p) (norm_nonneg _))
  -- `L_ε` as a double integral
  have h1 : ∫ s, (q s - q' s) *
        ((∫ t, kt ε (q s - q t) ∂μ0) - ∫ t, kt ε (q' s - q' t) ∂μ0) ∂μ0 =
      ∫ p, d p.1 * K p ∂P := by
    rw [hP, integral_prod _ hF]
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    have i1 : Integrable (fun t => kt ε (q s - q t)) μ0 := Integrable.of_bound
      (((measurable_kt ε).comp_aemeasurable (aemeasurable_const.sub hq)).aestronglyMeasurable)
      (1 / ε) (ae_of_all _ fun t => by rw [Real.norm_eq_abs]; exact abs_kt_le hε _)
    have i2 : Integrable (fun t => kt ε (q' s - q' t)) μ0 := Integrable.of_bound
      (((measurable_kt ε).comp_aemeasurable (aemeasurable_const.sub hq')).aestronglyMeasurable)
      (1 / ε) (ae_of_all _ fun t => by rw [Real.norm_eq_abs]; exact abs_kt_le hε _)
    show (q s - q' s) * ((∫ t, kt ε (q s - q t) ∂μ0) - ∫ t, kt ε (q' s - q' t) ∂μ0) =
      ∫ t, d s * K (s, t) ∂μ0
    rw [← integral_sub i1 i2, ← integral_const_mul]
  -- oddness under the swap
  have h2 : ∫ p, d p.1 * K p ∂P = -∫ p, d p.2 * K p ∂P := by
    rw [← integral_prod_swap (fun p => d p.1 * K p), ← integral_neg]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [hKdef, Prod.fst_swap, Prod.snd_swap]
    rw [show q p.2 - q p.1 = -(q p.1 - q p.2) by ring,
      show q' p.2 - q' p.1 = -(q' p.1 - q' p.2) by ring, kt_neg, kt_neg]
    ring
  -- the region estimate
  set S1 := {p : ℝ × ℝ | |p.1 - p.2| ≤ B * ε}
  set S2 := {p : ℝ × ℝ | |p.1 - p.2| ≤ B' * ε}
  have hS1 : MeasurableSet S1 := measurableSet_le (by fun_prop) measurable_const
  have hS2 : MeasurableSet S2 := measurableSet_le (by fun_prop) measurable_const
  have hI1 : Integrable (fun p => S1.indicator (1 : ℝ × ℝ → ℝ) p) P :=
    (integrable_const (1 : ℝ)).indicator hS1
  have hI2 : Integrable (fun p => S2.indicator (1 : ℝ × ℝ → ℝ) p) P :=
    (integrable_const (1 : ℝ)).indicator hS2
  have hae : ∀ᵐ p ∂P, p ∈ Ioo 0 m ×ˢ Ioo 0 m := by
    rw [hP, hμ0, Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)
  have hG : ∫ p, (d p.1 - d p.2) * K p ∂P ≤
      ∫ p, (S1.indicator 1 p + S2.indicator 1 p) ∂P := by
    refine integral_mono_ae (by
      refine (hF.sub hF').congr (ae_of_all _ fun p => ?_)
      simp only [Pi.sub_apply]; ring) (hI1.add hI2) (hae.mono fun p hp => ?_)
    obtain ⟨hs, ht⟩ := hp
    set a := q p.1 - q p.2
    set b := q' p.1 - q' p.2
    have hab : 0 ≤ a * b := by
      rcases le_total p.1 p.2 with h | h
      · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (hmo hs ht h))
          (sub_nonpos.2 (hmo' hs ht h))
      · exact mul_nonneg (sub_nonneg.2 (hmo ht hs h)) (sub_nonneg.2 (hmo' ht hs h))
    have e : (d p.1 - d p.2) * K p = (a - b) * (kt ε a - kt ε b) := by
      simp only [hddef, hKdef, a, b]; ring
    show (d p.1 - d p.2) * K p ≤ S1.indicator 1 p + S2.indicator 1 p
    rw [e]
    refine (scalar_le hε hab).trans (add_le_add ?_ ?_)
    · split_ifs with h
      · have : p ∈ S1 := by
          show |p.1 - p.2| ≤ B * ε
          exact (hsep _ hs _ ht).trans (mul_le_mul_of_nonneg_left h hB)
        rw [indicator_of_mem this]; rfl
      · exact indicator_nonneg (fun _ _ => zero_le_one) _
    · split_ifs with h
      · have : p ∈ S2 := by
          show |p.1 - p.2| ≤ B' * ε
          exact (hsep' _ hs _ ht).trans (mul_le_mul_of_nonneg_left h hB')
        rw [indicator_of_mem this]; rfl
      · exact indicator_nonneg (fun _ _ => zero_le_one) _
  have hH : ∫ p, (S1.indicator 1 p + S2.indicator 1 p) ∂P = P.real S1 + P.real S2 := by
    rw [integral_add hI1 hI2, integral_indicator_one hS1, integral_indicator_one hS2]
  have hG2 : ∫ p, (d p.1 - d p.2) * K p ∂P = ∫ p, d p.1 * K p ∂P - ∫ p, d p.2 * K p ∂P := by
    rw [← integral_sub hF hF']
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only; ring
  have hs1 := strip_le hm.le (mul_nonneg hB hε.le)
  have hs2 := strip_le hm.le (mul_nonneg hB' hε.le)
  rw [h1]
  have e2 : ∫ p, d p.1 * K p ∂P = (1 / 2) * ∫ p, (d p.1 - d p.2) * K p ∂P := by
    rw [hG2, h2]; ring
  rw [e2]
  have := hG.trans_eq hH
  nlinarith

/-! ## 4. Cauchy–Schwarz and the limit -/

lemma abs_integral_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ a, f a * g a ∂μ| ≤ Real.sqrt (∫ a, f a ^ 2 ∂μ) * Real.sqrt (∫ a, g a ^ 2 ∂μ) := by
  have h2 : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have hf' : MemLp (fun a => |f a|) (ENNReal.ofReal 2) μ := by
    rw [ENNReal.ofReal_ofNat]; exact hf.abs
  have hg' : MemLp (fun a => |g a|) (ENNReal.ofReal 2) μ := by
    rw [ENNReal.ofReal_ofNat]; exact hg.abs
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg h2 (ae_of_all _ fun a => abs_nonneg (f a))
    (ae_of_all _ fun a => abs_nonneg (g a)) hf' hg'
  have e : ∀ h : α → ℝ, (∫ a, |h a| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) =
      Real.sqrt (∫ a, h a ^ 2 ∂μ) := by
    intro h
    rw [Real.sqrt_eq_rpow]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun a => ?_)
    simp only
    rw [Real.rpow_two, sq_abs]
  rw [e f, e g] at hH
  calc |∫ a, f a * g a ∂μ| ≤ ∫ a, |f a * g a| ∂μ := by
        rw [← Real.norm_eq_abs]; exact (norm_integral_le_integral_norm _).trans (le_of_eq rfl)
    _ = ∫ a, |f a| * |g a| ∂μ := by simp_rw [abs_mul]
    _ ≤ _ := hH

/-- Pulled-back `L²` facts for one density. -/
lemma pullback_facts {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) (hm : 0 < ∫ y, ρ y) :
    (∀ ε : ℝ, 0 < ε →
      MemLp (fun s => hilbertTrunc ρ ε (qtl ρ s)) 2 (volume.restrict (Ioo 0 (∫ y, ρ y)))) ∧
    MemLp (fun s => hilbertPV ρ (qtl ρ s)) 2 (volume.restrict (Ioo 0 (∫ y, ρ y))) ∧
    Tendsto (fun ε => ∫ s in Ioo 0 (∫ y, ρ y),
        (hilbertTrunc ρ ε (qtl ρ s) - hilbertPV ρ (qtl ρ s)) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨B, -, hB⟩ := hilbertHyp_exists_bound hρ
  have hq := aemeasurable_qtl hρ.nonneg hρ.integrable hB
  have hmap := map_qtl hρ.nonneg hρ.integrable hB hm
  obtain ⟨-, -, ⟨hT, hPV, hlim⟩⟩ := root_Hilbert_truncations hρ
  have pull : ∀ F : ℝ → ℝ, MemLp F 2 (rhoMeasure ρ) →
      MemLp (fun s => F (qtl ρ s)) 2 (volume.restrict (Ioo 0 (∫ y, ρ y))) := by
    intro F hF
    rw [← hmap] at hF
    exact (memLp_map_measure_iff hF.aestronglyMeasurable hq).1 hF
  refine ⟨fun ε hε => pull _ (hT ε hε), pull _ hPV, ?_⟩
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hG : AEStronglyMeasurable (fun x => ‖hilbertTrunc ρ ε x - hilbertPV ρ x‖ ^ 2)
      ((volume.restrict (Ioo 0 (∫ y, ρ y))).map (qtl ρ)) := by
    rw [hmap]; exact ((hT ε hε).aestronglyMeasurable.sub hPV.aestronglyMeasurable).norm.pow 2
  rw [← hmap, integral_map hq hG]
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  simp only [Real.norm_eq_abs, sq_abs]

/-- **R-409128A9 `lem:root-Hilbert-quantiles`.** For densities `ρ, σ` satisfying the hypotheses of
R-064239ED with the same mass `m > 0`, and quantiles with `q − q̃ ∈ L²(0,m)`: both terms are
integrable and `∫_0^m (q − q̃)(s) [Hρ(q(s)) − Hσ(q̃(s))] ds ≤ 0`. -/
theorem root_Hilbert_quantiles {ρ σ : ℝ → ℝ} (hρ : HilbertHyp ρ) (hσ : HilbertHyp σ) {m : ℝ}
    (hm : 0 < m) (hρm : ∫ x, ρ x = m) (hσm : ∫ x, σ x = m)
    (hd : MemLp (fun s => qtl ρ s - qtl σ s) 2 (volume.restrict (Ioo 0 m))) :
    Integrable (fun s => (qtl ρ s - qtl σ s) * hilbertPV ρ (qtl ρ s))
        (volume.restrict (Ioo 0 m)) ∧
      Integrable (fun s => (qtl ρ s - qtl σ s) * hilbertPV σ (qtl σ s))
        (volume.restrict (Ioo 0 m)) ∧
      ∫ s in Ioo 0 m, (qtl ρ s - qtl σ s) * (hilbertPV ρ (qtl ρ s) - hilbertPV σ (qtl σ s))
        ≤ 0 := by
  set μ0 := volume.restrict (Ioo (0 : ℝ) m) with hμ0
  have : IsFiniteMeasure μ0 := isFiniteMeasure_restrict.2 (by simp)
  obtain ⟨B, hB0, hB⟩ := hilbertHyp_exists_bound hρ
  obtain ⟨B', hB'0, hB'⟩ := hilbertHyp_exists_bound hσ
  have hmρ : 0 < ∫ y, ρ y := hρm ▸ hm
  have hmσ : 0 < ∫ y, σ y := hσm ▸ hm
  obtain ⟨hTρ, hPρ, hLρ⟩ := pullback_facts hρ hmρ
  obtain ⟨hTσ, hPσ, hLσ⟩ := pullback_facts hσ hmσ
  rw [hρm] at hTρ hPρ hLρ
  rw [hσm] at hTσ hPσ hLσ
  have hqρ := aemeasurable_qtl hρ.nonneg hρ.integrable hB
  have hqσ := aemeasurable_qtl hσ.nonneg hσ.integrable hB'
  rw [hρm] at hqρ
  rw [hσm] at hqσ
  have hmoρ : MonotoneOn (qtl ρ) (Ioo 0 m) := by
    have := (qtl_strictMonoOn hρ.nonneg hρ.integrable hB).monotoneOn; rwa [hρm] at this
  have hmoσ : MonotoneOn (qtl σ) (Ioo 0 m) := by
    have := (qtl_strictMonoOn hσ.nonneg hσ.integrable hB').monotoneOn; rwa [hσm] at this
  have hsepρ : ∀ s ∈ Ioo 0 m, ∀ t ∈ Ioo 0 m, |s - t| ≤ B * |qtl ρ s - qtl ρ t| :=
    fun s hs t ht => qtl_separation hρ.nonneg hρ.integrable hB (hρm ▸ hs) (hρm ▸ ht)
  have hsepσ : ∀ s ∈ Ioo 0 m, ∀ t ∈ Ioo 0 m, |s - t| ≤ B' * |qtl σ s - qtl σ t| :=
    fun s hs t ht => qtl_separation hσ.nonneg hσ.integrable hB' (hσm ▸ hs) (hσm ▸ ht)
  set d := fun s => qtl ρ s - qtl σ s with hddef
  have hd1 : Integrable d μ0 := hd.integrable one_le_two
  -- integrability
  have iP1 : Integrable (fun s => d s * hilbertPV ρ (qtl ρ s)) μ0 := hd.integrable_mul hPρ
  have iP2 : Integrable (fun s => d s * hilbertPV σ (qtl σ s)) μ0 := hd.integrable_mul hPσ
  refine ⟨iP1, iP2, ?_⟩
  -- the truncated pairing
  set Lε : ℝ → ℝ := fun ε => ∫ s, d s *
      (hilbertTrunc ρ ε (qtl ρ s) - hilbertTrunc σ ε (qtl σ s)) ∂μ0 with hLεdef
  set L := ∫ s, d s * (hilbertPV ρ (qtl ρ s) - hilbertPV σ (qtl σ s)) ∂μ0 with hLdef
  have hbound : ∀ ε, 0 < ε → Lε ε ≤ m * (B + B') * ε := by
    intro ε hε
    have := trunc_pairing_le hm hqρ hqσ hmoρ hmoσ hB0 hB'0 hsepρ hsepσ hd1 hε
    refine le_of_eq_of_le ?_ this
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    show d s * (hilbertTrunc ρ ε (qtl ρ s) - hilbertTrunc σ ε (qtl σ s)) = _
    rw [hilbertTrunc_qtl hρ hmρ, hilbertTrunc_qtl hσ hmσ, hρm, hσm]
  -- convergence `L_ε → L`
  have hdiff : ∀ ε, 0 < ε → |Lε ε - L| ≤
      Real.sqrt (∫ s, d s ^ 2 ∂μ0) *
        (Real.sqrt (∫ s, (hilbertTrunc ρ ε (qtl ρ s) - hilbertPV ρ (qtl ρ s)) ^ 2 ∂μ0) +
          Real.sqrt (∫ s, (hilbertTrunc σ ε (qtl σ s) - hilbertPV σ (qtl σ s)) ^ 2 ∂μ0)) := by
    intro ε hε
    have hA := (hTρ ε hε).sub hPρ
    have hB2 := (hTσ ε hε).sub hPσ
    have iT1 : Integrable (fun s => d s * hilbertTrunc ρ ε (qtl ρ s)) μ0 :=
      hd.integrable_mul (hTρ ε hε)
    have iT2 : Integrable (fun s => d s * hilbertTrunc σ ε (qtl σ s)) μ0 :=
      hd.integrable_mul (hTσ ε hε)
    have e : Lε ε - L =
        ∫ s, d s * (hilbertTrunc ρ ε (qtl ρ s) - hilbertPV ρ (qtl ρ s)) ∂μ0 -
          ∫ s, d s * (hilbertTrunc σ ε (qtl σ s) - hilbertPV σ (qtl σ s)) ∂μ0 := by
      have e1 : ∫ s, d s * (hilbertTrunc ρ ε (qtl ρ s) - hilbertTrunc σ ε (qtl σ s)) ∂μ0 =
          ∫ s, d s * hilbertTrunc ρ ε (qtl ρ s) ∂μ0 - ∫ s, d s * hilbertTrunc σ ε (qtl σ s) ∂μ0 := by
        rw [← integral_sub iT1 iT2]
        exact integral_congr_ae (ae_of_all _ fun s => by beta_reduce; ring)
      have e2 : ∫ s, d s * (hilbertPV ρ (qtl ρ s) - hilbertPV σ (qtl σ s)) ∂μ0 =
          ∫ s, d s * hilbertPV ρ (qtl ρ s) ∂μ0 - ∫ s, d s * hilbertPV σ (qtl σ s) ∂μ0 := by
        rw [← integral_sub iP1 iP2]
        exact integral_congr_ae (ae_of_all _ fun s => by beta_reduce; ring)
      have e3 : ∫ s, d s * (hilbertTrunc ρ ε (qtl ρ s) - hilbertPV ρ (qtl ρ s)) ∂μ0 =
          ∫ s, d s * hilbertTrunc ρ ε (qtl ρ s) ∂μ0 - ∫ s, d s * hilbertPV ρ (qtl ρ s) ∂μ0 := by
        rw [← integral_sub iT1 iP1]
        exact integral_congr_ae (ae_of_all _ fun s => by beta_reduce; ring)
      have e4 : ∫ s, d s * (hilbertTrunc σ ε (qtl σ s) - hilbertPV σ (qtl σ s)) ∂μ0 =
          ∫ s, d s * hilbertTrunc σ ε (qtl σ s) ∂μ0 - ∫ s, d s * hilbertPV σ (qtl σ s) ∂μ0 := by
        rw [← integral_sub iT2 iP2]
        exact integral_congr_ae (ae_of_all _ fun s => by beta_reduce; ring)
      show (∫ s, d s * (hilbertTrunc ρ ε (qtl ρ s) - hilbertTrunc σ ε (qtl σ s)) ∂μ0) -
        (∫ s, d s * (hilbertPV ρ (qtl ρ s) - hilbertPV σ (qtl σ s)) ∂μ0) = _
      rw [e1, e2, e3, e4]; ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    rw [mul_add]
    exact add_le_add (abs_integral_mul_le hd hA) (abs_integral_mul_le hd hB2)
  have hsq : ∀ {f : ℝ → ℝ}, Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 0) →
      Tendsto (fun ε => Real.sqrt (f ε)) (𝓝[>] (0 : ℝ)) (𝓝 0) := fun h => by
    have := (Real.continuous_sqrt.tendsto 0).comp h
    rw [Real.sqrt_zero] at this
    exact this
  have hR : Tendsto (fun ε => Real.sqrt (∫ s, d s ^ 2 ∂μ0) *
      (Real.sqrt (∫ s, (hilbertTrunc ρ ε (qtl ρ s) - hilbertPV ρ (qtl ρ s)) ^ 2 ∂μ0) +
        Real.sqrt (∫ s, (hilbertTrunc σ ε (qtl σ s) - hilbertPV σ (qtl σ s)) ^ 2 ∂μ0)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using ((hsq hLρ).add (hsq hLσ)).const_mul (Real.sqrt (∫ s, d s ^ 2 ∂μ0))
  have hconv : Tendsto Lε (𝓝[>] (0 : ℝ)) (𝓝 L) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun ε => norm_nonneg _) ?_ hR
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [Real.norm_eq_abs]
    exact hdiff ε hε
  have hC : Tendsto (fun ε : ℝ => m * (B + B') * ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using h.const_mul (m * (B + B'))
  have hle : L ≤ 0 := le_of_tendsto_of_tendsto hconv hC
    (by filter_upwards [self_mem_nhdsWithin] with ε hε; exact hbound ε hε)
  exact hle

end QuantumNLS.RootHilbertQuantiles

#print axioms QuantumNLS.RootHilbertQuantiles.cdf_qtl
#print axioms QuantumNLS.RootHilbertQuantiles.map_qtl
#print axioms QuantumNLS.RootHilbertQuantiles.qtl_separation
#print axioms QuantumNLS.RootHilbertQuantiles.hilbertTrunc_qtl
#print axioms QuantumNLS.RootHilbertQuantiles.trunc_pairing_le
#print axioms QuantumNLS.RootHilbertQuantiles.root_Hilbert_quantiles
