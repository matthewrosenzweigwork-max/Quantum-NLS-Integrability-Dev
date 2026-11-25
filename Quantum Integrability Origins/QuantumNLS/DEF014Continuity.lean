import QuantumNLS.DEF014Phase
import QuantumNLS.D05TotalVariation

/-! Continuity of the actual indexed mass map in the norm topology of ell1.
No continuity, moving-boundary, or mass correspondence hypothesis is supplied. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Set Filter Topology MeasureTheory
open scoped ENNReal
namespace QuantumNLS.DEF014Continuity
open DEF014Phase
variable {L : ℝ} [Fact (0 < L)]

def masses (p : Param L) : ActionTorus.PosL1 := (facts p).masses

theorem masses_apply (p : Param L) (n : ℤ) :
    (masses p).1 n = (DEF014Phase.measure p (Ioo (separator p (n-1)) (separator p n))).toReal := rfl

theorem sum_masses (p : Param L) : ∑' n, (masses p).1 n = ‖p.2‖ ^ 2 :=
  (facts p).sum_masses

/-- Total variation controls every measurable interval, including a moving one. -/
theorem abs_measureReal_sub_le_tv (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {S : Set ℝ} (hS : MeasurableSet S) :
    |(μ S).toReal - (ν S).toReal| ≤ (TotalVariation.tvNorm μ ν).toReal := by
  have h := (μ.toSignedMeasure - ν.toSignedMeasure).norm_le_totalVariation S
  rw [Measure.toSignedMeasure_sub_apply hS, Real.norm_eq_abs] at h
  exact h.trans (ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono (subset_univ S)))

/-- For an atomless finite measure, interval masses depend continuously on both endpoints. -/
theorem continuous_interval_mass (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {a b : X → ℝ} (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun x => (μ (Ioo (a x) (b x))).toReal) := by
  rw [continuous_iff_continuousAt]
  intro x
  have ht : Tendsto (fun y => μ (Ioo (a y) (b y))) (𝓝 x)
      (𝓝 (μ (Ioo (a x) (b x)))) := by
    apply tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
      (𝓝 x) measurableSet_Ioo (fun _ => measurableSet_Ioo)
    have ha0 : ∀ᵐ t ∂μ, t ≠ a x := by
      simpa using (measure_eq_zero_iff_ae_notMem.mp (measure_singleton (a x) : μ {a x} = 0))
    have hb0 : ∀ᵐ t ∂μ, t ≠ b x := by
      simpa using (measure_eq_zero_iff_ae_notMem.mp (measure_singleton (b x) : μ {b x} = 0))
    filter_upwards [ha0, hb0] with t hat hbt
    have hl : ∀ᶠ y in 𝓝 x, a y < t ↔ a x < t := by
      rcases lt_or_gt_of_ne hat with ht | ht
      · exact ((ha.tendsto x).eventually (lt_mem_nhds ht)).mono (fun y hy => by simp [not_lt.mpr hy.le, not_lt.mpr ht.le])
      · exact ((ha.tendsto x).eventually (gt_mem_nhds ht)).mono (fun y hy => by simp [hy, ht])
    have hu : ∀ᶠ y in 𝓝 x, t < b y ↔ t < b x := by
      rcases lt_or_gt_of_ne hbt with ht | ht
      · exact ((hb.tendsto x).eventually (lt_mem_nhds ht)).mono (fun y hy => by simp [hy, ht])
      · exact ((hb.tendsto x).eventually (gt_mem_nhds ht)).mono (fun y hy => by simp [not_lt.mpr hy.le, not_lt.mpr ht.le])
    filter_upwards [hl, hu] with y hyl hyu
    simp only [mem_Ioo, hyl, hyu]
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht

/-- Each coordinate is jointly continuous at arbitrary physical inputs. -/
theorem continuous_coordinate (n : ℤ) : Continuous (fun p : Param L => (masses p).1 n) := by
  rw [continuous_iff_continuousAt]
  intro p
  let _ : NullSingletonClass (DEF014Phase.measure p) := PhysicalUnconditionalTrace.atomless p.1.2 p.2
  let S : Param L → Set ℝ := fun q => Ioo (separator q (n-1)) (separator q n)
  have hc : Continuous (fun q => (DEF014Phase.measure p (S q)).toReal) :=
    continuous_interval_mass (DEF014Phase.measure p) (continuous_separator (n-1)) (continuous_separator n)
  have htv : Tendsto (fun q : Param L =>
      TotalVariation.tvNorm (DEF014Phase.measure q) (DEF014Phase.measure p)) (𝓝 p) (𝓝 0) := by
    have h := (D05TotalVariation.tv_continuousAt p.1.2 p.2).comp
      (((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).tendsto p)
    simpa only [Function.comp_def, DEF014Phase.measure, PhysicalL2Normalization.measure_eq_Mmeas] using h
  have htvR : Tendsto (fun q : Param L =>
      (TotalVariation.tvNorm (DEF014Phase.measure q) (DEF014Phase.measure p)).toReal) (𝓝 p) (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp htv
  have hd : Tendsto (fun q : Param L =>
      (DEF014Phase.measure q (S q)).toReal - (DEF014Phase.measure p (S q)).toReal) (𝓝 p) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun _ => norm_nonneg _) (fun q => ?_) htvR
    simpa only [Real.norm_eq_abs] using
      abs_measureReal_sub_le_tv (DEF014Phase.measure q) (DEF014Phase.measure p) measurableSet_Ioo
  have h := hd.add hc.continuousAt.tendsto
  simpa only [ContinuousAt, zero_add, sub_add_cancel, masses_apply, S] using h

/-- Nonnegative ell1 vectors converge in norm when their coordinates and total masses converge. -/
theorem tendsto_posL1 {X : Type*} {F : Filter X}
    {a : X → ActionTorus.PosL1} {b : ActionTorus.PosL1}
    (hcoord : ∀ n, Tendsto (fun x => (a x).1 n) F (𝓝 (b.1 n)))
    (hmass : Tendsto (fun x => ∑' n, (a x).1 n) F (𝓝 (∑' n, b.1 n))) :
    Tendsto a F (𝓝 b) := by
  have hmin : Tendsto (fun x => ∑' n, min ((a x).1 n) (b.1 n)) F (𝓝 (∑' n, b.1 n)) := by
    apply tendsto_tsum_of_dominated_convergence (ActionTorus.summable_posL1 b)
    · intro n
      simpa using (hcoord n).min (tendsto_const_nhds (x := b.1 n))
    · exact Eventually.of_forall fun x n => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min ((a x).2 n) (b.2 n))]
        exact min_le_right _ _
  have hid (x : X) : ‖(a x).1 - b.1‖ =
      (∑' n, (a x).1 n) + (∑' n, b.1 n) - 2 * ∑' n, min ((a x).1 n) (b.1 n) := by
    have hmini : Summable (fun n => min ((a x).1 n) (b.1 n)) :=
      (ActionTorus.summable_posL1 b).of_nonneg_of_le
        (fun n => le_min ((a x).2 n) (b.2 n)) (fun _ => min_le_right _ _)
    have he (n : ℤ) : ‖(a x).1 n - b.1 n‖ =
        ((a x).1 n + b.1 n) - 2 * min ((a x).1 n) (b.1 n) := by
      rw [Real.norm_eq_abs]
      rcases le_total ((a x).1 n) (b.1 n) with h | h
      · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
      · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
    have hn := lp.norm_rpow_eq_tsum (p := (1 : ℝ≥0∞)) (by norm_num) ((a x).1 - b.1)
    simpa only [ENNReal.toReal_one, Real.rpow_one, lp.coeFn_sub, Pi.sub_apply, he,
      ((ActionTorus.summable_posL1 (a x)).add (ActionTorus.summable_posL1 b)).tsum_sub
        (hmini.mul_left 2),
      (ActionTorus.summable_posL1 (a x)).tsum_add (ActionTorus.summable_posL1 b),
      tsum_mul_left] using hn
  apply tendsto_subtype_rng.mpr
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [hid]
  have hz : (∑' n, b.1 n) + (∑' n, b.1 n) - 2 * (∑' n, b.1 n) = 0 := by ring
  simpa only [hz] using (hmass.add_const (∑' n, b.1 n)).sub (hmin.const_mul 2)

/-- DEF-014 continuity, jointly in positive coupling and arbitrary L2 input. -/
theorem continuous_masses : Continuous (masses (L := L)) := by
  rw [continuous_iff_continuousAt]
  intro p
  apply tendsto_posL1 (fun n => (continuous_coordinate n).tendsto p)
  simp_rw [sum_masses]
  exact ((continuous_norm.comp continuous_snd).pow 2).tendsto p



/-- Near a physical input, moving a separator within its common mass-free
band changes neither side of the cut, almost everywhere for the varying measure. -/
theorem eventually_separator_cut (p : Param L) (k : ℤ) :
    ∀ᶠ q : Param L in 𝓝 p, ∀ᵐ t ∂(DEF014Phase.measure q),
      (separator q k < t ↔ separator p k < t) ∧
      (t < separator q k ↔ t < separator p k) := by
  let b := separator p k
  obtain ⟨δ, hδ, hband⟩ := common_band p (x := b) ((facts p).separator_in_band k)
  have hs : ∀ᶠ q : Param L in 𝓝 p, |separator q k - b| < δ := by
    simpa [b, Real.dist_eq] using
      ((continuous_separator k).tendsto p).eventually (Metric.ball_mem_nhds _ hδ)
  filter_upwards [hband, hs] with q hq hsq
  have hz : DEF014Phase.measure q (Metric.ball b δ) = 0 :=
    measure_band_zero q Metric.isOpen_ball.measurableSet (fun t ht =>
      (hq t (by simpa [Metric.mem_ball, Real.dist_eq] using ht)).le)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with t ht
  have htδ : δ ≤ |t-b| := by
    simpa [Metric.mem_ball, Real.dist_eq, not_lt] using ht
  have hsq' := abs_lt.mp hsq
  by_cases htb : t ≤ b
  · rw [abs_of_nonpos (sub_nonpos.mpr htb)] at htδ
    constructor <;> constructor <;> intro h <;> dsimp [b] at * <;> linarith
  · have hbt : b ≤ t := (lt_of_not_ge htb).le
    rw [abs_of_nonneg (sub_nonneg.mpr hbt)] at htδ
    constructor <;> constructor <;> intro h <;> dsimp [b] at * <;> linarith

/-- A literal fixed-interval representation on a neighborhood of every
physical input, including collapsed masses. This is geometric support for
ROOT_mass_involution's fixed-contour argument, not an analyticity claim. -/
theorem eventually_mass_fixed_interval (p : Param L) (n : ℤ) :
    ∀ᶠ q : Param L in 𝓝 p, (masses q).1 n =
      (DEF014Phase.measure q (Ioo (separator p (n-1)) (separator p n))).toReal := by
  filter_upwards [eventually_separator_cut p (n-1), eventually_separator_cut p n]
    with q hlow hupp
  rw [masses_apply]
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [hlow, hupp] with t htlo hthi
  simp only [Set.mem_Ioo, htlo.1, hthi.2]

/-- Fixed-coupling version on the actual sourceFacts mass vector. -/
theorem continuous_physical_masses {κ : ℝ} (hκ : 0 < κ) :
    Continuous (fun u : PhysicalTensor.L2T L =>
      (PhysicalSourceFinal.sourceFacts hκ u).masses) := by
  have hc : Continuous (fun u : PhysicalTensor.L2T L =>
      masses ((⟨κ,hκ⟩ : {κ : ℝ // 0 < κ}),u)) :=
    continuous_masses.comp (continuous_const.prodMk continuous_id)
  simpa only [masses, facts] using hc

/-- Each actual physical interval mass is continuous on the full L2 carrier. -/
theorem continuous_physical_coordinate {κ : ℝ} (hκ : 0 < κ) (n : ℤ) :
    Continuous (fun u : PhysicalTensor.L2T L =>
      ((PhysicalSourceFinal.sourceFacts hκ u).masses).1 n) := by
  have hc : Continuous (fun u : PhysicalTensor.L2T L =>
      (masses ((⟨κ,hκ⟩ : {κ : ℝ // 0 < κ}),u)).1 n) :=
    (continuous_coordinate n).comp (continuous_const.prodMk continuous_id)
  simpa only [masses, facts] using hc

end QuantumNLS.DEF014Continuity

#print axioms QuantumNLS.DEF014Continuity.continuous_physical_masses
#print axioms QuantumNLS.DEF014Continuity.continuous_physical_coordinate
#print axioms QuantumNLS.DEF014Continuity.eventually_mass_fixed_interval
#print axioms QuantumNLS.DEF014Continuity.continuous_coordinate
#print axioms QuantumNLS.DEF014Continuity.continuous_masses
#print axioms QuantumNLS.DEF014Continuity.tendsto_posL1

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.DEF014Continuity." then
      pending := pending.push n
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"DEF014Continuity audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
