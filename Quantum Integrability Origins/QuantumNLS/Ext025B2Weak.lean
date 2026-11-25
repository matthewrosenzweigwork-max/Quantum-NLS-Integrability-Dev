import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Integral.Regular
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.UrysohnsLemma

/-! GP-10: explicit cutoff weak upgrade for finite Borel measures on the real
line. Each error is bounded by the missing cutoff mass, which tends to zero
using vague convergence and the separate mass convergence hypothesis. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped CompactlySupported
namespace QuantumNLS.Ext025B2Weak

lemma integral_one (μ : FiniteMeasure ℝ) : (∫ _ : ℝ, (1 : ℝ) ∂μ) = μ.mass := by
  simp [Measure.real, ← FiniteMeasure.ennreal_mass]

/-- Cutoffs with arbitrarily small missing mass, obtained from inner regularity. -/
theorem exists_cutoff (μ : FiniteMeasure ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ χ : C_c(ℝ, ℝ), (∀ x, χ x ∈ Icc 0 1) ∧
      (μ.mass : ℝ) - ∫ x, χ x ∂μ < ε := by
  obtain ⟨K, -, hK, hmass⟩ := MeasurableSet.univ.exists_isCompact_lt_add
    (μ := (μ : Measure ℝ)) (measure_ne_top _ _) (ε := ENNReal.ofReal ε) (ne_of_gt (ENNReal.ofReal_pos.mpr hε))
  obtain ⟨f, hfK, -, hfc, hfrange⟩ := exists_continuous_one_zero_of_isCompact
    hK isClosed_empty (disjoint_empty K)
  refine ⟨⟨f, hfc⟩, hfrange, ?_⟩
  have hlow : (μ : Measure ℝ).real K ≤ ∫ x, f x ∂μ := by
    have hi := f.continuous.integrable_of_hasCompactSupport hfc (μ := (μ : Measure ℝ))
    have hle := hi.measure_le_integral (Eventually.of_forall (fun x => (hfrange x).1))
      (fun x hx => by simpa using (hfK hx).ge)
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hle).trans_eq
      (ENNReal.toReal_ofReal (integral_nonneg (fun x => (hfrange x).1)))
  have hmass' := (ENNReal.toReal_lt_toReal (measure_ne_top _ _)
    (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩)).mpr hmass
  rw [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hε.le, ← FiniteMeasure.ennreal_mass] at hmass'
  change (μ.mass : ℝ) < (μ : Measure ℝ).real K + ε at hmass'
  change (μ.mass : ℝ) - (∫ x, f x ∂μ) < ε
  linarith

/-- The bound that makes the upgrade work even when the measures vary. -/
theorem cutoff_error (μ : FiniteMeasure ℝ) (f : BoundedContinuousFunction ℝ ℝ)
    (χ : C_c(ℝ, ℝ)) (hχ : ∀ x, χ x ∈ Icc 0 1) :
    |(∫ x, f x ∂μ) - ∫ x, χ x * f x ∂μ| ≤
      ‖f‖ * ((μ.mass : ℝ) - ∫ x, χ x ∂μ) := by
  have hiχ : Integrable (fun x => χ x) (μ : Measure ℝ) :=
    χ.continuous.integrable_of_hasCompactSupport χ.hasCompactSupport
  have hip : Integrable (fun x => χ x * f x) (μ : Measure ℝ) :=
    (χ.continuous.mul f.continuous).integrable_of_hasCompactSupport
      (χ.hasCompactSupport.mul_right)
  rw [← integral_sub (f.integrable (μ := (μ : Measure ℝ))) hip]
  calc
    |∫ x, f x - χ x * f x ∂μ| ≤ ∫ x, ‖f x - χ x * f x‖ ∂μ :=
      by
        simpa only [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm (μ := (μ : Measure ℝ)) (fun x => f x - χ x * f x))
    _ ≤ ∫ x, ‖f‖ * (1 - χ x) ∂μ := by
      apply integral_mono ((f.integrable (μ := (μ : Measure ℝ))).sub hip).norm
        ((integrable_const 1).sub hiχ |>.const_mul ‖f‖)
      intro x
      have hc := hχ x
      change ‖f x - χ x * f x‖ ≤ ‖f‖ * (1 - χ x)
      rw [show f x - χ x * f x = (1 - χ x) * f x by ring,
        norm_mul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hc.2)]
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (sub_nonneg.mpr hc.2)
    _ = ‖f‖ * ((μ.mass : ℝ) - ∫ x, χ x ∂μ) := by
      rw [integral_const_mul, integral_sub (integrable_const 1) hiχ, integral_one]

/-- Vague convergence and convergence of total masses imply convergence of all
bounded continuous real tests. No tightness premise is added. -/
theorem «FIN-EXT025-GP-10-weak-upgrade» {ι : Type*} {L : Filter ι}
    (u : ι → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (hv : ∀ f : C_c(ℝ, ℝ), Tendsto (fun n => ∫ x, f x ∂u n) L (𝓝 (∫ x, f x ∂μ)))
    (hm : Tendsto (fun n => ((u n).mass : ℝ)) L (𝓝 (μ.mass : ℝ))) :
    Tendsto u L (𝓝 μ) := by
  rw [FiniteMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε / (8 * (‖f‖ + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨χ, hχ, hsmall⟩ := exists_cutoff μ hδ
  let g : C_c(ℝ, ℝ) :=
    ⟨⟨fun x => χ x * f x, χ.continuous.mul f.continuous⟩,
      χ.hasCompactSupport.mul_right⟩
  have htail := hm.sub (hv χ)
  have ht : ∀ᶠ n in L, ((u n).mass : ℝ) - ∫ x, χ x ∂u n < 2 * δ :=
    htail.eventually (gt_mem_nhds (by linarith :
      (μ.mass : ℝ) - ∫ x, χ x ∂μ < 2 * δ))
  have hg : ∀ᶠ n in L, |(∫ x, g x ∂u n) - ∫ x, g x ∂μ| < ε / 2 := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp (hv g) (ε / 2) (by positivity))
  filter_upwards [ht, hg] with n hn hgn
  rw [Real.dist_eq]
  have ha := cutoff_error (u n) f χ hχ
  have hb := cutoff_error μ f χ hχ
  have he : |(∫ x, f x ∂u n) - ∫ x, f x ∂μ| ≤
      |(∫ x, f x ∂u n) - ∫ x, g x ∂u n| +
      |(∫ x, g x ∂u n) - ∫ x, g x ∂μ| +
      |(∫ x, f x ∂μ) - ∫ x, g x ∂μ| := by
    calc
      _ ≤ |(∫ x, f x ∂u n) - ∫ x, g x ∂u n| +
          |(∫ x, g x ∂u n) - ∫ x, f x ∂μ| := abs_sub_le _ _ _
      _ ≤ |(∫ x, f x ∂u n) - ∫ x, g x ∂u n| +
          (|(∫ x, g x ∂u n) - ∫ x, g x ∂μ| +
            |(∫ x, g x ∂μ) - ∫ x, f x ∂μ|) :=
          add_le_add le_rfl (abs_sub_le _ _ _)
      _ = _ := by rw [abs_sub_comm (∫ x, g x ∂μ)]; ring
  have hnorm := norm_nonneg f
  have han : |(∫ x, f x ∂u n) - ∫ x, g x ∂u n| ≤ ‖f‖ * (2 * δ) :=
    ha.trans (mul_le_mul_of_nonneg_left hn.le hnorm)
  have hbn : |(∫ x, f x ∂μ) - ∫ x, g x ∂μ| ≤ ‖f‖ * δ :=
    hb.trans (mul_le_mul_of_nonneg_left hsmall.le hnorm)
  have hδε : 8 * (‖f‖ + 1) * δ = ε := by dsimp [δ]; field_simp
  nlinarith

/-- The complex-test form used by Cauchy-transform consumers. -/
theorem «FIN-EXT025-GP-10-complex-upgrade» {ι : Type*} {L : Filter ι}
    (u : ι → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (hv : ∀ f : C_c(ℝ, ℝ), Tendsto (fun n => ∫ x, f x ∂u n) L (𝓝 (∫ x, f x ∂μ)))
    (hm : Tendsto (fun n => ((u n).mass : ℝ)) L (𝓝 (μ.mass : ℝ))) :
    ∀ f : BoundedContinuousFunction ℝ ℂ, Tendsto (fun n => ∫ x, f x ∂u n) L (𝓝 (∫ x, f x ∂μ)) :=
  (FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp
    («FIN-EXT025-GP-10-weak-upgrade» u μ hv hm)

/-- The same cutoff explicitly controls the mass outside a compact set. -/
theorem «FIN-EXT025-GP-10-cutoff-tightness» {ι : Type*} {L : Filter ι}
    (u : ι → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (hv : ∀ f : C_c(ℝ, ℝ), Tendsto (fun n => ∫ x, f x ∂u n) L (𝓝 (∫ x, f x ∂μ)))
    (hm : Tendsto (fun n => ((u n).mass : ℝ)) L (𝓝 (μ.mass : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Set ℝ, IsCompact K ∧ ∀ᶠ n in L, (u n : Measure ℝ).real Kᶜ < ε := by
  obtain ⟨χ, hχ, hsmall⟩ := exists_cutoff μ (half_pos hε)
  refine ⟨tsupport χ, χ.hasCompactSupport, ?_⟩
  have ht := (hm.sub (hv χ)).eventually
    (gt_mem_nhds (by linarith : (μ.mass : ℝ) - ∫ x, χ x ∂μ < ε))
  filter_upwards [ht] with n hn
  have hiχ : Integrable (fun x => χ x) (u n : Measure ℝ) :=
    χ.continuous.integrable_of_hasCompactSupport χ.hasCompactSupport
  have hi : Integrable (fun x => 1 - χ x) (u n : Measure ℝ) :=
    (integrable_const 1).sub hiχ
  have hb := hi.measure_le_integral
    (Eventually.of_forall (fun x => sub_nonneg.mpr (hχ x).2))
    (fun x (hx : x ∈ (tsupport χ)ᶜ) => by
      rw [image_eq_zero_of_notMem_tsupport hx]
      norm_num)
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun x => sub_nonneg.mpr (hχ x).2)),
    integral_sub (integrable_const 1) hiχ, integral_one] at hr
  exact hr.trans_lt hn

end QuantumNLS.Ext025B2Weak

#print axioms QuantumNLS.Ext025B2Weak.«FIN-EXT025-GP-10-cutoff-tightness»
#print axioms QuantumNLS.Ext025B2Weak.integral_one
#print axioms QuantumNLS.Ext025B2Weak.exists_cutoff
#print axioms QuantumNLS.Ext025B2Weak.cutoff_error
#print axioms QuantumNLS.Ext025B2Weak.«FIN-EXT025-GP-10-weak-upgrade»
#print axioms QuantumNLS.Ext025B2Weak.«FIN-EXT025-GP-10-complex-upgrade»

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants do
    if n.toString.startsWith "QuantumNLS.Ext025B2Weak." then
      pending := pending.push n
      roots := roots + 1
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
  Lean.logInfo m!"Ext025B2Weak audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
