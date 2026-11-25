import QuantumNLS.DEF014Joint
import QuantumNLS.FullMassLimit
import QuantumNLS.PhysicalL2Normalization

/-! Parameter continuity at actual open-band points and continuity of the
unique physical half-integer separators. Positive coupling is carried by
its usual open subtype; all L2 inputs, including vacuum, are permitted. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open Set Filter Topology MeasureTheory
open scoped BoundedContinuousFunction
namespace QuantumNLS.DEF014Phase
variable {L : ℝ} [Fact (0 < L)]
abbrev Param (L : ℝ) [Fact (0 < L)] := {κ : ℝ // 0 < κ} × PhysicalTensor.L2T L

def facts (p : Param L) := PhysicalSourceFinal.sourceFacts p.1.2 p.2

def separator (p : Param L) (n : ℤ) : ℝ := (facts p).phase.separator n

def phase (p : Param L) (x : ℝ) : ℝ := (PhysicalContinuousBoundary.boundary p.1.2 p.2 x).re

def measure (p : Param L) : Measure ℝ := PhysicalQuantumMeasure.measure p.1.2 p.2
instance finite (p : Param L) : IsFiniteMeasure (measure p) := inferInstanceAs
  (IsFiniteMeasure (PhysicalQuantumMeasure.measure p.1.2 p.2))

/-- Neighborhood extraction with an abstract function keeps the physical
Volterra definition out of the neighborhood proof's conversions. -/
theorem common_neighborhood {X : Type*} [TopologicalSpace X]
    (f : X × ℝ → ℝ) (hc : Continuous f) (p : X) (x : ℝ) (hx : f (p,x) < 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ q : X in 𝓝 p,
      ∀ t : ℝ, |t-x| < δ → f (q,t) < 2 := by
  have hn : {r : X × ℝ | f r < 2} ∈ 𝓝 (p,x) :=
    (hc.tendsto (p,x)).eventually (gt_mem_nhds hx)
  obtain ⟨U,hU,V,hV,hUV⟩ := mem_nhds_prod_iff.mp hn
  obtain ⟨δ,hδ,hb⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hU] with q hq t ht
  exact hUV ⟨hq,hb (by simpa [Real.dist_eq] using ht)⟩

/-- A fixed open-band point has a common band neighborhood for nearby parameters. -/
theorem common_band (p : Param L) {x : ℝ}
    (hx : |(L2SpatialTransfer.discriminant p.1.1 p.2 (x : ℂ)).re| < 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ q : Param L in 𝓝 p,
      ∀ t : ℝ, |t - x| < δ →
        |(L2SpatialTransfer.discriminant q.1.1 q.2 (t : ℂ)).re| < 2 := by
  have hmap : Continuous (fun r : Param L × ℝ =>
      (((r.1.1.1, r.1.2) : ℝ × PhysicalTensor.L2T L), (r.2 : ℂ))) := by
    fun_prop
  have hdisc := (DEF014Joint.continuous_discriminant_joint (L := L)).comp hmap
  have hc : Continuous (fun r : Param L × ℝ =>
      |(L2SpatialTransfer.discriminant r.1.1.1 r.1.2 (r.2 : ℂ)).re|) :=
    (Complex.continuous_re.comp hdisc).abs
  exact common_neighborhood _ hc p x hx

/-- This cutoff equals the real Cauchy kernel on every common support. -/
def kernel (x δ : ℝ) (hδ : 0 < δ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t => (x - t) / max (δ ^ 2) ((x - t) ^ 2)) (by
      apply Continuous.div (by fun_prop) (by fun_prop)
      intro t
      exact ne_of_gt (lt_of_lt_of_le (sq_pos_of_pos hδ) (le_max_left _ _)))
    (δ⁻¹) (by
      intro t
      rw [Real.norm_eq_abs, abs_div, abs_of_pos
        (lt_of_lt_of_le (sq_pos_of_pos hδ) (le_max_left _ _))]
      apply (div_le_iff₀ (lt_of_lt_of_le (sq_pos_of_pos hδ) (le_max_left _ _))).mpr
      rcases le_total |x - t| δ with ht | ht
      · rw [inv_mul_eq_div]
        apply (le_div_iff₀ hδ).mpr
        calc |x - t| * δ ≤ δ ^ 2 := by nlinarith
             _ ≤ max (δ ^ 2) ((x - t) ^ 2) := le_max_left _ _
      · have he : max (δ ^ 2) ((x - t) ^ 2) = (x - t) ^ 2 := by
          apply max_eq_right
          nlinarith [sq_abs (x - t)]
        rw [he, inv_mul_eq_div]
        apply (le_div_iff₀ hδ).mpr
        nlinarith [sq_abs (x - t)])

theorem kernel_eq (x δ : ℝ) (hδ : 0 < δ) {t : ℝ} (ht : δ ≤ |x - t|) :
    kernel x δ hδ t = (x - t)⁻¹ := by
  change (x - t) / max (δ ^ 2) ((x - t) ^ 2) = _
  have he : max (δ ^ 2) ((x - t) ^ 2) = (x - t) ^ 2 := by
    apply max_eq_right
    nlinarith [sq_abs (x - t)]
  rw [he]
  have hn : x - t ≠ 0 := by
    have : 0 < |x - t| := hδ.trans_le ht
    exact abs_pos.mp this
  field_simp

/-- Band vanishing includes the vacuum without a nonzero-input hypothesis. -/
theorem measure_band_zero (p : Param L) {S : Set ℝ} (hS : MeasurableSet S)
    (hband : ∀ t ∈ S, |(L2SpatialTransfer.discriminant p.1.1 p.2 (t : ℂ)).re| ≤ 2) :
    measure p S = 0 := by
  by_cases hu : p.2 = 0
  · simp [measure, hu]
  · exact PhysicalBandCauchy.measure_band_zero p.1.2 hu hS hband

/-- The selected boundary agrees with its real Cauchy integral on bands. -/
theorem phase_eq_integral (p : Param L) {x δ : ℝ} (hδ : 0 < δ)
    (hb : ∀ t : ℝ, |t - x| < δ →
      |(L2SpatialTransfer.discriminant p.1.1 p.2 (t : ℂ)).re| < 2) :
    phase p x = L * x / 2 - p.1.1 * ∫ t, kernel x δ hδ t ∂(measure p) := by
  by_cases hu : p.2 = 0
  · simp [phase, PhysicalContinuousBoundary.boundary_zero, hu, measure]
  · have hx := hb x (by simpa using hδ)
    rw [phase, PhysicalContinuousBoundary.band_eq p.1.2 hu hx]
    have hz : measure p (Metric.ball x δ) = 0 :=
      measure_band_zero p Metric.isOpen_ball.measurableSet (fun t ht =>
        (hb t (by simpa [Metric.mem_ball, Real.dist_eq] using ht)).le)
    have he : (fun t : ℝ => ((x : ℂ) - (t : ℂ))⁻¹) =ᵐ[measure p]
        fun t => (kernel x δ hδ t : ℂ) := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with t ht
      rw [kernel_eq x δ hδ (by simpa [Metric.mem_ball, Real.dist_eq,
        abs_sub_comm, not_lt] using ht)]
      simp
    simp only [SpatialTransfer.boundaryPhase, EmpiricalRapidity.cauchyTransform]
    change ((L : ℂ) * (x : ℂ) / 2 - (p.1.1 : ℂ) *
      (∫ t : ℝ, ((x : ℂ) - (t : ℂ))⁻¹ ∂(measure p))).re = _
    rw [integral_congr_ae he, integral_complex_ofReal]
    simp

theorem continuous_phase_at_band (p : Param L) {x : ℝ}
    (hx : |(L2SpatialTransfer.discriminant p.1.1 p.2 (x : ℂ)).re| < 2) :
    ContinuousAt (fun q : Param L => phase q x) p := by
  obtain ⟨δ, hδ, hband⟩ := common_band p hx
  have hm : Continuous (fun q : Param L => FullMass.Mfin q.1.1 q.2) :=
    FullMassLimit.continuous_Mfin.comp
      (((continuous_subtype_val.comp continuous_fst).subtype_mk
        (fun q => q.1.2.le)).prodMk continuous_snd)
  have hi := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp (hm.tendsto p))
    (kernel x δ hδ)
  have he (q : Param L) : (FullMass.Mfin q.1.1 q.2 : Measure ℝ) = measure q :=
    (PhysicalL2Normalization.measure_eq_Mmeas q.1.2 q.2).symm
  simp_rw [he] at hi
  have ht : Tendsto (fun q : Param L => L*x/2 - q.1.1 *
      ∫ t, kernel x δ hδ t ∂(measure q)) (𝓝 p)
      (𝓝 (L*x/2 - p.1.1 * ∫ t, kernel x δ hδ t ∂(measure p))) :=
    tendsto_const_nhds.sub
      (((continuous_subtype_val.comp continuous_fst).tendsto p).mul hi)
  have hbase := phase_eq_integral p hδ (Filter.Eventually.self_of_nhds hband)
  rw [← hbase] at ht
  exact ht.congr' (hband.mono fun q hq => (phase_eq_integral q hδ hq).symm)


/-- The actual selected separator varies continuously, jointly in positive
coupling and arbitrary physical L2 input. -/
theorem continuous_separator (n : ℤ) : Continuous (fun p : Param L => separator p n) := by
  rw [continuous_iff_continuousAt]
  intro p
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  let b := separator p n
  have hx : |(L2SpatialTransfer.discriminant p.1.1 p.2 (b : ℂ)).re| < 2 :=
    (facts p).separator_in_band n
  obtain ⟨δ, hδ, hband⟩ := common_band p hx
  have hb := Filter.Eventually.self_of_nhds hband
  let r := min δ ε / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrd : r < δ := by dsimp [r]; linarith [min_le_left δ ε]
  have hre : r < ε := by dsimp [r]; linarith [min_le_right δ ε]
  have hbl : |(L2SpatialTransfer.discriminant p.1.1 p.2 ((b-r : ℝ) : ℂ)).re| < 2 :=
    hb (b-r) (by simpa [abs_of_nonneg hr.le] using hrd)
  have hbr : |(L2SpatialTransfer.discriminant p.1.1 p.2 ((b+r : ℝ) : ℂ)).re| < 2 :=
    hb (b+r) (by simpa [abs_of_nonneg hr.le] using hrd)
  have hl : phase p (b-r) < MonotoneIndexedMasses.level n :=
    ((facts p).phase.lt_separator_iff _ n).mp (by change b-r < b; linarith)
  have hu : MonotoneIndexedMasses.level n < phase p (b+r) :=
    ((facts p).phase.separator_lt_iff _ n).mp (by change b < b+r; linarith)
  have hleft := (continuous_phase_at_band p hbl).tendsto.eventually (gt_mem_nhds hl)
  have hright := (continuous_phase_at_band p hbr).tendsto.eventually (lt_mem_nhds hu)
  filter_upwards [hleft, hright] with q hql hqr
  have h1 : b-r < separator q n := ((facts q).phase.lt_separator_iff _ n).mpr hql
  have h2 : separator q n < b+r := ((facts q).phase.separator_lt_iff _ n).mpr hqr
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end QuantumNLS.DEF014Phase

#print axioms QuantumNLS.DEF014Phase.continuous_phase_at_band
#print axioms QuantumNLS.DEF014Phase.continuous_separator

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.DEF014Phase." then
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
  Lean.logInfo m!"DEF014Phase audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
