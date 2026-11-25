import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB5Forward

/-! # Track B, package 3: the interaction-picture coefficient form of the `H⁻¹` Duhamel identity

`intA u n t = e^{it(2πn)²} û_n(t)` (`freePhase (-t) n * physicalFourier (u t) n`) and
`intG U n r = e^{ir(2πn)²}(-i) (2|U(r)|²U(r))^_n`. For an `L⁴` slab representative the scalar
functions `intG U n` are integrable on the slab, agree a.e. with the coordinates of the approved
`duhamelIntegrand U 0`, and (`isHm1Duhamel_iff_intA`) the approved `IsHm1Duhamel u U` is equivalent
to `intA u n t = intA u n 0 + ∫₀ᵗ intG U n` for all `n, t`.
-/

namespace LiebLiniger.FixedPeriod.ALLS.PdeB
open MeasureTheory NlsGge.Pilot NlsGge.NLS38 NlsGge.Birkhoff NlsGge.Sobolev38
open scoped ContDiff
set_option autoImplicit false
noncomputable section

/-- Interaction-picture coefficient `e^{it(2πn)²} û_n(t)`. -/
def intA (u : ℝ → PhysicalL2) (n : ℤ) (t : ℝ) : ℂ := freePhase (-t) n * physicalFourier (u t) n

/-- Interaction-picture forcing coefficient `e^{ir(2πn)²} (-i) N̂_n(r)`, `N = 2|U|²U`. -/
def intG (U : ℝ × PhysicalCircle → ℂ) (n : ℤ) (r : ℝ) : ℂ :=
  freePhase (-r) n * (-Complex.I * physicalFourier (fun x => cubicNL (U (r, x))) n)

/-- The slab measure `dt ⊗ dx` on `[a,b] × 𝕋`. -/
abbrev slabM (a b : ℝ) : Measure (ℝ × PhysicalCircle) :=
  spacetimeMeasure.restrict (Set.Icc a b ×ˢ (Set.univ : Set PhysicalCircle))

theorem coe38_add (r : ℝ) (x y : SobolevCarrier38 r) (n : ℤ) :
    carrierCoe38 r (x + y) n = carrierCoe38 r x n + carrierCoe38 r y n := rfl

theorem freePhase_neg_mul (t : ℝ) (n : ℤ) : freePhase (-t) n * freePhase t n = 1 := by
  rw [← freePhase_add, neg_add_cancel, freePhase_zero]

theorem freePhase_mul_neg (t : ℝ) (n : ℤ) : freePhase t n * freePhase (-t) n = 1 := by
  rw [mul_comm, freePhase_neg_mul]

theorem integrable_cubic_slabM {U : ℝ × PhysicalCircle → ℂ} {a b : ℝ}
    (hU : MemLp U 4 (slabM a b)) :
    Integrable (fun p => cubicNL (U p))
      (((volume : Measure ℝ).restrict (Set.Icc a b)).prod spatialMeasure) :=
  integrable_cubic_slab hU

theorem intG_ae_eq {U : ℝ × PhysicalCircle → ℂ} {a b : ℝ} (hU : MemLp U 4 (slabM a b)) (n : ℤ) :
    ∀ᵐ r ∂((volume : Measure ℝ).restrict (Set.Icc a b)),
      intG U n r = carrierCoe38 (-1) (duhamelIntegrand U 0 r) n := by
  have h := ae_integrable_slice (integrable_cubic_slabM hU)
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [h] with r hr hmem
  rw [duhamelIntegrand, carrierCoe38_freeProp, carrierCoe38_negIMul,
    carrierCoe38_fnToHm1 (hr hmem), zero_sub]
  rfl

theorem integrableOn_intG {U : ℝ × PhysicalCircle → ℂ} {a b : ℝ} (hU : MemLp U 4 (slabM a b))
    (n : ℤ) : IntegrableOn (intG U n) (Set.Icc a b) := by
  have h := integrable_duhamel_slab (integrable_cubic_slabM hU) 0
  have h2 := (carrierCoordCLM (-1) n).integrable_comp h
  refine h2.congr ?_
  filter_upwards [intG_ae_eq hU n] with r hr
  rw [hr]
  rfl

theorem intervalIntegrable_intG {U : ℝ × PhysicalCircle → ℂ} {a b : ℝ}
    (hU : MemLp U 4 (slabM a b)) (n : ℤ) {s t : ℝ} (hs : s ∈ Set.Icc a b)
    (ht : t ∈ Set.Icc a b) : IntervalIntegrable (intG U n) volume s t :=
  ((integrableOn_intG hU n).mono_set (Set.uIcc_subset_Icc hs ht)).intervalIntegrable

theorem memLp_slabM_of_isL4Loc {U : ℝ × PhysicalCircle → ℂ} (h4 : IsL4Loc U) (a b : ℝ) :
    MemLp U 4 (slabM a b) := by
  set T := max |a| |b|
  have ha := abs_le.mp (le_max_left |a| |b|)
  have hb := abs_le.mp (le_max_right |a| |b|)
  refine (h4 T).mono_measure (Measure.restrict_mono ?_ le_rfl)
  intro p hp
  exact ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, trivial⟩

/-- Coefficient form of the scalar Duhamel identity (time-`0` based). -/
theorem coeff_duhamel_iff {u : ℝ → PhysicalL2} {U : ℝ × PhysicalCircle → ℂ}
    (n : ℤ) (t : ℝ) :
    (physicalFourier (u t) n = freePhase t n * physicalFourier (u 0) n +
        ∫ r in (0 : ℝ)..t, freePhase (t - r) n *
          (-Complex.I * physicalFourier (fun x => cubicNL (U (r, x))) n)) ↔
      intA u n t = intA u n 0 + ∫ r in (0 : ℝ)..t, intG U n r := by
  have hint : ∀ c : ℂ, (∫ r in (0 : ℝ)..t, c * intG U n r) = c * ∫ r in (0 : ℝ)..t, intG U n r :=
    fun c => intervalIntegral.integral_const_mul c _
  have hrew : (∫ r in (0 : ℝ)..t, freePhase (t - r) n *
      (-Complex.I * physicalFourier (fun x => cubicNL (U (r, x))) n)) =
      freePhase t n * ∫ r in (0 : ℝ)..t, intG U n r := by
    rw [← hint]
    refine intervalIntegral.integral_congr fun r _ => ?_
    simp only [intG]
    rw [show t - r = t + -r by ring, freePhase_add]
    ring
  rw [hrew]
  simp only [intA, neg_zero, freePhase_zero, one_mul]
  constructor
  · intro h
    rw [h, mul_add, ← mul_assoc, freePhase_neg_mul, ← mul_assoc, freePhase_neg_mul, one_mul,
      one_mul]
  · intro h
    have h' := congrArg (fun z => freePhase t n * z) h
    rw [← mul_assoc, freePhase_mul_neg, one_mul] at h'
    rw [h']
    ring

/-- **Interaction-picture form** of the approved `H⁻¹` Duhamel identity. -/
theorem isHm1Duhamel_iff_intA {u : ℝ → PhysicalL2} {U : ℝ × PhysicalCircle → ℂ} (h4 : IsL4Loc U) :
    IsHm1Duhamel u U ↔ ∀ n t, intA u n t = intA u n 0 + ∫ r in (0 : ℝ)..t, intG U n r := by
  constructor
  · intro hD n t
    refine (coeff_duhamel_iff n t).1 ?_
    have h := congrArg (fun z => carrierCoe38 (-1) z n) (hD t).2
    rw [coe38_add, carrierCoe38_duhamelIntegral h4] at h
    exact h
  · intro h t
    refine ⟨duhamelIntegrand_intervalIntegrable h4 t 0 t, carrierExt38 (funext fun n => ?_)⟩
    rw [coe38_add, carrierCoe38_duhamelIntegral h4]
    exact (coeff_duhamel_iff n t).2 (h n t)

end

end LiebLiniger.FixedPeriod.ALLS.PdeB
