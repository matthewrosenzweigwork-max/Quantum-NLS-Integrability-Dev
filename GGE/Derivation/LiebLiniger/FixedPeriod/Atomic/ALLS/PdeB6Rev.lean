import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB6Mass

/-! # Track B, package 3: complex conjugation, time reversal, translation and congruence of
interval solutions

`conjL2` is complex conjugation on `L²(𝕋)` (isometric, involutive, `(conj v)^_n = conj(v̂_{-n})`).
For the interval-solution predicate `MassHyp u U a b` (continuity on `[a,b]`, `L⁴` slab representative,
slices, interaction-picture coefficient identities):
* `MassHyp.rev`: `t ↦ conj(u(-t))` with `(t,x) ↦ conj(U(-t,x))` solves on `[-b,-a]`;
* `MassHyp.shift`: `t ↦ u(t+c)` with `U(·+c,·)` solves on `[a-c,b-c]`;
* `MassHyp.congr`: change of `u` on `[a,b]` and of `U` off `(a,b) × 𝕋`.
-/

namespace LiebLiniger.FixedPeriod.ALLS.PdeB
open MeasureTheory Filter Topology NlsGge.Pilot NlsGge.NLS38 NlsGge.Birkhoff NlsGge.Sobolev38
open scoped ComplexConjugate ENNReal
set_option autoImplicit false
noncomputable section

attribute [local instance] isProbabilityMeasure_spatial

theorem memLp_conj_fun {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞} {f : α → ℂ}
    (hf : MemLp f p μ) : MemLp (fun x => conj (f x)) p μ :=
  hf.of_le (Complex.continuous_conj.comp_aestronglyMeasurable hf.aestronglyMeasurable)
    (ae_of_all _ fun x => by rw [Complex.norm_conj])

/-- Complex conjugation on `L²(𝕋)`. -/
def conjL2 (v : PhysicalL2) : PhysicalL2 := (memLp_conj_fun (Lp.memLp v)).toLp (fun x => conj (v x))

theorem coeFn_conjL2 (v : PhysicalL2) :
    (conjL2 v : PhysicalCircle → ℂ) =ᵐ[spatialMeasure] fun x => conj (v x) :=
  MemLp.coeFn_toLp _

theorem conjL2_sub (v w : PhysicalL2) : conjL2 v - conjL2 w = conjL2 (v - w) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_conjL2 v, coeFn_conjL2 w, coeFn_conjL2 (v - w),
    Lp.coeFn_sub (conjL2 v) (conjL2 w), Lp.coeFn_sub v w] with x h1 h2 h3 h4 h5
  rw [h4, Pi.sub_apply, h1, h2, h3, h5, Pi.sub_apply, map_sub]

theorem norm_conjL2 (v : PhysicalL2) : ‖conjL2 v‖ = ‖v‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (coeFn_conjL2 v)]
  congr 1
  exact eLpNorm_congr_norm_ae
    (Complex.continuous_conj.comp_aestronglyMeasurable (Lp.aestronglyMeasurable v))
    (Lp.aestronglyMeasurable v) (ae_of_all _ fun x => Complex.norm_conj _)

theorem continuous_conjL2 : Continuous conjL2 :=
  (Isometry.of_dist_eq fun v w => by
    rw [dist_eq_norm, dist_eq_norm, conjL2_sub, norm_conjL2]).continuous

theorem conjL2_conjL2 (v : PhysicalL2) : conjL2 (conjL2 v) = v := by
  refine Lp.ext ?_
  filter_upwards [coeFn_conjL2 (conjL2 v), coeFn_conjL2 v] with x h1 h2
  rw [h1, h2, Complex.conj_conj]

theorem physicalFourier_conj_fun (f : PhysicalCircle → ℂ) (n : ℤ) :
    physicalFourier (fun x => conj (f x)) n = conj (physicalFourier f (-n)) := by
  rw [physicalFourier_eq_conj, physicalFourier_eq_conj, ← integral_conj]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [map_mul, Complex.conj_conj]
  rw [fourier_neg]

theorem physicalFourier_conjL2 (v : PhysicalL2) (n : ℤ) :
    physicalFourier (conjL2 v) n = conj (physicalFourier v (-n)) := by
  rw [physicalFourier_congr_ae (coeFn_conjL2 v), physicalFourier_conj_fun]

theorem disp_neg (n : ℤ) : disp (-n) = disp n := by
  unfold disp; push_cast; ring

theorem conj_freePhase (t : ℝ) (n : ℤ) : conj (freePhase t n) = freePhase (-t) n := by
  unfold freePhase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem freePhase_neg_index (t : ℝ) (n : ℤ) : freePhase t (-n) = freePhase t n := by
  unfold freePhase; rw [disp_neg]

theorem cubicNL_conj (z : ℂ) : cubicNL (conj z) = conj (cubicNL z) := by
  simp only [cubicNL, map_mul, Complex.norm_conj, Complex.conj_ofReal, map_ofNat]

theorem intervalIntegral_conj_gen (f : ℝ → ℂ) (a b : ℝ) :
    ∫ x in a..b, conj (f x) = conj (∫ x in a..b, f x) := by
  rcases le_total a b with h | h
  · exact intervalIntegral_conj h
  · rw [intervalIntegral.integral_symm b a, intervalIntegral.integral_symm b a,
      intervalIntegral_conj h, map_neg]

/-- Time reversal of a trajectory. -/
def revL2 (u : ℝ → PhysicalL2) (t : ℝ) : PhysicalL2 := conjL2 (u (-t))

/-- Time reversal of a representative. -/
def revU (U : ℝ × PhysicalCircle → ℂ) (p : ℝ × PhysicalCircle) : ℂ := conj (U (-p.1, p.2))

theorem intA_rev (u : ℝ → PhysicalL2) (n : ℤ) (t : ℝ) :
    intA (revL2 u) n t = conj (intA u (-n) (-t)) := by
  simp only [intA, revL2, physicalFourier_conjL2, map_mul, conj_freePhase, freePhase_neg_index,
    neg_neg]

theorem intG_rev (U : ℝ × PhysicalCircle → ℂ) (n : ℤ) (r : ℝ) :
    intG (revU U) n r = -conj (intG U (-n) (-r)) := by
  simp only [intG, revU, cubicNL_conj, physicalFourier_conj_fun, map_mul, map_neg, Complex.conj_I,
    conj_freePhase, freePhase_neg_index, neg_neg]
  ring

/-- Time reflection `(t,x) ↦ (-t,x)`. -/
def tneg (p : ℝ × PhysicalCircle) : ℝ × PhysicalCircle := (-p.1, p.2)

theorem measurePreserving_tneg : MeasurePreserving tneg spacetimeMeasure spacetimeMeasure :=
  (Measure.measurePreserving_neg (volume : Measure ℝ)).prod (MeasurePreserving.id spatialMeasure)

theorem tneg_preimage (a b : ℝ) :
    tneg ⁻¹' (Set.Icc a b ×ˢ (Set.univ : Set PhysicalCircle)) = Set.Icc (-b) (-a) ×ˢ Set.univ := by
  ext p
  simp only [tneg, Set.mem_preimage, Set.mem_prod, Set.mem_Icc, Set.mem_univ, and_true]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

theorem tshift_preimage' (c a b : ℝ) :
    tshift c ⁻¹' (Set.Icc a b ×ˢ (Set.univ : Set PhysicalCircle)) =
      Set.Icc (a - c) (b - c) ×ˢ Set.univ := by
  ext p
  simp only [tshift, Set.mem_preimage, Set.mem_prod, Set.mem_Icc, Set.mem_univ, and_true]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

theorem ae_restrict_neg {a b : ℝ} {P : ℝ → Prop}
    (h : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Icc a b)), P t) :
    ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Icc (-b) (-a))), P (-t) := by
  rw [ae_restrict_iff' measurableSet_Icc] at h ⊢
  have h2 := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae h
  filter_upwards [h2] with t ht hmem
  exact ht ⟨by linarith [hmem.2], by linarith [hmem.1]⟩

theorem ae_restrict_add {a b c : ℝ} {P : ℝ → Prop}
    (h : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Icc a b)), P t) :
    ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Icc (a - c) (b - c))), P (t + c) := by
  rw [ae_restrict_iff' measurableSet_Icc] at h ⊢
  have h2 := (measurePreserving_add_right (volume : Measure ℝ) c).quasiMeasurePreserving.ae h
  filter_upwards [h2] with t ht hmem
  exact ht ⟨by linarith [hmem.1], by linarith [hmem.2]⟩

theorem ae_ne_real (c : ℝ) : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ c := by
  rw [ae_iff]
  simp

theorem ae_fst_ne (c : ℝ) : ∀ᵐ p ∂spacetimeMeasure, p.1 ≠ c := by
  rw [ae_iff]
  have e : {p : ℝ × PhysicalCircle | ¬p.1 ≠ c} = {c} ×ˢ Set.univ := by
    ext p; simp
  rw [e, spacetimeMeasure, Measure.prod_prod]
  simp

namespace MassHyp

variable {u : ℝ → PhysicalL2} {U : ℝ × PhysicalCircle → ℂ} {a b : ℝ}

/-- **Time reversal** of an interval solution. -/
theorem rev (H : MassHyp u U a b) : MassHyp (revL2 u) (revU U) (-b) (-a) where
  cont := continuous_conjL2.comp_continuousOn (H.cont.comp continuous_neg.continuousOn
    fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  memLp := by
    have hB : MeasurableSet (Set.Icc a b ×ˢ (Set.univ : Set PhysicalCircle)) :=
      measurableSet_Icc.prod MeasurableSet.univ
    have hmp := measurePreserving_tneg.restrict_preimage hB
    rw [tneg_preimage] at hmp
    exact (memLp_conj_fun H.memLp).comp_measurePreserving hmp
  slice := by
    filter_upwards [ae_restrict_neg H.slice] with t ht
    filter_upwards [ht, coeFn_conjL2 (u (-t))] with x h1 h2
    simp only [revU, revL2]
    rw [h2, h1]
  coeff := by
    intro n s hs t ht
    have hs' : -s ∈ Set.Icc a b := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have ht' : -t ∈ Set.Icc a b := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    rw [intA_rev, intA_rev, ← map_sub, H.coeff (-n) (-s) hs' (-t) ht',
      ← intervalIntegral_conj_gen]
    simp_rw [intG_rev]
    rw [intervalIntegral.integral_neg,
      intervalIntegral.integral_comp_neg (fun r => conj (intG U (-n) r)),
      intervalIntegral.integral_symm]

/-- **Time translation** of an interval solution. -/
theorem shift (H : MassHyp u U a b) (c : ℝ) :
    MassHyp (fun t => u (t + c)) (fun p => U (p.1 + c, p.2)) (a - c) (b - c) where
  cont := H.cont.comp (continuous_id.add continuous_const).continuousOn
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  memLp := by
    have hB : MeasurableSet (Set.Icc a b ×ˢ (Set.univ : Set PhysicalCircle)) :=
      measurableSet_Icc.prod MeasurableSet.univ
    have hmp := (measurePreserving_tshift c).restrict_preimage hB
    rw [tshift_preimage'] at hmp
    exact H.memLp.comp_measurePreserving hmp
  slice := ae_restrict_add H.slice
  coeff := by
    intro n s hs t ht
    have hs' : s + c ∈ Set.Icc a b := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have ht' : t + c ∈ Set.Icc a b := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hA : ∀ r, intA (fun t => u (t + c)) n r = freePhase c n * intA u n (r + c) := fun r => by
      simp only [intA]
      rw [← mul_assoc, ← freePhase_add]
      congr 2; ring
    have hG : ∀ r, intG (fun p => U (p.1 + c, p.2)) n r = freePhase c n * intG U n (r + c) :=
      fun r => by
        simp only [intG]
        rw [← mul_assoc (freePhase c n), ← freePhase_add]
        congr 2; ring
    rw [hA, hA, ← mul_sub, H.coeff n (s + c) hs' (t + c) ht']
    simp_rw [hG]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_add_right (fun r => intG U n r)]

/-- **Congruence**: change `u` only off `[a,b]` and `U` only off `(a,b) × 𝕋`. -/
theorem congr (H : MassHyp u U a b) {u' : ℝ → PhysicalL2} {U' : ℝ × PhysicalCircle → ℂ}
    (hu : ∀ t ∈ Set.Icc a b, u t = u' t)
    (hU : ∀ t ∈ Set.Ioo a b, ∀ x, U (t, x) = U' (t, x)) : MassHyp u' U' a b where
  cont := H.cont.congr fun t ht => (hu t ht).symm
  memLp := by
    refine H.memLp.ae_eq ?_
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod MeasurableSet.univ),
      ae_restrict_of_ae (ae_fst_ne a), ae_restrict_of_ae (ae_fst_ne b)] with p hp h1 h2
    have := hU p.1 ⟨lt_of_le_of_ne hp.1.1 (Ne.symm h1), lt_of_le_of_ne hp.1.2 h2⟩ p.2
    exact this
  slice := by
    filter_upwards [H.slice, ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (ae_ne_real a), ae_restrict_of_ae (ae_ne_real b)] with t ht hmem h1 h2
    have htt : t ∈ Set.Ioo a b := ⟨lt_of_le_of_ne hmem.1 (Ne.symm h1), lt_of_le_of_ne hmem.2 h2⟩
    rw [← hu t hmem]
    filter_upwards [ht] with x hx
    rw [← hU t htt x, hx]
  coeff := by
    intro n s hs t ht
    have hA : ∀ r ∈ Set.Icc a b, intA u' n r = intA u n r := fun r hr => by
      simp only [intA, hu r hr]
    rw [hA t ht, hA s hs, H.coeff n s hs t ht]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_ne_real a, ae_ne_real b] with r h1 h2 hr
    have hsub : Set.uIoc s t ⊆ Set.Icc a b :=
      Set.uIoc_subset_uIcc.trans (Set.uIcc_subset_Icc hs ht)
    have hrr := hsub hr
    have hrr' : r ∈ Set.Ioo a b := ⟨lt_of_le_of_ne hrr.1 (Ne.symm h1), lt_of_le_of_ne hrr.2 h2⟩
    simp only [intG]
    congr 3
    funext x
    rw [hU r hrr' x]

end MassHyp

end

end LiebLiniger.FixedPeriod.ALLS.PdeB
