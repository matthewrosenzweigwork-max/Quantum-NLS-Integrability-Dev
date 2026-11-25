import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB5Nonlin

/-! # Track B, package 2: Duhamel outputs on `[0,δ]` (existence, uniqueness, linearity, bounds)

`IsDuhOut δ F v w`: `v : ℝ → L²(𝕋)` is continuous, `l2ToHm1 (v t)` is the actual `H⁻¹` Bochner Duhamel
integral `duhH F t` for `t ∈ [0,δ]`, and `w` is an a.e.-strongly measurable spacetime function whose
slices are `v t` for a.e. `t`. For `F ∈ L^{4/3}([0,δ] × 𝕋)`:

* existence with the bounds of `duhamel_L43_slab` (`duhOut_exists`);
* uniqueness on `[0,δ]` (`IsDuhOut.unique`: `v = v'` on `[0,δ]`, `w = w'` a.e. on `[0,δ] × 𝕋`);
* linearity (`IsDuhOut.sub`) and invariance under a.e. change of the forcing (`IsDuhOut.congr`);
* the bounds hold for EVERY output (`duhOut_bound`).
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

open MeasureTheory Filter Topology NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38
open scoped ENNReal

attribute [local instance] isProbabilityMeasure_spatialMeasure

/-- Two spacetime functions with a.e. equal slices are a.e. equal. -/
theorem ae_eq_of_slices {ρ : Measure ℝ} [SFinite ρ] {W1 W2 : ℝ × PhysicalCircle → ℂ}
    (h1 : AEStronglyMeasurable W1 (ρ.prod spatialMeasure))
    (h2 : AEStronglyMeasurable W2 (ρ.prod spatialMeasure))
    (h : ∀ᵐ t ∂ρ, (fun x => W1 (t, x)) =ᵐ[spatialMeasure] (fun x => W2 (t, x))) :
    W1 =ᵐ[ρ.prod spatialMeasure] W2 := by
  have e1 := h1.ae_eq_mk
  have e2 := h2.ae_eq_mk
  have s1 := Measure.ae_ae_eq_curry_of_prod e1
  have s2 := Measure.ae_ae_eq_curry_of_prod e2
  have hset : MeasurableSet {p : ℝ × PhysicalCircle | h1.mk W1 p = h2.mk W2 p} :=
    measurableSet_eq_fun h1.stronglyMeasurable_mk.measurable h2.stronglyMeasurable_mk.measurable
  have hmk : h1.mk W1 =ᵐ[ρ.prod spatialMeasure] h2.mk W2 := by
    refine (Measure.ae_prod_iff_ae_ae hset).2 ?_
    filter_upwards [s1, s2, h] with t ht1 ht2 ht
    filter_upwards [ht1, ht2, ht] with x hx1 hx2 hx
    simp only [Function.curry_apply] at hx1 hx2
    rw [← hx1, ← hx2]
    exact hx
  exact e1.trans (hmk.trans e2.symm)

theorem integrable_of_memLp_slab {δ : ℝ} {F : ℝ × PhysicalCircle → ℂ}
    (hF : MemLp F (4 / 3) (slabMeasure δ)) : Integrable F (slabMeasure δ) := by
  have := isFiniteMeasure_slab 0 δ
  exact hF.integrable one_le_four_thirds

theorem intervalIntegrable_duhH_integrand {δ : ℝ} {F : ℝ × PhysicalCircle → ℂ}
    (hF : Integrable F (slabMeasure δ)) {t : ℝ} (ht : t ∈ Set.Icc 0 δ) :
    IntervalIntegrable
      (fun r => freeProp (-1) (t - r) (negIMul (-1) (fnToHm1 (fun x => F (r, x))))) volume 0 t := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1]
  exact IntegrableOn.mono_set (integrable_duhamel_slab hF t)
    (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl ht.2))

/-- Linearity of the actual `H⁻¹` Duhamel integral on `[0,δ]`. -/
theorem duhH_sub {δ : ℝ} {F G : ℝ × PhysicalCircle → ℂ} (hF : Integrable F (slabMeasure δ))
    (hG : Integrable G (slabMeasure δ)) {t : ℝ} (ht : t ∈ Set.Icc 0 δ) :
    duhH (F - G) t = duhH F t - duhH G t := by
  unfold duhH
  rw [← intervalIntegral.integral_sub (intervalIntegrable_duhH_integrand hF ht)
    (intervalIntegrable_duhH_integrand hG ht)]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_integrable_slice hF, ae_integrable_slice hG] with r hr1 hr2 hr
  rw [Set.uIoc_of_le ht.1] at hr
  have hrJ : r ∈ Set.Icc 0 δ := ⟨hr.1.le, hr.2.trans ht.2⟩
  have e : (fun x => (F - G) (r, x)) = (fun x => F (r, x)) - (fun x => G (r, x)) := rfl
  rw [e, fnToHm1_sub (hr1 hrJ) (hr2 hrJ), map_sub, map_sub]

/-- The actual `H⁻¹` Duhamel integral on `[0,δ]` only depends on the a.e. class of the forcing. -/
theorem duhH_congr {δ : ℝ} {F G : ℝ × PhysicalCircle → ℂ} (hF : Integrable F (slabMeasure δ))
    (hG : Integrable G (slabMeasure δ)) (hFG : F =ᵐ[slabMeasure δ] G) {t : ℝ}
    (ht : t ∈ Set.Icc 0 δ) : duhH F t = duhH G t := by
  have h := norm_duhamel_sub_le hF hG t ⟨le_rfl, ht.1.trans ht.2⟩ ht
  have h0 : ∫ p, ‖F p - G p‖ ∂slabMeasure δ = 0 := by
    rw [integral_congr_ae (g := fun _ => (0 : ℝ))]
    · simp
    · filter_upwards [hFG] with p hp
      rw [hp, sub_self, norm_zero]
  rw [h0, mul_zero] at h
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h)

/-- A Duhamel output on `[0,δ]` for the forcing `F`. -/
structure IsDuhOut (δ : ℝ) (F : ℝ × PhysicalCircle → ℂ) (v : ℝ → PhysicalL2)
    (w : ℝ × PhysicalCircle → ℂ) : Prop where
  cont : Continuous v
  ident : ∀ t ∈ Set.Icc 0 δ, l2ToHm1 (v t) = duhH F t
  aesm : AEStronglyMeasurable w stMeasure
  slice : ∀ᵐ t ∂(volume : Measure ℝ), (fun x => w (t, x)) =ᵐ[spatialMeasure] (v t : PhysicalCircle → ℂ)

theorem IsDuhOut.sub {δ : ℝ} {F G : ℝ × PhysicalCircle → ℂ} {v v' : ℝ → PhysicalL2}
    {w w' : ℝ × PhysicalCircle → ℂ} (h : IsDuhOut δ F v w) (h' : IsDuhOut δ G v' w')
    (hF : Integrable F (slabMeasure δ)) (hG : Integrable G (slabMeasure δ)) :
    IsDuhOut δ (F - G) (fun t => v t - v' t) (w - w') where
  cont := h.cont.sub h'.cont
  ident t ht := by rw [map_sub, h.ident t ht, h'.ident t ht, duhH_sub hF hG ht]
  aesm := h.aesm.sub h'.aesm
  slice := by
    filter_upwards [h.slice, h'.slice] with t h1 h2
    filter_upwards [h1, h2, Lp.coeFn_sub (v t) (v' t)] with x hx1 hx2 hx3
    rw [hx3, Pi.sub_apply, Pi.sub_apply, hx1, hx2]

theorem IsDuhOut.congr {δ : ℝ} {F G : ℝ × PhysicalCircle → ℂ} {v : ℝ → PhysicalL2}
    {w : ℝ × PhysicalCircle → ℂ} (h : IsDuhOut δ F v w) (hF : Integrable F (slabMeasure δ))
    (hG : Integrable G (slabMeasure δ)) (hFG : F =ᵐ[slabMeasure δ] G) : IsDuhOut δ G v w where
  cont := h.cont
  ident t ht := by rw [h.ident t ht, duhH_congr hF hG hFG ht]
  aesm := h.aesm
  slice := h.slice

/-- **Uniqueness of Duhamel outputs** on `[0,δ]`. -/
theorem IsDuhOut.unique {δ : ℝ} {F : ℝ × PhysicalCircle → ℂ} {v v' : ℝ → PhysicalL2}
    {w w' : ℝ × PhysicalCircle → ℂ} (h : IsDuhOut δ F v w) (h' : IsDuhOut δ F v' w') :
    (∀ t ∈ Set.Icc 0 δ, v t = v' t) ∧ w =ᵐ[slabMeasure δ] w' := by
  have hv : ∀ t ∈ Set.Icc 0 δ, v t = v' t := fun t ht =>
    l2ToHm1_injective (by rw [h.ident t ht, h'.ident t ht])
  refine ⟨hv, ae_eq_of_slices (h.aesm.mono_measure (slabMeasure_le δ))
    (h'.aesm.mono_measure (slabMeasure_le δ)) ?_⟩
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [h.slice, h'.slice] with t h1 h2 ht
  rw [hv t ht] at h1
  exact h1.trans h2.symm

/-- **Existence of Duhamel outputs** with the short-time bounds. -/
theorem duhOut_exists : ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
    ∀ F : ℝ × PhysicalCircle → ℂ, MemLp F (4 / 3) (slabMeasure δ) →
    ∃ (v : ℝ → PhysicalL2) (w : ℝ × PhysicalCircle → ℂ), IsDuhOut δ F v w ∧
      (∀ t, ‖v t‖ₑ ≤ K * ENNReal.ofReal (δ ^ (1 / 16 : ℝ)) * eLpNorm F (4 / 3) (slabMeasure δ)) ∧
      eLpNorm w 4 stMeasure ≤
        K * ENNReal.ofReal (δ ^ (1 / 16 : ℝ)) * eLpNorm F (4 / 3) (slabMeasure δ) := by
  obtain ⟨K, hK, h⟩ := duhamel_L43_slab
  refine ⟨K, hK, fun δ hδ hδ1 F hF => ?_⟩
  obtain ⟨v, w, h1, h2, h3, h4, h5, h6⟩ := h δ hδ hδ1 F hF
  exact ⟨v, w, ⟨h1, h2, h4, h6⟩, h3, h5⟩

/-- **The short-time bounds hold for every Duhamel output.** -/
theorem duhOut_bound : ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
    ∀ (F : ℝ × PhysicalCircle → ℂ) (v : ℝ → PhysicalL2) (w : ℝ × PhysicalCircle → ℂ),
      MemLp F (4 / 3) (slabMeasure δ) → IsDuhOut δ F v w →
      (∀ t ∈ Set.Icc 0 δ,
        ‖v t‖ₑ ≤ K * ENNReal.ofReal (δ ^ (1 / 16 : ℝ)) * eLpNorm F (4 / 3) (slabMeasure δ)) ∧
      eLpNorm w 4 (slabMeasure δ) ≤
        K * ENNReal.ofReal (δ ^ (1 / 16 : ℝ)) * eLpNorm F (4 / 3) (slabMeasure δ) := by
  obtain ⟨K, hK, h⟩ := duhOut_exists
  refine ⟨K, hK, fun δ hδ hδ1 F v w hF hout => ?_⟩
  obtain ⟨v', w', hout', hv', hw'⟩ := h δ hδ hδ1 F hF
  obtain ⟨he, hwe⟩ := hout.unique hout'
  refine ⟨fun t ht => by rw [he t ht]; exact hv' t, ?_⟩
  rw [eLpNorm_congr_ae hwe]
  exact (eLpNorm_mono_measure _ (slabMeasure_le δ)).trans hw'

/-- A chosen Duhamel output (junk `(0,0)` if none exists). -/
def duhPair (δ : ℝ) (F : ℝ × PhysicalCircle → ℂ) :
    (ℝ → PhysicalL2) × (ℝ × PhysicalCircle → ℂ) := by
  classical
  exact if h : ∃ p : (ℝ → PhysicalL2) × (ℝ × PhysicalCircle → ℂ), IsDuhOut δ F p.1 p.2
    then h.choose else (0, 0)

theorem duhPair_spec {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {F : ℝ × PhysicalCircle → ℂ}
    (hF : MemLp F (4 / 3) (slabMeasure δ)) :
    IsDuhOut δ F (duhPair δ F).1 (duhPair δ F).2 := by
  obtain ⟨K, -, h⟩ := duhOut_exists
  obtain ⟨v, w, hout, -⟩ := h δ hδ hδ1 F hF
  have hex : ∃ p : (ℝ → PhysicalL2) × (ℝ × PhysicalCircle → ℂ), IsDuhOut δ F p.1 p.2 :=
    ⟨(v, w), hout⟩
  unfold duhPair
  simp only [hex, ↓reduceDIte]
  exact hex.choose_spec

end LiebLiniger.FixedPeriod.ALLS.PdeB
