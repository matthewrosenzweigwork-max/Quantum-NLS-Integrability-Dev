import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB6Global

/-! # Track B: approved contracts 8, 9, 10 (time shift of the solution classes, representative
invariance)

Statements copied verbatim from the owner-approved `TRACK_B_EXACT_STATEMENTS_FOR_APPROVAL.txt`
(sha256 943a37c24a40c74b1e025c9f243c49372b9e071c313bebf28cda3ace2f3ca056).
Helpers: shifted test functions, translation invariance of `stripMeasure`, the measure-preserving
strip map `(t,x) ↦ (t, x mod 1)` from `stripMeasure` to `spacetimeMeasure`.
-/

namespace LiebLiniger.FixedPeriod.ALLS.PdeB
open MeasureTheory NlsGge.Pilot NlsGge.NLS38 NlsGge.Birkhoff NlsGge.Sobolev38
open scoped ContDiff
set_option autoImplicit false
noncomputable section

attribute [local instance] isProbabilityMeasure_spatial

theorem isSpacetimeTest_shift {φ : ℝ × ℝ → ℂ} (hφ : IsSpacetimeTest φ) (s : ℝ) :
    IsSpacetimeTest (fun q => φ (q.1 - s, q.2)) where
  smooth := hφ.smooth.comp ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd)
  periodic := fun t x => hφ.periodic (t - s) x
  compact_time := by
    obtain ⟨T, hT⟩ := hφ.compact_time
    refine ⟨T + |s|, fun t x ht => hT (t - s) x ?_⟩
    have h1 : |t| ≤ |t - s| + |s| := by
      have := abs_add_le (t - s) s
      rwa [sub_add_cancel] at this
    linarith

theorem measurePreserving_stripShift (s : ℝ) :
    MeasurePreserving (fun p : ℝ × ℝ => (p.1 + s, p.2)) stripMeasure stripMeasure :=
  (measurePreserving_add_right (volume : Measure ℝ) s).prod
    (MeasurePreserving.id ((volume : Measure ℝ).restrict (Set.Ioc 0 1)))

theorem isDistributionalNLS_shift {U : ℝ × PhysicalCircle → ℂ} (hD : IsDistributionalNLS U)
    (s : ℝ) : IsDistributionalNLS (fun p => U (p.1 + s, p.2)) := by
  intro φ hφ
  obtain ⟨hl, hr, he⟩ := hD (fun q => φ (q.1 - s, q.2)) (isSpacetimeTest_shift hφ s)
  have hmp := measurePreserving_stripShift s
  have hlhs : (fun p : ℝ × ℝ => U (p.1 + s, (p.2 : PhysicalCircle)) *
      (iteratedDeriv 2 (fun y => φ (p.1, y)) p.2 -
        Complex.I * deriv (fun s' => φ (s', p.2)) p.1)) =
      (fun q : ℝ × ℝ => U (q.1, (q.2 : PhysicalCircle)) *
        (iteratedDeriv 2 (fun y => φ (q.1 - s, y)) q.2 -
          Complex.I * deriv (fun s' => φ (s' - s, q.2)) q.1)) ∘ (fun p : ℝ × ℝ => (p.1 + s, p.2)) := by
    funext p
    simp only [Function.comp_apply, add_sub_cancel_right]
    rw [deriv_comp_sub_const (f := fun s' => φ (s', p.2)), add_sub_cancel_right]
  have hrhs : (fun p : ℝ × ℝ => cubicNL (U (p.1 + s, (p.2 : PhysicalCircle))) * φ p) =
      (fun q : ℝ × ℝ => cubicNL (U (q.1, (q.2 : PhysicalCircle))) * φ (q.1 - s, q.2)) ∘
        (fun p : ℝ × ℝ => (p.1 + s, p.2)) := by
    funext p
    simp only [Function.comp_apply, add_sub_cancel_right]
  refine ⟨?_, ?_, ?_⟩
  · simp only
    rw [hlhs]
    exact (hmp.integrable_comp_emb (MeasurableEquiv.addRight s |>.prodCongr
      (MeasurableEquiv.refl ℝ)).measurableEmbedding).2 hl
  · simp only
    rw [hrhs]
    exact (hmp.integrable_comp_emb (MeasurableEquiv.addRight s |>.prodCongr
      (MeasurableEquiv.refl ℝ)).measurableEmbedding).2 hr
  · have memb : MeasurableEmbedding (fun p : ℝ × ℝ => (p.1 + s, p.2)) :=
      (MeasurableEquiv.addRight s |>.prodCongr (MeasurableEquiv.refl ℝ)).measurableEmbedding
    simp only
    rw [hlhs, hrhs]
    have e1 := hmp.integral_comp memb (fun q : ℝ × ℝ => U (q.1, (q.2 : PhysicalCircle)) *
        (iteratedDeriv 2 (fun y => φ (q.1 - s, y)) q.2 -
          Complex.I * deriv (fun s' => φ (s' - s, q.2)) q.1))
    have e2 := hmp.integral_comp memb
      (fun q : ℝ × ℝ => cubicNL (U (q.1, (q.2 : PhysicalCircle))) * φ (q.1 - s, q.2))
    exact e1.trans (he.trans e2.symm)

/-! ### Approved contracts 8 and 9 -/

theorem isL2ClassSolution_shift (u : ℝ → PhysicalL2) (hu : IsL2ClassSolution u) (s : ℝ) :
    IsL2ClassSolution (fun t => u (t + s)) := by
  obtain ⟨hc, U, hrep, h4, hD⟩ := hu
  exact ⟨hc.comp (continuous_id.add continuous_const), fun p => U (p.1 + s, p.2),
    isSpacetimeRep_shift hrep s, isL4Loc_shift h4 s, isDistributionalNLS_shift hD s⟩

theorem isL2NLSSolution_shift (u : ℝ → PhysicalL2) (hu : IsL2NLSSolution u) (s : ℝ) :
    IsL2NLSSolution (fun t => u (t + s)) := by
  obtain ⟨hc, U, hrep, h4, hD, hH⟩ := hu
  exact ⟨hc.comp (continuous_id.add continuous_const), fun p => U (p.1 + s, p.2),
    isSpacetimeRep_shift hrep s, isL4Loc_shift h4 s, isDistributionalNLS_shift hD s,
    isHm1Duhamel_shift h4 hH s⟩

/-! ### Approved contract 10 -/

/-- The strip map `(t,x) ↦ (t, x mod 1)` is measure preserving. -/
theorem measurePreserving_stripMap :
    MeasurePreserving (fun p : ℝ × ℝ => (p.1, (p.2 : PhysicalCircle))) stripMeasure
      spacetimeMeasure := by
  have h := AddCircle.measurePreserving_mk (T := (1 : ℝ)) 0
  rw [zero_add] at h
  have hv : (volume : Measure PhysicalCircle) = spatialMeasure := by
    rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]
    rfl
  rw [hv] at h
  exact (MeasurePreserving.id (volume : Measure ℝ)).prod h

theorem isDistributionalNLS_congr {U V : ℝ × PhysicalCircle → ℂ}
    (hUV : U =ᵐ[spacetimeMeasure] V) (hD : IsDistributionalNLS U) : IsDistributionalNLS V := by
  intro φ hφ
  obtain ⟨hl, hr, he⟩ := hD φ hφ
  have hae : (fun p : ℝ × ℝ => U (p.1, (p.2 : PhysicalCircle))) =ᵐ[stripMeasure]
      fun p => V (p.1, (p.2 : PhysicalCircle)) :=
    measurePreserving_stripMap.quasiMeasurePreserving.ae_eq_comp hUV
  have hl' : (fun p : ℝ × ℝ => U (p.1, (p.2 : PhysicalCircle)) *
      (iteratedDeriv 2 (fun y => φ (p.1, y)) p.2 -
        Complex.I * deriv (fun s => φ (s, p.2)) p.1)) =ᵐ[stripMeasure]
      (fun p : ℝ × ℝ => V (p.1, (p.2 : PhysicalCircle)) *
      (iteratedDeriv 2 (fun y => φ (p.1, y)) p.2 -
        Complex.I * deriv (fun s => φ (s, p.2)) p.1)) := by
    filter_upwards [hae] with p hp
    rw [hp]
  have hr' : (fun p : ℝ × ℝ => cubicNL (U (p.1, (p.2 : PhysicalCircle))) * φ p) =ᵐ[stripMeasure]
      (fun p : ℝ × ℝ => cubicNL (V (p.1, (p.2 : PhysicalCircle))) * φ p) := by
    filter_upwards [hae] with p hp
    rw [hp]
  exact ⟨hl.congr hl', hr.congr hr', by rw [← integral_congr_ae hl', ← integral_congr_ae hr']; exact he⟩

theorem rep_congr_imp (u : ℝ → PhysicalL2) (U V : ℝ × PhysicalCircle → ℂ)
    (hUV : U =ᵐ[spacetimeMeasure] V)
    (h : IsSpacetimeRep u U ∧ IsL4Loc U ∧ IsDistributionalNLS U ∧ IsHm1Duhamel u U) :
    IsSpacetimeRep u V ∧ IsL4Loc V ∧ IsDistributionalNLS V ∧ IsHm1Duhamel u V := by
  obtain ⟨hrep, h4, hD, hH⟩ := h
  have h4V : IsL4Loc V := fun T => (h4 T).ae_eq (ae_restrict_of_ae hUV)
  have hslice : ∀ᵐ t ∂(volume : Measure ℝ), (fun x => U (t, x)) =ᵐ[spatialMeasure] fun x => V (t, x) :=
    Measure.ae_ae_of_ae_prod hUV
  refine ⟨⟨hrep.aesm.congr hUV, ?_⟩, h4V, isDistributionalNLS_congr hUV hD, fun t => ?_⟩
  · filter_upwards [hrep.slice, hslice] with t h1 h2
    exact h2.symm.trans h1
  · refine ⟨duhamelIntegrand_intervalIntegrable h4V t 0 t, ?_⟩
    rw [(hH t).2]
    congr 1
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hslice] with r hr _
    simp only [duhamelIntegrand]
    rw [fnToHm1_congr_ae (g := fun x => cubicNL (V (r, x)))
      (by filter_upwards [hr] with x hx; rw [hx])]

theorem solution_rep_congr (u : ℝ → PhysicalL2) (U V : ℝ × PhysicalCircle → ℂ)
    (hUV : U =ᵐ[spacetimeMeasure] V) :
    (IsSpacetimeRep u U ∧ IsL4Loc U ∧ IsDistributionalNLS U ∧ IsHm1Duhamel u U) ↔
      (IsSpacetimeRep u V ∧ IsL4Loc V ∧ IsDistributionalNLS V ∧ IsHm1Duhamel u V) := by
  exact ⟨rep_congr_imp u U V hUV, rep_congr_imp u V U hUV.symm⟩

end

end LiebLiniger.FixedPeriod.ALLS.PdeB
