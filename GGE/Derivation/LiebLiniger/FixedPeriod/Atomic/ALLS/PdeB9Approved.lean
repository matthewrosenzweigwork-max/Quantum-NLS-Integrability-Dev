import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB9Series

/-! # Track B: approved contract 24 (`isL2NLSSolution_of_isNLSSolM`)

Statement copied verbatim from the owner-approved `TRACK_B_EXACT_STATEMENTS_FOR_APPROVAL.txt`
(sha256 943a37c24a40c74b1e025c9f243c49372b9e071c313bebf28cda3ace2f3ca056).

Proof (the `H¹` bridge). Let `a t = physicalFourier (u t)` be a coefficient solution
`IsNLSSolM m a`, `m ≥ 1`; it is an `h¹` solution (`isNLSSol_of_isNLSSolM38`).
* `ℓ¹ ≤ C₁ h¹` (`isL1_of_hn_one`) makes `a t` absolutely summable and `t ↦ a t` continuous in
  `ℓ¹`, hence `t ↦ serC (a t)` continuous in `C(𝕋, ℂ)` (`norm_serC_sub_le`);
* `serC (a t)` represents `u t` (`physicalH1Continuous_toLp`), so `u` is continuous in `L²`;
* the representative `serRep u (t, x) = serC (a t) x` is jointly continuous, hence an
  `IsSpacetimeRep` and `IsL4Loc` (bounded on the compact slabs);
* `physicalFourier (cubicNL ∘ serC (a r)) = nonlin (a r)` (`physicalFourier_cubicNL_serC`), so the
  coefficient ODE gives `HasDerivAt (intA u n) (intG U n r) r`; the fundamental theorem of
  calculus (with `intervalIntegrable_intG`) gives the coefficient Duhamel form, i.e.
  `IsHm1Duhamel` (`isHm1Duhamel_iff_intA`);
* approved contract 6 (`l2_class_duhamel`, ⇐) gives `IsDistributionalNLS`.
-/

namespace LiebLiniger.FixedPeriod.ALLS.PdeB
open MeasureTheory NlsGge.Pilot NlsGge.NLS38 NlsGge.Birkhoff NlsGge.Sobolev38
open scoped ContDiff
set_option autoImplicit false
noncomputable section

attribute [local instance] isProbabilityMeasure_spatialMeasure

/-- The spacetime representative `(t, x) ↦ ∑ₙ û_n(t) e_n(x)`. -/
def serRep (u : ℝ → PhysicalL2) (p : ℝ × PhysicalCircle) : ℂ :=
  serC (physicalFourier (u p.1)) p.2

theorem isL1_of_sol {u : ℝ → PhysicalL2} (h1 : IsNLSSol (fun t => physicalFourier (u t))) (t : ℝ) :
    IsL1 (physicalFourier (u t)) :=
  (isL1_of_hn_one _ (h1.mem t)).1

theorem toLp_serC_of_sol {u : ℝ → PhysicalL2} (h1 : IsNLSSol (fun t => physicalFourier (u t)))
    (t : ℝ) : ContinuousMap.toLp (E := ℂ) 2 spatialMeasure ℂ (serC (physicalFourier (u t))) = u t :=
  NlsGge.Analysis.physicalH1Continuous_toLp (u t) ((physicalFourier_mem_one_iff38 _).1 (h1.mem t))

/-- `ℓ¹` distance of two solution times is controlled by their `h¹` carrier distance. -/
theorem l1_sub_le_of_sol {u : ℝ → PhysicalL2} (h1 : IsNLSSol (fun t => physicalFourier (u t)))
    (t s : ℝ) :
    ∑' n : ℤ, ‖physicalFourier (u t) n - physicalFourier (u s) n‖ ≤
      C1 * ‖carrierMk38 ((1 : ℕ) : ℝ) (physicalFourier (u t)) (h1.mem t) -
        carrierMk38 ((1 : ℕ) : ℝ) (physicalFourier (u s)) (h1.mem s)‖ := by
  set D := carrierMk38 ((1 : ℕ) : ℝ) (physicalFourier (u t)) (h1.mem t) -
    carrierMk38 ((1 : ℕ) : ℝ) (physicalFourier (u s)) (h1.mem s) with hD_def
  have hD : carrierCoe38 ((1 : ℕ) : ℝ) D =
      fun n => physicalFourier (u t) n - physicalFourier (u s) n := by
    rw [hD_def, carrierCoe38_sub']
    rfl
  have h := (isL1_of_hn_one _ (carrierCoe38_mem _ D)).2
  rw [hn_coe38, hD] at h
  exact h

theorem continuous_serC_of_sol {u : ℝ → PhysicalL2}
    (h1 : IsNLSSol (fun t => physicalFourier (u t))) :
    Continuous fun t => serC (physicalFourier (u t)) := by
  set G : ℝ → SobolevCarrier38 ((1 : ℕ) : ℝ) :=
    fun t => carrierMk38 ((1 : ℕ) : ℝ) (physicalFourier (u t)) (h1.mem t) with hG
  have hGc : Continuous G := h1.cont
  rw [continuous_iff_continuousAt]
  intro t
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Filter.Tendsto (fun s => C1 * ‖G s - G t‖) (nhds t) (nhds (C1 * 0)) := by
    have := ((hGc.tendsto t).sub_const (G t)).norm
    rw [sub_self, norm_zero] at this
    exact this.const_mul C1
  rw [mul_zero] at hlim
  refine squeeze_zero (fun s => norm_nonneg _) (fun s => ?_) hlim
  exact (norm_serC_sub_le (isL1_of_sol h1 s) (isL1_of_sol h1 t)).trans (l1_sub_le_of_sol h1 s t)

theorem continuous_serRep {u : ℝ → PhysicalL2} (h1 : IsNLSSol (fun t => physicalFourier (u t))) :
    Continuous (serRep u) := by
  have hF := continuous_serC_of_sol h1
  have h := (ContinuousEval.continuous_eval (F := C(PhysicalCircle, ℂ))).comp
    (hF.prodMap continuous_id)
  exact h

theorem continuous_of_sol {u : ℝ → PhysicalL2} (h1 : IsNLSSol (fun t => physicalFourier (u t))) :
    Continuous u :=
  ((ContinuousMap.toLp (E := ℂ) 2 spatialMeasure ℂ).continuous.comp
    (continuous_serC_of_sol h1)).congr fun t => toLp_serC_of_sol h1 t

theorem isSpacetimeRep_serRep {u : ℝ → PhysicalL2}
    (h1 : IsNLSSol (fun t => physicalFourier (u t))) : IsSpacetimeRep u (serRep u) where
  aesm := (continuous_serRep h1).aestronglyMeasurable
  slice := Filter.Eventually.of_forall fun t => by
    have h := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) spatialMeasure
      (serC (physicalFourier (u t)))
    rw [toLp_serC_of_sol h1 t] at h
    exact h.symm

theorem isL4Loc_of_continuous {U : ℝ × PhysicalCircle → ℂ} (hU : Continuous U) : IsL4Loc U := by
  intro T
  have hK : IsCompact (Set.Icc (-T) T ×ˢ (Set.univ : Set PhysicalCircle)) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hU.continuousOn
  have : IsFiniteMeasure
      (spacetimeMeasure.restrict (Set.Icc (-T) T ×ˢ (Set.univ : Set PhysicalCircle))) := by
    unfold spacetimeMeasure
    rw [slab_eq]
    exact isFiniteMeasure_slab (-T) T
  refine MemLp.of_bound hU.aestronglyMeasurable C ?_
  exact ae_restrict_of_forall_mem (measurableSet_Icc.prod MeasurableSet.univ) hC

theorem isHm1Duhamel_serRep {u : ℝ → PhysicalL2}
    (h1 : IsNLSSol (fun t => physicalFourier (u t))) : IsHm1Duhamel u (serRep u) := by
  have h4 := isL4Loc_of_continuous (continuous_serRep h1)
  rw [isHm1Duhamel_iff_intA h4]
  intro n t
  have hderiv : ∀ r : ℝ, HasDerivAt (intA u n) (intG (serRep u) n r) r := by
    intro r
    have h := (hasDerivAt_freePhase_neg n r).mul (h1.deriv r n)
    have hN : physicalFourier (fun x => cubicNL (serRep u (r, x))) n =
        nonlin (physicalFourier (u r)) n :=
      physicalFourier_cubicNL_serC (isL1_of_sol h1 r) n
    unfold intG
    rw [hN]
    convert h using 1
    · rfl
    · ring
  have hint : IntervalIntegrable (intG (serRep u) n) volume 0 t :=
    intervalIntegrable_intG (memLp_slabM_of_isL4Loc h4 (min 0 t) (max 0 t)) n
      ⟨min_le_left 0 t, le_max_left 0 t⟩ ⟨min_le_right 0 t, le_max_right 0 t⟩
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hderiv r) hint
  rw [hFTC]
  ring

/-! ### Approved contract 24 -/

theorem isL2NLSSolution_of_isNLSSolM (m : ℕ) (hm : 1 ≤ m) (u : ℝ → PhysicalL2)
    (hsol : IsNLSSolM m (fun t => physicalFourier (u t))) : IsL2NLSSolution u := by
  have h1 : IsNLSSol (fun t => physicalFourier (u t)) := isNLSSol_of_isNLSSolM38 m hm hsol
  have hc := continuous_of_sol h1
  have hrep := isSpacetimeRep_serRep h1
  have h4 := isL4Loc_of_continuous (continuous_serRep h1)
  have hD := isHm1Duhamel_serRep h1
  unfold IsL2NLSSolution
  exact ⟨hc, serRep u, hrep, h4, (l2_class_duhamel u (serRep u) hc hrep h4).2 hD, hD⟩

end

end LiebLiniger.FixedPeriod.ALLS.PdeB
