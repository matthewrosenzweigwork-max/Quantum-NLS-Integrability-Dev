import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB5Unique

/-! # Track B, package 2: time translation of the representative

For `U_s(t,x) = U(t+s,x)`: `IsL4Loc U → IsL4Loc U_s`, `IsSpacetimeRep u U → IsSpacetimeRep u(·+s) U_s`
(translation `(t,x) ↦ (t+s,x)` preserves `dt ⊗ dx`), and `IsHm1Duhamel u U → IsHm1Duhamel u(·+s) U_s`
(`duhamel_shift`). These are the Duhamel/representative parts of the approved shift contracts 8–9
(the distributional part is not treated here).
-/

namespace LiebLiniger.FixedPeriod.ALLS.PdeB
open MeasureTheory NlsGge.Pilot NlsGge.NLS38 NlsGge.Birkhoff NlsGge.Sobolev38
open scoped ContDiff
set_option autoImplicit false
noncomputable section

attribute [local instance] isProbabilityMeasure_spatialMeasure

/-- The time shift `(t,x) ↦ (t+s,x)`. -/
def tshift (s : ℝ) (p : ℝ × PhysicalCircle) : ℝ × PhysicalCircle := (p.1 + s, p.2)

theorem measurePreserving_tshift (s : ℝ) :
    MeasurePreserving (tshift s) spacetimeMeasure spacetimeMeasure :=
  (measurePreserving_add_right (volume : Measure ℝ) s).prod (MeasurePreserving.id spatialMeasure)

theorem tshift_preimage (s T : ℝ) :
    tshift s ⁻¹' (Set.Icc (-T + s) (T + s) ×ˢ (Set.univ : Set PhysicalCircle)) =
      Set.Icc (-T) T ×ˢ Set.univ := by
  ext p
  simp only [tshift, Set.mem_preimage, Set.mem_prod, Set.mem_Icc, Set.mem_univ, and_true]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

theorem isL4Loc_shift {U : ℝ × PhysicalCircle → ℂ} (h4 : IsL4Loc U) (s : ℝ) :
    IsL4Loc (fun p => U (p.1 + s, p.2)) := by
  intro T
  have hB : MeasurableSet (Set.Icc (-T + s) (T + s) ×ˢ (Set.univ : Set PhysicalCircle)) :=
    measurableSet_Icc.prod MeasurableSet.univ
  have hmp := (measurePreserving_tshift s).restrict_preimage hB
  rw [tshift_preimage] at hmp
  have hsub : Set.Icc (-T + s) (T + s) ⊆ Set.Icc (-(|T| + |s|)) (|T| + |s|) := by
    intro r hr
    constructor
    · linarith [hr.1, neg_abs_le T, neg_abs_le s, le_abs_self T]
    · linarith [hr.2, le_abs_self T, le_abs_self s]
  have hU : MemLp U 4 (spacetimeMeasure.restrict
      (Set.Icc (-T + s) (T + s) ×ˢ (Set.univ : Set PhysicalCircle))) :=
    (h4 (|T| + |s|)).mono_measure (Measure.restrict_mono (Set.prod_mono hsub le_rfl) le_rfl)
  exact hU.comp_measurePreserving hmp

theorem isSpacetimeRep_shift {u : ℝ → PhysicalL2} {U : ℝ × PhysicalCircle → ℂ}
    (hU : IsSpacetimeRep u U) (s : ℝ) :
    IsSpacetimeRep (fun t => u (t + s)) (fun p => U (p.1 + s, p.2)) where
  aesm := hU.aesm.comp_measurePreserving (measurePreserving_tshift s)
  slice := (measurePreserving_add_right (volume : Measure ℝ) s).quasiMeasurePreserving.ae hU.slice

theorem isHm1Duhamel_shift {u : ℝ → PhysicalL2} {U : ℝ × PhysicalCircle → ℂ} (h4 : IsL4Loc U)
    (hD : IsHm1Duhamel u U) (s : ℝ) :
    IsHm1Duhamel (fun t => u (t + s)) (fun p => U (p.1 + s, p.2)) := by
  intro t
  refine ⟨duhamelIntegrand_intervalIntegrable (isL4Loc_shift h4 s) t 0 t, ?_⟩
  simp only [zero_add]
  exact duhamel_shift u U h4 hD s t

end

end LiebLiniger.FixedPeriod.ALLS.PdeB
