import Mathlib
import NlsGge.Birkhoff.F09Limit38d
import NlsGge.Birkhoff.F09Limit38g
import NlsGge.Birkhoff.F09Limit38e
import NlsGge.Birkhoff.W05FiniteGap38
import NlsGge.Birkhoff.W11Equivalence38c
import NlsGge.Birkhoff.W06Jacobian38
import NlsGge.ThirdConsultation.T.ECarrier98

                                                                                                                      
                                                                                                                                                        
                                                                                                                    
                                                                                                                 
                                                                                        
set_option autoImplicit false

open MeasureTheory Filter Topology NlsGge.Pilot NlsGge.Measure NlsGge.Birkhoff
open scoped ENNReal BoundedContinuousFunction

noncomputable section

namespace NlsGge.Atomic.T.T008Core

/-- The E-space limit law with the canonical density, at a fixed normalizer `Z`. -/
def lawE (B : BirkhoffInput38) (O : OneSmoothingInput38 B) {lo up : ℝ} (c : BoundedCoefficients lo up)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) (δ : (ℤ → ℂ) → ℝ) (Z : ℝ) :
    Measure (ECarrier38 c s) :=
  ENNReal.ofReal Z⁻¹ •
    (fullWeightedSequenceGaussian c s).withDensity
      (fun x => ENNReal.ofReal
        (fW06_38 c s hs (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δ x))

theorem map_eq (B : BirkhoffInput38) (O : OneSmoothingInput38 B) {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ) (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4)
    (δ : (ℤ → ℂ) → ℝ)
    (hδ : RamerDivergence38 c s (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δ)
    (Z : ℝ) (hZ : Z = B.ZW38 c.val) :
    (lawE B O c s hs hs' δ Z).map (physOfE38 c s) = B.muW38 c.val := by
  set f := fW06_38 c s hs (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δ with hf
  have W := B.weight_W11 O c hs hs' δ hδ
  have hZpos : 0 < Z := hZ ▸ B.ZW_pos_W11 c
  have hmeas : Measurable (physOfE38 c s) := (measurableEmbedding_physOfE38 c s).measurable
  haveI : IsProbabilityMeasure (B.muW38 c.val) :=
    B.isProbabilityMeasure_muW38 lo up c.val c.property.1 (coef_bound38 c) (coef_upper38 c)
  ext A hA
  have hS : MeasurableSet (physOfE38 c s ⁻¹' A) := hmeas hA
  rw [Measure.map_apply hmeas hA]
  set S : Set (FullWeightedHilbert c s) := physOfE38 c s ⁻¹' A with hSdef
  have hS' : MeasurableSet S := hS
  show (ENNReal.ofReal Z⁻¹ • (fullWeightedSequenceGaussian c s).withDensity
      (fun x : FullWeightedHilbert c s => ENNReal.ofReal (f x))) S = _
  rw [Measure.smul_apply, withDensity_apply _ hS', smul_eq_mul]
  -- the W11 identity at the indicator of A
  have hmu := W.muW (A.indicator 1)
  rw [integral_indicator_one hA] at hmu
  have hind : (fun x : FullWeightedHilbert c s => f x * A.indicator (1 : PhysicalL2 → ℝ) (physOfE38 c s x)) =
      S.indicator f := by
    funext x
    by_cases hx : physOfE38 c s x ∈ A
    · have hxS : x ∈ S := hx
      rw [Set.indicator_of_mem hxS, Set.indicator_of_mem hx, Pi.one_apply, mul_one]
    · have hxS : x ∉ S := hx
      rw [Set.indicator_of_notMem hxS, Set.indicator_of_notMem hx, mul_zero]
  rw [hind, integral_indicator hS', ← hZ] at hmu
  have hnn : 0 ≤ᵐ[(fullWeightedSequenceGaussian c s).restrict S] f :=
    ae_restrict_of_ae W.nonneg
  rw [← ofReal_integral_eq_lintegral_ofReal W.integrable.integrableOn hnn,
    ← ENNReal.ofReal_mul (inv_nonneg.2 hZpos.le), ← one_div, ← hmu, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

theorem limit (B : BirkhoffInput38) (O : OneSmoothingInput38 B) {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ) (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4)
    (δ : (ℤ → ℂ) → ℝ)
    (hδ : RamerDivergence38 c s (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δ)
    (Z : ℝ) (hZ : Z = B.ZW38 c.val) (F : ECarrier38 c s →ᵇ ℝ) :
    Integrable F (lawE B O c s hs hs' δ Z) ∧
    Tendsto (fun N : ℕ => ∫ x, F (projE38 c s N x) * fN38 c s N x
        ∂(fullWeightedSequenceGaussian c s)) atTop
      (𝓝 (Z * ∫ x, F x ∂(lawE B O c s hs hs' δ Z))) := by
  have hmap := map_eq B O c s hs hs' δ hδ Z hZ
  have hemb := measurableEmbedding_physOfE38 c s
  haveI : IsProbabilityMeasure (B.muW38 c.val) :=
    B.isProbabilityMeasure_muW38 lo up c.val c.property.1 (coef_bound38 c) (coef_upper38 c)
  have huniv : lawE B O c s hs hs' δ Z Set.univ = 1 := by
    rw [← Set.preimage_univ (f := physOfE38 c s), ← Measure.map_apply hemb.measurable MeasurableSet.univ,
      hmap, measure_univ]
  haveI : IsFiniteMeasure (lawE B O c s hs hs' δ Z) := ⟨by rw [huniv]; exact ENNReal.one_lt_top⟩
  refine ⟨BoundedContinuousFunction.integrable _ F, ?_⟩
  classical
  set G : PhysicalL2 → ℝ := Function.extend (physOfE38 c s) F (fun _ => 0) with hGdef
  have hG : ∀ y, G (physOfE38 c s y) = F y := fun y =>
    (physOfE38_injective c s).extend_apply F _ y
  have hGc : Continuous (fun y : ECarrier38 c s => G (physOfE38 c s y)) := by
    simp only [hG]; exact F.continuous
  have hGb : ∃ M, ∀ y : ECarrier38 c s, |G (physOfE38 c s y)| ≤ M :=
    ⟨‖F‖, fun y => by rw [hG, ← Real.norm_eq_abs]; exact F.norm_coe_le_norm y⟩
  have hlim := B.fullunnorm_Es38 O c hs hs' G hGc hGb
  have hint : ∫ u, G u ∂(B.muW38 c.val) = ∫ x, F x ∂(lawE B O c s hs hs' δ Z) := by
    rw [← hmap, hemb.integral_map]
    simp only [hG]
  simp only [hG] at hlim
  rw [hint, ← hZ] at hlim
  exact hlim

end NlsGge.Atomic.T.T008Core

