import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! DEF-035, explicit owner repair D2 (2026-11-16). Literal tails and truncations.
Fixed real p > 0; powers at zero are zero. No coupling is implicit. -/
set_option autoImplicit false
noncomputable section
open Filter MeasureTheory Topology
open scoped ENNReal BoundedContinuousFunction
namespace QuantumNLS.Def035TruncationR24m

/-- The extended integral keeps infinite moments visible. -/
def tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (G : Ω → ℝ) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, if ENNReal.ofReal R < ENNReal.ofReal (G x) then ENNReal.ofReal (G x) else 0 ∂μ

/-- Literal uniform integrability on possibly varying probability spaces. -/
def TailUI {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) (G : ∀ n, Ω n → ℝ) : Prop :=
  Tendsto (fun R : ℝ => ⨆ n, tail (μ n) (G n) R) atTop (𝓝 0)

/-- The literal p-power tail condition of DEF-035. Its contract requires p > 0. -/
def UniformPowerTail {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) (X : ∀ n, Ω n → ℝ) (p : ℝ) : Prop :=
  TailUI μ (fun n x => (X n x) ^ p)

/-- Bounded continuous truncation, including at negative inputs. -/
def clip (R : ℝ) (hR : 0 ≤ R) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => min (max x 0) R, (continuous_id.max continuous_const).min continuous_const⟩
    R (fun x y => by
      change |min (max x 0) R - min (max y 0) R| ≤ R
      rw [abs_le]
      have hx : 0 ≤ min (max x 0) R := le_min (le_max_right _ _) hR
      have hy : 0 ≤ min (max y 0) R := le_min (le_max_right _ _) hR
      constructor <;> linarith [min_le_right (max x 0) R, min_le_right (max y 0) R])

@[simp] theorem clip_apply (R : ℝ) (hR : 0 ≤ R) (x : ℝ) :
    clip R hR x = min (max x 0) R := rfl

theorem clip_nonneg (R : ℝ) (hR : 0 ≤ R) (x : ℝ) : 0 ≤ clip R hR x :=
  le_min (le_max_right _ _) hR

theorem clip_of_nonneg (R : ℝ) (hR : 0 ≤ R) {x : ℝ} (hx : 0 ≤ x) :
    clip R hR x = min x R := by simp [clip_apply, max_eq_left hx]

theorem truncation_bounds {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (G : Ω → ℝ) (hG : AEMeasurable G μ) (R : ℝ) (hR : 0 ≤ R) :
    (∫⁻ x, ENNReal.ofReal (clip R hR (G x)) ∂μ) ≤ (∫⁻ x, ENNReal.ofReal (G x) ∂μ) ∧
    (∫⁻ x, ENNReal.ofReal (G x) ∂μ) ≤
      (∫⁻ x, ENNReal.ofReal (clip R hR (G x)) ∂μ) + tail μ G R := by
  constructor
  · apply lintegral_mono
    intro x
    dsimp only
    rw [clip_apply, ENNReal.ofReal_min, ENNReal.ofReal_max, ENNReal.ofReal_zero,
      max_eq_left (show (0 : ℝ≥0∞) ≤ _ from bot_le)]
    exact min_le_left _ _
  · calc
      _ ≤ ∫⁻ x, ENNReal.ofReal (clip R hR (G x)) +
          (if ENNReal.ofReal R < ENNReal.ofReal (G x) then ENNReal.ofReal (G x) else 0) ∂μ := by
        apply lintegral_mono
        intro x
        dsimp only
        split_ifs with hx
        · exact le_add_left le_rfl
        · rw [add_zero, clip_apply, ENNReal.ofReal_min, ENNReal.ofReal_max,
            ENNReal.ofReal_zero, max_eq_left (show (0 : ℝ≥0∞) ≤ _ from bot_le), min_eq_left (le_of_not_gt hx)]
      _ = _ := lintegral_add_left'
        (((clip R hR).continuous.measurable.comp_aemeasurable hG).ennreal_ofReal) _

theorem clipped_integral_tendsto {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    {Ω' : Type*} [MeasurableSpace Ω'] (ν : Measure Ω') [IsProbabilityMeasure ν]
    (G : ∀ n, Ω n → ℝ) (g : Ω' → ℝ)
    (hd : TendstoInDistribution G atTop g μ ν) (R : ℝ) (hR : 0 ≤ R) :
    Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (clip R hR (G n x)) ∂μ n) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal (clip R hR (g x)) ∂ν)) := by
  have hc := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    hd.forall_aemeasurable hd.aemeasurable_limit).1 hd (clip R hR)
  have hi : ∀ n, Integrable (fun x => clip R hR (G n x)) (μ n) := fun n =>
    Integrable.of_bound ((clip R hR).continuous.measurable.comp_aemeasurable
      (hd.forall_aemeasurable n)).aestronglyMeasurable R
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (clip_nonneg R hR _)]; exact min_le_right _ _)
  have hi' : Integrable (fun x => clip R hR (g x)) ν :=
    Integrable.of_bound ((clip R hR).continuous.measurable.comp_aemeasurable
      hd.aemeasurable_limit).aestronglyMeasurable R
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (clip_nonneg R hR _)]; exact min_le_right _ _)
  simpa only [Function.comp_def, ofReal_integral_eq_lintegral_ofReal (hi _) (ae_of_all _ (fun x => clip_nonneg R hR _)),
    ofReal_integral_eq_lintegral_ofReal hi' (ae_of_all _ (fun x => clip_nonneg R hR _))]
    using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hc

/-- Increasing truncations recover the full extended expectation without assuming integrability. -/
theorem clipped_limit {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (g : Ω → ℝ) (hg : AEMeasurable g μ) :
    Tendsto (fun k : ℕ => ∫⁻ x, ENNReal.ofReal (clip (k : ℝ) (by positivity) (g x)) ∂μ)
      atTop (𝓝 (∫⁻ x, ENNReal.ofReal (g x) ∂μ)) := by
  apply lintegral_tendsto_of_tendsto_of_monotone
  · intro k
    exact ((clip (k : ℝ) (by positivity)).continuous.measurable.comp_aemeasurable hg).ennreal_ofReal
  · exact ae_of_all _ fun x i j hij => ENNReal.ofReal_le_ofReal
      (min_le_min_left _ (by exact_mod_cast hij))
  · refine ae_of_all _ fun x => ?_
    have h : ∀ᶠ k : ℕ in atTop, max (g x) 0 ≤ (k : ℝ) :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop _)
    apply tendsto_const_nhds.congr'
    filter_upwards [h] with k hk
    simp [clip_apply, min_eq_left hk, ENNReal.ofReal_max]

#print axioms truncation_bounds
#print axioms clipped_integral_tendsto
#print axioms clipped_limit
end QuantumNLS.Def035TruncationR24m
