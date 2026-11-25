import NlsGge.Ramer.DivergenceIdentificationGlobal
import NlsGge.Ramer.HypothesisBridge
import NlsGge.Analysis.RegularizedDeterminant.All

/-!
# The Ramer density `J_T` (v2, `prop:gaussiancommon`)

`J_T = |det₂(I + D_H K)| exp(-δK - ½‖K‖²_H)` as a function on `ℤ → ℂ`, composed with the
realization `R`.  See `RamerDensity.md`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace NlsGge.Ramer

open NlsGge.Pilot NlsGge.Analysis.RegularizedDeterminant

variable {lower upper : ℝ}

/-- The Hilbert–Schmidt `H`-derivative `D_H K(x) = D_E K(x) ∘ i`. -/
def hsDerivH (c : BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s)
    (K : FullWeightedHilbert c s → ActualCM c) (x : FullWeightedHilbert c s) :
    HilbertSchmidt (ActualCM c) (ActualCM c) :=
  cmFactorHS c s hs (fderiv ℝ K x)

theorem hsDerivH_toCLM (c : BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s)
    (K : FullWeightedHilbert c s → ActualCM c) (x : FullWeightedHilbert c s) :
    (hsDerivH c s hs K x).toCLM =
      (fderiv ℝ K x).comp (cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s))) :=
  cmFactorHS_toCLM c s hs _

theorem hsDerivH_sub_norm_le (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s)
    (K : FullWeightedHilbert c s → ActualCM c) (x y : FullWeightedHilbert c s) :
    ‖hsDerivH c s hs K x - hsDerivH c s hs K y‖ ≤
      ‖fderiv ℝ K x - fderiv ℝ K y‖ * ‖cmInclusionHS c s hs‖ := by
  have h : hsDerivH c s hs K x - hsDerivH c s hs K y =
      cmFactorHS c s hs (fderiv ℝ K x - fderiv ℝ K y) := by
    apply HilbertSchmidt.ext
    intro v
    rw [HilbertSchmidt.toCLM_sub, sub_apply]
    have e : ∀ D : FullWeightedHilbert c s →L[ℝ] ActualCM c,
        (cmFactorHS c s hs D).toCLM v =
          D (cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s)) v) :=
      fun D => congrArg (fun f => f v) (cmFactorHS_toCLM c s hs D)
    unfold hsDerivH
    exact (congrArg₂ (fun a b => a - b) (e (fderiv ℝ K x)) (e (fderiv ℝ K y))).trans
      (e (fderiv ℝ K x - fderiv ℝ K y)).symm
  rw [h]
  exact cmFactorHS_norm_le c s hs _

theorem continuous_hsDerivH (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s)
    (K : FullWeightedHilbert c s → ActualCM c) (hK : ContDiff ℝ 1 K) :
    Continuous (hsDerivH c s hs K) := by
  have hDc : Continuous (fderiv ℝ K) := hK.continuous_fderiv (by norm_num)
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun y => ‖fderiv ℝ K y - fderiv ℝ K x‖) (𝓝 x) (𝓝 0) := by
    have := (hDc.tendsto x).sub_const (fderiv ℝ K x)
    simpa using this.norm
  have h1 := h0.mul_const ‖cmInclusionHS c s hs‖
  rw [zero_mul] at h1
  exact squeeze_zero (fun y => norm_nonneg _) (fun y => hsDerivH_sub_norm_le c s hs K y x) h1

theorem continuous_det2_hsDerivH (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s)
    (K : FullWeightedHilbert c s → ActualCM c) (hK : ContDiff ℝ 1 K) :
    Continuous (fun x => det2 (hsDerivH c s hs K x)) :=
  continuous_det2.comp (continuous_hsDerivH c s hs K hK)

/-- The Ramer density `J_T` as a function of the sequence `z`. -/
def ramerJ (c : BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s)
    (K : FullWeightedHilbert c s → ActualCM c) (δK : (ℤ → ℂ) → ℝ) (z : ℤ → ℂ) : ℝ :=
  |det2 (hsDerivH c s hs K (NlsGge.Measure.fullWeightedSequenceRealization c s z))| *
    Real.exp (-δK z - ‖K (NlsGge.Measure.fullWeightedSequenceRealization c s z)‖ ^ 2 / 2)

theorem aestronglyMeasurable_ramerJ (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s)
    (K : FullWeightedHilbert c s → ActualCM c) (hK : ContDiff ℝ 1 K)
    (δK : (ℤ → ℂ) → ℝ)
    (hδ : AEStronglyMeasurable δK
      (NlsGge.Measure.fullWeightSequenceGaussian c.val)) :
    AEStronglyMeasurable (ramerJ c s hs K δK)
      (NlsGge.Measure.fullWeightSequenceGaussian c.val) := by
  have hRm : Measurable (NlsGge.Measure.fullWeightedSequenceRealization c s) :=
    NlsGge.Measure.measurable_fullWeightedSequenceRealization c s
  have h1 : Measurable (fun z => |det2 (hsDerivH c s hs K
      (NlsGge.Measure.fullWeightedSequenceRealization c s z))|) :=
    ((continuous_det2_hsDerivH c s hs K hK).abs.measurable).comp hRm
  have h2 : Measurable (fun z => ‖K (NlsGge.Measure.fullWeightedSequenceRealization c s z)‖ ^ 2 / 2) :=
    ((hK.continuous.norm.pow 2).div_const 2).measurable.comp hRm
  refine h1.aestronglyMeasurable.mul ?_
  exact (Real.continuous_exp.comp_aestronglyMeasurable
    ((hδ.neg).sub h2.aestronglyMeasurable))

/-- Positivity in the bridge setting. -/
theorem ramerJ_pos (c : BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s)
    (T : FullWeightedHilbert c s ≃ₜ FullWeightedHilbert c s)
    (K K' : FullWeightedHilbert c s → ActualCM c)
    (hT : ∀ x, T x = x + cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s)) (K x))
    (hTs : ∀ y, T.symm y = y + cmToFullWeightedHilbert c s
      (le_of_lt (by linarith : 0 < s)) (K' y))
    (hK : ContDiff ℝ 1 K) (hK' : ContDiff ℝ 1 K')
    (δK : (ℤ → ℂ) → ℝ) (z : ℤ → ℂ) :
    0 < ramerJ c s hs K δK z := by
  unfold ramerJ
  refine mul_pos (abs_pos.2 ?_) (Real.exp_pos _)
  obtain ⟨L, hL, hLs⟩ := exists_inverse_id_add_HDeriv
    (cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s)))
    (cmToFullWeightedHilbert_injective c s _) T K K' hT hTs
    (hK.differentiable (by norm_num)) (hK'.differentiable (by norm_num))
    (NlsGge.Measure.fullWeightedSequenceRealization c s z)
  apply det2_ne_zero_of_isUnit
  set x := NlsGge.Measure.fullWeightedSequenceRealization c s z with hx
  have hA : ∀ h, (hsDerivH c s hs K x).toCLM h =
      fderiv ℝ K x (cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s)) h) :=
    fun h => congrArg (fun f => f h) (hsDerivH_toCLM c s hs K x)
  have hA' : ∀ h, (hsDerivH c s hs K' (T x)).toCLM h =
      fderiv ℝ K' (T x) (cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s)) h) :=
    fun h => congrArg (fun f => f h) (hsDerivH_toCLM c s hs K' (T x))
  have hLp : ∀ h, L h = h + (hsDerivH c s hs K x).toCLM h := by
    intro h
    exact (congrArg (fun F => F h) hL).trans (congrArg (fun w => h + w) (hA h).symm)
  have hLsp : ∀ h, L.symm h = h + (hsDerivH c s hs K' (T x)).toCLM h := by
    intro h
    exact (congrArg (fun F => F h) hLs).trans (congrArg (fun w => h + w) (hA' h).symm)
  refine ⟨⟨1 + (hsDerivH c s hs K x).toCLM, 1 + (hsDerivH c s hs K' (T x)).toCLM,
    ?_, ?_⟩, rfl⟩
  · ext h
    have := L.apply_symm_apply h
    rw [hLsp, hLp] at this
    simpa [add_comm] using this
  · ext h
    have := L.symm_apply_apply h
    rw [hLp, hLsp] at this
    simpa [add_comm] using this

end NlsGge.Ramer
