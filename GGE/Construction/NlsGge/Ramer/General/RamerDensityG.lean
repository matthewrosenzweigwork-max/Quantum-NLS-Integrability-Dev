import NlsGge.Ramer.General.HypothesisBridgeG
import NlsGge.Analysis.RegularizedDeterminant.All

/-!
# The Ramer density `J_T` over a `RamerSetting`

`J_T = |det₂(I + D_H K)| exp(-δK - ½‖K‖²_H)` as a function on `ℤ → ℂ`, composed with the
realization `S.R`. Adapted from `NlsGge/Ramer/RamerDensity.lean`, with `S.incl_hs` supplying the
Hilbert–Schmidt structure of the inclusion `S.H → S.E`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Analysis.RegularizedDeterminant

variable (S : NlsGge.Ramer.General.RamerSetting)

/-- The inclusion `S.incl : S.H → S.E` packaged as a Hilbert–Schmidt operator
(old: `cmInclusionHS`). -/
def inclHS : HilbertSchmidt S.H S.E :=
  HilbertSchmidt.ofCLM S.incl
    (isHilbertSchmidt_of_summable (basis S.H) (S.incl_hs _))

@[simp] theorem inclHS_toCLM : S.inclHS.toCLM = S.incl := rfl

/-- The rectangular factorization `D ↦ D ∘ incl` as a Hilbert–Schmidt operator
(old: `cmFactorHS`). -/
def factorHS {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (D : S.E →L[ℝ] G) : HilbertSchmidt S.H G :=
  HilbertSchmidt.postcompose D S.inclHS

@[simp] theorem factorHS_toCLM {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℝ G] [CompleteSpace G] (D : S.E →L[ℝ] G) :
    (S.factorHS D).toCLM = D.comp S.incl := rfl

theorem factorHS_norm_le {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℝ G] [CompleteSpace G] (D : S.E →L[ℝ] G) :
    ‖S.factorHS D‖ ≤ D.opNorm * ‖S.inclHS‖ :=
  HilbertSchmidt.norm_postcompose_le D S.inclHS

/-- The Hilbert–Schmidt `H`-derivative `D_H K(x) = D_E K(x) ∘ i`. (Old: `hsDerivH`.) -/
def hsDerivH (K : S.E → S.H) (x : S.E) : HilbertSchmidt S.H S.H :=
  S.factorHS (fderiv ℝ K x)

theorem hsDerivH_toCLM (K : S.E → S.H) (x : S.E) :
    (S.hsDerivH K x).toCLM = (fderiv ℝ K x).comp S.incl :=
  S.factorHS_toCLM _

theorem hsDerivH_sub_norm_le (K : S.E → S.H) (x y : S.E) :
    ‖S.hsDerivH K x - S.hsDerivH K y‖ ≤ ‖fderiv ℝ K x - fderiv ℝ K y‖ * ‖S.inclHS‖ := by
  have h : S.hsDerivH K x - S.hsDerivH K y = S.factorHS (fderiv ℝ K x - fderiv ℝ K y) := by
    apply HilbertSchmidt.ext
    intro v
    rw [HilbertSchmidt.toCLM_sub, sub_apply]
    have e : ∀ D : S.E →L[ℝ] S.H, (S.factorHS D).toCLM v = D (S.incl v) :=
      fun D => congrArg (fun f => f v) (S.factorHS_toCLM D)
    unfold hsDerivH
    exact (congrArg₂ (fun a b => a - b) (e (fderiv ℝ K x)) (e (fderiv ℝ K y))).trans
      (e (fderiv ℝ K x - fderiv ℝ K y)).symm
  rw [h]
  exact S.factorHS_norm_le _

theorem continuous_hsDerivH (K : S.E → S.H) (hK : ContDiff ℝ 1 K) :
    Continuous (S.hsDerivH K) := by
  have hDc : Continuous (fderiv ℝ K) := hK.continuous_fderiv (by norm_num)
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun y => ‖fderiv ℝ K y - fderiv ℝ K x‖) (𝓝 x) (𝓝 0) := by
    have := (hDc.tendsto x).sub_const (fderiv ℝ K x)
    simpa using this.norm
  have h1 := h0.mul_const ‖S.inclHS‖
  rw [zero_mul] at h1
  exact squeeze_zero (fun y => norm_nonneg _) (fun y => S.hsDerivH_sub_norm_le K y x) h1

theorem continuous_det2_hsDerivH (K : S.E → S.H) (hK : ContDiff ℝ 1 K) :
    Continuous (fun x => det2 (S.hsDerivH K x)) :=
  continuous_det2.comp (S.continuous_hsDerivH K hK)

/-- The Ramer density `J_T` as a function of the sequence `z`. (Old: `ramerJ`.) -/
def ramerJ (K : S.E → S.H) (δK : (ℤ → ℂ) → ℝ) (z : ℤ → ℂ) : ℝ :=
  |det2 (S.hsDerivH K (S.R z))| * Real.exp (-δK z - ‖K (S.R z)‖ ^ 2 / 2)

theorem aestronglyMeasurable_ramerJ (K : S.E → S.H) (hK : ContDiff ℝ 1 K)
    (δK : (ℤ → ℂ) → ℝ) (hδ : AEStronglyMeasurable δK S.γ) :
    AEStronglyMeasurable (S.ramerJ K δK) S.γ := by
  have hRm : Measurable S.R := S.measurable_R
  have h1 : Measurable (fun z => |det2 (S.hsDerivH K (S.R z))|) :=
    ((S.continuous_det2_hsDerivH K hK).abs.measurable).comp hRm
  have h2 : Measurable (fun z => ‖K (S.R z)‖ ^ 2 / 2) :=
    ((hK.continuous.norm.pow 2).div_const 2).measurable.comp hRm
  refine h1.aestronglyMeasurable.mul ?_
  exact (Real.continuous_exp.comp_aestronglyMeasurable
    ((hδ.neg).sub h2.aestronglyMeasurable))

/-- Positivity in the bridge setting. (Old: `ramerJ_pos`.) -/
theorem ramerJ_pos (T : S.E ≃ₜ S.E) (K K' : S.E → S.H)
    (hT : ∀ x, T x = x + S.incl (K x))
    (hTs : ∀ y, T.symm y = y + S.incl (K' y))
    (hK : ContDiff ℝ 1 K) (hK' : ContDiff ℝ 1 K')
    (δK : (ℤ → ℂ) → ℝ) (z : ℤ → ℂ) :
    0 < S.ramerJ K δK z := by
  unfold ramerJ
  refine mul_pos (abs_pos.2 ?_) (Real.exp_pos _)
  obtain ⟨L, hL, hLs⟩ := NlsGge.Ramer.exists_inverse_id_add_HDeriv S.incl
    S.incl_injective T K K' hT hTs
    (hK.differentiable (by norm_num)) (hK'.differentiable (by norm_num))
    (S.R z)
  apply det2_ne_zero_of_isUnit
  set x := S.R z with hx
  have hA : ∀ h, (S.hsDerivH K x).toCLM h = fderiv ℝ K x (S.incl h) :=
    fun h => congrArg (fun f => f h) (S.hsDerivH_toCLM K x)
  have hA' : ∀ h, (S.hsDerivH K' (T x)).toCLM h = fderiv ℝ K' (T x) (S.incl h) :=
    fun h => congrArg (fun f => f h) (S.hsDerivH_toCLM K' (T x))
  have hLp : ∀ h, L h = h + (S.hsDerivH K x).toCLM h := by
    intro h
    exact (congrArg (fun F => F h) hL).trans (congrArg (fun w => h + w) (hA h).symm)
  have hLsp : ∀ h, L.symm h = h + (S.hsDerivH K' (T x)).toCLM h := by
    intro h
    exact (congrArg (fun F => F h) hLs).trans (congrArg (fun w => h + w) (hA' h).symm)
  refine ⟨⟨1 + (S.hsDerivH K x).toCLM, 1 + (S.hsDerivH K' (T x)).toCLM,
    ?_, ?_⟩, rfl⟩
  · ext h
    have := L.apply_symm_apply h
    rw [hLsp, hLp] at this
    simpa [add_comm] using this
  · ext h
    have := L.symm_apply_apply h
    rw [hLp, hLsp] at this
    simpa [add_comm] using this

end NlsGge.Ramer.General.RamerSetting
