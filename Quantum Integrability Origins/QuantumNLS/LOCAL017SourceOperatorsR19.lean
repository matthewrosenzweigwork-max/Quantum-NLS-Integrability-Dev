import QuantumNLS.LOCAL017SourceFormR19

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Metric Filter Topology MeasureTheory
namespace QuantumNLS.LOCAL017SourceR19
open Ext025A4BanachComplexification Ext025A4BanachSeries
abbrev Cov := LOCAL017Haar.Cov
abbrev CCov := CH →L[ℂ] ℂ
abbrev CForm := CH →L[ℂ] CCov

-- Register the standard operator instances explicitly for these nested spaces.
instance : NormedAddCommGroup CCov := ContinuousLinearMap.toNormedAddCommGroup
instance : NormedSpace ℂ CCov := ContinuousLinearMap.toNormedSpace
instance : NormedSpace ℝ CCov := ContinuousLinearMap.toNormedSpace
instance : NormedAddCommGroup CForm := ContinuousLinearMap.toNormedAddCommGroup
instance : NormedSpace ℂ CForm := ContinuousLinearMap.toNormedSpace
instance : NormedSpace ℝ CForm := ContinuousLinearMap.toNormedSpace

def covLift : Cov →L[ℝ] CCov :=
  LinearMap.mkContinuous
    { toFun := fun A => cxLin (Complex.ofRealCLM.comp A)
      map_add' := fun A B => by ext z; simp [cxLin_apply]; ring
      map_smul' := fun c A => by
        ext z
        simp [cxLin_apply, Complex.real_smul]
        ring }
    2 (fun A => by
      refine (norm_cxLin_le _).trans ?_
      have hh := ContinuousLinearMap.opNorm_comp_le Complex.ofRealCLM A
      have hn : ‖Complex.ofRealCLM‖ ≤ 1 :=
        ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simp)
      have hh' := hh.trans (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hn (norm_nonneg A))
      linarith)

@[simp] theorem covLift_real (A : Cov) (h : H) : covLift A (Cx.ι h) = (A h : ℂ) := by
  simp [covLift, cxLin_apply]

theorem norm_covLift : ‖covLift‖ ≤ 2 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

def formLift : Form →L[ℝ] CForm :=
  LinearMap.mkContinuous
    { toFun := fun A => cxLin (covLift.comp A)
      map_add' := fun A B => by ext z h; simp [cxLin_apply]; ring
      map_smul' := fun c A => by
        ext z h
        simp [cxLin_apply, Complex.real_smul]
        ring }
    4 (fun A => by
      refine (norm_cxLin_le _).trans ?_
      have hh := (ContinuousLinearMap.opNorm_comp_le covLift A).trans
        (mul_le_mul_of_nonneg_right norm_covLift (norm_nonneg A))
      linarith)

@[simp] theorem formLift_real (A : Form) (z h : H) :
    formLift A (Cx.ι z) (Cx.ι h) = (A z h : ℂ) := by
  simp [formLift, cxLin_apply]

theorem norm_formLift : ‖formLift‖ ≤ 4 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

/-- Extend both form arguments and the complexified value complex linearly. -/
def formCx : CF →L[ℂ] CForm := cxLin formLift

@[simp] theorem formCx_real (A : Form) (z h : H) :
    formCx (Cx.ι A) (Cx.ι z) (Cx.ι h) = (A z h : ℂ) := by
  change formLift A (Cx.ι z) (Cx.ι h) + Complex.I * formLift 0 (Cx.ι z) (Cx.ι h) = _
  rw [formLift_real, formLift_real]
  simp

theorem norm_formCx : ‖formCx‖ ≤ 8 :=
  (norm_cxLin_le _).trans (by linarith [norm_formLift])

/-- The original two-form, complexified in all three variables. -/
theorem source_complex_form (S : ResetMoser.Hyp) :
    ∃ R > (0 : ℝ), R ≤ S.R ∧ ∃ C ≥ (0 : ℝ), ∃ G : CH → CForm,
      AnalyticOnNhd ℂ G (ball 0 R) ∧
      (∀ z ∈ ball (0 : CH) R, ‖G z‖ ≤ C * ‖z‖^2) ∧
      (∀ x ∈ ball (0 : H) R, ∀ v w, G (Cx.ι x) (Cx.ι v) (Cx.ι w) =
        (ResetMoser.Dl S x v w : ℂ)) := by
  obtain ⟨R, hR, hRS, C, hC, g, hg, hb, he⟩ := source_form S
  refine ⟨R, hR, hRS, 8*C, by positivity, fun z => formCx (g z), ?_, ?_, ?_⟩
  · intro z hz
    exact (formCx.analyticAt _).comp (hg z hz)
  · intro z hz
    calc
      ‖formCx (g z)‖ ≤ ‖formCx‖ * ‖g z‖ := formCx.le_opNorm _
      _ ≤ 8 * (C * ‖z‖^2) := mul_le_mul norm_formCx (hb z hz) (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  · intro x hx v w
    change formCx (g (Cx.ι x)) (Cx.ι v) (Cx.ι w) = _
    rw [he x hx]
    exact formCx_real _ _ _

end QuantumNLS.LOCAL017SourceR19
