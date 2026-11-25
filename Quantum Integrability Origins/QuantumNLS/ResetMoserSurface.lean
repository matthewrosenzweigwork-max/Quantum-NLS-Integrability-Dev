import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# `thm:reset-moser` (LOCAL-017), stage 3d-1 (item 2(c), analytic core): the surface lemma

Source: `symplectic_correction.tex`, "The periods of a radial primitive": "The restriction of `α` to the torus is closed by isotropy. Its integral depends only
on the winding vector: this can be proved by lifting to `ℝ^{|F|}` and integrating the closed form along rectangle boundaries." The cone (Poincaré)
primitive of a closed form is differentiated along an arbitrary `C¹` curve of base angles by the standard two-parameter-surface computation. This module
is the abstract analytic core and involves no Hilbert-space structure beyond a real normed space `E`.

`surface_deriv`: let `β : E → (E →L ℝ)` be Fréchet differentiable on an open `U` with continuous derivative `β'`, let `σ(r,s) ∈ U` be a surface with
`∂_sσ = v`, `∂_rσ = u`, `∂_s u = w = ∂_r v` (all jointly continuous) on which `β'` is symmetric in the pair `(v,u)` (i.e. `dβ(v,u) = 0`). Then
`d/ds ∫_0^1 β_{σ(r,s)}(u(r,s)) dr = β_{σ(1,s)}(v(1,s)) − β_{σ(0,s)}(v(0,s))`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped Interval

namespace QuantumNLS.ResetMoserSurface

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem surface_deriv {U : Set E} (hU : IsOpen U)
    {β : E → (E →L[ℝ] ℝ)} {β' : E → (E →L[ℝ] (E →L[ℝ] ℝ))}
    (hβ : ∀ x ∈ U, HasFDerivAt β (β' x) x) (hβ' : ContinuousOn β' U)
    {σ u v w : ℝ → ℝ → E}
    (hσU : ∀ r s, σ r s ∈ U)
    (h1 : ∀ r s, HasDerivAt (fun s' => σ r s') (v r s) s)
    (h2 : ∀ r s, HasDerivAt (fun r' => σ r' s) (u r s) r)
    (h3 : ∀ r s, HasDerivAt (fun s' => u r s') (w r s) s)
    (h4 : ∀ r s, HasDerivAt (fun r' => v r' s) (w r s) r)
    (hσc : Continuous (fun p : ℝ × ℝ => σ p.1 p.2)) (huc : Continuous (fun p : ℝ × ℝ => u p.1 p.2))
    (hvc : Continuous (fun p : ℝ × ℝ => v p.1 p.2)) (hwc : Continuous (fun p : ℝ × ℝ => w p.1 p.2))
    (hclosed : ∀ r s, β' (σ r s) (v r s) (u r s) = β' (σ r s) (u r s) (v r s)) (s₀ : ℝ) :
    HasDerivAt (fun s => ∫ r in (0 : ℝ)..1, β (σ r s) (u r s))
      (β (σ 1 s₀) (v 1 s₀) - β (σ 0 s₀) (v 0 s₀)) s₀ := by
  have hβc : ContinuousOn β U := fun x hx => (hβ x hx).continuousAt.continuousWithinAt
  have hβσ : Continuous (fun p : ℝ × ℝ => β (σ p.1 p.2)) :=
    hβc.comp_continuous hσc (fun p => hσU p.1 p.2)
  have hβ'σ : Continuous (fun p : ℝ × ℝ => β' (σ p.1 p.2)) :=
    hβ'.comp_continuous hσc (fun p => hσU p.1 p.2)
  -- the derivative integrand
  set F' : ℝ → ℝ → ℝ := fun r s => β' (σ r s) (v r s) (u r s) + β (σ r s) (w r s) with hF'
  have hF'c : Continuous (fun p : ℝ × ℝ => F' p.1 p.2) :=
    ((hβ'σ.clm_apply hvc).clm_apply huc).add (hβσ.clm_apply hwc)
  have hdiff : ∀ r s, HasDerivAt (fun s' => β (σ r s') (u r s')) (F' r s) s := by
    intro r s
    have hc := (hβ (σ r s) (hσU r s)).comp_hasDerivAt s (h1 r s)
    exact hc.clm_apply (h3 r s)
  -- the `r`-derivative of `Q = β(σ)(v)`
  have hQ : ∀ r s, HasDerivAt (fun r' => β (σ r' s) (v r' s)) (F' r s) r := by
    intro r s
    have hc := (hβ (σ r s) (hσU r s)).comp_hasDerivAt r (h2 r s)
    have := hc.clm_apply (h4 r s)
    refine this.congr_deriv ?_
    simp only [hF', Function.comp]
    rw [hclosed r s]
  have hQint : ∫ r in (0 : ℝ)..1, F' r s₀ = β (σ 1 s₀) (v 1 s₀) - β (σ 0 s₀) (v 0 s₀) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hQ r s₀) ?_
    exact (hF'c.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
  -- dominated differentiation
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod
    (isCompact_closedBall s₀ 1) |>.exists_bound_of_continuousOn hF'c.continuousOn
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := 1) (F := fun s r => β (σ r s) (u r s)) (F' := fun s r => F' r s)
    (x₀ := s₀) (s := ball s₀ 1) (bound := fun _ => B) (ball_mem_nhds s₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hQint] at hmain
    exact hmain.2
  · refine Filter.Eventually.of_forall fun s => ?_
    exact ((hβσ.comp (continuous_id.prodMk continuous_const)).clm_apply
      (huc.comp (continuous_id.prodMk continuous_const))).aestronglyMeasurable
  · exact (((hβσ.comp (continuous_id.prodMk continuous_const)).clm_apply
      (huc.comp (continuous_id.prodMk continuous_const))).intervalIntegrable _ _)
  · exact (hF'c.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun r hr s hs => ?_
    rw [uIoc_of_le zero_le_one] at hr
    exact hB (r, s) ⟨⟨hr.1.le, hr.2⟩, mem_closedBall.2 (mem_ball.1 hs).le⟩
  · exact intervalIntegrable_const
  · filter_upwards with r hr s hs
    exact hdiff r s

end QuantumNLS.ResetMoserSurface

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoserSurface.surface_deriv
