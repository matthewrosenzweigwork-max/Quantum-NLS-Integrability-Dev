import NlsGge.GK38.AbelianRectangularExcision
import Mathlib.Tactic.FunProp

/-! SOURCE ONLY: genuine rectangular-frame excision from four actual
holomorphic closed cells. Edge integrability is EARNED before all cancellation.
No integral identity, period value, homotopy, or spectral placement is assumed.
Exact targets+English were written before proofs. UNCOMPILED. -/
set_option autoImplicit false
open Set Metric MeasureTheory
open scoped Interval
namespace NlsGge.GK38
noncomputable section

theorem p6Rect_edges_integrable38 (F : ℂ → ℂ) (a b c d : ℝ)
    (hF : ContinuousOn F ((Set.uIcc a b) ×ℂ (Set.uIcc c d))) :
    IntervalIntegrable (fun x : ℝ => F ((x : ℂ)+(c : ℂ)*Complex.I)) volume a b ∧
    IntervalIntegrable (fun x : ℝ => F ((x : ℂ)+(d : ℂ)*Complex.I)) volume a b ∧
    IntervalIntegrable (fun y : ℝ => F ((a : ℂ)+(y : ℂ)*Complex.I)) volume c d ∧
    IntervalIntegrable (fun y : ℝ => F ((b : ℂ)+(y : ℂ)*Complex.I)) volume c d := by
  have hc : ContinuousOn (fun x : ℝ => F ((x : ℂ)+(c : ℂ)*Complex.I)) (Set.uIcc a b) := by
    refine hF.comp (show ContinuousOn (fun x : ℝ => (x : ℂ)+(c : ℂ)*Complex.I) (Set.uIcc a b) from by fun_prop) ?_
    intro x hx
    simpa [Complex.mem_reProdIm] using hx
  have hd : ContinuousOn (fun x : ℝ => F ((x : ℂ)+(d : ℂ)*Complex.I)) (Set.uIcc a b) := by
    refine hF.comp (show ContinuousOn (fun x : ℝ => (x : ℂ)+(d : ℂ)*Complex.I) (Set.uIcc a b) from by fun_prop) ?_
    intro x hx
    simpa [Complex.mem_reProdIm] using hx
  have ha : ContinuousOn (fun y : ℝ => F ((a : ℂ)+(y : ℂ)*Complex.I)) (Set.uIcc c d) := by
    refine hF.comp (show ContinuousOn (fun y : ℝ => (a : ℂ)+(y : ℂ)*Complex.I) (Set.uIcc c d) from by fun_prop) ?_
    intro y hy
    simpa [Complex.mem_reProdIm] using hy
  have hb : ContinuousOn (fun y : ℝ => F ((b : ℂ)+(y : ℂ)*Complex.I)) (Set.uIcc c d) := by
    refine hF.comp (show ContinuousOn (fun y : ℝ => (b : ℂ)+(y : ℂ)*Complex.I) (Set.uIcc c d) from by fun_prop) ?_
    intro y hy
    simpa [Complex.mem_reProdIm] using hy
  exact ⟨hc.intervalIntegrable,hd.intervalIntegrable,ha.intervalIntegrable,hb.intervalIntegrable⟩

theorem p6Rect_frame_boundary_identity38 (F : ℂ → ℂ) (a l r b c lo hi d : ℝ)
    (hc0 : IntervalIntegrable (fun x : ℝ => F ((x : ℂ)+(c : ℂ)*Complex.I)) volume a l)
    (hc1 : IntervalIntegrable (fun x : ℝ => F ((x : ℂ)+(c : ℂ)*Complex.I)) volume l r)
    (hc2 : IntervalIntegrable (fun x : ℝ => F ((x : ℂ)+(c : ℂ)*Complex.I)) volume r b)
    (hd0 : IntervalIntegrable (fun x : ℝ => F ((x : ℂ)+(d : ℂ)*Complex.I)) volume a l)
    (hd1 : IntervalIntegrable (fun x : ℝ => F ((x : ℂ)+(d : ℂ)*Complex.I)) volume l r)
    (hd2 : IntervalIntegrable (fun x : ℝ => F ((x : ℂ)+(d : ℂ)*Complex.I)) volume r b)
    (hl0 : IntervalIntegrable (fun y : ℝ => F ((l : ℂ)+(y : ℂ)*Complex.I)) volume c lo)
    (hl1 : IntervalIntegrable (fun y : ℝ => F ((l : ℂ)+(y : ℂ)*Complex.I)) volume lo hi)
    (hl2 : IntervalIntegrable (fun y : ℝ => F ((l : ℂ)+(y : ℂ)*Complex.I)) volume hi d)
    (hr0 : IntervalIntegrable (fun y : ℝ => F ((r : ℂ)+(y : ℂ)*Complex.I)) volume c lo)
    (hr1 : IntervalIntegrable (fun y : ℝ => F ((r : ℂ)+(y : ℂ)*Complex.I)) volume lo hi)
    (hr2 : IntervalIntegrable (fun y : ℝ => F ((r : ℂ)+(y : ℂ)*Complex.I)) volume hi d) :
    p6RectBoundary38 F a b c d =
      p6RectBoundary38 F a l c d + p6RectBoundary38 F r b c d +
      p6RectBoundary38 F l r c lo + p6RectBoundary38 F l r hi d +
      p6RectBoundary38 F l r lo hi := by
  have houter := p6RectBoundary_horizontal_split38 F a l b c d
    hc0 (hc1.trans hc2) hd0 (hd1.trans hd2)
  have hmiddle := p6RectBoundary_horizontal_split38 F l r b c d hc1 hc2 hd1 hd2
  have hmidbottom := p6RectBoundary_vertical_split38 F l r c lo d
    hl0 (hl1.trans hl2) hr0 (hr1.trans hr2)
  have hmidtop := p6RectBoundary_vertical_split38 F l r lo hi d hl1 hl2 hr1 hr2
  rw [houter,hmiddle,hmidbottom,hmidtop]
  abel

theorem p6Rect_frame_excision38 (F : ℂ → ℂ) (a l r b c lo hi d : ℝ)
    (hclo : c ≤ lo) (hlohi : lo ≤ hi) (hhid : hi ≤ d)
    (hleft : DifferentiableOn ℂ F ((Set.uIcc a l) ×ℂ (Set.uIcc c d)))
    (hright : DifferentiableOn ℂ F ((Set.uIcc r b) ×ℂ (Set.uIcc c d)))
    (hbottom : DifferentiableOn ℂ F ((Set.uIcc l r) ×ℂ (Set.uIcc c lo)))
    (htop : DifferentiableOn ℂ F ((Set.uIcc l r) ×ℂ (Set.uIcc hi d))) :
    p6RectBoundary38 F a b c d = p6RectBoundary38 F l r lo hi := by
  have hL := p6Rect_edges_integrable38 F a l c d hleft.continuousOn
  have hR := p6Rect_edges_integrable38 F r b c d hright.continuousOn
  have hB := p6Rect_edges_integrable38 F l r c lo hbottom.continuousOn
  have hT := p6Rect_edges_integrable38 F l r hi d htop.continuousOn
  have hsub : Set.uIcc lo hi ⊆ Set.uIcc c d :=
    Set.uIcc_subset_uIcc (Set.mem_uIcc_of_le hclo (hlohi.trans hhid))
      (Set.mem_uIcc_of_le (hclo.trans hlohi) hhid)
  have hinnerL : IntervalIntegrable
      (fun y : ℝ => F ((l : ℂ)+(y : ℂ)*Complex.I)) volume lo hi :=
    hL.2.2.2.mono_set hsub
  have hinnerR : IntervalIntegrable
      (fun y : ℝ => F ((r : ℂ)+(y : ℂ)*Complex.I)) volume lo hi :=
    hR.2.2.1.mono_set hsub
  have hframe := p6Rect_frame_boundary_identity38 F a l r b c lo hi d
    hL.1 hB.1 hR.1 hL.2.1 hT.2.1 hR.2.1
    hB.2.2.1 hinnerL hT.2.2.1 hB.2.2.2 hinnerR hT.2.2.2
  rw [p6RectBoundary_zero_of_differentiableOn38 F a l c d hleft,
    p6RectBoundary_zero_of_differentiableOn38 F r b c d hright,
    p6RectBoundary_zero_of_differentiableOn38 F l r c lo hbottom,
    p6RectBoundary_zero_of_differentiableOn38 F l r hi d htop] at hframe
  simpa using hframe

end
end NlsGge.GK38
