import NlsGge.GK38.AbelianQuarterArcGeometry
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

/-! SOURCE ONLY: four genuine square-edge CIs from the actual annular slab.
No analyticity inside the filled square is assumed: that interior may contain
actual cuts. Only each literal edge trace is used. Exact target+English
preceded proof. UNCOMPILED, outside current scientific scope. -/
set_option autoImplicit false
open Set Metric MeasureTheory
open scoped Interval
namespace NlsGge.GK38
noncomputable section

theorem p6Annulus_square_edges_integrable38 (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (p6SquareAnnulus38 c r)) :
    IntervalIntegrable (fun x : ℝ => f ((x : ℂ)+((c.im-r : ℝ) : ℂ)*Complex.I))
      volume (c.re-r) (c.re+r) ∧
    IntervalIntegrable (fun x : ℝ => f ((x : ℂ)+((c.im+r : ℝ) : ℂ)*Complex.I))
      volume (c.re-r) (c.re+r) ∧
    IntervalIntegrable (fun y : ℝ => f (((c.re-r : ℝ) : ℂ)+(y : ℂ)*Complex.I))
      volume (c.im-r) (c.im+r) ∧
    IntervalIntegrable (fun y : ℝ => f (((c.re+r : ℝ) : ℂ)+(y : ℂ)*Complex.I))
      volume (c.im-r) (c.im+r) := by
  have hhor (e : ℝ) (he : |e-c.im|=r) :
      IntervalIntegrable (fun x : ℝ => f ((x : ℂ)+(e : ℂ)*Complex.I))
        volume (c.re-r) (c.re+r) := by
    apply ContinuousOn.intervalIntegrable
    refine hf.continuousOn.comp
      (show ContinuousOn (fun x : ℝ => (x : ℂ)+(e : ℂ)*Complex.I)
        (Set.uIcc (c.re-r) (c.re+r)) from by fun_prop) ?_
    intro x hx
    rw [Set.uIcc_of_le (by linarith : c.re-r ≤ c.re+r)] at hx
    refine ⟨?_,?_⟩
    · have hn := Complex.abs_im_le_norm (((x : ℂ)+(e : ℂ)*Complex.I)-c)
      simpa [he] using hn
    · have hre : |x-c.re| ≤ r := abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩
      simpa using hre
  have hver (e : ℝ) (he : |e-c.re|=r) :
      IntervalIntegrable (fun y : ℝ => f ((e : ℂ)+(y : ℂ)*Complex.I))
        volume (c.im-r) (c.im+r) := by
    apply ContinuousOn.intervalIntegrable
    refine hf.continuousOn.comp
      (show ContinuousOn (fun y : ℝ => (e : ℂ)+(y : ℂ)*Complex.I)
        (Set.uIcc (c.im-r) (c.im+r)) from by fun_prop) ?_
    intro y hy
    refine ⟨?_,?_⟩
    · have hn := Complex.abs_re_le_norm (((e : ℂ)+(y : ℂ)*Complex.I)-c)
      simpa [he] using hn
    · simpa using he.le
  have hminus (x : ℝ) : |(x-r)-x|=r := by
    have he : (x-r)-x = -r := by ring
    rw [he,abs_neg,abs_of_nonneg hr]
  have hplus (x : ℝ) : |(x+r)-x|=r := by
    have he : (x+r)-x = r := by ring
    rw [he,abs_of_nonneg hr]
  exact ⟨hhor (c.im-r) (hminus c.im),hhor (c.im+r) (hplus c.im),
    hver (c.re-r) (hminus c.re),hver (c.re+r) (hplus c.re)⟩

end
end NlsGge.GK38
