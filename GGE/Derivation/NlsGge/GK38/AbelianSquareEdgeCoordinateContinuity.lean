import NlsGge.GK38.AbelianSquareEdgeIntegrability

/-! SOURCE ONLY: coordinate continuity on actual annular square-edge traces.
No filled-square analyticity. These concrete facts discharge the affine-line
primitive's continuity premises. Exact target/English preceded proof.
UNCOMPILED/no native scope. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

theorem p6Annulus_edge_coordinate_continuity38 (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (p6SquareAnnulus38 c r)) :
    (∀ e : ℝ, |e-c.im|=r →
      ContinuousOn (fun x : ℝ => f ((e : ℂ)*Complex.I+(x : ℂ)*(1 : ℂ)))
        (Set.uIcc (c.re-r) (c.re+r))) ∧
    (∀ e : ℝ, |e-c.re|=r →
      ContinuousOn (fun y : ℝ => f ((e : ℂ)+(y : ℂ)*Complex.I))
        (Set.uIcc (c.im-r) (c.im+r))) := by
  constructor
  · intro e he
    refine hf.continuousOn.comp
      (show ContinuousOn (fun x : ℝ => (e : ℂ)*Complex.I+(x : ℂ)*(1 : ℂ))
        (Set.uIcc (c.re-r) (c.re+r)) from by fun_prop) ?_
    intro x hx
    rw [Set.uIcc_of_le (by linarith : c.re-r ≤ c.re+r)] at hx
    refine ⟨?_,?_⟩
    · have hn := Complex.abs_im_le_norm (((e : ℂ)*Complex.I+(x : ℂ)*(1 : ℂ))-c)
      simpa [he] using hn
    · have hre : |x-c.re| ≤ r := abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩
      simpa using hre
  · intro e he
    refine hf.continuousOn.comp
      (show ContinuousOn (fun y : ℝ => (e : ℂ)+(y : ℂ)*Complex.I)
        (Set.uIcc (c.im-r) (c.im+r)) from by fun_prop) ?_
    intro y hy
    refine ⟨?_,?_⟩
    · have hn := Complex.abs_re_le_norm (((e : ℂ)+(y : ℂ)*Complex.I)-c)
      simpa [he] using hn
    · simpa using he.le

end
end NlsGge.GK38
