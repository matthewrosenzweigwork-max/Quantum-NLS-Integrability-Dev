import NlsGge.GK38.AbelianOriginalColumnExcision

/-! SOURCE ONLY: original finite-column horizontal CIs and earned outer height.
Exact targets and English preceded proofs. Neither a contour identity nor a
period value is assumed. ROOT supplies the genuine original-prefix inclusion.
UNCOMPILED, outside currently released next4 scientific scope. -/
set_option autoImplicit false
open Set Metric MeasureTheory
open scoped Interval
namespace NlsGge.GK38
noncomputable section

theorem p6RealCenter_radius_lt_of_closedBall_inside38 (c : ℂ) (r H : ℝ)
    (hc : c.im = 0) (hr : 0 ≤ r)
    (hinside : closedBall c r ⊆ ball (0 : ℂ) H) : r < H := by
  have hz : c+(r : ℂ)*Complex.I ∈ closedBall c r := by
    apply mem_closedBall_iff_norm.mpr
    simp [abs_of_nonneg hr]
  have hnorm : ‖c+(r : ℂ)*Complex.I‖ < H :=
    mem_ball_zero_iff.mp (hinside hz)
  have him : r ≤ ‖c+(r : ℂ)*Complex.I‖ := by
    simpa [hc, abs_of_nonneg hr] using Complex.abs_im_le_norm (c+(r : ℂ)*Complex.I)
  exact him.trans_lt hnorm

theorem p6Original_column_horizontal_integrable38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 φ C R)
    (n : ℤ) (a b H : ℝ)
    (haPrev : (C (n-1)).re+R (n-1) < a)
    (hbNext : b < (C (n+1)).re-R (n+1))
    (haOwn : a ≤ (C n).re-R n) (hbOwn : (C n).re+R n ≤ b)
    (hH : R n ≤ H) (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f univ) :
    IntervalIntegrable (fun x : ℝ => f ((x : ℂ)+(-H : ℂ)*Complex.I) /
      canonRoot38 φ ((x : ℂ)+(-H : ℂ)*Complex.I)) volume a b ∧
    IntervalIntegrable (fun x : ℝ => f ((x : ℂ)+(H : ℂ)*Complex.I) /
      canonRoot38 φ ((x : ℂ)+(H : ℂ)*Complex.I)) volume a b := by
  have hr : 0 < R n := isolating_radius_pos38 hfam n
  have hab : a ≤ b := by linarith
  have hH0 : 0 ≤ H := le_trans (le_of_lt hr) hH
  have hcenter : (C n).im = 0 := by
    obtain ⟨c,N,hgeom,hspectral⟩ := hfam
    exact (hgeom.1 n).2
  have hfree := p6Original_strip_outside_disc_cut_free38 φ C R hfam n a b haPrev hbNext
  have hquotient := (p2Quotient_analytic38 φ hφ f hf).continuousOn
  have hCI (y : ℝ) (hy : R n ≤ |y|) :
      IntervalIntegrable (fun x : ℝ => f ((x : ℂ)+(y : ℂ)*Complex.I) /
        canonRoot38 φ ((x : ℂ)+(y : ℂ)*Complex.I)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    refine hquotient.comp (show ContinuousOn (fun x : ℝ => (x : ℂ)+(y : ℂ)*Complex.I)
      (Set.uIcc a b) from by fun_prop) ?_
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    apply hfree
    refine ⟨by simpa using hx.1, by simpa using hx.2, ?_⟩
    have him := Complex.abs_im_le_norm (((x : ℂ)+(y : ℂ)*Complex.I)-C n)
    have him' : |y| ≤ ‖((x : ℂ)+(y : ℂ)*Complex.I)-C n‖ := by
      simpa [hcenter] using him
    exact hy.trans him'
  exact ⟨(by simpa only [Complex.ofReal_neg] using (hCI (-H) (by simpa [abs_of_nonneg hH0] using hH))),
    hCI H (by simpa [abs_of_nonneg hH0] using hH)⟩

end
end NlsGge.GK38
