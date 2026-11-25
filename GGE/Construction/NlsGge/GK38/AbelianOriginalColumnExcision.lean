import NlsGge.GK38.AbelianOriginalStripGeometry
import NlsGge.GK38.AbelianRectangularFrame
import NlsGge.GK38.AbelianPeriods

/-! SOURCE ONLY: actual supplied-disc column excision, not a cell oracle.
All four CLOSED frame cells are proved cut-free using actual coordinate/norm
bounds, then actual quotient analyticity earns Cauchy and all required edge CI.
Exact target+English preceded proof. UNCOMPILED, outside current four scope. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

theorem p6Original_column_quotient_excision38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 φ C R)
    (n : ℤ) (a b H : ℝ)
    (haPrev : (C (n-1)).re+R (n-1) < a)
    (hbNext : b < (C (n+1)).re-R (n+1))
    (haOwn : a ≤ (C n).re-R n) (hbOwn : (C n).re+R n ≤ b)
    (hH : R n ≤ H) (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f univ) :
    p6RectBoundary38 (fun z : ℂ => f z/canonRoot38 φ z) a b (-H) H =
      p6RectBoundary38 (fun z : ℂ => f z/canonRoot38 φ z)
        ((C n).re-R n) ((C n).re+R n) (-R n) (R n) := by
  let L : ℝ := (C n).re-R n
  let U : ℝ := (C n).re+R n
  have hr : 0 < R n := isolating_radius_pos38 hfam n
  have hLU : L ≤ U := by dsimp [L,U]; linarith
  have haL : a ≤ L := haOwn
  have hUb : U ≤ b := hbOwn
  have hcenter : (C n).im = 0 := by
    obtain ⟨c,N,hgeom,hspectral⟩ := hfam
    exact (hgeom.1 n).2
  have hfree := p6Original_strip_outside_disc_cut_free38 φ C R hfam n a b haPrev hbNext
  have hleft : (Set.uIcc a L) ×ℂ (Set.uIcc (-H) H) ⊆ actionCutDomain38 φ := by
    intro z hz
    obtain ⟨hx,hy⟩ := Complex.mem_reProdIm.mp hz
    rw [Set.uIcc_of_le haL] at hx
    apply hfree
    refine ⟨hx.1,hx.2.trans (hLU.trans hUb),?_⟩
    have hn := Complex.abs_re_le_norm (z-C n)
    simp only [Complex.sub_re] at hn
    have ha := neg_le_abs (z.re-(C n).re)
    dsimp [L] at hx
    linarith [hx.2]
  have hright : (Set.uIcc U b) ×ℂ (Set.uIcc (-H) H) ⊆ actionCutDomain38 φ := by
    intro z hz
    obtain ⟨hx,hy⟩ := Complex.mem_reProdIm.mp hz
    rw [Set.uIcc_of_le hUb] at hx
    apply hfree
    refine ⟨(haL.trans hLU).trans hx.1,hx.2,?_⟩
    have hn := Complex.abs_re_le_norm (z-C n)
    simp only [Complex.sub_re] at hn
    have ha := le_abs_self (z.re-(C n).re)
    dsimp [U] at hx
    linarith [hx.1]
  have hbottom : (Set.uIcc L U) ×ℂ (Set.uIcc (-H) (-R n)) ⊆ actionCutDomain38 φ := by
    intro z hz
    obtain ⟨hx,hy⟩ := Complex.mem_reProdIm.mp hz
    rw [Set.uIcc_of_le hLU] at hx
    rw [Set.uIcc_of_le (neg_le_neg hH)] at hy
    apply hfree
    refine ⟨haL.trans hx.1,hx.2.trans hUb,?_⟩
    have hn := Complex.abs_im_le_norm (z-C n)
    simp only [Complex.sub_im,hcenter,sub_zero] at hn
    have ha := neg_le_abs z.im
    linarith [hy.2]
  have htop : (Set.uIcc L U) ×ℂ (Set.uIcc (R n) H) ⊆ actionCutDomain38 φ := by
    intro z hz
    obtain ⟨hx,hy⟩ := Complex.mem_reProdIm.mp hz
    rw [Set.uIcc_of_le hLU] at hx
    rw [Set.uIcc_of_le hH] at hy
    apply hfree
    refine ⟨haL.trans hx.1,hx.2.trans hUb,?_⟩
    have hn := Complex.abs_im_le_norm (z-C n)
    simp only [Complex.sub_im,hcenter,sub_zero] at hn
    have ha := le_abs_self z.im
    linarith [hy.1]
  have hquotient := p2Quotient_analytic38 φ hφ f hf
  exact p6Rect_frame_excision38 (fun z : ℂ => f z/canonRoot38 φ z) a L U b
    (-H) (-R n) (R n) H (neg_le_neg hH) (by linarith) hH
    (hquotient.mono hleft).differentiableOn (hquotient.mono hright).differentiableOn
    (hquotient.mono hbottom).differentiableOn (hquotient.mono htop).differentiableOn

end
end NlsGge.GK38
