import NlsGge.GK38.AbelianOriginalFiniteSquareExcision
import NlsGge.GK38.AbelianCircleSquareIntegral

/-! SOURCE ONLY: actual finite-hole Cauchy decomposition into genuine periods.
The supplied original family, all signed labels/finite head and complex data
remain. Circle/edge/period CIs are earned before each identity. No excision
or period-value premise. Exact targets/English preceded proof.
UNCOMPILED/no native scope. -/
set_option autoImplicit false
open Set Metric MeasureTheory
open scoped Interval
namespace NlsGge.GK38
noncomputable section

theorem p6Original_finite_circle_period_excision38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 φ C R)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f univ) :
    ∃ L : ℕ, ∀ ν : ℕ, L ≤ ν →
      CircleIntegrable (fun z : ℂ => f z/canonRoot38 φ z) 0 (ν*Real.pi+Real.pi/2) ∧
      circleIntegral (fun z : ℂ => f z/canonRoot38 φ z) 0 (ν*Real.pi+Real.pi/2) =
        ∑ k ∈ Finset.range (2*ν+1), abelianPeriod38 ((k : ℤ)-ν) φ f := by
  obtain ⟨c,N,hgeom,hspec⟩ := hfam
  have hfam : IsolatingFamily38 φ C R := ⟨c,N,hgeom,hspec⟩
  obtain ⟨Ls,hsquare⟩ := p6Original_finite_square_excision38 φ hφ C R hfam f hf
  obtain ⟨La,hannulus⟩ := p6Actual_midpoint_square_annulus_cut_domain38 φ C R hfam
  have hlocal (m : ℤ) := p6Circle_square_integral38
    (fun z : ℂ => f z/canonRoot38 φ z) (C m) (R m) (isolating_radius_pos38 hfam m)
    (p6Isolating_quotient_square_annulus_analytic38 φ hφ C R hfam m f hf)
  have hrebase (m : ℤ) := abelianPeriod_fullfamily_realization38 φ hφ
    (discC φ) C (discR φ) R (isolating_family38 φ hφ) hfam m f hf
  refine ⟨max Ls La,fun ν hν => ?_⟩
  have hsν : Ls ≤ ν := le_trans (le_max_left _ _) hν
  have haν : La ≤ ν := le_trans (le_max_right _ _) hν
  let H : ℝ := ν*Real.pi+Real.pi/2
  have hH : 0 < H := by dsimp [H]; positivity
  have hqanalytic : AnalyticOnNhd ℂ (fun z : ℂ => f z/canonRoot38 φ z)
      (p6SquareAnnulus38 0 H) := by
    apply (p2Quotient_analytic38 φ hφ f hf).mono
    intro z hz
    exact hannulus ν haν z (by simpa [p6SquareAnnulus38,H] using hz.1)
      (by simpa [p6SquareAnnulus38,H] using hz.2)
  have houter := p6Circle_square_integral38
    (fun z : ℂ => f z/canonRoot38 φ z) 0 H hH hqanalytic
  refine ⟨houter.1,?_⟩
  calc
    _ = p6RectBoundary38 (fun z : ℂ => f z/canonRoot38 φ z) (-H) H (-H) H := by
      simpa only [Complex.zero_re,Complex.zero_im,zero_sub,zero_add] using
        houter.2.2.2.2.2
    _ = ∑ k ∈ Finset.range (2*ν+1),
        p6RectBoundary38 (fun z : ℂ => f z/canonRoot38 φ z)
          ((C ((k : ℤ)-ν)).re-R ((k : ℤ)-ν))
          ((C ((k : ℤ)-ν)).re+R ((k : ℤ)-ν))
          (-R ((k : ℤ)-ν)) (R ((k : ℤ)-ν)) := hsquare ν hsν
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      let m : ℤ := (k : ℤ)-ν
      have hsmall := (hlocal m).2.2.2.2.2
      have hsmallreal :
          circleIntegral (fun z : ℂ => f z/canonRoot38 φ z) (C m) (R m) =
          p6RectBoundary38 (fun z : ℂ => f z/canonRoot38 φ z)
            ((C m).re-R m) ((C m).re+R m) (-R m) (R m) := by
        simpa only [(hgeom.1 m).2,zero_sub,zero_add] using hsmall
      exact hsmallreal.symm.trans (hrebase m).2.2.symm

end
end NlsGge.GK38
