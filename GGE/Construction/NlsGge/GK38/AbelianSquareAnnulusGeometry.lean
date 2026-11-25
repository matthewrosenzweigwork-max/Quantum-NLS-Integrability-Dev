import NlsGge.GK38.ActionContourGeometry
import NlsGge.GK38.AbelianPeriods
import Mathlib.Tactic.Linarith

/-! SOURCE ONLY: the actual original-disc annular vertical slab is cut-free.
This earns the analytic domain for a local circle-to-square deformation.
No contour identity is assumed. Exact targets+English preceded proof authoring.
UNCOMPILED; no native scope is inferred from source preparation. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

def p6SquareAnnulus38 (c : ℂ) (r : ℝ) : Set ℂ :=
  {z | r ≤ ‖z-c‖ ∧ |z.re-c.re| ≤ r}

theorem p6Isolating_square_annulus_avoids_cuts38 (φ : PotPair)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 φ C R) (n : ℤ) :
    p6SquareAnnulus38 (C n) (R n) ⊆ actionCutDomain38 φ := by
  intro z hz
  change z ∉ gapSegments38 φ
  intro hcut
  obtain ⟨c,N,hgeom,hspectral⟩ := hfam
  obtain ⟨m,hzm⟩ := mem_iUnion.mp hcut
  have hb : z ∈ ball (C m) (R m) := (hspectral.1 m).1 hzm
  have hnorm : R n ≤ ‖z-C n‖ := hz.1
  have hre : |z.re-(C n).re| ≤ R n := hz.2
  rcases lt_trichotomy m n with hmn | hmn | hnm
  · have hl := contour_left_bound38 C R c N hgeom hmn hb
    have hlo := (abs_le.mp hre).1
    linarith
  · subst m
    exact (not_lt_of_ge hnorm) (mem_ball_iff_norm.mp hb)
  · have hr := contour_right_bound38 C R c N hgeom hnm hb
    have hhi := (abs_le.mp hre).2
    linarith

theorem p6Isolating_quotient_square_annulus_analytic38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 φ C R) (n : ℤ)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f univ) :
    AnalyticOnNhd ℂ (fun z : ℂ => f z/canonRoot38 φ z)
      (p6SquareAnnulus38 (C n) (R n)) := by
  exact (p2Quotient_analytic38 φ hφ f hf).mono
    (p6Isolating_square_annulus_avoids_cuts38 φ C R hfam n)

end
end NlsGge.GK38
