import NlsGge.GK38.AbelianRectangularExcision
import NlsGge.GK38.ContourActionDeformation
import Lean.Elab.Tactic.Omega

/-! SOURCE ONLY: literal original adjacent-disc bounds isolate the actual cut
inside a vertical column. This earns finite-frame holomorphic-cell geometry;
no integral/cutavoidance identity is assumed. ROOT owns outerprefix/tail work.
Exact targets+English preceded proofs. UNCOMPILED, outside current four scope. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

theorem p6Original_disc_upper_mono38 (φ : PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 φ C R) (m n : ℤ) (hmn : m ≤ n) :
    (C m).re+R m ≤ (C n).re+R n := by
  rcases lt_or_eq_of_le hmn with hlt | rfl
  · have hsep := p6Isolating_horizontal_separation38 φ C R hfam m n hlt
    have hr := isolating_radius_pos38 hfam n
    linarith
  · exact le_rfl

theorem p6Original_disc_lower_mono38 (φ : PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 φ C R) (m n : ℤ) (hmn : m ≤ n) :
    (C m).re-R m ≤ (C n).re-R n := by
  rcases lt_or_eq_of_le hmn with hlt | rfl
  · have hsep := p6Isolating_horizontal_separation38 φ C R hfam m n hlt
    have hr := isolating_radius_pos38 hfam m
    linarith
  · exact le_rfl

theorem p6Original_vertical_strip_cut_label38 (φ : PotPair)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 φ C R)
    (n : ℤ) (a b : ℝ)
    (ha : (C (n-1)).re+R (n-1) < a)
    (hb : b < (C (n+1)).re-R (n+1))
    (z : ℂ) (hzlo : a ≤ z.re) (hzhi : z.re ≤ b) (hzcut : z ∈ gapSegments38 φ) :
    z ∈ segment ℝ (lamMinus φ n) (lamPlus φ n) := by
  obtain ⟨c,N,hgeom,hspectral⟩ := hfam
  have hf : IsolatingFamily38 φ C R := ⟨c,N,hgeom,hspectral⟩
  obtain ⟨m,hzm⟩ := mem_iUnion.mp hzcut
  have hball := (hspectral.1 m).1 hzm
  have hzabs : |z.re-(C m).re| < R m :=
    (Complex.abs_re_le_norm (z-C m)).trans_lt (mem_ball_iff_norm.mp hball)
  rcases lt_trichotomy m n with hmn | hmn | hnm
  · have hmono := p6Original_disc_upper_mono38 φ C R hf m (n-1) (by omega)
    have hupper := (abs_lt.mp hzabs).2
    linarith
  · subst m
    exact hzm
  · have hmono := p6Original_disc_lower_mono38 φ C R hf (n+1) m (by omega)
    have hlower := (abs_lt.mp hzabs).1
    linarith

theorem p6Original_strip_outside_disc_cut_free38 (φ : PotPair)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 φ C R)
    (n : ℤ) (a b : ℝ)
    (ha : (C (n-1)).re+R (n-1) < a)
    (hb : b < (C (n+1)).re-R (n+1)) :
    {z : ℂ | a ≤ z.re ∧ z.re ≤ b ∧ R n ≤ ‖z-C n‖} ⊆ actionCutDomain38 φ := by
  intro z hz
  change z ∉ gapSegments38 φ
  intro hcut
  have hown := p6Original_vertical_strip_cut_label38 φ C R hfam n a b ha hb z hz.1 hz.2.1 hcut
  obtain ⟨c,N,hgeom,hspectral⟩ := hfam
  have hball := (hspectral.1 n).1 hown
  exact (not_lt_of_ge hz.2.2) (mem_ball_iff_norm.mp hball)

end
end NlsGge.GK38
