import NlsGge.GK38.ContourActionDeformation
import Mathlib.Tactic.Linarith

/-! SOURCE-ONLY geometry for the finite-hole Cauchy step. The supplied
isolating family is retained. Its finite prefix lies strictly inside the
midpoint circle; its infinite tail lies strictly outside the vertical slab
containing the outer square. No contour-integral identity is assumed. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

theorem p6Counting_closed_disc_inside_midpoint38 (ν : ℕ) (m : ℤ)
    (hm : |m| ≤ (ν : ℤ)) :
    closedBall (countingCenter38 m) (Real.pi/4) ⊆
      ball (0 : ℂ) (ν*Real.pi+Real.pi/2) := by
  intro z hz
  have hsmall : ‖z-countingCenter38 m‖ ≤ Real.pi/4 := mem_closedBall_iff_norm.mp hz
  have hcenter := countingCenter_low_norm38 hm
  have hnorm : ‖z‖ ≤ ‖z-countingCenter38 m‖+‖countingCenter38 m‖ := by
    simpa only [sub_add_cancel] using norm_add_le (z-countingCenter38 m) (countingCenter38 m)
  apply mem_ball_zero_iff.mpr
  nlinarith [Real.pi_pos]

theorem p6Isolating_closed_prefix_inside_midpoint38
    (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hgeom : IsolatingGeometry38 C R c N) :
    ∃ L : ℕ, N ≤ L ∧ ∀ ν : ℕ, L ≤ ν → ∀ m : ℤ, |m| ≤ (ν : ℤ) →
      closedBall (C m) (R m) ⊆ ball (0 : ℂ) (ν*Real.pi+Real.pi/2) := by
  obtain ⟨L,hNL,hL⟩ := central_finite_fit38 C R c N hgeom
  refine ⟨L,hNL,fun ν hν m hm z hz => ?_⟩
  by_cases hsmall : |m| ≤ (N : ℤ)
  · have hzold := (hL ν hν).2 m hsmall hz
    have hnorm := mem_ball_zero_iff.mp hzold
    apply mem_ball_zero_iff.mpr
    dsimp only [countingRadius38] at hnorm
    nlinarith [Real.pi_pos]
  · have htail := hgeom.2.2.2.2 m (lt_of_not_ge hsmall)
    rw [htail.1,htail.2.1] at hz
    exact p6Counting_closed_disc_inside_midpoint38 ν m hm hz

theorem p6Isolating_closed_tail_outside_midpoint_slab38
    (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hgeom : IsolatingGeometry38 C R c N)
    (ν : ℕ) (hν : N ≤ ν) (m : ℤ) (hm : (ν : ℤ) < |m|)
    (z : ℂ) (hz : z ∈ closedBall (C m) (R m)) :
    ν*Real.pi+Real.pi/2 < |z.re| := by
  have hNν : (N : ℤ) ≤ ν := by exact_mod_cast hν
  have htail := hgeom.2.2.2.2 m (hNν.trans_lt hm)
  rw [htail.1,htail.2.1] at hz
  have hsmall : |z.re-(countingCenter38 m).re| ≤ Real.pi/4 := by
    have h := (Complex.abs_re_le_norm (z-countingCenter38 m)).trans
      (mem_closedBall_iff_norm.mp hz)
    simpa only [Complex.sub_re] using h
  have hreal : |(countingCenter38 m).re|=‖countingCenter38 m‖ :=
    Complex.abs_re_eq_norm.mpr (by simp [countingCenter38])
  have hcenter : ((ν : ℝ)+1)*Real.pi ≤ |(countingCenter38 m).re| :=
    (countingCenter_far_norm38 hm).trans_eq hreal.symm
  have htriangle : |(countingCenter38 m).re| ≤
      |z.re-(countingCenter38 m).re|+|z.re| := by
    calc
      _ = |((countingCenter38 m).re-z.re)+z.re| := by rw [sub_add_cancel]
      _ ≤ |(countingCenter38 m).re-z.re|+|z.re| := abs_add_le _ _
      _ = _ := by rw [abs_sub_comm]
  nlinarith [Real.pi_pos]

theorem p6Actual_midpoint_square_annulus_cut_domain38
    (φ : PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 φ C R) :
    ∃ L : ℕ, ∀ ν : ℕ, L ≤ ν → ∀ z : ℂ,
      ν*Real.pi+Real.pi/2 ≤ ‖z‖ → |z.re| ≤ ν*Real.pi+Real.pi/2 →
      z ∈ actionCutDomain38 φ := by
  obtain ⟨c,N,hgeom,hspec⟩ := hfam
  obtain ⟨L,hNL,hL⟩ := p6Isolating_closed_prefix_inside_midpoint38 C R c N hgeom
  refine ⟨L,fun ν hν z hnorm hre hcut => ?_⟩
  obtain ⟨m,hm⟩ := mem_iUnion.mp hcut
  have hz : z ∈ closedBall (C m) (R m) :=
    ball_subset_closedBall ((hspec.1 m).1 hm)
  by_cases hsmall : |m| ≤ (ν : ℤ)
  · exact (not_lt_of_ge hnorm) (mem_ball_zero_iff.mp (hL ν hν m hsmall hz))
  · exact (not_lt_of_ge hre)
      (p6Isolating_closed_tail_outside_midpoint_slab38 C R c N hgeom ν
        (hNL.trans hν) m (lt_of_not_ge hsmall) z hz)

end
end NlsGge.GK38
