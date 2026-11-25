import NlsGge.GK38.AbelianFullComplexInverse
import NlsGge.GK38.AbelianFixedGapCube
import Mathlib.Analysis.Normed.Ring.Units

/-! A genuine uniform inverse norm on the FIXED compact actual full gap cube.
Actual invertibility is proved before the totalized inverse is used. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38.P6FullJacobian
noncomputable section

theorem full_Qstar_inverse_continuousAt (T : Lib.L2Seq →L[ℂ] Lib.L2Seq)
    (hT : T.IsInvertible) : ContinuousAt
      (fun S : Lib.L2Seq →L[ℂ] Lib.L2Seq => S.inverse) T := by
  rw [← ContinuousLinearMap.ringInverse_eq_inverse]
  obtain ⟨e,he⟩ := hT
  rw [← he]
  change ContinuousAt Ring.inverse (e.toUnit : Lib.L2Seq →L[ℂ] Lib.L2Seq)
  exact NormedRing.inverse_continuousAt e.toUnit

theorem full_gap_original_family_placement (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 (realSlice u) C R) (s : P6RealSpace38)
    (hs : s ∈ p5FullRealGapCube38 u) :
    ∀ k : ℤ, Lib.sigmaOf (p6RealInclude38 s) k ∈ closedBall (C k) (R k) := by
  obtain ⟨c,N,hg,hsp⟩ := hfam
  intro k
  have hk := ball_subset_closedBall ((hsp.1 k).1 (hs k))
  simpa only [Lib.sigmaOf,countingCenter38,p6RealInclude_apply38,add_comm] using hk

theorem full_gap_Qstar_inverse_bound (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 (realSlice u) C R) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ p5FullRealGapCube38 u,
      (p6Qstar38 (realSlice u) (p6RealInclude38 s)).IsInvertible ∧
      ‖(p6Qstar38 (realSlice u) (p6RealInclude38 s)).inverse‖ ≤ B := by
  let Q : P6RealSpace38 → Lib.L2Seq →L[ℂ] Lib.L2Seq :=
    fun s => p6Qstar38 (realSlice u) (p6RealInclude38 s)
  have hpair : Continuous (fun s : P6RealSpace38 => (realSlice u,p6RealInclude38 s)) :=
    continuous_const.prodMk p6RealInclude38.continuous
  have hQ : Continuous Q := by
    apply continuous_iff_continuousAt.mpr
    intro s
    have ha : AnalyticAt ℂ (fun p : PotPair × Lib.L2Seq => p6Qstar38 p.1 p.2)
        (realSlice u,p6RealInclude38 s) :=
      p6Qstar_joint_analytic38 (realSlice u,p6RealInclude38 s)
        ⟨realSlice_mem_gkW u,mem_univ _⟩
    change ContinuousAt
      ((fun p : PotPair × Lib.L2Seq => p6Qstar38 p.1 p.2) ∘
        (fun t : P6RealSpace38 => (realSlice u,p6RealInclude38 t))) s
    exact ContinuousAt.comp
      (f := fun t : P6RealSpace38 => (realSlice u,p6RealInclude38 t))
      (g := fun p : PotPair × Lib.L2Seq => p6Qstar38 p.1 p.2)
      (x := s) ha.continuousAt (hpair.continuousAt (x := s))
  have hinv : ∀ s ∈ p5FullRealGapCube38 u, (Q s).IsInvertible := by
    intro s hs
    exact original_family_complex_Qstar_inverse u C R hfam s
      (full_gap_original_family_placement u C R hfam s hs)
  have hcont : ContinuousOn (fun s => (Q s).inverse) (p5FullRealGapCube38 u) := by
    intro s hs
    exact ((full_Qstar_inverse_continuousAt (Q s) (hinv s hs)).comp
      hQ.continuousAt).continuousWithinAt
  obtain ⟨B,hB⟩ := (p5FullRealGapCube_isCompact38 u).exists_bound_of_continuousOn hcont
  refine ⟨max B 0,le_max_right _ _,?_⟩
  intro s hs
  exact ⟨hinv s hs,(hB s hs).trans (le_max_left _ _)⟩

end
end NlsGge.GK38.P6FullJacobian
