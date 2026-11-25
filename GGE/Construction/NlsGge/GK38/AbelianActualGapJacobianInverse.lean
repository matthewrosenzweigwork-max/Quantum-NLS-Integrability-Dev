import NlsGge.GK38.AbelianRealJacobianInverse
import NlsGge.GK38.AbelianFixedGapCube
import NlsGge.GK38.AbelianInputCompletion
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-! Discharge actual P5 derivative invertibility on every actual closed-gap
input by completing the missing coordinate inside its ORIGINAL family disc. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38.P4NumeratorVariation
noncomputable section

theorem actual_gap_real_jacobian_inverse (n : ℤ) (u : PhysicalL2)
    (t : P3RealSpace38 n) (ht : t ∈ p5RealGapCube38 n u) :
    (fderiv ℝ (p3RealFn38 n u) t).IsInvertible := by
  let C : ℤ → ℂ := discC (realSlice u)
  let R : ℤ → ℝ := discR (realSlice u)
  have hfam : IsolatingFamily38 (realSlice u) C R :=
    isolating_family38 (realSlice u) (realSlice_mem_gkW u)
  obtain ⟨c,N,hg,hsp⟩ := hfam
  let s : Lib.L2Seq := p5CompleteInput38 n (C n) (p3RealInclude38 n t)
  have hs : ∀ k : ℤ, (s k).im=0 :=
    p5Complete_real38 n (C n) (hg.1 n).2 (p3RealInclude38 n t)
      (fun m => Complex.ofReal_im (t m))
  have hown : ∀ m : P2Index38 n,
      Lib.sigmaOf (p2Extend38 n (p3RealInclude38 n t)) m.1 ∈ ball (C m.1) (R m.1) := by
    intro m
    have hm := (hsp.1 m.1).1 (ht m)
    simpa only [Lib.sigmaOf,p2Extend_at38,p3RealInclude_apply38,countingCenter38] using hm
  have hσ : ∀ k : ℤ, Lib.sigmaOf s k ∈ closedBall (C k) (R k) :=
    fun k => ball_subset_closedBall
      (p5Complete_original_discs38 n (p3RealInclude38 n t) C R c N hg hown k)
  have he := original_family_real_jacobian_inverse n u C R ⟨c,N,hg,hsp⟩ s hs hσ
  change ∃ e : P3RealSpace38 n ≃L[ℝ] P3RealSpace38 n,
    e.toContinuousLinearMap=fderiv ℝ (p3RealFn38 n u) t
  simpa only [s,p5Complete_restrict38,p3RealPart_include38] using he

end
end NlsGge.GK38.P4NumeratorVariation
