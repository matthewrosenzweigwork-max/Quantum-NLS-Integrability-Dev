import NlsGge.GK38.AngleActualNormalizedQuadraticQuotients
import NlsGge.GK38.AbelianGlobalLocalNormalizedBallAgreement

/-! Earned local quadratic quotient mass transfers to ANY actual globally
normalized omitted branch by actual inverse continuation on ONE EXPLICIT
common ball chosen BEFORE ALL signed n. Full nth completions are not compared. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem angleGlobal_normalized_local_quadratic_quotient_lp38
    (W : Set PotPair) (hW : IsOpen W) (hWW : W ⊆ gkW)
    (F : (n : ℤ) → PotPair → P2Space38 n)
    (hFa : ∀ n, AnalyticOnNhd ℂ (F n) W)
    (hFspec : ∀ n : ℤ, ∀ φ ∈ W, p2Fn38 n (φ,F n φ)=0 ∧
      (fderiv ℂ (fun y : P2Space38 n => p2Fn38 n (φ,y)) (F n φ)).IsInvertible)
    (hFreal : ∀ n : ℤ, ∀ u : PhysicalL2, ∃ t : P3RealSpace38 n,
      t ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u t=0 ∧
      F n (realSlice u)=p3RealInclude38 n t)
    (u : PhysicalL2) (huW : realSlice u ∈ W)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 (realSlice u) C R) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 < B ∧ ball (realSlice u) ρ ⊆ W ∧
      ∀ n : ℤ, ∀ φ ∈ ball (realSlice u) ρ,
        ∃ A : P2Space38 n,
          (∀ m : P2Index38 n,
            A m=(countingCenter38 m.1+F n φ m-tauN φ m.1)/gamma2 φ m.1) ∧
          Summable (fun m : P2Index38 n => ‖A m‖^2) ∧
          (∑' m : P2Index38 n,‖A m‖^2) ≤ B ∧
          ∀ m : P2Index38 n,
            countingCenter38 m.1+F n φ m=tauN φ m.1+gamma2 φ m.1*A m := by
  obtain ⟨d,B,hd,hB,_hdW,hbranches⟩ :=
    angleActual_normalized_common_quadratic_quotient_lp38 u C R hfam
  obtain ⟨a,ha,haW⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds huW)
  let ρ : ℝ := min a d
  have hρ : 0 < ρ := lt_min ha hd
  have hρd : ρ ≤ d := min_le_right _ _
  have hρW : ball (realSlice u) ρ ⊆ W :=
    (ball_subset_ball (min_le_left _ _)).trans haW
  have hsubd : ball (realSlice u) ρ ⊆ ball (realSlice u) d := ball_subset_ball hρd
  refine ⟨ρ,B,hρ,hB,hρW,?_⟩
  intro n
  obtain ⟨t,ht,htz,S,hSbase,hSan,hSspec⟩ := hbranches n
  obtain ⟨q,hq,hqz,hFbase⟩ := hFreal n u
  have hSq : p2Restrict38 n (S (realSlice u))=p3RealInclude38 n t := by
    rw [hSbase,p6GapCubeComplete_restrict38]
  have heq := p6Global_local_normalized_ball_agreement38 n W hW hWW (F n)
    (hFa n).continuousOn (fun φ hφ => (hFspec n φ hφ).1)
    (fun φ hφ => (hFspec n φ hφ).2) u huW d S hSan.continuousOn
    (fun φ hφ => (hSspec φ hφ).1) ρ hρ hρd hρW q t ⟨hq,hqz⟩ ⟨ht,htz⟩ hFbase hSq
  intro φ hφ
  obtain ⟨A,hA,hAs,hAB,hroot⟩ := (hSspec φ (hsubd hφ)).2.2
  have hcoord (m : P2Index38 n) :
      Lib.sigmaOf (S φ) m.1=countingCenter38 m.1+F n φ m := by
    rw [heq φ hφ,p2Restrict_apply38]
    rfl
  refine ⟨A,?_,hAs,hAB,?_⟩
  · intro m
    rw [← hcoord m]
    exact hA m
  · intro m
    rw [← hcoord m]
    exact hroot m

end
end NlsGge.GK38
