import Armstrong.Work.RawBetaMagnitudeNearestProof
import Armstrong.Work.RawBetaMagnitudeInverseGeometry

/-!
# Working proof of the GK15.1 inverse-distance consequence

This consumes the working sharp nearest-endpoint theorem and the already accepted
elementary inverse-geometry theorem. It remains in Work/ and does not seal either
frozen anchor.
-/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem gk151_inverseDistance_bound_working38
    (W : Set PotPair) (hWopen : IsOpen W)
    (hreal : range realSlice ⊆ W) (hWgk : W ⊆ gkW)
    (F : (n : ℤ) → PotPair → P2Space38 n)
    (hFanalytic : ∀ n : ℤ, AnalyticOnNhd ℂ (F n) W)
    (hFn : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W →
      p2Fn38 n (phi, F n phi) = 0)
    (hFinv : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W →
      (fderiv ℂ (fun y : P2Space38 n => p2Fn38 n (phi,y))
        (F n phi)).IsInvertible)
    (hperiod : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W → ∀ m : ℤ,
      abelianPeriod38 m phi (p6PsiNumerator38 n (F n) phi) =
        if m = n then 2 * (Real.pi : ℂ) else 0)
    (hFreal : ∀ (n : ℤ) (u : PhysicalL2), ∃ t : P3RealSpace38 n,
      t ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u t = 0 ∧
        F n (realSlice u) = p3RealInclude38 n t) :
    ∃ Wbeta : Set PotPair,
      IsOpen Wbeta ∧ range realSlice ⊆ Wbeta ∧ Wbeta ⊆ W ∧
      ∀ phi : PotPair, phi ∈ Wbeta →
        ∃ V : Set PotPair, ∃ C : ℝ,
          IsOpen V ∧ phi ∈ V ∧ V ⊆ Wbeta ∧ 0 < C ∧
          ∀ psi : {chi : PotPair // chi ∈ W}, psi.1 ∈ V →
            ∀ n m : ℤ, ∀ hmn : m ≠ n,
              ‖gkSourceBeta38 W hWopen hreal hWgk F
                hFanalytic hFn hperiod n m hmn psi‖ <=
              C * (‖lamPlus psi.1 m - lamMinus psi.1 m‖ +
                ‖muSeq psi.1 m - tauN psi.1 m‖) * Lib.c3w n m := by
  obtain ⟨Wbeta, hWbetaOpen, hrealBeta, hbetaW, hnear⟩ :=
    gk151_nearestEndpoint_bound_working38
      W hWopen hreal hWgk F hFanalytic hFn hFinv hperiod hFreal
  refine ⟨Wbeta, hWbetaOpen, hrealBeta, hbetaW, ?_⟩
  intro phi hphi
  obtain ⟨V, C, hV, hphiV, hVW, hC, hbound⟩ := hnear phi hphi
  refine ⟨V, C, hV, hphiV, hVW, hC, ?_⟩
  intro psi hpsi n m hmn
  have hsharp := hbound psi hpsi n m hmn
  have hgeom := raw_beta_magnitude_inverse_geometry38
    (lamMinus psi.1 m) (lamPlus psi.1 m) (muSeq psi.1 m)
  have htau := tauN_value38 psi.1 (hWgk psi.2) m
  have hgeom' :
      Real.sqrt (‖lamPlus psi.1 m - lamMinus psi.1 m‖ +
        min ‖muSeq psi.1 m - lamMinus psi.1 m‖
          ‖muSeq psi.1 m - lamPlus psi.1 m‖) *
        Real.sqrt (min ‖muSeq psi.1 m - lamMinus psi.1 m‖
          ‖muSeq psi.1 m - lamPlus psi.1 m‖) <=
      ‖lamPlus psi.1 m - lamMinus psi.1 m‖ +
        ‖muSeq psi.1 m - tauN psi.1 m‖ := by
    rw [htau]
    simpa only [norm_sub_rev (lamMinus psi.1 m) (lamPlus psi.1 m), add_comm] using hgeom
  have hs1 := mul_le_mul_of_nonneg_left hgeom' hC.le
  have hs2 := mul_le_mul_of_nonneg_right hs1 (Lib.c3w_nonneg n m)
  exact hsharp.trans (by
    simpa only [mul_assoc] using hs2)

end
end NlsGge.GK38
