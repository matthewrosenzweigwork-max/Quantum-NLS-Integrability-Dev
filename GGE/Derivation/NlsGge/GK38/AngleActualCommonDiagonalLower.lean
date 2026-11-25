import NlsGge.GK38.AngleActualComplexDiagonalLower
import NlsGge.GK38.AngleCompactDiagonalLower

/-! Actual positive common complex DIAGONAL lower bound near the full real
gap cube. The sole remaining explicit analytic premise is genuine signed
OPnorm convergence, not the desired diagonal bound or an inverse oracle. -/
set_option autoImplicit false
open Set Metric Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem angleFullGap_local_diagonal_lower_of_signed_limit38 (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 (realSlice u) C R)
    (s : P6RealSpace38) (hs : s ∈ p5FullRealGapCube38 u)
    (hlimit : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ n : ℤ, (N : ℤ) < |n| →
        ‖p6PaddedJacobian38 n (realSlice u) (p6RealInclude38 s)-
          p6Qstar38 (realSlice u) (p6RealInclude38 s)‖ < ε) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ q : PotPair × Lib.L2Seq in
      nhds (realSlice u,p6RealInclude38 s), ∀ n m : ℤ,
        d ≤ ‖p6PaddedJacobian38 n q.1 q.2 (lp.single 2 m (1 : ℂ)) m‖ := by
  have hσ := P6FullJacobian.full_gap_original_family_placement u C R hfam s hs
  let p : PotPair × Lib.L2Seq := (realSlice u,p6RealInclude38 s)
  let T : ℤ → (PotPair × Lib.L2Seq) → Lib.L2Seq →L[ℂ] Lib.L2Seq :=
    fun n q => p6PaddedJacobian38 n q.1 q.2
  have hS := angleActual_Qstar_complex_diagonal_lower38 u C R hfam s hσ
  have hbase := fun n => angleActual_padded_complex_diagonal_lower38 u C R hfam s hσ n
  have hequi (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ q in nhds p, ∀ n : ℤ, ‖T n q-T n p‖ < ε := by
    simpa only [dist_eq_norm] using
      p6PaddedJacobian_equicontinuousAt38 p (realSlice_mem_gkW u) ε hε
  exact angleAllSigned_diagonal_lower_eventually38 T
    (p6Qstar38 (realSlice u) (p6RealInclude38 s)) p hS hbase hlimit hequi

theorem angleFullGap_common_complex_diagonal_lower_of_signed_limit38
    (u : PhysicalL2) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 (realSlice u) C R)
    (hlimit : ∀ s : P6RealSpace38, s ∈ p5FullRealGapCube38 u →
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
        ∀ n : ℤ, (N : ℤ) < |n| →
          ‖p6PaddedJacobian38 n (realSlice u) (p6RealInclude38 s)-
            p6Qstar38 (realSlice u) (p6RealInclude38 s)‖ < ε) :
    ∃ d : ℝ, ∃ U : Set PotPair, ∃ V : Set Lib.L2Seq,
      0 < d ∧ IsOpen U ∧ IsOpen V ∧ realSlice u ∈ U ∧ U ⊆ gkW ∧
      p6RealInclude38 '' p5FullRealGapCube38 u ⊆ V ∧
      ∀ φ ∈ U, ∀ s ∈ V, ∀ n m : ℤ,
        d ≤ ‖p6PaddedJacobian38 n φ s (lp.single 2 m (1 : ℂ)) m‖ := by
  let K : Set Lib.L2Seq := p6RealInclude38 '' p5FullRealGapCube38 u
  let T : ℤ → (PotPair × Lib.L2Seq) → Lib.L2Seq →L[ℂ] Lib.L2Seq :=
    fun n q => p6PaddedJacobian38 n q.1 q.2
  have hK : IsCompact K := (p5FullRealGapCube_isCompact38 u).image p6RealInclude38.continuous
  have hlocal : ∀ t ∈ K, ∃ d : ℝ, 0 < d ∧
      ∀ᶠ q in nhds (realSlice u,t), ∀ n m : ℤ,
        d ≤ ‖T n q (lp.single 2 m (1 : ℂ)) m‖ := by
    rintro t ⟨s,hs,rfl⟩
    exact angleFullGap_local_diagonal_lower_of_signed_limit38 u C R hfam s hs (hlimit s hs)
  exact angleAll_diagonal_lower_product_tube38 (realSlice u) gkW
    isOpen_gkW (realSlice_mem_gkW u) K hK T hlocal

end
end NlsGge.GK38
