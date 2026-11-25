import NlsGge.GK38.AbelianCompactUniformInverseBound
import NlsGge.GK38.AbelianFullCompactInverseBound

/-! Actual common inverse-norm tube with the genuine signed operator limit
as the SOLE remaining analytic premise. Its concrete realization is separate. -/
set_option autoImplicit false
open Set Metric Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem p6FullGap_local_inverse_bound_of_signed_limit38 (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 (realSlice u) C R)
    (s : P6RealSpace38) (hs : s ∈ p5FullRealGapCube38 u)
    (hlimit : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℤ, (N : ℤ) < |n| →
      ‖p6PaddedJacobian38 n (realSlice u) (p6RealInclude38 s)-
        p6Qstar38 (realSlice u) (p6RealInclude38 s)‖ < ε) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ q : PotPair × Lib.L2Seq in
      𝓝 (realSlice u,p6RealInclude38 s), ∀ n : ℤ,
      (p6PaddedJacobian38 n q.1 q.2).IsInvertible ∧
      ‖(p6PaddedJacobian38 n q.1 q.2).inverse‖ ≤ B := by
  let p : PotPair × Lib.L2Seq := (realSlice u,p6RealInclude38 s)
  let T : ℤ → (PotPair × Lib.L2Seq) → Lib.L2Seq →L[ℂ] Lib.L2Seq :=
    fun n q => p6PaddedJacobian38 n q.1 q.2
  have hequi := fun ε hε => p6PaddedJacobian_equicontinuousAt38 p (realSlice_mem_gkW u) ε hε
  have hcont (n : ℤ) : ContinuousAt (T n) p := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hequi ε hε] with q hq
    exact hq n
  have hS : (p6Qstar38 (realSlice u) (p6RealInclude38 s)).IsInvertible :=
    P6FullJacobian.original_family_complex_Qstar_inverse u C R hfam s
      (P6FullJacobian.full_gap_original_family_placement u C R hfam s hs)
  exact P6InverseNeighborhood.all_signed_inverse_bounded_eventually T
    (p6Qstar38 (realSlice u) (p6RealInclude38 s)) p hS
    (fun n => p6PaddedJacobian_full_gap_inverse38 n u C R hfam s hs) hcont
    (by simpa only [dist_eq_norm] using hlimit) hequi

theorem p6FullGap_complex_uniform_inverse_bound_tube_of_signed_limit38 (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 (realSlice u) C R)
    (hlimit : ∀ s : P6RealSpace38, s ∈ p5FullRealGapCube38 u → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ n : ℤ, (N : ℤ) < |n| →
        ‖p6PaddedJacobian38 n (realSlice u) (p6RealInclude38 s)-
          p6Qstar38 (realSlice u) (p6RealInclude38 s)‖ < ε) :
    ∃ B : ℝ, ∃ U : Set PotPair, ∃ V : Set Lib.L2Seq,
      0 < B ∧ IsOpen U ∧ IsOpen V ∧ realSlice u ∈ U ∧ U ⊆ gkW ∧
      p6RealInclude38 '' p5FullRealGapCube38 u ⊆ V ∧
      ∀ φ : PotPair, φ ∈ U → ∀ s : Lib.L2Seq, s ∈ V →
        ∀ n : ℤ, (p6PaddedJacobian38 n φ s).IsInvertible ∧
          ‖(p6PaddedJacobian38 n φ s).inverse‖ ≤ B := by
  let K : Set Lib.L2Seq := p6RealInclude38 '' p5FullRealGapCube38 u
  let T : ℤ → (PotPair × Lib.L2Seq) → Lib.L2Seq →L[ℂ] Lib.L2Seq :=
    fun n q => p6PaddedJacobian38 n q.1 q.2
  have hK : IsCompact K := (p5FullRealGapCube_isCompact38 u).image p6RealInclude38.continuous
  have hlocal : ∀ t ∈ K, ∃ B : ℝ, 0 < B ∧
      ∀ᶠ q in 𝓝 (realSlice u,t), ∀ n : ℤ,
        (T n q).IsInvertible ∧ ‖(T n q).inverse‖ ≤ B := by
    rintro t ⟨s,hs,rfl⟩
    exact p6FullGap_local_inverse_bound_of_signed_limit38 u C R hfam s hs (hlimit s hs)
  exact P6InverseNeighborhood.all_index_inverse_bound_product_tube (realSlice u) gkW
    isOpen_gkW (realSlice_mem_gkW u) K hK T hlocal

end
end NlsGge.GK38
