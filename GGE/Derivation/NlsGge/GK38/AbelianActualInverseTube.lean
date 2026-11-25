import NlsGge.GK38.AbelianAllIndexInverseNeighborhood
import NlsGge.GK38.AbelianPaddedOriginalRealInverse
import NlsGge.GK38.AbelianPaddedJacobianEquicontinuity
import Mathlib.Topology.Compactness.Compact

/-! All inverse premises and equicontinuity are ACTUAL here. The remaining
explicit premise is the genuine signed operator-norm limit on the fixed gap
cube; its separate proof must be supplied before calling the tube concrete. -/
set_option autoImplicit false
open Set Metric Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem p6PaddedJacobian_equicontinuousAt38 (p : PotPair × Lib.L2Seq)
    (hp : p.1 ∈ gkW) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ q in 𝓝 p, ∀ n : ℤ,
      dist (p6PaddedJacobian38 n q.1 q.2) (p6PaddedJacobian38 n p.1 p.2) < ε := by
  obtain ⟨r,L,hr,hL,_hdom,hLip⟩ := p6PaddedJacobian_local_uniform_lipschitz38 p.1 hp p.2
  have hLp : 0 < L+1 := by linarith
  let δ : ℝ := min r (ε/(L+1))
  have hδ : 0 < δ := lt_min hr (div_pos hε hLp)
  filter_upwards [ball_mem_nhds p hδ] with q hq n
  have hqr : q ∈ ball p r := ball_subset_ball (min_le_left _ _) hq
  have hdist : ‖q-p‖ < ε/(L+1) :=
    (mem_ball_iff_norm.mp hq).trans_le (min_le_right _ _)
  have hmul : (L+1)*‖q-p‖ < ε := by
    have hh := mul_lt_mul_of_pos_left hdist hLp
    simpa only [mul_div_cancel₀ _ hLp.ne'] using hh
  rw [dist_eq_norm]
  exact (hLip n q hqr p (mem_ball_self hr)).trans_lt
    ((mul_le_mul_of_nonneg_right (by linarith : L ≤ L+1) (norm_nonneg _)).trans_lt hmul)

def p6AllIndexInverseLocus38 : Set (PotPair × Lib.L2Seq) :=
  interior ((gkW ×ˢ (univ : Set Lib.L2Seq)) ∩
    {p | ∀ n : ℤ, (p6PaddedJacobian38 n p.1 p.2).IsInvertible})

theorem p6FullGap_mem_inverseLocus_of_signed_limit38 (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 (realSlice u) C R)
    (s : P6RealSpace38) (hs : s ∈ p5FullRealGapCube38 u)
    (hlimit : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℤ, (N : ℤ) < |n| →
      ‖p6PaddedJacobian38 n (realSlice u) (p6RealInclude38 s)-
        p6Qstar38 (realSlice u) (p6RealInclude38 s)‖ < ε) :
    (realSlice u,p6RealInclude38 s) ∈ p6AllIndexInverseLocus38 := by
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
  have hinv := P6InverseNeighborhood.all_signed_invertible_eventually T
    (p6Qstar38 (realSlice u) (p6RealInclude38 s)) p hS
    (fun n => p6PaddedJacobian_full_gap_inverse38 n u C R hfam s hs) hcont
    (by simpa only [dist_eq_norm] using hlimit) hequi
  have hdom : gkW ×ˢ (univ : Set Lib.L2Seq) ∈ 𝓝 p :=
    (isOpen_gkW.prod isOpen_univ).mem_nhds ⟨realSlice_mem_gkW u,mem_univ _⟩
  exact mem_interior_iff_mem_nhds.mpr (inter_mem hdom hinv)

theorem p6InverseLocus_mem_implies_inverse38 (p : PotPair × Lib.L2Seq)
    (hp : p ∈ p6AllIndexInverseLocus38) (n : ℤ) :
    (p6PaddedJacobian38 n p.1 p.2).IsInvertible :=
  (interior_subset hp).2 n

theorem p6Abstract_compact_open_tube38 {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (W : Set X) (hW : IsOpen W) (hx : x ∈ W)
    (K : Set Y) (hK : IsCompact K) (O : Set (X × Y)) (hO : IsOpen O)
    (hKO : ∀ y ∈ K, (x,y) ∈ O) :
    ∃ U : Set X, ∃ V : Set Y,
      IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ U ⊆ W ∧ K ⊆ V ∧ U ×ˢ V ⊆ O := by
  have hsub : ({x} : Set X) ×ˢ K ⊆ O := by
    rintro ⟨a,b⟩ ⟨ha,hb⟩
    have hax : a=x := mem_singleton_iff.mp ha
    exact hax.symm ▸ hKO b hb
  obtain ⟨U,V,hU,hV,hbase,hKV,hUV⟩ :=
    generalized_tube_lemma (s := ({x} : Set X)) (t := K) (n := O)
      isCompact_singleton hK hO hsub
  exact ⟨U ∩ W,V,hU.inter hW,hV,⟨hbase (mem_singleton x),hx⟩,
    inter_subset_right,hKV,fun p hp => hUV ⟨hp.1.1,hp.2⟩⟩

theorem p6FullGap_complex_inverse_tube_of_signed_limit38 (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 (realSlice u) C R)
    (hlimit : ∀ s : P6RealSpace38, s ∈ p5FullRealGapCube38 u → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ n : ℤ, (N : ℤ) < |n| →
        ‖p6PaddedJacobian38 n (realSlice u) (p6RealInclude38 s)-
          p6Qstar38 (realSlice u) (p6RealInclude38 s)‖ < ε) :
    ∃ U : Set PotPair, ∃ V : Set Lib.L2Seq,
      IsOpen U ∧ IsOpen V ∧ realSlice u ∈ U ∧ U ⊆ gkW ∧
      p6RealInclude38 '' p5FullRealGapCube38 u ⊆ V ∧
      ∀ φ : PotPair, φ ∈ U → ∀ s : Lib.L2Seq, s ∈ V →
        ∀ n : ℤ, (p6PaddedJacobian38 n φ s).IsInvertible := by
  let K : Set Lib.L2Seq := p6RealInclude38 '' p5FullRealGapCube38 u
  have hK : IsCompact K := (p5FullRealGapCube_isCompact38 u).image p6RealInclude38.continuous
  have hKO : ∀ t ∈ K, (realSlice u,t) ∈ p6AllIndexInverseLocus38 := by
    rintro t ⟨s,hs,rfl⟩
    exact p6FullGap_mem_inverseLocus_of_signed_limit38 u C R hfam s hs (hlimit s hs)
  obtain ⟨U,V,hU,hV,hbase,hUW,hKV,hUV⟩ :=
    p6Abstract_compact_open_tube38 (realSlice u) gkW isOpen_gkW
      (realSlice_mem_gkW u) K hK p6AllIndexInverseLocus38 isOpen_interior hKO
  refine ⟨U,V,hU,hV,hbase,hUW,hKV,?_⟩
  intro φ hφ s hs n
  exact p6InverseLocus_mem_implies_inverse38 (φ,s) (hUV ⟨hφ,hs⟩) n


end
end NlsGge.GK38
