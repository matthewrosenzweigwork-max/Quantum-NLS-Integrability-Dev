import NlsGge.GK38.AbelianRatioCutBound

/-! UNCOMPILED compact-input ratio bound. The finite cover is taken over a
GENUINELY compact set of full inputs, not an infinite-dimensional open ball. -/
set_option autoImplicit false
open Set Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem p6OmittedRatio_compact_input_bound38 (φ : PotPair) (hφ : φ ∈ gkW)
    (K : Set Lib.L2Seq) (hK : IsCompact K) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ s ∈ K, ∀ m : ℤ,
      ∀ z ∈ segment ℝ (lamMinus φ m) (lamPlus φ m),
        ‖p2OmittedRatio38 m ((φ,s),z)‖ ≤ H := by
  classical
  have hlocal (s₀ : Lib.L2Seq) :
      ∃ V : Set Lib.L2Seq, V ∈ 𝓝 s₀ ∧ ∃ H : ℝ, 0 ≤ H ∧ ∀ s ∈ V,
        ∀ m : ℤ, ∀ z ∈ segment ℝ (lamMinus φ m) (lamPlus φ m),
          ‖p2OmittedRatio38 m ((φ,s),z)‖ ≤ H := by
    obtain ⟨U,hU,_hUW,V,hV,H,hH,hb⟩ := p2OmittedRatio_all_cut_bound38 φ hφ s₀
    exact ⟨V,hV,H,hH,fun s hs m z hz => hb φ (mem_of_mem_nhds hU) s hs m z hz⟩
  choose V hV H hH hb using hlocal
  obtain ⟨T,_hTK,hcover⟩ := hK.elim_nhds_subcover V (fun s _hs => hV s)
  refine ⟨∑ s ∈ T, H s,Finset.sum_nonneg (fun s _ => hH s),?_⟩
  intro s hs m z hz
  obtain ⟨t,ht⟩ := mem_iUnion.mp (hcover hs)
  obtain ⟨htT,hsV⟩ := mem_iUnion.mp ht
  exact (hb t s hsV m z hz).trans (Finset.single_le_sum (fun t _ => hH t) htT)

end
end NlsGge.GK38
