import NlsGge.GK38.IsolatingPersistence
import NlsGge.GK38.IsolatingRealSpectral
import NlsGge.GK38.IsolatingTopology

/-! GK I.12: actual certified real balls and the connected open neighbourhood.
Local circle families are fixed; the global selectors are only pointwise choices. -/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem certified_real_ball_exists38 (u : PhysicalL2) : ∃ ρ : ℝ, CertifiedRealBall38 u ρ := by
  obtain ⟨C, R, hfamily⟩ := real_center_spectral38 u
  obtain ⟨ρ, hρ, c, N, hgeom, hspec⟩ := fixed_family_persistence38 (realSlice u) C R hfamily
  exact ⟨ρ, hρ, C, R, c, N, hgeom, hspec⟩

theorem realSlice_mem_gkW (u : PhysicalL2) : realSlice u ∈ gkW :=
  realSlice_mem_gkW_of_certified38 certified_real_ball_exists38 u

theorem isPreconnected_gkW : IsPreconnected gkW :=
  isPreconnected_gkW_of_certified38 certified_real_ball_exists38

theorem isConnected_gkW38 : IsConnected gkW :=
  isConnected_gkW_of_certified38 certified_real_ball_exists38

theorem isolating_aux_simple38 (φ : PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfamily : IsolatingFamily38 φ C R) (n : ℤ) :
    analyticOrderAt (dirichletChar φ) (muSeq φ n) = 1 ∧
    analyticOrderAt (neumannChar38 φ) (nuSeq38 φ n) = 1 ∧
    analyticOrderAt (deriv (discrim φ)) (lamDot φ n) = 1 := by
  obtain ⟨c, N₀, hgeom, hspec⟩ := hfamily
  obtain ⟨U, hU, N, _, hcount⟩ := prescribed_common_counting38 φ 0
  obtain ⟨_, hd, hm, hn⟩ := hcount φ (mem_of_mem_nhds hU)
  have hsμ := (hspec.1 n).2.2.2.2.2.1
  have hsν := (hspec.1 n).2.2.2.2.2.2.1
  have hsc := (hspec.1 n).2.2.2.2.2.2.2.1
  refine ⟨counting_nodup_order_one38 hm (C n) (R n) (hsμ ▸ Multiset.nodup_singleton _) ?_,
    counting_nodup_order_one38 hn (C n) (R n) (hsν ▸ Multiset.nodup_singleton _) ?_,
    counting_nodup_order_one38 hd (C n) (R n) (hsc ▸ Multiset.nodup_singleton _) ?_⟩
  · rw [← hsμ]
    simp
  · rw [← hsν]
    simp
  · rw [← hsc]
    simp

theorem isolating_final_contract38 :
    IsOpen gkW ∧ IsPreconnected gkW ∧ (∀ u : PhysicalL2, realSlice u ∈ gkW) ∧
    (∀ φ ∈ gkW, ∃ V : Set PotPair, V ∈ 𝓝 φ ∧ V ⊆ gkW ∧ IsOpen V ∧ IsConnected V ∧
      ∃ C : ℤ → ℂ, ∃ R : ℤ → ℝ, ∃ c : ℝ, ∃ N : ℕ,
        IsolatingGeometry38 C R c N ∧ ∀ ψ ∈ V, IsolatingSpectral38 ψ C R) ∧
    (∃ C : PotPair → ℤ → ℂ, ∃ R : PotPair → ℤ → ℝ,
      ∀ φ ∈ gkW, IsolatingFamily38 φ (C φ) (R φ)) :=
  ⟨isOpen_gkW, isPreconnected_gkW, realSlice_mem_gkW, local_isolatingFamily_common38,
    discC, discR, isolating_family38⟩

end
end NlsGge.GK38
