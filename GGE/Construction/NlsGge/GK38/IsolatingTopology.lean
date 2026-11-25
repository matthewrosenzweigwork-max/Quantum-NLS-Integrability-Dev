import NlsGge.GK38.IsolatingGeometry

/-! Topology and local fixed-family extraction for the exact certified-ball union.
Real inclusion and global connectedness are assembled after certified-ball existence. -/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem isOpen_gkW : IsOpen gkW := by
  apply isOpen_iff_mem_nhds.mpr
  rintro φ ⟨u, ρ, hcert, hφ⟩
  exact Filter.mem_of_superset (isOpen_ball.mem_nhds hφ) (fun ψ hψ => ⟨u, ρ, hcert, hψ⟩)

theorem isolating_anchored_union38 (A : Set PotPair) (B : PhysicalL2 → ℝ → Set PotPair)
    (P : PhysicalL2 → ℝ → Prop) (hA : IsPreconnected A)
    (hB : ∀ u ρ, P u ρ → IsPreconnected (B u ρ))
    (hmeet : ∀ u ρ, P u ρ → (A ∩ B u ρ).Nonempty)
    (hcover : A ⊆ {φ | ∃ u ρ, P u ρ ∧ φ ∈ B u ρ}) :
    IsPreconnected {φ | ∃ u ρ, P u ρ ∧ φ ∈ B u ρ} := by
  apply isPreconnected_of_forall_pair
  rintro x ⟨u, ρ, hu, hx⟩ y ⟨v, σ, hv, hy⟩
  have h₁ := hA.union' (hmeet u ρ hu) (hB u ρ hu)
  have h₂ := h₁.union' ((hmeet v σ hv).mono (fun z hz => ⟨Or.inl hz.1, hz.2⟩)) (hB v σ hv)
  refine ⟨(A ∪ B u ρ) ∪ B v σ, ?_, Or.inl (Or.inr hx), Or.inr hy, h₂⟩
  intro z hz
  rcases hz with (hz | hz) | hz
  · exact hcover hz
  · exact ⟨u, ρ, hu, hz⟩
  · exact ⟨v, σ, hv, hz⟩

theorem realSlice_mem_gkW_of_certified38
    (hcert : ∀ u : PhysicalL2, ∃ ρ : ℝ, CertifiedRealBall38 u ρ) (u : PhysicalL2) : realSlice u ∈ gkW := by
  obtain ⟨ρ, hρ⟩ := hcert u
  exact ⟨u, ρ, hρ, mem_ball_self hρ.1⟩

theorem isPreconnected_gkW_of_certified38
    (hcert : ∀ u : PhysicalL2, ∃ ρ : ℝ, CertifiedRealBall38 u ρ) : IsPreconnected gkW := by
  apply isolating_anchored_union38 (range realSlice)
    (fun u ρ => ball (realSlice u) ρ) CertifiedRealBall38
  · exact isPreconnected_range continuous_realSlice
  · intro u ρ _
    exact isPreconnected_ball
  · intro u ρ hρ
    exact ⟨realSlice u, mem_range_self u, mem_ball_self hρ.1⟩
  · rintro φ ⟨u, rfl⟩
    exact realSlice_mem_gkW_of_certified38 hcert u

theorem isConnected_gkW_of_certified38
    (hcert : ∀ u : PhysicalL2, ∃ ρ : ℝ, CertifiedRealBall38 u ρ) : IsConnected gkW :=
  ⟨⟨realSlice 0, realSlice_mem_gkW_of_certified38 hcert 0⟩, isPreconnected_gkW_of_certified38 hcert⟩

theorem local_isolatingFamily_common38 (φ : PotPair) (hφ : φ ∈ gkW) :
    ∃ V : Set PotPair, V ∈ 𝓝 φ ∧ V ⊆ gkW ∧ IsOpen V ∧ IsConnected V ∧
      ∃ C : ℤ → ℂ, ∃ R : ℤ → ℝ, ∃ c : ℝ, ∃ N : ℕ,
        IsolatingGeometry38 C R c N ∧ ∀ ψ ∈ V, IsolatingSpectral38 ψ C R := by
  obtain ⟨u, ρ, hcert, hφball⟩ := hφ
  obtain ⟨hρ, C, R, c, N, hgeom, hspec⟩ := hcert
  let δ : ℝ := (ρ - dist φ (realSlice u)) / 2
  have hδ : 0 < δ := by dsimp only [δ]; linarith [mem_ball.mp hφball]
  have hsub : ball φ δ ⊆ ball (realSlice u) ρ := by
    intro ψ hψ
    have hh := dist_triangle ψ φ (realSlice u)
    rw [mem_ball] at hψ ⊢
    dsimp only [δ] at hψ
    linarith [mem_ball.mp hφball]
  refine ⟨ball φ δ, ball_mem_nhds φ hδ, ?_, isOpen_ball, isConnected_ball hδ,
    C, R, c, N, hgeom, fun ψ hψ => hspec ψ (hsub hψ)⟩
  intro ψ hψ
  exact ⟨u, ρ, ⟨hρ, C, R, c, N, hgeom, hspec⟩, hsub hψ⟩

theorem local_isolatingFamily (φ : PotPair) (hφ : φ ∈ gkW) :
    ∃ V : Set PotPair, V ∈ 𝓝 φ ∧ V ⊆ gkW ∧ IsOpen V ∧ IsConnected V ∧
      ∃ C : ℤ → ℂ, ∃ R : ℤ → ℝ, ∀ ψ ∈ V, IsolatingFamily38 ψ C R := by
  obtain ⟨V, hV, hsub, hopen, hconn, C, R, c, N, hgeom, hspec⟩ := local_isolatingFamily_common38 φ hφ
  exact ⟨V, hV, hsub, hopen, hconn, C, R, fun ψ hψ => ⟨c, N, hgeom, hspec ψ hψ⟩⟩

theorem exists_isolating_family38 (φ : PotPair) (hφ : φ ∈ gkW) :
    ∃ C : ℤ → ℂ, ∃ R : ℤ → ℝ, IsolatingFamily38 φ C R := by
  obtain ⟨V, hV, _, _, _, C, R, hspec⟩ := local_isolatingFamily φ hφ
  exact ⟨C, R, hspec φ (mem_of_mem_nhds hV)⟩

def discC (φ : PotPair) : ℤ → ℂ := by
  classical
  exact if hφ : φ ∈ gkW then (exists_isolating_family38 φ hφ).choose else countingCenter38

def discR (φ : PotPair) : ℤ → ℝ := by
  classical
  exact if hφ : φ ∈ gkW then (exists_isolating_family38 φ hφ).choose_spec.choose else fun _ => Real.pi / 4

def discU (φ : PotPair) (n : ℤ) : Set ℂ := ball (discC φ n) (discR φ n)

theorem isolating_family38 (φ : PotPair) (hφ : φ ∈ gkW) : IsolatingFamily38 φ (discC φ) (discR φ) := by
  simp only [discC, discR, dite_eq_left hφ]
  exact (exists_isolating_family38 φ hφ).choose_spec.choose_spec

theorem isolating (φ : PotPair) (hφ : φ ∈ gkW) :
    Pairwise (fun m n => Disjoint (discU φ m) (discU φ n)) ∧
      (∀ n : ℤ, (Lib.zeroMultiset (perChar φ) (discU φ n)).card = 2) ∧
      (∀ z : ℂ, perChar φ z = 0 → ∃ n : ℤ, z ∈ discU φ n) := by
  obtain ⟨c, N, hgeom, hspec⟩ := isolating_family38 φ hφ
  exact ⟨isolating_geometry_disjoint38 _ _ c N hgeom,
    fun n => (hspec.1 n).2.2.2.2.2.2.2.2.1, hspec.2.1⟩

end
end NlsGge.GK38
