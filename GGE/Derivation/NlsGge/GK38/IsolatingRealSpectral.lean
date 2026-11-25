import NlsGge.GK38.IsolatingRealGeometry
import NlsGge.GK38.IsolatingRootMultisets

/-! Complete actual real-center spectral certificates, retaining all four
zero multisets, all boundaries and exhaustive coverage, including collapsed gaps. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem real_periodic_label_orders38 (u : PhysicalL2) (n : ℤ) :
    analyticOrderAt (perChar (realSlice u)) (lamMinus (realSlice u) n) =
      (if lamMinus (realSlice u) n = lamPlus (realSlice u) n then 2 else 1) ∧
    analyticOrderAt (perChar (realSlice u)) (lamPlus (realSlice u) n) =
      (if lamMinus (realSlice u) n = lamPlus (realSlice u) n then 2 else 1) := by
  rw [(lamPlus_real u n).2, (lamPlus_real u n).1, order_at_gapEnd, order_at_gapUpper38]
  by_cases hh : actualGapLowerAllE02_38 u n = actualGapUpperAllE02_38 u n
  · simp [hh]
  · have hlt := lt_of_le_of_ne (gap_endpoint_levels38 u n).1 hh
    simp [hh, hlt]

theorem real_spectral_of_gap_circles38 (u : PhysicalL2) (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hgeom : IsolatingGeometry38 C R c N)
    (hgap : ∀ n : ℤ, Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) ⊆
      {x : ℝ | (x : ℂ) ∈ ball (C n) (R n)}) : IsolatingSpectral38 (realSlice u) C R := by
  have hA : ∀ n : ℤ, lamMinus (realSlice u) n ∈ ball (C n) (R n) := by
    intro n
    rw [(lamPlus_real u n).2]
    exact hgap n ⟨le_rfl, (gap_endpoint_levels38 u n).1⟩
  have hB : ∀ n : ℤ, lamPlus (realSlice u) n ∈ ball (C n) (R n) := by
    intro n
    rw [(lamPlus_real u n).1]
    exact hgap n ⟨(gap_endpoint_levels38 u n).1, le_rfl⟩
  have hμ : ∀ n : ℤ, muSeq (realSlice u) n ∈ ball (C n) (R n) := by
    intro n
    rw [muSeq_eq_gkMu38]
    exact hgap n (gkMu_mem_gap38 u n)
  have hν : ∀ n : ℤ, nuSeq38 (realSlice u) n ∈ ball (C n) (R n) := by
    intro n
    have hv := nuSeq38_real_gap_simple u n
    have he : nuSeq38 (realSlice u) n = ((nuSeq38 (realSlice u) n).re : ℂ) :=
      Complex.ext (by rfl) (by simpa only [Complex.ofReal_im] using hv.1)
    rw [he]
    exact hgap n ⟨hv.2.1, hv.2.2.1⟩
  have hcrit : ∀ n : ℤ, lamDot (realSlice u) n ∈ ball (C n) (R n) := by
    intro n
    have hv := lamDot_between u n
    have he : lamDot (realSlice u) n = ((lamDot (realSlice u) n).re : ℂ) :=
      Complex.ext (by rfl) (by simpa only [Complex.ofReal_im] using hv.1)
    rw [he]
    exact hgap n ⟨hv.2.1, hv.2.2⟩
  have hperLabels : ∀ z : ℂ, perChar (realSlice u) z = 0 →
      ∃ n : ℤ, z = lamMinus (realSlice u) n ∨ z = lamPlus (realSlice u) n := by
    intro z hz
    obtain ⟨n, he | he⟩ := (perChar_zero_iff u z).mp hz
    · exact ⟨n, Or.inl (he.trans (lamPlus_real u n).2.symm)⟩
    · exact ⟨n, Or.inr (he.trans (lamPlus_real u n).1.symm)⟩
  have hperCover : ∀ z : ℂ, perChar (realSlice u) z = 0 → ∃ n : ℤ, z ∈ ball (C n) (R n) := by
    intro z hz
    obtain ⟨n, he | he⟩ := hperLabels z hz
    · exact ⟨n, he.symm ▸ hA n⟩
    · exact ⟨n, he.symm ▸ hB n⟩
  have hmuCover : ∀ z : ℂ, dirichletChar (realSlice u) z = 0 → ∃ n : ℤ, z ∈ ball (C n) (R n) := by
    intro z hz
    obtain ⟨n, hn⟩ := ((muSeq_enumeration38 (realSlice u)).2.1 z).mp hz
    exact ⟨n, hn ▸ hμ n⟩
  have hnuCover : ∀ z : ℂ, neumannChar38 (realSlice u) z = 0 → ∃ n : ℤ, z ∈ ball (C n) (R n) := by
    intro z hz
    obtain ⟨n, hn⟩ := ((nuSeq38_enumeration (realSlice u)).2.1 z).mp hz
    exact ⟨n, hn ▸ hν n⟩
  have hcritCover : ∀ z : ℂ, deriv (discrim (realSlice u)) z = 0 → ∃ n : ℤ, z ∈ ball (C n) (R n) := by
    intro z hz
    obtain ⟨n, hn⟩ := ((lamDot_enumeration38 (realSlice u)).2.1 z).mp hz
    exact ⟨n, hn ▸ hcrit n⟩
  have hpPair := isolating_pair_multiset38 (perChar (realSlice u)) (lamMinus (realSlice u))
    (lamPlus (realSlice u)) C R c N (analyticOnNhd_perChar_z _) hgeom hA hB hperLabels
    (fun n => (real_periodic_label_orders38 u n).1) (fun n => (real_periodic_label_orders38 u n).2)
  have hdSingle := isolating_singleton_multiset38 (dirichletChar (realSlice u)) (muSeq (realSlice u))
    C R c N (analyticOnNhd_dirichletChar_z _) hgeom hμ
    (fun z hz => ((muSeq_enumeration38 (realSlice u)).2.1 z).mp hz) (muSeq_simple38 u)
  have hnSingle := isolating_singleton_multiset38 (neumannChar38 (realSlice u)) (nuSeq38 (realSlice u))
    C R c N (analyticOnNhd_neumannChar38_z _) hgeom hν
    (fun z hz => ((nuSeq38_enumeration (realSlice u)).2.1 z).mp hz)
    (fun n => (nuSeq38_real_gap_simple u n).2.2.2)
  have hcSingle := isolating_singleton_multiset38 (deriv (discrim (realSlice u))) (lamDot (realSlice u))
    C R c N (analyticOnNhd_discrimDeriv38 _) hgeom hcrit
    (fun z hz => ((lamDot_enumeration38 (realSlice u)).2.1 z).mp hz) (lamDot_simple38 u)
  refine ⟨fun n => ⟨(convex_ball (C n) (R n)).segment_subset (hA n) (hB n),
    hμ n, hν n, hcrit n, hpPair n, hdSingle n, hnSingle n, hcSingle n, ?_, ?_, ?_, ?_, ?_⟩,
    hperCover, hmuCover, hnuCover, hcritCover⟩
  · rw [← hpPair n]
    simp
  · rw [← hdSingle n]
    simp
  · rw [← hnSingle n]
    simp
  · rw [← hcSingle n]
    simp
  · intro z hz
    exact ⟨isolating_boundary_ne38 _ C R c N hgeom hperCover n z hz,
      isolating_boundary_ne38 _ C R c N hgeom hmuCover n z hz,
      isolating_boundary_ne38 _ C R c N hgeom hnuCover n z hz,
      isolating_boundary_ne38 _ C R c N hgeom hcritCover n z hz⟩

theorem real_center_spectral38 (u : PhysicalL2) :
    ∃ C : ℤ → ℂ, ∃ R : ℤ → ℝ, IsolatingFamily38 (realSlice u) C R := by
  obtain ⟨C, R, c, N, hgeom, hgap⟩ := real_center_geometry38 u
  exact ⟨C, R, c, N, hgeom, real_spectral_of_gap_circles38 u C R c N hgeom hgap⟩

end
end NlsGge.GK38
