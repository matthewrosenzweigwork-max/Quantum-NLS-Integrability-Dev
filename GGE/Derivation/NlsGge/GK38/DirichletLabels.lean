import NlsGge.GK38.DirichletCounting

/-! # D1: canonical multiplicity-preserving Dirichlet labels

The least proved certified cutoff fixes the definition; all-cutoff compatibility
makes one local cutoff valid across the whole neighbourhood. -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem exists_dirichlet_cutoff38 (φ : PotPair) :
    ∃ N : ℕ, RootCountingAt38 (dirichletChar φ) 1 N := by
  obtain ⟨U, hU, N, hN⟩ := dirichlet_counting_lemma38 φ
  exact ⟨N, hN φ (mem_of_mem_nhds hU)⟩

def canonicalDirichletCutoff38 (φ : PotPair) : ℕ := by
  classical
  exact Nat.find (exists_dirichlet_cutoff38 φ)

theorem canonicalDirichletCutoff_spec38 (φ : PotPair) :
    RootCountingAt38 (dirichletChar φ) 1 (canonicalDirichletCutoff38 φ) := by
  classical
  exact Nat.find_spec (exists_dirichlet_cutoff38 φ)

def muSeq (φ : PotPair) : ℤ → ℂ :=
  criticalCandidate38 (dirichletChar φ) (canonicalDirichletCutoff38 φ)

theorem muSeq_eq_candidate38 (φ : PotPair) {N : ℕ}
    (h : RootCountingAt38 (dirichletChar φ) 1 N) :
    muSeq φ = criticalCandidate38 (dirichletChar φ) N :=
  criticalCandidate_cutoff_invariant38 (canonicalDirichletCutoff_spec38 φ) h

theorem muSeq_mono38 (φ : PotPair) {i j : ℤ} (hij : i ≤ j) :
    complexLexLE38 (muSeq φ i) (muSeq φ j) :=
  criticalCandidate_mono38 (canonicalDirichletCutoff_spec38 φ) hij

theorem muSeq_enumeration38 (φ : PotPair) : RootEnumeration38 (dirichletChar φ) (muSeq φ) :=
  criticalCandidate_enumeration38 (canonicalDirichletCutoff_spec38 φ)

theorem muSeq_root38 (φ : PotPair) (n : ℤ) : dirichletChar φ (muSeq φ n) = 0 :=
  (muSeq_enumeration38 φ).1 n

theorem muSeq_occurrence38 (φ : PotPair) (z : ℂ) :
    {n : ℤ | muSeq φ n = z}.Finite ∧
      Set.encard {n : ℤ | muSeq φ n = z} = analyticOrderAt (dirichletChar φ) z :=
  (muSeq_enumeration38 φ).2.2 z

/-- Identical free divisor multisets give identical generic q=1 candidates. -/
theorem dirichlet_free_candidates38 (N : ℕ) (n : ℤ) :
    criticalCandidate38 (dirichletChar 0) N n =
      criticalCandidate38 (deriv (discrim 0)) N n := by
  simp only [criticalCandidate38, centralRoots, smallRoots, dirichlet_free_multiset38]

theorem muSeq_zero38 (n : ℤ) : muSeq 0 n = countingCenter38 n := by
  rw [muSeq_eq_candidate38 0 (free_dirichlet_counting38 (N := 1) (by norm_num)),
    dirichlet_free_candidates38]
  rw [← lamDot_eq_candidate38 0 (free_critical_counting38 (N := 1) (by norm_num)), lamDot_zero38]

/-- Actual singleton far multisets and full central multiset, on one common neighbourhood. -/
theorem dirichlet_local_multisets38 (φ₀ : PotPair) :
  ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ ∃ N : ℕ, 0 < N ∧
    ∀ φ : PotPair, φ ∈ U →
      (∀ n : ℤ, (N : ℤ) < |n| → ({muSeq φ n} : Multiset ℂ) =
        Lib.zeroMultiset (dirichletChar φ) (ball (countingCenter38 n) (Real.pi / 4))) ∧
      ((Finset.Icc (-(N : ℤ)) (N : ℤ)).val.map (muSeq φ) =
        Lib.zeroMultiset (dirichletChar φ) (ball (0 : ℂ) (countingRadius38 N))) := by
  obtain ⟨U, hU, N, hN⟩ := dirichlet_counting_lemma38 φ₀
  refine ⟨U, hU, N, (hN φ₀ (mem_of_mem_nhds hU)).1, fun φ hφ => ?_⟩
  have h := hN φ hφ
  rw [muSeq_eq_candidate38 φ h]
  exact ⟨fun n hn => criticalCandidate_small_multiset38 h hn,
    criticalCandidate_central_multiset38 h⟩

end
end NlsGge.GK38
