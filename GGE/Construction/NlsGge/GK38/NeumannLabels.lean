import NlsGge.GK38.NeumannChar
import NlsGge.GK38.DirichletRealGapIndex
import NlsGge.GK38.RealTypeMultiplicity

/-! GK I.5/I.7: actual canonical Neumann labels and same-gap transport. -/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

def nuSeq38 (φ : PotPair) (n : ℤ) : ℂ := muSeq (-φ) n

theorem nuSeq38_enumeration (φ : PotPair) : RootEnumeration38 (neumannChar38 φ) (nuSeq38 φ) := by
  change RootEnumeration38 (neumannChar38 φ) (muSeq (-φ))
  rw [neumannChar38_fun_eq_dirichlet_neg]
  exact muSeq_enumeration38 (-φ)

theorem nuSeq38_root (φ : PotPair) (n : ℤ) : neumannChar38 φ (nuSeq38 φ n) = 0 :=
  (nuSeq38_enumeration φ).1 n

theorem nuSeq38_occurrence (φ : PotPair) (z : ℂ) :
    {n : ℤ | nuSeq38 φ n = z}.Finite ∧
      Set.encard {n : ℤ | nuSeq38 φ n = z} = analyticOrderAt (neumannChar38 φ) z :=
  (nuSeq38_enumeration φ).2.2 z

theorem neumann_counting_iff38 (φ : PotPair) (N : ℕ) :
    RootCountingAt38 (neumannChar38 φ) 1 N ↔ RootCountingAt38 (dirichletChar (-φ)) 1 N := by
  rw [neumannChar38_fun_eq_dirichlet_neg]

theorem nuSeq38_eq_candidate (φ : PotPair) {N : ℕ}
    (h : RootCountingAt38 (neumannChar38 φ) 1 N) :
    nuSeq38 φ = criticalCandidate38 (neumannChar38 φ) N := by
  rw [neumannChar38_fun_eq_dirichlet_neg]
  exact muSeq_eq_candidate38 (-φ) ((neumann_counting_iff38 φ N).mp h)

theorem neumann_local_multisets38 (φ₀ : PotPair) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ ∃ N : ℕ, 0 < N ∧ ∀ φ ∈ U,
      RootCountingAt38 (neumannChar38 φ) 1 N ∧
      (∀ n : ℤ, (N : ℤ) < |n| → ({nuSeq38 φ n} : Multiset ℂ) =
        Lib.zeroMultiset (neumannChar38 φ) (ball (countingCenter38 n) (Real.pi / 4))) ∧
      ((Finset.Icc (-(N : ℤ)) (N : ℤ)).val.map (nuSeq38 φ) =
        Lib.zeroMultiset (neumannChar38 φ) (ball (0 : ℂ) (countingRadius38 N))) := by
  obtain ⟨V, hV, N, hN⟩ := dirichlet_counting_lemma38 (-φ₀)
  have hU : (fun φ : PotPair => -φ) ⁻¹' V ∈ 𝓝 φ₀ :=
    continuous_neg.continuousAt.preimage_mem_nhds hV
  refine ⟨_, hU, N, (hN (-φ₀) (mem_of_mem_nhds hV)).1, fun φ hφ => ?_⟩
  have h := hN (-φ) hφ
  have he : nuSeq38 φ = criticalCandidate38 (dirichletChar (-φ)) N := muSeq_eq_candidate38 (-φ) h
  rw [neumannChar38_fun_eq_dirichlet_neg]
  refine ⟨h, ?_, ?_⟩
  · intro n hn
    rw [he]
    exact criticalCandidate_small_multiset38 h hn
  · rw [he]
    exact criticalCandidate_central_multiset38 h

theorem lamSeq_neg38 (φ : PotPair) : lamSeq (-φ) = lamSeq φ :=
  lamSeq_eq_of_perChar_eq38 (perChar_neg38 φ)

theorem lamMinus_neg38 (φ : PotPair) (n : ℤ) : lamMinus (-φ) n = lamMinus φ n :=
  congrFun (lamSeq_neg38 φ) (2 * n)

theorem lamPlus_neg38 (φ : PotPair) (n : ℤ) : lamPlus (-φ) n = lamPlus φ n :=
  congrFun (lamSeq_neg38 φ) (2 * n + 1)

theorem discrimDeriv_neg38 (φ : PotPair) : deriv (discrim (-φ)) = deriv (discrim φ) := by
  rw [discrim_neg38]

theorem lamDot_neg38 (φ : PotPair) : lamDot (-φ) = lamDot φ :=
  lamDot_eq_of_discrimDeriv_eq38 (discrimDeriv_neg38 φ)

theorem gapLower_neg38 (u : PhysicalL2) (n : ℤ) :
    actualGapLowerAllE02_38 (-u) n = actualGapLowerAllE02_38 u n := by
  apply Complex.ofReal_injective
  rw [← (lamPlus_real (-u) n).2, ← (lamPlus_real u n).2, realSlice_neg, lamMinus_neg38]

theorem gapUpper_neg38 (u : PhysicalL2) (n : ℤ) :
    actualGapUpperAllE02_38 (-u) n = actualGapUpperAllE02_38 u n := by
  apply Complex.ofReal_injective
  rw [← (lamPlus_real (-u) n).1, ← (lamPlus_real u n).1, realSlice_neg, lamPlus_neg38]

theorem nuSeq38_real_gap_simple (u : PhysicalL2) (n : ℤ) :
    (nuSeq38 (realSlice u) n).im = 0 ∧
      actualGapLowerAllE02_38 u n ≤ (nuSeq38 (realSlice u) n).re ∧
      (nuSeq38 (realSlice u) n).re ≤ actualGapUpperAllE02_38 u n ∧
      analyticOrderAt (neumannChar38 (realSlice u)) (nuSeq38 (realSlice u) n) = 1 := by
  have hgap := gkMu_mem_gap38 (-u) n
  rw [gapLower_neg38, gapUpper_neg38] at hgap
  have he : nuSeq38 (realSlice u) n = (gkMu (-u) n : ℂ) := by
    simpa only [nuSeq38, ← realSlice_neg] using muSeq_eq_gkMu38 (-u) n
  refine ⟨by rw [he]; simp, ?_, ?_, ?_⟩
  · simpa only [he, Complex.ofReal_re] using hgap.1
  · simpa only [he, Complex.ofReal_re] using hgap.2
  · simpa only [nuSeq38, neumannChar38_fun_eq_dirichlet_neg, ← realSlice_neg] using muSeq_simple38 (-u) n

theorem nuSeq38_zero (n : ℤ) : nuSeq38 0 n = countingCenter38 n := by
  simp only [nuSeq38, neg_zero, muSeq_zero38]

end
end NlsGge.GK38
