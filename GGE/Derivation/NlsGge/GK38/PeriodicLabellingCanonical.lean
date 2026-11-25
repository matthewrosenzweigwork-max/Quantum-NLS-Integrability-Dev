import NlsGge.GK38.PeriodicLabellingInvariance
import NlsGge.GK38.PeriodicLabellingCounting

/-! # S2: canonical multiplicity-preserving spectral labels -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem exists_simultaneous_cutoff38 (φ : PotPair) :
    ∃ N : ℕ, RootCountingAt38 (perChar φ) 2 N ∧ RootCountingAt38 (deriv (discrim φ)) 1 N := by
  obtain ⟨U, hU, N, hN⟩ := simultaneous_counting_lemma38 φ
  exact ⟨N, hN φ (mem_of_mem_nhds hU)⟩

def canonicalCountingCutoff38 (φ : PotPair) : ℕ := by
  classical
  exact Nat.find (exists_simultaneous_cutoff38 φ)

theorem canonicalCountingCutoff_spec38 (φ : PotPair) :
    RootCountingAt38 (perChar φ) 2 (canonicalCountingCutoff38 φ) ∧
      RootCountingAt38 (deriv (discrim φ)) 1 (canonicalCountingCutoff38 φ) :=
  by
  classical
  exact Nat.find_spec (exists_simultaneous_cutoff38 φ)

def lamSeq (φ : PotPair) : ℤ → ℂ := periodicCandidate38 (perChar φ) (canonicalCountingCutoff38 φ)
def lamMinus (φ : PotPair) (n : ℤ) : ℂ := lamSeq φ (2 * n)
def lamPlus (φ : PotPair) (n : ℤ) : ℂ := lamSeq φ (2 * n + 1)
def lamDot (φ : PotPair) : ℤ → ℂ := criticalCandidate38 (deriv (discrim φ)) (canonicalCountingCutoff38 φ)

theorem lamSeq_eq_candidate38 (φ : PotPair) {N : ℕ} (h : RootCountingAt38 (perChar φ) 2 N) :
    lamSeq φ = periodicCandidate38 (perChar φ) N :=
  periodicCandidate_cutoff_invariant38 (canonicalCountingCutoff_spec38 φ).1 h

theorem lamDot_eq_candidate38 (φ : PotPair) {N : ℕ} (h : RootCountingAt38 (deriv (discrim φ)) 1 N) :
    lamDot φ = criticalCandidate38 (deriv (discrim φ)) N :=
  criticalCandidate_cutoff_invariant38 (canonicalCountingCutoff_spec38 φ).2 h

theorem lamSeq_mono38 (φ : PotPair) {i j : ℤ} (hij : i ≤ j) : complexLexLE38 (lamSeq φ i) (lamSeq φ j) :=
  periodicCandidate_mono38 (canonicalCountingCutoff_spec38 φ).1 hij

theorem lamDot_mono38 (φ : PotPair) {i j : ℤ} (hij : i ≤ j) : complexLexLE38 (lamDot φ i) (lamDot φ j) :=
  criticalCandidate_mono38 (canonicalCountingCutoff_spec38 φ).2 hij

theorem lamSeq_enumeration38 (φ : PotPair) : RootEnumeration38 (perChar φ) (lamSeq φ) :=
  periodicCandidate_enumeration38 (canonicalCountingCutoff_spec38 φ).1

theorem lamDot_enumeration38 (φ : PotPair) : RootEnumeration38 (deriv (discrim φ)) (lamDot φ) :=
  criticalCandidate_enumeration38 (canonicalCountingCutoff_spec38 φ).2

theorem lamMinus_le_lamPlus38 (φ : PotPair) (n : ℤ) : complexLexLE38 (lamMinus φ n) (lamPlus φ n) :=
  lamSeq_mono38 φ (by omega)

theorem lamPlus_le_lamMinus_next38 (φ : PotPair) (n : ℤ) : complexLexLE38 (lamPlus φ n) (lamMinus φ (n + 1)) :=
  lamSeq_mono38 φ (by omega)

/-- Combined even/odd occurrences retain the full characteristic multiplicity. -/
theorem lamMinusPlus_occurrence38 (φ : PotPair) (z : ℂ) :
    Set.encard {n : ℤ | lamMinus φ n = z} + Set.encard {n : ℤ | lamPlus φ n = z} =
      analyticOrderAt (perChar φ) z := rootEnumeration_even_odd_encard38 (lamSeq_enumeration38 φ) z

theorem lamMinusPlus_occurrence_bounds38 (φ : PotPair) (z : ℂ) :
    Set.encard {n : ℤ | lamMinus φ n = z} ≤ analyticOrderAt (perChar φ) z ∧
      Set.encard {n : ℤ | lamPlus φ n = z} ≤ analyticOrderAt (perChar φ) z :=
  rootEnumeration_even_odd_bounds38 (lamSeq_enumeration38 φ) z

theorem lamDot_occurrence38 (φ : PotPair) (z : ℂ) :
    {n : ℤ | lamDot φ n = z}.Finite ∧ Set.encard {n : ℤ | lamDot φ n = z} =
      analyticOrderAt (deriv (discrim φ)) z := (lamDot_enumeration38 φ).2.2 z

theorem labelling_local_multisets38 (φ₀ : PotPair) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ ∃ N : ℕ, 0 < N ∧
      ∀ φ : PotPair, φ ∈ U →
        (∀ n : ℤ, (N : ℤ) < |n| →
          (lamMinus φ n ::ₘ lamPlus φ n ::ₘ 0) =
            Lib.zeroMultiset (perChar φ) (ball (countingCenter38 n) (Real.pi / 4)) ∧
          ({lamDot φ n} : Multiset ℂ) =
            Lib.zeroMultiset (deriv (discrim φ)) (ball (countingCenter38 n) (Real.pi / 4))) ∧
        ((Finset.Icc (-(2 * (N : ℤ))) (2 * (N : ℤ) + 1)).val.map (lamSeq φ) =
          Lib.zeroMultiset (perChar φ) (ball (0 : ℂ) (countingRadius38 N))) ∧
        ((Finset.Icc (-(N : ℤ)) (N : ℤ)).val.map (lamDot φ) =
          Lib.zeroMultiset (deriv (discrim φ)) (ball (0 : ℂ) (countingRadius38 N))) := by
  obtain ⟨U, hU, N, hN⟩ := simultaneous_counting_lemma38 φ₀
  have hpos : 0 < N := (hN φ₀ (mem_of_mem_nhds hU)).1.1
  refine ⟨U, hU, N, hpos, fun φ hφ => ?_⟩
  obtain ⟨hp, hd⟩ := hN φ hφ
  have heP := lamSeq_eq_candidate38 φ hp
  have heD := lamDot_eq_candidate38 φ hd
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    simpa only [lamMinus, lamPlus, heP, heD] using
      And.intro (periodicCandidate_small_multiset38 hp hn) (criticalCandidate_small_multiset38 hd hn)
  · rw [heP]
    exact periodicCandidate_central_multiset38 hp
  · rw [heD]
    exact criticalCandidate_central_multiset38 hd

end
end NlsGge.GK38
