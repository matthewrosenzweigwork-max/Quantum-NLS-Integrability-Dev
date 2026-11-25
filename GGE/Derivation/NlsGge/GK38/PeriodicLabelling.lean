import NlsGge.GK38.PeriodicLabellingFreeLabels

/-! # S2: periodic and critical labelling package (GK Lemmas 6.3 and 6.5)

Every root occurs with its full analytic multiplicity. The real/imaginary Lex
ordering is compatible with every certified cutoff, and the least simultaneous
cutoff only supplies canonical implementation data. Individual complex labels
are not asserted continuous. Central roots need not be simple.
-/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem periodic_labelling38 :
    (∀ (φ : PotPair) (i j : ℤ), i ≤ j → complexLexLE38 (lamSeq φ i) (lamSeq φ j)) ∧
    (∀ φ : PotPair, RootEnumeration38 (perChar φ) (lamSeq φ)) ∧
    (∀ (φ : PotPair) (N : ℕ), RootCountingAt38 (perChar φ) 2 N →
      lamSeq φ = periodicCandidate38 (perChar φ) N) ∧
    (∀ n : ℤ, lamMinus 0 n = countingCenter38 n ∧ lamPlus 0 n = countingCenter38 n) :=
  ⟨fun φ _ _ h => lamSeq_mono38 φ h, lamSeq_enumeration38,
    fun φ _ h => lamSeq_eq_candidate38 φ h, fun n => ⟨lamMinus_zero38 n, lamPlus_zero38 n⟩⟩

theorem critical_labelling38 :
    (∀ (φ : PotPair) (i j : ℤ), i ≤ j → complexLexLE38 (lamDot φ i) (lamDot φ j)) ∧
    (∀ φ : PotPair, RootEnumeration38 (deriv (discrim φ)) (lamDot φ)) ∧
    (∀ (φ : PotPair) (N : ℕ), RootCountingAt38 (deriv (discrim φ)) 1 N →
      lamDot φ = criticalCandidate38 (deriv (discrim φ)) N) ∧
    (∀ n : ℤ, lamDot 0 n = countingCenter38 n) :=
  ⟨fun φ _ _ h => lamDot_mono38 φ h, lamDot_enumeration38,
    fun φ _ h => lamDot_eq_candidate38 φ h, lamDot_zero38⟩

theorem labelling_multiplicity_bounds38 (φ : PotPair) (z : ℂ) :
    Set.encard {n : ℤ | lamMinus φ n = z} ≤ analyticOrderAt (perChar φ) z ∧
      Set.encard {n : ℤ | lamPlus φ n = z} ≤ analyticOrderAt (perChar φ) z ∧
      Set.encard {n : ℤ | lamDot φ n = z} ≤ analyticOrderAt (deriv (discrim φ)) z :=
  ⟨(lamMinusPlus_occurrence_bounds38 φ z).1, (lamMinusPlus_occurrence_bounds38 φ z).2,
    (lamDot_occurrence38 φ z).2.le⟩

/-- Equal characteristic functions have the same canonical periodic sequence. -/
theorem lamSeq_eq_of_perChar_eq38 {φ ψ : PotPair} (he : perChar φ = perChar ψ) :
    lamSeq φ = lamSeq ψ := by
  have hc := (canonicalCountingCutoff_spec38 φ).1
  have hp : RootCountingAt38 (perChar ψ) 2 (canonicalCountingCutoff38 φ) := by
    simpa only [he] using hc
  rw [lamSeq_eq_candidate38 φ hc, lamSeq_eq_candidate38 ψ hp, he]

/-- Equal discriminant derivatives have the same canonical critical sequence. -/
theorem lamDot_eq_of_discrimDeriv_eq38 {φ ψ : PotPair}
    (he : deriv (discrim φ) = deriv (discrim ψ)) : lamDot φ = lamDot ψ := by
  have hc := (canonicalCountingCutoff_spec38 φ).2
  have hp : RootCountingAt38 (deriv (discrim ψ)) 1 (canonicalCountingCutoff38 φ) := by
    simpa only [he] using hc
  rw [lamDot_eq_candidate38 φ hc, lamDot_eq_candidate38 ψ hp, he]

end
end NlsGge.GK38
