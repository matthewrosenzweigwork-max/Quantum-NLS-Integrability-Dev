import NlsGge.GK38.IsolatingOrderedLabelsCandidates
import NlsGge.GK38.NeumannLabels

/-! The same canonical complex labels occupy each prescribed isolating circle. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

theorem ordered_circle_labels38 (φ : PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hgeom : IsolatingGeometry38 C R c N)
    (hp : RootCountingAt38 (perChar φ) 2 N)
    (hd : RootCountingAt38 (deriv (discrim φ)) 1 N)
    (hm : RootCountingAt38 (dirichletChar φ) 1 N)
    (hn : RootCountingAt38 (neumannChar38 φ) 1 N)
    (hsub : ∀ n : ℤ, |n| ≤ (N : ℤ) → ball (C n) (R n) ⊆ ball 0 (countingRadius38 N))
    (hc : ∀ n : ℤ, (Lib.zeroMultiset (perChar φ) (ball (C n) (R n))).card = 2 ∧
      (Lib.zeroMultiset (dirichletChar φ) (ball (C n) (R n))).card = 1 ∧
      (Lib.zeroMultiset (neumannChar38 φ) (ball (C n) (R n))).card = 1 ∧
      (Lib.zeroMultiset (deriv (discrim φ)) (ball (C n) (R n))).card = 1) :
    ∀ n : ℤ, (lamMinus φ n ::ₘ lamPlus φ n ::ₘ 0) =
        Lib.zeroMultiset (perChar φ) (ball (C n) (R n)) ∧
      ({muSeq φ n} : Multiset ℂ) = Lib.zeroMultiset (dirichletChar φ) (ball (C n) (R n)) ∧
      ({nuSeq38 φ n} : Multiset ℂ) = Lib.zeroMultiset (neumannChar38 φ) (ball (C n) (R n)) ∧
      ({lamDot φ n} : Multiset ℂ) = Lib.zeroMultiset (deriv (discrim φ)) (ball (C n) (R n)) := by
  intro n
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [lamMinus, lamPlus, lamSeq_eq_candidate38 φ hp] using
      isolating_periodic_candidate_multiset38 hp C R c hgeom hsub (fun k _ => (hc k).1) n
  · rw [muSeq_eq_candidate38 φ hm]
    exact isolating_critical_candidate_multiset38 hm C R c hgeom hsub (fun k _ => (hc k).2.1) n
  · rw [nuSeq38_eq_candidate φ hn]
    exact isolating_critical_candidate_multiset38 hn C R c hgeom hsub (fun k _ => (hc k).2.2.1) n
  · rw [lamDot_eq_candidate38 φ hd]
    exact isolating_critical_candidate_multiset38 hd C R c hgeom hsub (fun k _ => (hc k).2.2.2) n

end
end NlsGge.GK38
