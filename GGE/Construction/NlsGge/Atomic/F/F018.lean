import Mathlib
import NlsGge.ThirdConsultation.F.Round5
import NlsGge.ThirdConsultation.F.Wick018A
import NlsGge.ThirdConsultation.F.Wick018B
import NlsGge.ThirdConsultation.F.Wick018C
import NlsGge.ThirdConsultation.F.Wick018D1
import NlsGge.ThirdConsultation.F.Wick018D2
import NlsGge.Hierarchy.RiccatiLocalRemainderSobolev38
import NlsGge.Hierarchy.GaussianTailContractionsF06C2_38

                                                                                                                          
                                                                                                                                          
set_option autoImplicit false
noncomputable section
open Filter Topology

namespace NlsGge.ThirdConsultation.F
open MeasureTheory NlsGge.Pilot NlsGge.Sobolev38
open NlsGge.HierarchyRiccati.Core NlsGge.Measure
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem f018 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ)
    (hβ : ∀ j ≤ m, 0 < β j)
    (N : ℕ) (hN : 1 ≤ N) (z : FourierPlane N) :
    (∀ j : ℕ, j ≤ m → ∀ q : Jet →₀ ℕ,
      q ∈ (normalizedRemainder38 j).support →
        (∀ R ∈ contractionPatterns q, ∃ k l : ℕ,
          1 ≤ k ∧ (tailUnbar q R).card = k ∧
          (tailBar q R).card = k ∧ R.card = 2 * l ∧
          q.degree = 2 * k + 2 * l) ∧
        Integrable (fun s => localRemainderMonomialValue38 m j q
          (toCarrier38 _
            (planeElement38 ((m - 1 : ℕ) : ℝ) N z +
              tailRealization38 m N s))) (gammaM38 m β) ∧
        (∫ s, localRemainderMonomialValue38 m j q
          (toCarrier38 _
            (planeElement38 ((m - 1 : ℕ) : ℝ) N z +
              tailRealization38 m N s)) ∂gammaM38 m β) -
          localRemainderMonomialValue38 m j q
            (toCarrier38 _
              (planeElement38 ((m - 1 : ℕ) : ℝ) N z)) =
          ∑ R ∈ contractionPatterns q,
            contractedMonomial m β N j z q R) ∧
    contractionCorrection38 m β N z =
      ∑ j ∈ Finset.range (m + 1), β j *
        ∑ q ∈ (normalizedRemainder38 j).support,
          ∑ R ∈ contractionPatterns q,
            contractedMonomial m β N j z q R := by
  have hβ0 : ∀ i ≤ m, 0 ≤ β i := fun i hi => (hβ i hi).le
  have hint : ∀ j ≤ m, ∀ q ∈ (normalizedRemainder38 j).support,
      Integrable (fun s => localRemainderMonomialValue38 m j q
        (toCarrier38 _ (planeElement38 ((m - 1 : ℕ) : ℝ) N z + tailRealization38 m N s)))
        (gammaM38 m β) := fun j _ q _ =>
    (Wick018C.tendsto_integral_monomial m β hm hβ0 (hβ 0 (Nat.zero_le _)) (hβ m le_rfl) j q N
      (planeElement38 ((m - 1 : ℕ) : ℝ) N z)).1
  have hexp : ∀ j ≤ m, ∀ q ∈ (normalizedRemainder38 j).support,
      (∫ s, localRemainderMonomialValue38 m j q
          (toCarrier38 _ (planeElement38 ((m - 1 : ℕ) : ℝ) N z + tailRealization38 m N s))
          ∂gammaM38 m β) -
        localRemainderMonomialValue38 m j q
          (toCarrier38 _ (planeElement38 ((m - 1 : ℕ) : ℝ) N z)) =
        ∑ R ∈ contractionPatterns q, contractedMonomial m β N j z q R :=
    fun j hj q hq => Wick018D2.expectation_tail m β hm hβ j hj q hq N hN z
  refine ⟨fun j hj q hq => ⟨fun R hR => Wick018D2.pattern_counting q
    (Wick018D2.gauge_zero j q hq) R hR, hint j hj q hq, hexp j hj q hq⟩, ?_⟩
  unfold contractionCorrection38 vSobolev38 localRemainderSobolev38
  have hj' : ∀ j ∈ Finset.range (m + 1), j ≤ m := fun j hj => Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have hsum : ∀ j ∈ Finset.range (m + 1), Integrable (fun s => ∑ q ∈ (normalizedRemainder38 j).support,
      localRemainderMonomialValue38 m j q
        (toCarrier38 _ (planeElement38 ((m - 1 : ℕ) : ℝ) N z + tailRealization38 m N s)))
      (gammaM38 m β) := fun j hj =>
    integrable_finset_sum _ (fun q hq => hint j (hj' j hj) q hq)
  rw [integral_finset_sum _ (fun j hj => (hsum j hj).const_mul (β j))]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [integral_const_mul, integral_finset_sum _ (fun q hq => hint j (hj' j hj) q hq),
    ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl fun q hq => hexp j (hj' j hj) q hq

end NlsGge.ThirdConsultation.F
end

