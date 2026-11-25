import Mathlib
import NlsGge.ThirdConsultation.F.Round5
import NlsGge.ThirdConsultation.F.Wick018A
import NlsGge.ThirdConsultation.F.Wick018B
import NlsGge.Atomic.F.F016
import NlsGge.Hierarchy.RiccatiLocalRemainderSobolev38
import NlsGge.Hierarchy.GaussianTailContractionsF06C2_38

                                                                                                          
                                                                                               
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.Measure

namespace NlsGge.ThirdConsultation.F
attribute [local instance] Classical.propDecidable

namespace Wick018C

open Filter Topology

/-- C1: generic form of `tendsto_integral_trunc38` for any continuous `V` with a polynomial bound. -/
theorem tendsto_integral_trunc_gen (m : ℕ) (β : ℕ → ℝ) (hm : 2 ≤ m) (hβ : ∀ i ≤ m, 0 ≤ β i)
    (h0 : 0 < β 0) (hM : 0 < β m)
    (V : SobolevHilbert ((m - 1 : ℕ) : ℝ) → ℝ) (hV : Continuous V) (C : ℝ) (hC0 : 0 ≤ C) (p : ℕ)
    (hC : ∀ y, |V y| ≤ C * (1 + ‖y‖ ^ p))
    (N : ℕ) (x : SobolevHilbert ((m - 1 : ℕ) : ℝ)) :
    Integrable (fun s => V (x + tailRealization38 m N s)) (gammaM38 m β) ∧
    Tendsto (fun N' : ℕ => ∫ s, V (x + truncRealization38 m N N' s) ∂gammaM38 m β)
      atTop (𝓝 (∫ s, V (x + tailRealization38 m N s) ∂gammaM38 m β)) := by
  set c := ‖x‖
  set γ := gammaM38 m β
  have hmom : ∀ k : ℕ, Integrable (fun s => ‖tailRealization38 m N s‖ ^ k) γ := fun k => by
    obtain ⟨_, _, h⟩ := tailRealization_moment38 hm hβ h0 hM k
    exact (h N).1
  set bound : (ℤ → ℂ) → ℝ := fun s => C * (1 + (‖tailRealization38 m N s‖ + c) ^ p) with hbound
  have hbi : Integrable bound γ := by
    have hsum : Integrable (fun s => ∑ i ∈ Finset.range (p + 1),
        ‖tailRealization38 m N s‖ ^ i * c ^ (p - i) * (p.choose i : ℝ)) γ :=
      integrable_finsetSum _ fun i _ => ((hmom i).mul_const _).mul_const _
    have heq : bound = fun s => C * (1 + ∑ i ∈ Finset.range (p + 1),
        ‖tailRealization38 m N s‖ ^ i * c ^ (p - i) * (p.choose i : ℝ)) := by
      funext s
      simp only [hbound, add_pow]
    rw [heq]
    exact ((integrable_const 1).add hsum).const_mul C
  have hcont : Continuous (fun y : SobolevHilbert ((m - 1 : ℕ) : ℝ) => V (x + y)) :=
    hV.comp (continuous_const.add continuous_id)
  have hle : ∀ y : SobolevHilbert ((m - 1 : ℕ) : ℝ), ∀ s, ‖y‖ ≤ ‖tailRealization38 m N s‖ →
      ‖V (x + y)‖ ≤ bound s := by
    intro y s hy
    rw [Real.norm_eq_abs]
    refine (hC _).trans (mul_le_mul_of_nonneg_left ?_ hC0)
    gcongr
    calc ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le _ _
      _ ≤ ‖tailRealization38 m N s‖ + c := by linarith
  refine ⟨hbi.mono' (hcont.measurable.comp (measurable_tailRealization38 N)).aestronglyMeasurable
    (Eventually.of_forall fun s => hle _ s le_rfl), ?_⟩
  have hae := ae_trunc_tendsto38 hm hβ h0 hM N
  refine tendsto_integral_of_dominated_convergence bound
    (fun N' => (hcont.measurable.comp (measurable_truncRealization38 N N')).aestronglyMeasurable)
    hbi (fun N' => ?_) ?_
  · filter_upwards [hae] with s hs
    exact hle _ s (hs.2 N')
  · filter_upwards [hae] with s hs
    exact (hcont.tendsto _).comp hs.1

/-- C2 (W6): per-monomial integrability and removal of the upper cutoff. -/
theorem tendsto_integral_monomial (m : ℕ) (β : ℕ → ℝ) (hm : 2 ≤ m) (hβ : ∀ i ≤ m, 0 ≤ β i)
    (h0 : 0 < β 0) (hM : 0 < β m) (j : ℕ) (q : Jet →₀ ℕ) (N : ℕ)
    (x : SobolevHilbert ((m - 1 : ℕ) : ℝ)) :
    Integrable (fun s => localRemainderMonomialValue38 m j q
        (toCarrier38 _ (x + tailRealization38 m N s))) (gammaM38 m β) ∧
    Tendsto (fun N' : ℕ => ∫ s, localRemainderMonomialValue38 m j q
        (toCarrier38 _ (x + truncRealization38 m N N' s)) ∂gammaM38 m β)
      atTop (𝓝 (∫ s, localRemainderMonomialValue38 m j q
        (toCarrier38 _ (x + tailRealization38 m N s)) ∂gammaM38 m β)) := by
  obtain ⟨C, hC0, hC⟩ := localRemainderMonomialValue38_bound m j q
  exact tendsto_integral_trunc_gen m β hm hβ h0 hM
    (fun y => localRemainderMonomialValue38 m j q (toCarrier38 _ y))
    ((continuous_localRemainderMonomialValue38 m j q).comp (continuous_toCarrier38 _))
    C hC0 (2 * m + 2) (fun y => hC (toCarrier38 _ y)) N x

theorem wickMatchingSum_eq_zero_of_card_ne (m : ℕ) (β : ℕ → ℝ) (N : ℕ) (q : Jet →₀ ℕ)
    (R : Finset (OccType38 q)) (h : (tailUnbar q R).card ≠ (tailBar q R).card) :
    wickMatchingSum m β N q R = 0 := by
  have : IsEmpty (↥(tailUnbar q R) ≃ ↥(tailBar q R)) :=
    ⟨fun e => h (by simpa using Fintype.card_congr e)⟩
  unfold wickMatchingSum
  exact Finset.sum_eq_zero (fun σ _ => (this.false σ).elim)

/-- C3 (W5): the finite-cutoff matching sum tends to `wickMatchingSum` as `N' → ∞`. -/
theorem tendsto_wickMatchingSumFin (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 < β j)
    (N : ℕ) (hN : 1 ≤ N) (q : Jet →₀ ℕ) (hord : ∀ t, occOrd38 q t ≤ m - 1)
    (R : Finset (OccType38 q)) :
    Tendsto (fun N' : ℕ => Wick018B.wickMatchingSumFin m β N N' q R) atTop
      (𝓝 (wickMatchingSum m β N q R)) := by
  by_cases h : (tailUnbar q R).card = (tailBar q R).card
  · have e : ∀ N' : ℕ, Wick018B.wickMatchingSumFin m β N N' q R =
        ∑ σ : (↥(tailUnbar q R) ≃ ↥(tailBar q R)), ∏ i : ↥(tailUnbar q R),
          Wick018B.tailCovarianceFin m β N N' (occOrd38 q i.1) (occOrd38 q (σ i).1) := by
      intro N'
      unfold Wick018B.wickMatchingSumFin
      rw [if_pos h]
    simp only [e]
    unfold wickMatchingSum
    refine tendsto_finset_sum _ (fun σ _ => tendsto_finset_prod _ (fun i _ => ?_))
    exact F016L5.tendsto_partial_cov m hm β hβ N _ _ hN (hord _) (hord _)
  · rw [wickMatchingSum_eq_zero_of_card_ne m β N q R h]
    have e : ∀ N' : ℕ, Wick018B.wickMatchingSumFin m β N N' q R = 0 := by
      intro N'
      unfold Wick018B.wickMatchingSumFin
      rw [if_neg h]
    simp only [e]
    exact tendsto_const_nhds

end Wick018C

end NlsGge.ThirdConsultation.F
end

#print axioms NlsGge.ThirdConsultation.F.Wick018C.tendsto_wickMatchingSumFin
#print axioms NlsGge.ThirdConsultation.F.Wick018C.tendsto_integral_monomial
