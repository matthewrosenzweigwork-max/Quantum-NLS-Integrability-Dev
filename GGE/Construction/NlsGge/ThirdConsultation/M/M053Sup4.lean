import Mathlib
import NlsGge.GK38.PairPotential
import NlsGge.GK38.PairVolterraProbe
import NlsGge.GK38.NeumannGauge
import NlsGge.GK38.PoissonDirichletReal
import NlsGge.Hierarchy.RiccatiAttachedRecursionCore
import NlsGge.Hierarchy.RiccatiPolynomialEvaluationAPI
import NlsGge.Atomic.M.M003
import NlsGge.Atomic.G1.G1036
import NlsGge.ThirdConsultation.G1.NormCalculus
import NlsGge.ThirdConsultation.G1.WkbStructure
import NlsGge.ThirdConsultation.KSPSSupport
import NlsGge.ThirdConsultation.KSPSRiccatiHost
import NlsGge.Atomic.KSPS.KSPS010
import NlsGge.ThirdConsultation.M.M053Sup3

                                                        
                                                                                                                
                                                                                                           
                                                                                                      
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace NlsGge.ThirdConsultation.M
noncomputable section
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign NlsGge.HierarchyRiccati.Core
open NlsGge.ThirdConsultation.KSPS
attribute [local instance] Classical.propDecidable

/-- The weak-derivative jet family of a pair, as in the (private) `sourceHierarchyJet`. -/
def hierarchyJetL2 {N : ℕ} (φ : SobolevC N) (v : Jet) : PhysicalL2 :=
  (weakDerivative^[v.2]) (if v.1 then (toPotPair φ).2 else (toPotPair φ).1)

theorem wdIter_sobolev (N m : ℕ) (u : PhysicalL2) (hu : physicalSobolev (N : ℝ) u) (hm : m ≤ N) :
    physicalSobolev ((N - m : ℕ) : ℝ) ((weakDerivative^[m]) u) := by
  induction m with
  | zero => simpa using hu
  | succ m ih =>
    have h := ih (by omega)
    rw [Function.iterate_succ_apply']
    have e : N - m = (N - (m + 1)) + 1 := by omega
    rw [e] at h
    exact (psn_deriv (N - (m + 1)) h).1

theorem hierarchyJetL2_sobolev {N : ℕ} (φ : SobolevC N) (v : Jet) (hv : v.2 + 1 ≤ N) :
    physicalSobolev 1 (hierarchyJetL2 φ v) := by
  have hp := NlsGge.ThirdConsultation.KSPSSupport.pairSobolev_toPotPair φ
  have hb : physicalSobolev (N : ℝ) (if v.1 then (toPotPair φ).2 else (toPotPair φ).1) := by
    cases v.1
    · simpa using hp.1
    · simpa using hp.2
  have h := wdIter_sobolev N v.2 _ hb (by omega)
  have h1 := (psn_mono (m := 1) (m' := N - v.2) (by omega) h).1
  simpa [hierarchyJetL2] using h1

theorem hierarchyJetL2_deriv {N : ℕ} (φ : SobolevC N) (v : Jet) :
    weakDerivative (hierarchyJetL2 φ v) = hierarchyJetL2 φ (v.1, v.2 + 1) := by
  unfold hierarchyJetL2
  rw [← Function.iterate_succ_apply' weakDerivative]

theorem eq_of_cover_ae (u v : PhysicalL2)
    (h : ∀ᵐ x : ℝ, coverRep38 u x = coverRep38 v x) : u = v :=
  NlsGge.GK38.PoissonDirichlet38.physicalL2_eq_of_coverRep_Icc38 u v (ae_restrict_of_ae h)

theorem coverRep38_finset_sum_ae {ι : Type*} (I : Finset ι) (g : ι → PhysicalL2) (f : ι → ℝ → ℂ)
    (hg : ∀ i ∈ I, ∀ᵐ s : ℝ, coverRep38 (g i) s = f i s) :
    ∀ᵐ s : ℝ, coverRep38 (∑ i ∈ I, g i) s = ∑ i ∈ I, f i s := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact coverRep38_zero_ae
  | @insert a I ha ih =>
    filter_upwards [coverRep38_add_ae (g a) (∑ i ∈ I, g i),
      hg a (Finset.mem_insert_self a I),
      ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))] with s h1 h2 h3
    rw [Finset.sum_insert ha, Finset.sum_insert ha, h1, h2, h3]

theorem left_cover_eq_polyEval {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N) :
    ∀ k : ℕ, 1 ≤ k → k ≤ N + 1 →
      ∀ᵐ x : ℝ, coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.left φ k) x =
        polynomialEvaluation (fun v => coverRep38 (hierarchyJetL2 φ v) x) (p k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk1 hkN
  by_cases hk : k = 1
  · subst hk
    have e : NlsGge.ThirdConsultation.KSPSRiccati.left φ 1 = -(toPotPair φ).2 := by
      simp [NlsGge.ThirdConsultation.KSPSRiccati.left, NlsGge.ThirdConsultation.KSPSRiccati.coefficient,
        wkbR_one]
    rw [e, p_one]
    filter_upwards [coverRep38_neg_ae (toPotPair φ).2] with x hx
    rw [hx]
    simp [hierarchyJetL2]
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hk'1 : 1 ≤ k' := by omega
    have hk'N : k' ≤ N := by omega
    have hW := WKB_residual_regularity N hN φ
    obtain ⟨_, _, _, hrec, _⟩ := hW
    obtain ⟨hprods, hside, heq⟩ := hrec false k' hk'1 hk'N
    -- realise p k' by a field w, identify it with left k'
    have hjo : NlsGge.Atomic.M003.jetOrd (k' - 1) (p k') := by
      have := NlsGge.Atomic.M003.p_jetOrd (k' - 1)
      rwa [Nat.sub_add_cancel hk'1] at this
    obtain ⟨w, hw1, ew, dw⟩ := polyRealised_of_jetOrd (hierarchyJetL2 φ) (k' - 1)
      (fun v hv => hierarchyJetL2_sobolev φ v (by omega))
      (fun v _ => hierarchyJetL2_deriv φ v) (p k') hjo
    have hIH' := ih k' (by omega) hk'1 (by omega)
    have hwl : NlsGge.ThirdConsultation.KSPSRiccati.left φ k' = w := by
      apply eq_of_cover_ae
      filter_upwards [hIH', ew] with x h1 h2
      rw [h1, h2]
    -- recurrence of the formal polynomials
    have hp := p_recurrence (k' - 1)
    rw [show k' - 1 + 2 = k' + 1 by omega, show k' - 1 + 1 = k' by omega] at hp
    have hsum : (Finset.Icc 1 (k' - 1)).attach.sum (fun l => p (k' - l.1) * p l.1) =
        ∑ l ∈ Finset.Icc 1 (k' - 1), p (k' - l) * p l :=
      Finset.sum_attach (Finset.Icc 1 (k' - 1)) (fun l => p (k' - l) * p l)
    rw [hsum] at hp
    -- covers of the recurrence product
    have hcoef : ∀ j, NlsGge.ThirdConsultation.KSPSRiccati.left φ j =
        NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false j := fun j => rfl
    have hRp : ∀ᵐ x : ℝ, coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.recurrenceProduct φ false k') x =
        ∑ j ∈ Finset.Icc 1 (k' - 1),
          polynomialEvaluation (fun v => coverRep38 (hierarchyJetL2 φ v) x) (p (k' - j)) *
          polynomialEvaluation (fun v => coverRep38 (hierarchyJetL2 φ v) x) (p j) := by
      refine coverRep38_finset_sum_ae _ _ _ (fun j hj => ?_)
      have hj' := Finset.mem_Icc.mp hj
      have h1 := ih j (by omega) hj'.1 (by omega)
      have h2 := ih (k' - j) (by omega) (by omega) (by omega)
      have hpj := hprods j hj
      filter_upwards [g36_s2b_coverRep_mul_ae _ _ hpj, h1, h2] with x a b c
      rw [a]
      change coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.left φ j) x *
        coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.left φ (k' - j)) x = _
      rw [b, c]; ring
    have hside' : productInL2 (toPotPair φ).1
        (NlsGge.ThirdConsultation.KSPSRiccati.recurrenceProduct φ false k') := by
      simpa [NlsGge.ThirdConsultation.KSPSRiccati.sidePotential] using hside
    have hstep : NlsGge.ThirdConsultation.KSPSRiccati.left φ (k' + 1) =
        weakDerivative w + physicalProduct (toPotPair φ).1
          (NlsGge.ThirdConsultation.KSPSRiccati.recurrenceProduct φ false k') := by
      rw [← hwl]
      have := heq
      simpa [NlsGge.ThirdConsultation.KSPSRiccati.left, NlsGge.ThirdConsultation.KSPSRiccati.signedDerivative,
        NlsGge.ThirdConsultation.KSPSRiccati.sidePotential] using this
    rw [hstep, hp]
    filter_upwards [coverRep38_add_ae (weakDerivative w) (physicalProduct (toPotPair φ).1
        (NlsGge.ThirdConsultation.KSPSRiccati.recurrenceProduct φ false k')),
      g36_s2b_coverRep_mul_ae _ _ hside', dw, hRp] with x a b c d
    rw [a, b, c, d]
    simp [hierarchyJetL2]

end
end NlsGge.ThirdConsultation.M
