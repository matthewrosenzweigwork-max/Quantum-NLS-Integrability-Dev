import Mathlib
import NlsGge.Atomic.G6.G6029Host
import NlsGge.ThirdConsultation.KO.Basic

                                                                                                                          
                                                                                                                  
                                                                                                           
                                                                                                             
                                                                                                                          
                                                                                                                    
                                                                                                                    
                           
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped Classical ENNReal InnerProductSpace
open NlsGge.ThirdConsultation (finiteGap)

namespace NlsGge.GKDefinitionDesign
namespace G6029Aux
noncomputable section

theorem finite_support_mem (z : ℤ → ℂ) (hz : (Function.support z).Finite) (r : ℝ) :
    z ∈ seqSobolev38 r := by
  show Memℓp (weightedCoordinates (sobolevModeWeight r) z) 2
  refine memℓp_gen ?_
  refine summable_of_finite_support (hz.subset ?_)
  intro n hn
  simp only [Function.mem_support] at hn ⊢
  intro h0
  apply hn
  simp [weightedCoordinates, h0]

theorem truncate_apply (N : ℕ) (z : Lib.L2Z) (n : ℤ) :
    (truncatePhysicalCoordinates N z : ℤ → ℂ) n = if n ∈ Lib.win N then z n else 0 := by
  unfold truncatePhysicalCoordinates
  have h := map_sum (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n) (fun k => lp.single 2 k (z k)) (Lib.win N)
  have e : ∀ x : Lib.L2Z, lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n x = (x : ℤ → ℂ) n := fun x => rfl
  rw [e] at h
  rw [h]
  simp only [e, lp.single_apply]
  split_ifs with hn
  · rw [Finset.sum_eq_single n]
    · simp
    · intro b _ hb; simp [Pi.single_apply, Ne.symm hb]
    · intro h'; exact absurd hn h'
  · refine Finset.sum_eq_zero (fun k hk => ?_)
    have : n ≠ k := fun h => hn (h ▸ hk)
    simp [Pi.single_apply, this]

theorem G6029_of
    (hact : ∀ (u : PhysicalL2) (n : ℤ), ‖physicalBirkhoff u n‖ ^ 2 = actualGapActionAllE02_38 u n)
    (h2030 : ∀ (u : PhysicalL2) (n : ℤ),
      gkActionC38 (realSlice u) n = (actualGapActionAllE02_38 u n : ℂ) ∧
      0 ≤ actualGapActionAllE02_38 u n ∧
      (actualGapActionAllE02_38 u n=0 ↔
        actualGapLowerAllE02_38 u n=actualGapUpperAllE02_38 u n))
    (h6023 : ∀ (u : PhysicalL2) (m : ℕ),
      fourierSeq38 u ∈ seqSobolev38 (m : ℝ) ↔
        (physicalBirkhoff u : ℤ → ℂ) ∈ seqSobolev38 (m : ℝ))
    (hright : Function.RightInverse physicalInverseBirkhoff physicalBirkhoff)
    (u : PhysicalL2) :
  ((Function.support (physicalBirkhoff u : ℤ → ℂ)).Finite ↔ finiteGap u) ∧
  (finiteGap u → ∀ m : ℕ, fourierSeq38 u ∈ seqSobolev38 (m : ℝ)) ∧
  (∀ N : ℕ, finiteGap (finiteGapTruncation N u) ∧
    ∀ m : ℕ, fourierSeq38 (finiteGapTruncation N u) ∈ seqSobolev38 (m : ℝ)) := by
  have hsupp : ∀ v : PhysicalL2, Function.support (physicalBirkhoff v : ℤ → ℂ) =
      {n : ℤ | actualGapLowerAllE02_38 v n ≠ actualGapUpperAllE02_38 v n} := by
    intro v
    ext n
    simp only [Function.mem_support, Set.mem_setOf_eq]
    constructor
    · intro h heq
      apply h
      have h3 := (h2030 v n).2.2.2 heq
      rw [← hact v n] at h3
      exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h3)
    · intro h h0
      apply h
      apply (h2030 v n).2.2.1
      rw [← hact v n, h0, norm_zero]
      norm_num
  have hiff : ∀ v : PhysicalL2, (Function.support (physicalBirkhoff v : ℤ → ℂ)).Finite ↔ finiteGap v := by
    intro v
    rw [hsupp v]
    rfl
  have hsm : ∀ v : PhysicalL2, finiteGap v → ∀ m : ℕ, fourierSeq38 v ∈ seqSobolev38 (m : ℝ) := by
    intro v hv m
    exact (h6023 v m).2 (finite_support_mem _ ((hiff v).2 hv) _)
  refine ⟨hiff u, hsm u, fun N => ?_⟩
  have hfin : finiteGap (finiteGapTruncation N u) := by
    rw [← hiff]
    unfold finiteGapTruncation
    rw [hright]
    refine (Lib.win N).finite_toSet.subset ?_
    intro n hn
    simp only [Function.mem_support] at hn
    rw [truncate_apply] at hn
    by_contra h
    exact hn (if_neg h)
  exact ⟨hfin, hsm _ hfin⟩

end
end G6029Aux
end NlsGge.GKDefinitionDesign
