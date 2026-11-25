import Mathlib
import NlsGge.Atomic.M.M008Host
import NlsGge.Atomic.M.M008Loops
import NlsGge.Atomic.M.M008Collapsed
import NlsGge.Atomic.M.M008EndpointConst
import NlsGge.Atomic.M.M008Endpoint

/- M-008 SUPPORT EndpointChains (proof development, AUTHOR; not reviewed).  Conjunct (6) of Pro round 6 section 10E
   `omega_gap_period_zero`: every admissible endpoint chain has total joint improper integral 0 (each piece gets its own
   `HasEndpointIntegral`, the finite sum telescopes along `ChainCompatible`).  Open gap: one primitive `F` of `omega` on the cut
   disc with the SAME limit `l` at both gap endpoints (`omega_primitive_common_limit`).  Collapsed gap: the primitive of the
   removable extension (S1) on the convex isolating disc, or constant chains. -/
set_option autoImplicit false
open Set Filter MeasureTheory Topology Metric
open NlsGge.Pilot NlsGge.GK38
open NlsGge.GK38.Lib.SlitContours

namespace NlsGge.ThirdConsultation.MContour
noncomputable section

/-- Generic assembly: pieces with a primitive `F` and endpoint values `S i`, `E i` that match along the chain. -/
theorem endpointChain_of_primitive (φ : PotPair) (m : ℕ) (p : Fin (m + 1) → ℝ → ℂ)
    (U : Set ℂ) (hω : ContinuousOn (omega φ) U)
    (F : ℂ → ℂ) (hF : ∀ z ∈ U, HasDerivAt F (omega φ z) z)
    (hpc : ∀ i, ContinuousOn (p i) (Icc (0 : ℝ) 1))
    (hpd : ∀ i, ContDiffOn ℝ 1 (p i) (Ioo (0 : ℝ) 1))
    (hmem : ∀ i, ∀ t ∈ Ioo (0 : ℝ) 1, p i t ∈ U)
    (S E : Fin (m + 1) → ℂ)
    (h0 : ∀ i, Tendsto F (𝓝[U] (p i 0)) (𝓝 (S i)))
    (h1 : ∀ i, Tendsto F (𝓝[U] (p i 1)) (𝓝 (E i)))
    (hcompat : ∀ j : Fin m, E j.castSucc = S j.succ)
    (hends : E (Fin.last m) = S 0) :
    HasFiniteChainIntegral φ m p 0 := by
  refine ⟨fun i => E i - S i, fun i => ?_, ?_⟩
  · exact endpointIntegral_of_primitive φ U hω F hF (p i) (hpc i) (hpd i) (hmem i) (S i) (E i)
      (h0 i) (h1 i)
  · rw [Finset.sum_sub_distrib, Fin.sum_univ_castSucc (f := E), Fin.sum_univ_succ (f := S)]
    simp only [hcompat]
    rw [hends]
    ring

/-- Collapsed gap: a primitive of `omega` on the cut disc that is continuous on the whole isolating disc. -/
theorem omega_collapsed_primitive (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ)
    (hgap : lamMinus φ n = lamPlus φ n) :
    ∃ Fc : ℂ → ℂ, (∀ z ∈ (gapDiscSeg φ hφ n).domain, HasDerivAt Fc (omega φ z) z) ∧
      ∀ z ∈ discU φ n, ContinuousAt Fc z := by
  have hdom : (gapDiscSeg φ hφ n).domain = discU φ n \ segment ℝ (lamMinus φ n) (lamPlus φ n) := rfl
  obtain ⟨f, hfan, hfeq⟩ := omega_extends_collapsed_complex φ hφ n hgap.symm
  obtain ⟨Fc, hFc⟩ := (convex_ball (discC φ n) (discR φ n)).exists_forall_hasDerivWithinAt
    hfan.differentiableOn
  refine ⟨Fc, fun z hz => ?_, fun z hz => ?_⟩
  · rw [hdom] at hz
    have hzne : z ≠ lamMinus φ n := fun h => hz.2 (h ▸ left_mem_segment ℝ _ _)
    have := (hFc z hz.1).hasDerivAt (isOpen_ball.mem_nhds hz.1)
    rwa [hfeq z hz.1 hzne] at this
  · exact ((hFc z hz).hasDerivAt (isOpen_ball.mem_nhds hz)).continuousAt

/-- **Conjunct (6) of the section-10E head.** -/
theorem omega_endpointChain_zero (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) (m : ℕ)
    (p : Fin (m + 1) → ℝ → ℂ) (hp : AdmissibleEndpointChain φ n m p) :
    HasFiniteChainIntegral φ m p 0 := by
  obtain ⟨hc, hreg, h00, h1l, hcase⟩ := hp
  set D := gapDiscSeg φ hφ n with hD
  have hf : DifferentiableOn ℂ (omega φ) D.domain := omega_differentiableOn_domain φ hφ n
  have hdom : D.domain = discU φ n \ segment ℝ (lamMinus φ n) (lamPlus φ n) := rfl
  by_cases hgap : lamMinus φ n = lamPlus φ n
  · rcases hcase with ⟨hint, hjunc⟩ | ⟨-, hconst⟩
    · obtain ⟨Fc, hFU, hFcont⟩ := omega_collapsed_primitive φ hφ n hgap
      have hstart : ∀ i : Fin (m + 1), p i 0 ∈ discU φ n := by
        intro i
        by_cases hi : i = 0
        · subst hi
          rw [h00]
          exact own_segment_subset_disc φ hφ n (left_mem_segment ℝ _ _)
        · obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 hi
          rw [← hc j]
          exact (hjunc j).1
      have hend : ∀ i : Fin (m + 1), p i 1 ∈ discU φ n := by
        intro i
        by_cases hi : i = Fin.last m
        · subst hi
          rw [h1l]
          exact own_segment_subset_disc φ hφ n (right_mem_segment ℝ _ _)
        · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.2 hi
          exact (hjunc j).1
      refine endpointChain_of_primitive φ m p D.domain hf.continuousOn Fc hFU
        (fun i => (hreg i).1) (fun i => (hreg i).2)
        (fun i t ht => by rw [hdom]; exact hint i t ht)
        (fun i => Fc (p i 0)) (fun i => Fc (p i 1))
        (fun i => (hFcont _ (hstart i)).tendsto.mono_left nhdsWithin_le_nhds)
        (fun i => (hFcont _ (hend i)).tendsto.mono_left nhdsWithin_le_nhds)
        (fun j => by simp only [hc j]) ?_
      show Fc (p (Fin.last m) 1) = Fc (p 0 0)
      rw [h1l, h00, hgap]
    · refine ⟨fun _ => 0, fun i => ?_, by simp⟩
      refine omega_endpointCurve_zero φ hφ n (p i) ⟨(hreg i).1, (hreg i).2, ?_, ?_, Or.inr ⟨hgap, hconst i⟩⟩
      · exact (hconst i 0 ⟨le_refl _, zero_le_one⟩)
      · rw [hconst i 1 ⟨zero_le_one, le_refl _⟩, hgap]
  · rcases hcase with ⟨hint, hjunc⟩ | ⟨hg, -⟩
    · obtain ⟨F, hF, ℓ, hℓ0, hℓ1⟩ := omega_primitive_common_limit φ hφ n hgap
      have hjd : ∀ j : Fin m, p j.castSucc 1 ∈ D.domain := fun j => by rw [hdom]; exact hjunc j
      refine endpointChain_of_primitive φ m p D.domain hf.continuousOn F hF
        (fun i => (hreg i).1) (fun i => (hreg i).2)
        (fun i t ht => by rw [hdom]; exact hint i t ht)
        (fun i => if i = 0 then ℓ else F (p i 0))
        (fun i => if i = Fin.last m then ℓ else F (p i 1))
        (fun i => ?_) (fun i => ?_) (fun j => ?_) ?_
      · by_cases hi : i = 0
        · subst hi
          simp only [if_true]
          rw [h00]
          exact hℓ0
        · simp only [if_neg hi]
          obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 hi
          have hm : p j.succ 0 ∈ D.domain := by rw [← hc j]; exact hjd j
          exact (hF _ hm).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      · by_cases hi : i = Fin.last m
        · subst hi
          simp only [if_true]
          rw [h1l]
          exact hℓ1
        · simp only [if_neg hi]
          obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.2 hi
          exact (hF _ (hjd j)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      · simp only [if_neg (Fin.castSucc_lt_last j).ne, if_neg (Fin.succ_ne_zero j)]
        rw [hc j]
      · simp
    · exact absurd hg hgap

end
end NlsGge.ThirdConsultation.MContour
