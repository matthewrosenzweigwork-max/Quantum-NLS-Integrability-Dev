import Mathlib
import NlsGge.Atomic.G5.G5005Host
import NlsGge.ThirdConsultation.G5.G5005Support1
import NlsGge.ThirdConsultation.G5.G5005Support2
import NlsGge.ThirdConsultation.G5.G5005Support3
import NlsGge.Atomic.G5.G5001Host
import NlsGge.Atomic.G5.G5004Host
import NlsGge.Atomic.G1.G1029
import NlsGge.Atomic.G1.G1087
import NlsGge.GK38.DirichletRealWinding
import NlsGge.GK38.DirichletL2

                                                                                 
                                                                                                    
                                                                                                                
                                                                                                                     
                                                       
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.G5005Support1 NlsGge.ThirdConsultation.G5005Support2
  NlsGge.ThirdConsultation.G5005Support3

namespace NlsGge.ThirdConsultation.G5005Support4
noncomputable section

theorem class_smul_sub_smul (c d : ℂ) (g h : PairKernelCont38) :
    pairKernelL2Class38 (c • g - d • h) = c • pairKernelL2Class38 g - d • pairKernelL2Class38 h := by
  have h1 := map_sub pairKernelL2CLM38 (c • g) (d • h)
  rw [map_smul, map_smul] at h1
  simpa only [pairKernelL2CLM38_apply] using h1

theorem gkMu_sub_cast (u : PhysicalL2) (n : ℤ) :
    ((gkMu u n : ℝ) : ℂ) - (n : ℂ) * (Real.pi : ℂ) = ((gkMu u n - (n : ℝ) * Real.pi : ℝ) : ℂ) := by
  push_cast; ring

theorem eps_summable (u : PhysicalL2) :
    Summable (fun n : ℤ => |gkMu u n - (n : ℝ) * Real.pi| ^ 2) := by
  have h := muSeq_summable38 (realSlice u)
  refine h.congr (fun n => ?_)
  rw [muSeq_eq_gkMu38, gkMu_sub_cast, Complex.norm_real, Real.norm_eq_abs]

theorem hyp_phi (u : PhysicalL2) :
    Real.sqrt (‖(realSlice u).1‖ ^ 2 + ‖(realSlice u).2‖ ^ 2) ≤ 2 * (‖u‖ + 1) := by
  have h1 : ‖(realSlice u).1‖ = ‖u‖ := rfl
  have h2 : ‖(realSlice u).2‖ = ‖u‖ := starLp.norm_map u
  rw [h1, h2]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have : 0 ≤ ‖u‖ := norm_nonneg _
  nlinarith

theorem hyp_xi (u : PhysicalL2) (n : ℤ) :
    ‖((gkMu u n : ℝ) : ℂ) - (n : ℂ) * (Real.pi : ℂ)‖ ≤ ‖u‖ := by
  rw [gkMu_sub_cast, Complex.norm_real, Real.norm_eq_abs]
  exact gkMu_global_displacement38 u n

theorem norm_radiusQuotientLeading (n : ℤ) : ‖radiusQuotientLeading n‖ = 1 / 2 := by
  unfold radiusQuotientLeading
  rw [norm_div, norm_neg, norm_zpow]
  simp

theorem q_bound (u : PhysicalL2)
    (hq : Summable (fun n : ℤ => ‖radiusQuotient n (realSlice u) - radiusQuotientLeading n‖ ^ 2)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℤ, ‖radiusQuotient n (realSlice u)‖ ≤ M := by
  refine ⟨1 / 2 + Real.sqrt (∑' n : ℤ, ‖radiusQuotient n (realSlice u) - radiusQuotientLeading n‖ ^ 2),
    by positivity, fun n => ?_⟩
  have h1 : ‖radiusQuotient n (realSlice u) - radiusQuotientLeading n‖ ^ 2 ≤
      ∑' m : ℤ, ‖radiusQuotient m (realSlice u) - radiusQuotientLeading m‖ ^ 2 :=
    hq.le_tsum n (fun m _ => sq_nonneg _)
  have h2 := Real.abs_le_sqrt h1
  rw [abs_of_nonneg (norm_nonneg _)] at h2
  have h3 : ‖radiusQuotient n (realSlice u)‖ ≤
      ‖radiusQuotientLeading n‖ + ‖radiusQuotient n (realSlice u) - radiusQuotientLeading n‖ := by
    have := norm_add_le (radiusQuotientLeading n) (radiusQuotient n (realSlice u) - radiusQuotientLeading n)
    simpa [add_sub_cancel] using this
  rw [norm_radiusQuotientLeading] at h3
  linarith

/-- Conjunct (5) of G5-005. -/
theorem part5 (u : PhysicalL2)
    (hq : Summable (fun n : ℤ => ‖radiusQuotient n (realSlice u) - radiusQuotientLeading n‖ ^ 2)) :
    Memℓp (fun n : ℤ => pairGradientNorm
      (radiusQuotient n (realSlice u) •
          pairGradient (fun ψ => antiDiscrim ψ (muSeq (realSlice u) n)) (realSlice u) -
        (Complex.I / 2) • (fourierMode 1 n - fourierMode (-1) n))) 2 := by
  obtain ⟨M, hM0, hM⟩ := q_bound u hq
  obtain ⟨C, hC⟩ := NlsGge.Atomic.G1029S3.G1029_main (2 * (‖u‖ + 1)) ‖u‖
  obtain ⟨-, -, -, h29⟩ := hC (realSlice u) (fun n => (gkMu u n : ℂ)) (hyp_phi u) (hyp_xi u)
  have hA : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ k : Fin 2,
      Summable (fun n : ℤ => ‖NlsGge.Atomic.G1087S2.P6.Gdf (realSlice u) (gkMu u n : ℂ) t k -
        NlsGge.Atomic.G1087S2.P6.leadf (gkMu u n : ℂ) t k‖ ^ 2) ∧
      ∑' n : ℤ, ‖NlsGge.Atomic.G1087S2.P6.Gdf (realSlice u) (gkMu u n : ℂ) t k -
        NlsGge.Atomic.G1087S2.P6.leadf (gkMu u n : ℂ) t k‖ ^ 2 ≤ C :=
    fun t h0 h1 k => (h29 t h0 h1 k).2
  have hε := eps_summable u
  set Ce : ℝ := ∑' n : ℤ, |gkMu u n - (n : ℝ) * Real.pi| ^ 2 with hCe
  set Cr : ℝ := ∑' n : ℤ, ‖radiusQuotient n (realSlice u) - radiusQuotientLeading n‖ ^ 2 with hCr
  let R : ℤ → PairKernelCont38 := fun n =>
    radiusQuotient n (realSlice u) • gradAntiDiscrimCont38 (realSlice u) (muSeq (realSlice u) n) -
      (Complex.I / 2) • fkD n
  have hfun : (fun n : ℤ => pairGradientNorm
      (radiusQuotient n (realSlice u) •
          pairGradient (fun ψ => antiDiscrim ψ (muSeq (realSlice u) n)) (realSlice u) -
        (Complex.I / 2) • (fourierMode 1 n - fourierMode (-1) n))) =
      fun n : ℤ => pairGradientNorm (pairKernelL2Class38 (R n)) := by
    funext n
    rw [pairGradient_antiDiscrim, ← class_fkD n, ← class_smul_sub_smul]
  rw [hfun]
  refine memlp_of_sq_summable ?_
  refine summable_pgn_sq R (B := 3 * M ^ 2 * (C + C) + 6 * M ^ 2 * Ce + 6 * Cr) ∅ (fun t S _ => ?_)
  have ht0 : 0 ≤ t.1 := t.2.1
  have ht1 : t.1 ≤ 1 := t.2.2
  -- notation for the three scalar sequences
  set a : ℤ → Fin 2 → ℝ := fun n k => ‖NlsGge.Atomic.G1087S2.P6.Gdf (realSlice u) (gkMu u n : ℂ) t.1 k -
        NlsGge.Atomic.G1087S2.P6.leadf (gkMu u n : ℂ) t.1 k‖ with ha
  set e : ℤ → ℝ := fun n => |gkMu u n - (n : ℝ) * Real.pi| with he
  set r : ℤ → ℝ := fun n => ‖radiusQuotient n (realSlice u) - radiusQuotientLeading n‖ with hr
  have hpt : ∀ n : ℤ, ∀ k : Fin 2, ‖R n t k‖ ≤ M * a n k + M * e n + r n := by
    intro n k
    have hmem : t.1 ∈ Icc (0 : ℝ) 1 := t.2
    have hR : R n t k = radiusQuotient n (realSlice u) *
        gradAntiDiscrim38 (realSlice u) (gkMu u n : ℂ) t.1 k -
        (Complex.I / 2) * pairKernelExt38 (fkD n) t.1 k := by
      simp only [R, ContinuousMap.sub_apply, ContinuousMap.smul_apply, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul, muSeq_eq_gkMu38]
      rw [pairKernelExt38_of_mem _ hmem]
      rfl
    rw [hR, gradAnti_eq_Gdf _ _ hmem k]
    have hs : ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n) = 1 := by
      rw [← mul_zpow]; norm_num
    refine core_bound (radiusQuotient n (realSlice u)) (radiusQuotientLeading n) _
      (NlsGge.Atomic.G1087S2.P6.leadf (gkMu u n : ℂ) t.1 k)
      (NlsGge.Atomic.G1087S2.P6.leadf ((n : ℂ) * (Real.pi : ℂ)) t.1 k)
      (pairKernelExt38 (fkD n) t.1 k) ((-1 : ℂ) ^ n) M (a n k) (e n) (r n) ?_ ?_ (hM n) le_rfl ?_ le_rfl
      (norm_lead0 n hmem k)
    · have h := lead0_eq n hmem k
      rw [h, ← mul_assoc, hs, one_mul]
    · unfold radiusQuotientLeading; ring
    · have h := lead_dist (gkMu u n) ((n : ℝ) * Real.pi) t.1 hmem k
      have e1 : (((n : ℝ) * Real.pi : ℝ) : ℂ) = (n : ℂ) * (Real.pi : ℂ) := by push_cast; ring
      rw [e1] at h
      exact h
  have hmass : ∀ n : ℤ, ‖R n t 0‖ ^ 2 + ‖R n t 1‖ ^ 2 ≤
      3 * M ^ 2 * (a n 0 ^ 2 + a n 1 ^ 2) + 6 * M ^ 2 * e n ^ 2 + 6 * r n ^ 2 := by
    intro n
    have h0 := hpt n 0
    have h1 := hpt n 1
    have a0 : 0 ≤ a n 0 := norm_nonneg _
    have a1 : 0 ≤ a n 1 := norm_nonneg _
    have e0 : 0 ≤ e n := abs_nonneg _
    have r0 : 0 ≤ r n := norm_nonneg _
    have b0 : ‖R n t 0‖ ^ 2 ≤ (M * a n 0 + M * e n + r n) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h0 2
    have b1 : ‖R n t 1‖ ^ 2 ≤ (M * a n 1 + M * e n + r n) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (M * a n 0 - M * e n), sq_nonneg (M * e n - r n), sq_nonneg (M * a n 0 - r n),
      sq_nonneg (M * a n 1 - M * e n), sq_nonneg (M * a n 1 - r n)]
  have hsa : ∀ k : Fin 2, ∑ n ∈ S, a n k ^ 2 ≤ C := fun k =>
    ((hA t.1 ht0 ht1 k).1.sum_le_tsum S (fun n _ => sq_nonneg _)).trans (hA t.1 ht0 ht1 k).2
  have hse : ∑ n ∈ S, e n ^ 2 ≤ Ce := hε.sum_le_tsum S (fun n _ => sq_nonneg _)
  have hsr : ∑ n ∈ S, r n ^ 2 ≤ Cr := hq.sum_le_tsum S (fun n _ => sq_nonneg _)
  calc ∑ n ∈ S, (‖R n t 0‖ ^ 2 + ‖R n t 1‖ ^ 2)
      ≤ ∑ n ∈ S, (3 * M ^ 2 * (a n 0 ^ 2 + a n 1 ^ 2) + 6 * M ^ 2 * e n ^ 2 + 6 * r n ^ 2) :=
        Finset.sum_le_sum (fun n _ => hmass n)
    _ = 3 * M ^ 2 * (∑ n ∈ S, a n 0 ^ 2 + ∑ n ∈ S, a n 1 ^ 2) + 6 * M ^ 2 * ∑ n ∈ S, e n ^ 2 +
          6 * ∑ n ∈ S, r n ^ 2 := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ 3 * M ^ 2 * (C + C) + 6 * M ^ 2 * Ce + 6 * Cr := by
        have := hsa 0
        have := hsa 1
        have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
        nlinarith

end
end NlsGge.ThirdConsultation.G5005Support4
