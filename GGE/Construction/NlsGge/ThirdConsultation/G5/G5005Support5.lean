import Mathlib
import NlsGge.Atomic.G5.G5005Host
import NlsGge.ThirdConsultation.G5.G5005Support1
import NlsGge.ThirdConsultation.G5.G5005Support2
import NlsGge.ThirdConsultation.G5.G5005Support4
import NlsGge.ThirdConsultation.KO.Basic
import NlsGge.Atomic.G5.G5001Host
import NlsGge.GK38.GradEigenClosedSpectral
import NlsGge.Atomic.G1.G1029

                                                                                 
                                                                                                    
                                        
                                                                                                          
                                                                                                            
                                                                                                         
                                                                                                                 
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.G5005Support1 NlsGge.ThirdConsultation.G5005Support2
  NlsGge.ThirdConsultation.G5005Support4

namespace NlsGge.ThirdConsultation.G5005Support5
noncomputable section

theorem sq_summable_of_memlp {f : ℤ → ℝ} (h : Memℓp f 2) : Summable (fun n => f n ^ 2) := by
  have := (memℓp_gen_iff (by simp)).mp h
  simpa [Real.norm_eq_abs, sq_abs] using this

/-- Conjunct (3) of G5-005. -/
theorem part3 (u : PhysicalL2) (hu : NlsGge.ThirdConsultation.finiteGap u) :
    Memℓp (fun n : ℤ => pairGradientNorm
      (antiDiscrim (realSlice u) (muSeq (realSlice u) n) •
        pairGradient (radiusQuotient n) (realSlice u))) 2 := by
  have hz : ∀ n : ℤ, n ∉ hu.toFinset → antiDiscrim (realSlice u) (muSeq (realSlice u) n) = 0 := by
    intro n hn
    have hn' : ¬ (NlsGge.SpectralFoundations.actualGapLowerAllE02_38 u n ≠
        NlsGge.SpectralFoundations.actualGapUpperAllE02_38 u n) := by
      exact fun h => hn (hu.mem_toFinset.mpr h)
    have hc : u ∈ NlsGge.GK38.GradEigen38.Z n := not_not.mp hn'
    rw [muSeq_eq_gkMu38]
    exact (NlsGge.GK38.GradEigen38.closed_dirichlet_anti_and_deriv_zero u n hc).1
  refine memlp_of_sq_summable (summable_of_ne_finset_zero (s := hu.toFinset) (fun n hn => ?_))
  rw [hz n hn, zero_smul]
  have : pairGradientNorm (0 : PotPair) = 0 := by
    unfold pairGradientNorm; simp
  rw [this]; ring

theorem pgn_class_fkE_sq_le (n : ℤ) : pairGradientNorm (pairKernelL2Class38 (fkE n)) ^ 2 ≤ 2 := by
  have h := sum_pgn_sq_le (fun _ : ℤ => fkE n) (B := 2) {0} (fun t => by
    have h0 := fkE_apply0 n t.2
    have h1 := fkE_apply1 n t.2
    have e0 : (fkE n) t 0 = pairKernelExt38 (fkE n) t.1 0 := by rw [pairKernelExt38_of_mem _ t.2]
    have e1 : (fkE n) t 1 = pairKernelExt38 (fkE n) t.1 1 := by rw [pairKernelExt38_of_mem _ t.2]
    simp only [Finset.sum_singleton, e0, e1, h0, h1, Complex.norm_exp]
    simp
    norm_num)
  simpa using h

/-- Conjunct (4) of G5-005. -/
theorem part4 (u : PhysicalL2)
    (hq : Summable (fun n : ℤ => ‖radiusQuotient n (realSlice u) - radiusQuotientLeading n‖ ^ 2))
    (h2 : Memℓp (fun n : ℤ => pairGradientNorm
      (pairGradient (fun ψ => muSeq ψ n) (realSlice u) -
        (1 / 2 : ℂ) • (fourierMode 1 n + fourierMode (-1) n))) 2) :
    Memℓp (fun n : ℤ => pairGradientNorm
      ((radiusQuotient n (realSlice u) * deriv (antiDiscrim (realSlice u)) (muSeq (realSlice u) n)) •
        pairGradient (fun ψ => muSeq ψ n) (realSlice u))) 2 := by
  obtain ⟨M, hM0, hM⟩ := q_bound u hq
  obtain ⟨C, hC⟩ := NlsGge.Atomic.G1029S3.G1029_main (2 * (‖u‖ + 1)) ‖u‖
  obtain ⟨-, -, hd, -⟩ := hC (realSlice u) (fun n => (gkMu u n : ℂ)) (hyp_phi u) (hyp_xi u)
  have hd' : Summable (fun n : ℤ =>
      ‖deriv (antiDiscrim (realSlice u)) (muSeq (realSlice u) n)‖ ^ 2) := by
    simp only [muSeq_eq_gkMu38]
    exact hd.1
  have hrem := sq_summable_of_memlp h2
  set Crem : ℝ := ∑' n : ℤ, pairGradientNorm
      (pairGradient (fun ψ => muSeq ψ n) (realSlice u) -
        (1 / 2 : ℂ) • (fourierMode 1 n + fourierMode (-1) n)) ^ 2 with hCrem
  set K2 : ℝ := 2 * Crem + 1 with hK2
  have hφ : realSlice u ∈ gkW := realSlice_mem_gkW u
  have hK : ∀ n : ℤ, pairGradientNorm (pairGradient (fun ψ => muSeq ψ n) (realSlice u)) ^ 2 ≤ K2 := by
    intro n
    have e : pairGradient (fun ψ => muSeq ψ n) (realSlice u) =
        (pairGradient (fun ψ => muSeq ψ n) (realSlice u) -
          (1 / 2 : ℂ) • (fourierMode 1 n + fourierMode (-1) n)) +
        (1 / 2 : ℂ) • (fourierMode 1 n + fourierMode (-1) n) := (sub_add_cancel _ _).symm
    have h1 := pgn_add_sq (pairGradient (fun ψ => muSeq ψ n) (realSlice u) -
          (1 / 2 : ℂ) • (fourierMode 1 n + fourierMode (-1) n))
        ((1 / 2 : ℂ) • (fourierMode 1 n + fourierMode (-1) n))
    rw [← e] at h1
    have h2' : pairGradientNorm (pairGradient (fun ψ => muSeq ψ n) (realSlice u) -
          (1 / 2 : ℂ) • (fourierMode 1 n + fourierMode (-1) n)) ^ 2 ≤ Crem :=
      hrem.le_tsum n (fun m _ => sq_nonneg _)
    have h3 : pairGradientNorm ((1 / 2 : ℂ) • (fourierMode 1 n + fourierMode (-1) n)) ^ 2 ≤ 1 / 2 := by
      rw [← class_fkE, pgn_smul, mul_pow]
      have := pgn_class_fkE_sq_le n
      have h4 : ‖(1 / 2 : ℂ)‖ ^ 2 = 1 / 4 := by norm_num
      rw [h4]
      linarith
    linarith
  refine memlp_of_sq_summable ?_
  refine (hd'.mul_left (M ^ 2 * K2)).of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_)
  rw [pgn_smul, mul_pow, norm_mul, mul_pow]
  have hq2 : ‖radiusQuotient n (realSlice u)‖ ^ 2 ≤ M ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hM n) 2
  have hK' := hK n
  have hd0 : 0 ≤ ‖deriv (antiDiscrim (realSlice u)) (muSeq (realSlice u) n)‖ ^ 2 := sq_nonneg _
  have hP0 : 0 ≤ pairGradientNorm (pairGradient (fun ψ => muSeq ψ n) (realSlice u)) ^ 2 := sq_nonneg _
  calc ‖radiusQuotient n (realSlice u)‖ ^ 2 *
        ‖deriv (antiDiscrim (realSlice u)) (muSeq (realSlice u) n)‖ ^ 2 *
        pairGradientNorm (pairGradient (fun ψ => muSeq ψ n) (realSlice u)) ^ 2
      ≤ M ^ 2 * ‖deriv (antiDiscrim (realSlice u)) (muSeq (realSlice u) n)‖ ^ 2 * K2 := by
        gcongr
    _ = M ^ 2 * K2 * ‖deriv (antiDiscrim (realSlice u)) (muSeq (realSlice u) n)‖ ^ 2 := by ring

end
end NlsGge.ThirdConsultation.G5005Support5
