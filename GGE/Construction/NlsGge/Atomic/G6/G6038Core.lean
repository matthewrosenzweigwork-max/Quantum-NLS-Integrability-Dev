import Mathlib
import NlsGge.Atomic.G6.G6038Host

                                                                                                                          
                                                                                                             
                                                                                                                    
                                                                                                                
                                                                                                                
                                                             
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped ENNReal
open NlsGge.GK38
open NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.G6038S
noncomputable section

theorem hasSum_norm1 (I : ComplexActionSpace) : HasSum (fun n : ℤ => ‖I n‖) ‖I‖ := by
  have h := lp.hasSum_norm (p := (1 : ℝ≥0∞)) (by norm_num) I
  simpa only [ENNReal.toReal_one, Real.rpow_one] using h

theorem root_apply (I : ComplexActionSpace) (n : ℤ) : complexActionRoot I n = Complex.sqrt (I n) := rfl

theorem norm_root_sq (I : ComplexActionSpace) : ‖complexActionRoot I‖ ^ 2 = ‖I‖ := by
  have h := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (complexActionRoot I)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  have he : (fun n : ℤ => ‖complexActionRoot I n‖ ^ 2) = fun n => ‖I n‖ := by
    funext n
    rw [root_apply, ← norm_pow, NlsGge.GK38.Lib.sqrt_sq]
  rw [he] at h
  exact h.unique (hasSum_norm1 I)

theorem trunc_apply (N : ℕ) (I : ComplexActionSpace) (n : ℤ) :
    (truncateComplexActions N I : ℤ → ℂ) n = if n ∈ Lib.win N then I n else 0 := by
  unfold truncateComplexActions
  have h := map_sum (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 1 n) (fun k => lp.single 1 k (I k)) (Lib.win N)
  have e : ∀ x : ComplexActionSpace, lp.evalCLM ℂ (fun _ : ℤ => ℂ) 1 n x = (x : ℤ → ℂ) n := fun x => rfl
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

theorem norm_trunc_le (N : ℕ) (I : ComplexActionSpace) : ‖truncateComplexActions N I‖ ≤ ‖I‖ := by
  have hT := hasSum_norm1 (truncateComplexActions N I)
  have hI := hasSum_norm1 I
  rw [← hT.tsum_eq, ← hI.tsum_eq]
  refine hT.summable.tsum_le_tsum (fun n => ?_) hI.summable
  rw [trunc_apply]
  split_ifs
  · exact le_rfl
  · rw [norm_zero]; exact norm_nonneg _

theorem G6038_of (f : ComplexDiagonalSpace → ℂ) (r M : ℝ)
    (hr : 0 < r) (hbd : ∀ x ∈ Metric.ball (0 : ComplexDiagonalSpace) r, ‖f x‖ ≤ M) :
  (∀ I : ComplexActionSpace, ‖complexActionRoot I‖^2 = ‖I‖ ∧
    ∀ n : ℤ, (complexActionRoot I n)^2 = I n) ∧
  ∀ (N : ℕ) (I : ComplexActionSpace), ‖I‖ < r^2 →
    ‖finiteActionDescent f N I‖ ≤ M := by
  refine ⟨fun I => ⟨norm_root_sq I, fun n => by rw [root_apply, NlsGge.GK38.Lib.sqrt_sq]⟩, fun N I hI => ?_⟩
  unfold finiteActionDescent actionDescent
  apply hbd
  rw [Metric.mem_ball, dist_zero_right]
  have h2 : ‖complexActionRoot (truncateComplexActions N I)‖ ^ 2 < r ^ 2 := by
    rw [norm_root_sq]; exact lt_of_le_of_lt (norm_trunc_le N I) hI
  exact lt_of_pow_lt_pow_left₀ 2 hr.le h2

end
end NlsGge.ThirdConsultation.G6038S
