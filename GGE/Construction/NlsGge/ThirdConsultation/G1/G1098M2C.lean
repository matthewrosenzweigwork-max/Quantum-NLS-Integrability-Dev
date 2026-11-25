import NlsGge.GK38.PairAsymptoticsSeq
import NlsGge.Atomic.G1.G1062
import NlsGge.ThirdConsultation.G1.G1098M2B

                                                                      
                                                                     
                                                                                             
                                                                                             
                                                                                       
                                                                                                 
                                                                        
                                                                                              
set_option autoImplicit false
open Filter Topology MeasureTheory Set
open scoped Matrix.Norms.Elementwise
open NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.G1098M2B
namespace NlsGge.ThirdConsultation.G1098M2C
noncomputable section

/-- The state's value at `t` is the matrix column combination of the fundamental solution. -/
theorem state_apply_fundPair (φ : PotPair) (z : ℂ) (a : PairVec38) (t : Set.Icc (0 : ℝ) 1)
    (i : Fin 2) :
    state φ z a t i = a 0 * fundPair φ z t i 0 + a 1 * fundPair φ z t i 1 := by
  have hext : ext38 (fundContP φ z) (t : ℝ) = fundContP φ z t := ext38_of_mem _ t.2
  show (a 0 • fundColumn38 φ z t 0 + a 1 • fundColumn38 φ z t 1) i = _
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, fundColumn38, hext]
  rfl

/-- The fundamental solution at zero potential is the free solution. -/
theorem fundPair_zero_eq_freeFund (z : ℂ) (t : Set.Icc (0 : ℝ) 1) :
    fundPair 0 z t = freeFund z t := by
  rw [fundPair_eq, fundCont_zero]

/-- Dirichlet labels at zero potential are `nπ`. -/
theorem muSeq_zero_nPi (n : ℤ) : muSeq 0 n = (n : ℂ) * (Real.pi : ℂ) := by
  rw [muSeq_zero38]
  rfl

theorem complexDirState_apply_one (φ : PotPair) (n : ℤ) (t : Set.Icc (0 : ℝ) 1) :
    complexDirState φ n t 1 = fundPair φ (muSeq φ n) t 1 0 + fundPair φ (muSeq φ n) t 1 1 := by
  unfold complexDirState
  rw [state_apply_fundPair]
  simp

theorem complexDirState_zero_apply_one (n : ℤ) (t : Set.Icc (0 : ℝ) 1) :
    complexDirState 0 n t 1 =
      freeFund ((n : ℂ) * (Real.pi : ℂ)) t 1 0 + freeFund ((n : ℂ) * (Real.pi : ℂ)) t 1 1 := by
  rw [complexDirState_apply_one, muSeq_zero_nPi, fundPair_zero_eq_freeFund]

/-- The Dirichlet state error is the row sum of the matrix difference from the vacuum. -/
theorem complexDirState_sub_eq (φ : PotPair) (n : ℤ) (t : Set.Icc (0 : ℝ) 1) :
    complexDirState φ n t 1 - complexDirState 0 n t 1 =
      (fundPair φ (muSeq φ n) t - freeFund ((n : ℂ) * (Real.pi : ℂ)) t) 1 0 +
        (fundPair φ (muSeq φ n) t - freeFund ((n : ℂ) * (Real.pi : ℂ)) t) 1 1 := by
  rw [complexDirState_apply_one, complexDirState_zero_apply_one]
  simp only [Matrix.sub_apply]
  ring

theorem norm_row_sum_sq_le (M : Matrix (Fin 2) (Fin 2) ℂ) :
    ‖M 1 0 + M 1 1‖ ^ 2 ≤ 4 * ‖M‖ ^ 2 := by
  have h : ‖M 1 0 + M 1 1‖ ≤ 2 * ‖M‖ := by
    calc ‖M 1 0 + M 1 1‖ ≤ ‖M 1 0‖ + ‖M 1 1‖ := norm_add_le _ _
      _ ≤ ‖M‖ + ‖M‖ :=
          add_le_add (Matrix.norm_entry_le_entrywise_sup_norm M) (Matrix.norm_entry_le_entrywise_sup_norm M)
      _ = 2 * ‖M‖ := by ring
  calc ‖M 1 0 + M 1 1‖ ^ 2 ≤ (2 * ‖M‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = 4 * ‖M‖ ^ 2 := by ring

theorem norm_add_sq_le_two (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    ‖X + Y‖ ^ 2 ≤ 2 * ‖X‖ ^ 2 + 2 * ‖Y‖ ^ 2 := by
  calc ‖X + Y‖ ^ 2 ≤ (‖X‖ + ‖Y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le X Y) 2
    _ ≤ 2 * ‖X‖ ^ 2 + 2 * ‖Y‖ ^ 2 := by nlinarith [sq_nonneg (‖X‖ - ‖Y‖)]

theorem row_entry_sq_le_of_add (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    ‖(X + Y) 1 0 + (X + Y) 1 1‖ ^ 2 ≤ 8 * ‖X‖ ^ 2 + 8 * ‖Y‖ ^ 2 := by
  calc ‖(X + Y) 1 0 + (X + Y) 1 1‖ ^ 2 ≤ 4 * ‖X + Y‖ ^ 2 := norm_row_sum_sq_le (X + Y)
    _ ≤ 4 * (2 * ‖X‖ ^ 2 + 2 * ‖Y‖ ^ 2) := by
        have := norm_add_sq_le_two X Y
        linarith
    _ = 8 * ‖X‖ ^ 2 + 8 * ‖Y‖ ^ 2 := by ring

/-- Pointwise (in `n` and `t`) square bound for the Dirichlet state error. -/
theorem complexDirState_sub_sq_le (φ : PotPair) (n : ℤ) (t : Set.Icc (0 : ℝ) 1) :
    ‖complexDirState φ n t 1 - complexDirState 0 n t 1‖ ^ 2 ≤
      8 * ‖fundPair φ (muSeq φ n) t - freeFund (muSeq φ n) t‖ ^ 2 +
        8 * ‖freeFund (muSeq φ n) t - freeFund ((n : ℂ) * (Real.pi : ℂ)) t‖ ^ 2 := by
  rw [complexDirState_sub_eq,
    show fundPair φ (muSeq φ n) t - freeFund ((n : ℂ) * (Real.pi : ℂ)) t =
      (fundPair φ (muSeq φ n) t - freeFund (muSeq φ n) t) +
        (freeFund (muSeq φ n) t - freeFund ((n : ℂ) * (Real.pi : ℂ)) t) by abel]
  exact row_entry_sq_le_of_add _ _

/-- Uniform square-sum bound for the complex Dirichlet state error, at each `t ∈ [0,1]`. -/
theorem complexDirState_sub_l2 (R c S : ℝ) :
    ∃ C : ℝ, ∀ φ : PotPair, ‖φ‖ ≤ R → (∀ n : ℤ, ‖muSeq φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ c) →
      Summable (fun n : ℤ => ‖muSeq φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) →
      (∑' n : ℤ, ‖muSeq φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) ≤ S →
      ∀ t : Set.Icc (0 : ℝ) 1,
        Summable (fun n : ℤ => ‖complexDirState φ n t 1 - complexDirState 0 n t 1‖ ^ 2) ∧
        (∑' n : ℤ, ‖complexDirState φ n t 1 - complexDirState 0 n t 1‖ ^ 2) ≤ C := by
  obtain ⟨CX, hCX⟩ := fundPair_seq_l2 R (max c 0)
  refine ⟨8 * CX + 8 * ((2 * Real.exp (max c 0)) ^ 2 * S), fun φ hφ hμ hs hS t => ?_⟩
  have hμ' : ∀ n : ℤ, ‖muSeq φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ max c 0 :=
    fun n => (hμ n).trans (le_max_left c 0)
  obtain ⟨hXs, hXle⟩ := hCX φ hφ (muSeq φ) hμ' t
  obtain ⟨hYs, hYle⟩ := freeFund_shift_l2 (le_max_right c 0) hμ' hs t
  have hbound : ∀ n : ℤ, ‖complexDirState φ n t 1 - complexDirState 0 n t 1‖ ^ 2 ≤
      8 * ‖fundPair φ (muSeq φ n) t - freeFund (muSeq φ n) t‖ ^ 2 +
        8 * ‖freeFund (muSeq φ n) t - freeFund ((n : ℂ) * (Real.pi : ℂ)) t‖ ^ 2 :=
    fun n => complexDirState_sub_sq_le φ n t
  have hXs8 := hXs.mul_left 8
  have hYs8 := hYs.mul_left 8
  have hsum := hXs8.add hYs8
  have hdom : Summable (fun n : ℤ => ‖complexDirState φ n t 1 - complexDirState 0 n t 1‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _) hbound hsum
  refine ⟨hdom, ?_⟩
  have hB : (∑' n : ℤ, ‖freeFund (muSeq φ n) t - freeFund ((n : ℂ) * (Real.pi : ℂ)) t‖ ^ 2) ≤
      (2 * Real.exp (max c 0)) ^ 2 * S :=
    hYle.trans (mul_le_mul_of_nonneg_left hS (by positivity))
  calc ∑' n : ℤ, ‖complexDirState φ n t 1 - complexDirState 0 n t 1‖ ^ 2
      ≤ ∑' n : ℤ, (8 * ‖fundPair φ (muSeq φ n) t - freeFund (muSeq φ n) t‖ ^ 2 +
          8 * ‖freeFund (muSeq φ n) t - freeFund ((n : ℂ) * (Real.pi : ℂ)) t‖ ^ 2) :=
        Summable.tsum_le_tsum hbound hdom hsum
    _ = 8 * ∑' n : ℤ, ‖fundPair φ (muSeq φ n) t - freeFund (muSeq φ n) t‖ ^ 2 +
        8 * ∑' n : ℤ, ‖freeFund (muSeq φ n) t - freeFund ((n : ℂ) * (Real.pi : ℂ)) t‖ ^ 2 := by
        rw [Summable.tsum_add hXs8 hYs8, tsum_mul_left, tsum_mul_left]
    _ ≤ 8 * CX + 8 * ((2 * Real.exp (max c 0)) ^ 2 * S) := by
        linarith

end
end NlsGge.ThirdConsultation.G1098M2C
