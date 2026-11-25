import NlsGge.GK38.PairAsymptoticsSeq
import NlsGge.Atomic.G1.G1062
import NlsGge.ThirdConsultation.G1.G1098Host
import NlsGge.ThirdConsultation.G1.G1098M2B
import NlsGge.ThirdConsultation.G1.G1098M2C

                                                                     
                                                                    
                                                                                        
                                                                                               
                                                                                 
                                                                                                   
                                                                                                 
                                                                                              
                          
set_option autoImplicit false
open Filter Topology MeasureTheory Set
open scoped Matrix.Norms.Elementwise
open NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.G1098M2C
open NlsGge.ThirdConsultation.G1098M2B
namespace NlsGge.ThirdConsultation.G1098M2CT
noncomputable section

/-- The closed-interval point `t = 1`. -/
def tOneIcc : Set.Icc (0 : ℝ) 1 := ⟨1, by norm_num, le_rfl⟩

/-- Vacuum-subtracted fundamental matrix error, square-summable with one constant (Theorem 2.4 with
the free-shift estimate M2b). The constant is independent of `t`. -/
theorem fundPair_vacuum_error_l2 (R c S : ℝ) :
    ∃ C : ℝ, ∀ φ : PotPair, ‖φ‖ ≤ R → (∀ n : ℤ, ‖muSeq φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ c) →
      Summable (fun n : ℤ => ‖muSeq φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) →
      (∑' n : ℤ, ‖muSeq φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) ≤ S →
      ∀ t : Set.Icc (0 : ℝ) 1,
        Summable (fun n : ℤ =>
          ‖fundPair φ (muSeq φ n) t - freeFund ((n : ℂ) * (Real.pi : ℂ)) t‖ ^ 2) ∧
        (∑' n : ℤ, ‖fundPair φ (muSeq φ n) t - freeFund ((n : ℂ) * (Real.pi : ℂ)) t‖ ^ 2) ≤ C := by
  obtain ⟨CX, hCX⟩ := fundPair_seq_l2 R (max c 0)
  refine ⟨2 * CX + 2 * ((2 * Real.exp (max c 0)) ^ 2 * S), fun φ hφ hμ hs hS t => ?_⟩
  have hμ' : ∀ n : ℤ, ‖muSeq φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ max c 0 :=
    fun n => (hμ n).trans (le_max_left c 0)
  obtain ⟨hXs, hXle⟩ := hCX φ hφ (muSeq φ) hμ' t
  obtain ⟨hYs, hYle⟩ := freeFund_shift_l2 (le_max_right c 0) hμ' hs t
  have hbound : ∀ n : ℤ,
      ‖fundPair φ (muSeq φ n) t - freeFund ((n : ℂ) * (Real.pi : ℂ)) t‖ ^ 2 ≤
        2 * ‖fundPair φ (muSeq φ n) t - freeFund (muSeq φ n) t‖ ^ 2 +
          2 * ‖freeFund (muSeq φ n) t - freeFund ((n : ℂ) * (Real.pi : ℂ)) t‖ ^ 2 := by
    intro n
    rw [show fundPair φ (muSeq φ n) t - freeFund ((n : ℂ) * (Real.pi : ℂ)) t =
      (fundPair φ (muSeq φ n) t - freeFund (muSeq φ n) t) +
        (freeFund (muSeq φ n) t - freeFund ((n : ℂ) * (Real.pi : ℂ)) t) by abel]
    exact norm_add_sq_le_two _ _
  have hXs2 := hXs.mul_left 2
  have hYs2 := hYs.mul_left 2
  have hsum := hXs2.add hYs2
  have hdom : Summable (fun n : ℤ =>
      ‖fundPair φ (muSeq φ n) t - freeFund ((n : ℂ) * (Real.pi : ℂ)) t‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _) hbound hsum
  refine ⟨hdom, ?_⟩
  have hB : (∑' n : ℤ, ‖freeFund (muSeq φ n) t - freeFund ((n : ℂ) * (Real.pi : ℂ)) t‖ ^ 2) ≤
      (2 * Real.exp (max c 0)) ^ 2 * S :=
    hYle.trans (mul_le_mul_of_nonneg_left hS (by positivity))
  calc ∑' n : ℤ, ‖fundPair φ (muSeq φ n) t - freeFund ((n : ℂ) * (Real.pi : ℂ)) t‖ ^ 2
      ≤ ∑' n : ℤ, (2 * ‖fundPair φ (muSeq φ n) t - freeFund (muSeq φ n) t‖ ^ 2 +
          2 * ‖freeFund (muSeq φ n) t - freeFund ((n : ℂ) * (Real.pi : ℂ)) t‖ ^ 2) :=
        Summable.tsum_le_tsum hbound hdom hsum
    _ = 2 * ∑' n : ℤ, ‖fundPair φ (muSeq φ n) t - freeFund (muSeq φ n) t‖ ^ 2 +
        2 * ∑' n : ℤ, ‖freeFund (muSeq φ n) t - freeFund ((n : ℂ) * (Real.pi : ℂ)) t‖ ^ 2 := by
        rw [Summable.tsum_add hXs2 hYs2, tsum_mul_left, tsum_mul_left]
    _ ≤ 2 * CX + 2 * ((2 * Real.exp (max c 0)) ^ 2 * S) := by linarith

/-- Column sums of a matrix are bounded by twice its elementwise maximum norm. -/
theorem norm_col_sum_le (M : Matrix (Fin 2) (Fin 2) ℂ) (j : Fin 2) :
    ‖M 0 j + M 1 j‖ ≤ 2 * ‖M‖ := by
  calc ‖M 0 j + M 1 j‖ ≤ ‖M 0 j‖ + ‖M 1 j‖ := norm_add_le _ _
    _ ≤ ‖M‖ + ‖M‖ :=
        add_le_add (Matrix.norm_entry_le_entrywise_sup_norm M) (Matrix.norm_entry_le_entrywise_sup_norm M)
    _ = 2 * ‖M‖ := by ring

/-- Entries of the free solution at `z = nπ` (real) have modulus at most one on `[0,1]`. -/
theorem freeFund_nPi_entry_le (n : ℤ) (t : Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    ‖freeFund ((n : ℂ) * (Real.pi : ℂ)) t i j‖ ≤ 1 := by
  have h := norm_freeE_entry_le ((n : ℂ) * (Real.pi : ℂ)) (t : ℝ) i j
  have him : ((n : ℂ) * (Real.pi : ℂ)).im = 0 := by simp [Complex.mul_im]
  rw [him, abs_zero, zero_mul, Real.exp_zero] at h
  exact h

theorem freeFund_nPi_col_sum_le (n : ℤ) (t : Set.Icc (0 : ℝ) 1) (j : Fin 2) :
    ‖freeFund ((n : ℂ) * (Real.pi : ℂ)) t 0 j + freeFund ((n : ℂ) * (Real.pi : ℂ)) t 1 j‖ ≤ 2 := by
  calc ‖freeFund ((n : ℂ) * (Real.pi : ℂ)) t 0 j + freeFund ((n : ℂ) * (Real.pi : ℂ)) t 1 j‖
      ≤ ‖freeFund ((n : ℂ) * (Real.pi : ℂ)) t 0 j‖ + ‖freeFund ((n : ℂ) * (Real.pi : ℂ)) t 1 j‖ :=
        norm_add_le _ _
    _ ≤ 1 + 1 := add_le_add (freeFund_nPi_entry_le n t 0 j) (freeFund_nPi_entry_le n t 1 j)
    _ = 2 := by norm_num

/-- Seed difference, first index (column 1 of the monodromy). -/
theorem seed_sub_le (A B : Matrix (Fin 2) (Fin 2) ℂ) (j : Fin 2) :
    ‖(A 0 j + A 1 j) - (B 0 j + B 1 j)‖ ≤ 2 * ‖A - B‖ := by
  have h : (A 0 j + A 1 j) - (B 0 j + B 1 j) = (A - B) 0 j + (A - B) 1 j := by
    simp only [Matrix.sub_apply]; ring
  rw [h]
  exact norm_col_sum_le (A - B) j

/-- Seed difference, second index (negated column). -/
theorem seed_neg_sub_le (A B : Matrix (Fin 2) (Fin 2) ℂ) (j : Fin 2) :
    ‖-(A 0 j + A 1 j) - -(B 0 j + B 1 j)‖ ≤ 2 * ‖A - B‖ := by
  have h : -(A 0 j + A 1 j) - -(B 0 j + B 1 j) = -((A - B) 0 j + (A - B) 1 j) := by
    simp only [Matrix.sub_apply]; ring
  rw [h, norm_neg]
  exact norm_col_sum_le (A - B) j

/-- Scalar estimate: `|a f - a₀ g| ≤ p(1+q) + 2q` when `|a - a₀| ≤ p`, `|a₀| ≤ 2`, `|g| ≤ 1` and
`|f - g| ≤ q`. -/
theorem norm_mul_sub_mul_le {a a0 f g : ℂ} {p q : ℝ} (hp : ‖a - a0‖ ≤ p) (ha0 : ‖a0‖ ≤ 2)
    (hg : ‖g‖ ≤ 1) (hfg : ‖f - g‖ ≤ q) :
    ‖a * f - a0 * g‖ ≤ p * (1 + q) + 2 * q := by
  have hf : ‖f‖ ≤ 1 + q := by
    have h1 : f = g + (f - g) := by ring
    have h2 := norm_add_le g (f - g)
    rw [← h1] at h2
    linarith
  have key : a * f - a0 * g = (a - a0) * f + a0 * (f - g) := by ring
  rw [key]
  have hp0 : 0 ≤ p := le_trans (norm_nonneg _) hp
  have h1 : ‖a - a0‖ * ‖f‖ ≤ p * (1 + q) := mul_le_mul hp hf (norm_nonneg _) hp0
  have h2 : ‖a0‖ * ‖f - g‖ ≤ 2 * q := mul_le_mul ha0 hfg (norm_nonneg _) (by norm_num)
  calc ‖(a - a0) * f + a0 * (f - g)‖ ≤ ‖(a - a0) * f‖ + ‖a0 * (f - g)‖ := norm_add_le _ _
    _ = ‖a - a0‖ * ‖f‖ + ‖a0‖ * ‖f - g‖ := by rw [norm_mul, norm_mul]
    _ ≤ p * (1 + q) + 2 * q := by linarith

/-- Algebraic square bound used for the terminal state. -/
theorem sq_bound_alg (D q CV T : ℝ) (hD : 0 ≤ D) (hq : 0 ≤ q) (hT : 0 ≤ T)
    (hTle : T ≤ 4 * D * (1 + q) + 4 * q) (hq2 : q ^ 2 ≤ CV) :
    T ^ 2 ≤ 64 * (1 + CV) * D ^ 2 + 32 * q ^ 2 := by
  have h1 : T ^ 2 ≤ (4 * D * (1 + q) + 4 * q) ^ 2 := pow_le_pow_left₀ hT hTle 2
  have h2 : (4 * D * (1 + q) + 4 * q) ^ 2 ≤ 2 * (4 * D * (1 + q)) ^ 2 + 2 * (4 * q) ^ 2 := by
    nlinarith [sq_nonneg (4 * D * (1 + q) - 4 * q)]
  have h3 : (1 + q) ^ 2 ≤ 2 + 2 * q ^ 2 := by nlinarith [sq_nonneg (q - 1)]
  have h4 : D ^ 2 * (1 + q) ^ 2 ≤ D ^ 2 * (2 + 2 * q ^ 2) :=
    mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
  have h5 : D ^ 2 * q ^ 2 ≤ D ^ 2 * CV := mul_le_mul_of_nonneg_left hq2 (sq_nonneg _)
  nlinarith [h1, h2, h4, h5]

/-- Terminal-state formula at `t`, from `state_apply_fundPair`. -/
theorem complexTerminalState_apply_one (φ : PotPair) (n : ℤ) (t : Set.Icc (0 : ℝ) 1) :
    complexTerminalState φ n t 1 =
      terminalSeed φ (muSeq φ n) 0 * fundPair φ (muSeq φ n) t 1 0 +
        terminalSeed φ (muSeq φ n) 1 * fundPair φ (muSeq φ n) t 1 1 := by
  unfold complexTerminalState
  rw [state_apply_fundPair]

/-- The terminal seed is the column-sum vector of the monodromy `fundPair _ 1`. -/
theorem terminalSeed_eq_fundPair (φ : PotPair) (z : ℂ) :
    terminalSeed φ z = ![fundPair φ z tOneIcc 0 1 + fundPair φ z tOneIcc 1 1,
      -(fundPair φ z tOneIcc 0 0 + fundPair φ z tOneIcc 1 0)] := rfl

/-- Algebraic core: the difference of two terminal combinations, bounded by `Δ = A - B` (the
monodromy error) and `δ = F - G` (the state error at `t`). -/
theorem terminal_core_bound (A B F G : Matrix (Fin 2) (Fin 2) ℂ)
    (hB : ∀ i j, ‖B i j‖ ≤ 1) (hG : ∀ i j, ‖G i j‖ ≤ 1) :
    ‖((A 0 1 + A 1 1) * F 1 0 + (-(A 0 0 + A 1 0)) * F 1 1) -
        ((B 0 1 + B 1 1) * G 1 0 + (-(B 0 0 + B 1 0)) * G 1 1)‖ ≤
      4 * ‖A - B‖ * (1 + ‖F - G‖) + 4 * ‖F - G‖ := by
  have hF0 : ‖F 1 0 - G 1 0‖ ≤ ‖F - G‖ := by
    rw [← Matrix.sub_apply]; exact Matrix.norm_entry_le_entrywise_sup_norm _
  have hF1 : ‖F 1 1 - G 1 1‖ ≤ ‖F - G‖ := by
    rw [← Matrix.sub_apply]; exact Matrix.norm_entry_le_entrywise_sup_norm _
  have hb0 : ‖B 0 1 + B 1 1‖ ≤ 2 :=
    (norm_add_le _ _).trans (by linarith [hB 0 1, hB 1 1])
  have hb1 : ‖-(B 0 0 + B 1 0)‖ ≤ 2 := by
    rw [norm_neg]; exact (norm_add_le _ _).trans (by linarith [hB 0 0, hB 1 0])
  have hT0 := norm_mul_sub_mul_le (seed_sub_le A B 1) hb0 (hG 1 0) hF0
  have hT1 := norm_mul_sub_mul_le (seed_neg_sub_le A B 0) hb1 (hG 1 1) hF1
  have hsplit : ((A 0 1 + A 1 1) * F 1 0 + (-(A 0 0 + A 1 0)) * F 1 1) -
        ((B 0 1 + B 1 1) * G 1 0 + (-(B 0 0 + B 1 0)) * G 1 1) =
      ((A 0 1 + A 1 1) * F 1 0 - (B 0 1 + B 1 1) * G 1 0) +
        ((-(A 0 0 + A 1 0)) * F 1 1 - (-(B 0 0 + B 1 0)) * G 1 1) := by ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  linarith

/-- Pointwise (in `n` and `t`) bound on the terminal state error, given the uniform bound
`‖δ‖² ≤ CV` for the fundamental error at time `t`. -/
theorem terminal_pointwise_bound (φ : PotPair) (n : ℤ) (t : Set.Icc (0 : ℝ) 1) (CV : ℝ)
    (hδ : ‖fundPair φ (muSeq φ n) t - freeFund ((n : ℂ) * (Real.pi : ℂ)) t‖ ^ 2 ≤ CV) :
    ‖complexTerminalState φ n t 1 - complexTerminalState 0 n t 1‖ ^ 2 ≤
      64 * (1 + CV) *
          ‖fundPair φ (muSeq φ n) tOneIcc - freeFund ((n : ℂ) * (Real.pi : ℂ)) tOneIcc‖ ^ 2 +
        32 * ‖fundPair φ (muSeq φ n) t - freeFund ((n : ℂ) * (Real.pi : ℂ)) t‖ ^ 2 := by
  have hVac : complexTerminalState 0 n t 1 =
      terminalSeed 0 (muSeq 0 n) 0 * fundPair 0 (muSeq 0 n) t 1 0 +
        terminalSeed 0 (muSeq 0 n) 1 * fundPair 0 (muSeq 0 n) t 1 1 :=
    complexTerminalState_apply_one 0 n t
  rw [complexTerminalState_apply_one φ n t, hVac, muSeq_zero_nPi, terminalSeed_eq_fundPair,
    terminalSeed_eq_fundPair]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    fundPair_zero_eq_freeFund]
  exact sq_bound_alg _ _ CV _ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (terminal_core_bound _ _ _ _ (fun i j => freeFund_nPi_entry_le n tOneIcc i j)
      (fun i j => freeFund_nPi_entry_le n t i j)) hδ

/-- Uniform square-sum bound for the complex terminal state error, at each `t ∈ [0,1]`. -/
theorem complexTerminalState_sub_l2 (R c S : ℝ) :
    ∃ C : ℝ, ∀ φ : PotPair, ‖φ‖ ≤ R → (∀ n : ℤ, ‖muSeq φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ c) →
      Summable (fun n : ℤ => ‖muSeq φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) →
      (∑' n : ℤ, ‖muSeq φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) ≤ S →
      ∀ t : Set.Icc (0 : ℝ) 1,
        Summable (fun n : ℤ =>
          ‖complexTerminalState φ n t 1 - complexTerminalState 0 n t 1‖ ^ 2) ∧
        (∑' n : ℤ, ‖complexTerminalState φ n t 1 - complexTerminalState 0 n t 1‖ ^ 2) ≤ C := by
  obtain ⟨CV, hV⟩ := fundPair_vacuum_error_l2 R c S
  refine ⟨64 * (1 + CV) * CV + 32 * CV, fun φ hφ hμ hs hS t => ?_⟩
  obtain ⟨hΔs, hΔle⟩ := hV φ hφ hμ hs hS tOneIcc
  obtain ⟨hδs, hδle⟩ := hV φ hφ hμ hs hS t
  have hCV0 : 0 ≤ CV := (tsum_nonneg fun n : ℤ => sq_nonneg _).trans hΔle
  have hδpt : ∀ n : ℤ, ‖fundPair φ (muSeq φ n) t - freeFund ((n : ℂ) * (Real.pi : ℂ)) t‖ ^ 2 ≤ CV :=
    fun n => (hδs.le_tsum n (fun j _ => sq_nonneg _)).trans hδle
  have hpt : ∀ n : ℤ, ‖complexTerminalState φ n t 1 - complexTerminalState 0 n t 1‖ ^ 2 ≤
      64 * (1 + CV) *
          ‖fundPair φ (muSeq φ n) tOneIcc - freeFund ((n : ℂ) * (Real.pi : ℂ)) tOneIcc‖ ^ 2 +
        32 * ‖fundPair φ (muSeq φ n) t - freeFund ((n : ℂ) * (Real.pi : ℂ)) t‖ ^ 2 :=
    fun n => terminal_pointwise_bound φ n t CV (hδpt n)
  have hR := (hΔs.mul_left (64 * (1 + CV))).add (hδs.mul_left 32)
  have hL : Summable (fun n : ℤ =>
      ‖complexTerminalState φ n t 1 - complexTerminalState 0 n t 1‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _) hpt hR
  refine ⟨hL, ?_⟩
  have h1 : 64 * (1 + CV) * (∑' n : ℤ,
      ‖fundPair φ (muSeq φ n) tOneIcc - freeFund ((n : ℂ) * (Real.pi : ℂ)) tOneIcc‖ ^ 2) ≤
      64 * (1 + CV) * CV := mul_le_mul_of_nonneg_left hΔle (by positivity)
  have h2 : 32 * (∑' n : ℤ,
      ‖fundPair φ (muSeq φ n) t - freeFund ((n : ℂ) * (Real.pi : ℂ)) t‖ ^ 2) ≤ 32 * CV :=
    mul_le_mul_of_nonneg_left hδle (by norm_num)
  calc ∑' n : ℤ, ‖complexTerminalState φ n t 1 - complexTerminalState 0 n t 1‖ ^ 2
      ≤ ∑' n : ℤ, (64 * (1 + CV) *
          ‖fundPair φ (muSeq φ n) tOneIcc - freeFund ((n : ℂ) * (Real.pi : ℂ)) tOneIcc‖ ^ 2 +
        32 * ‖fundPair φ (muSeq φ n) t - freeFund ((n : ℂ) * (Real.pi : ℂ)) t‖ ^ 2) :=
        Summable.tsum_le_tsum hpt hL hR
    _ = 64 * (1 + CV) * (∑' n : ℤ,
          ‖fundPair φ (muSeq φ n) tOneIcc - freeFund ((n : ℂ) * (Real.pi : ℂ)) tOneIcc‖ ^ 2) +
        32 * (∑' n : ℤ,
          ‖fundPair φ (muSeq φ n) t - freeFund ((n : ℂ) * (Real.pi : ℂ)) t‖ ^ 2) := by
        rw [Summable.tsum_add (hΔs.mul_left _) (hδs.mul_left _), tsum_mul_left, tsum_mul_left]
    _ ≤ 64 * (1 + CV) * CV + 32 * CV := by linarith

end
end NlsGge.ThirdConsultation.G1098M2CT
