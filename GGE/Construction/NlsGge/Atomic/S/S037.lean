                                                                                                                         
                                                                                                                                        
import NlsGge.Schur.FiniteLogDetEstimate38V1

                                                                                                                                                                                                    
                                                                           
                                                                                        
                                                                                         
                                                                                  

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace NlsGge.ThirdConsultation.S

def operatorNorm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) : ℝ := ‖B‖

def matrixHSNorm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, (B i j) ^ 2)

namespace S037Aux

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem hsNonneg (X : Matrix ι ι ℝ) : 0 ≤ matrixHSNorm X := by
  unfold matrixHSNorm; exact Real.sqrt_nonneg _

theorem eN_flat_gen (g : ι × ι → ℝ) :
    NlsGge.Schur.eN g = Real.sqrt (∑ i, ∑ j, g (i, j) ^ 2) := by
  unfold NlsGge.Schur.eN
  rw [EuclideanSpace.norm_eq, Fintype.sum_prod_type]
  simp [Real.norm_eq_abs, sq_abs]

theorem trace_cs (X Y : Matrix ι ι ℝ) :
    |Matrix.trace (X * Y)| ≤ matrixHSNorm X * matrixHSNorm Y := by
  have h := NlsGge.Schur.abs_dot_le (fun p : ι × ι => X p.1 p.2) (fun p : ι × ι => Y p.2 p.1)
  have hs : ∑ p : ι × ι, X p.1 p.2 * Y p.2 p.1 = Matrix.trace (X * Y) := by
    rw [Fintype.sum_prod_type]
    simp [Matrix.trace, Matrix.mul_apply]
  have hX : NlsGge.Schur.eN (fun p : ι × ι => X p.1 p.2) = matrixHSNorm X := by
    rw [eN_flat_gen]; rfl
  have hY : NlsGge.Schur.eN (fun p : ι × ι => Y p.2 p.1) = matrixHSNorm Y := by
    rw [eN_flat_gen]
    unfold matrixHSNorm
    rw [Finset.sum_comm]
  rw [hs, hX, hY] at h
  exact h

theorem hs_mul_left (X B : Matrix ι ι ℝ) :
    matrixHSNorm (X * B) ≤ ‖X‖ * matrixHSNorm B := by
  have hcol : ∀ j : ι, ∑ i, (X * B) i j ^ 2 ≤ ‖X‖ ^ 2 * ∑ i, B i j ^ 2 := by
    intro j
    have hcolval : (fun i => (X * B) i j) = X *ᵥ (fun k => B k j) := by
      funext i; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    have hv : NlsGge.Schur.eN (fun i => (X * B) i j) ≤
        ‖X‖ * NlsGge.Schur.eN (fun k => B k j) := by
      rw [hcolval]
      exact NlsGge.Schur.opBound_of_norm X (fun k => B k j)
    have hsq := pow_le_pow_left₀ (NlsGge.Schur.eN_nonneg _) hv 2
    rw [mul_pow, NlsGge.Schur.eN_sq, NlsGge.Schur.eN_sq] at hsq
    exact hsq
  have hsum : ∑ i, ∑ j, (X * B) i j ^ 2 ≤ ‖X‖ ^ 2 * ∑ i, ∑ j, B i j ^ 2 := by
    calc ∑ i, ∑ j, (X * B) i j ^ 2 = ∑ j, ∑ i, (X * B) i j ^ 2 := Finset.sum_comm
      _ ≤ ∑ j, ‖X‖ ^ 2 * ∑ i, B i j ^ 2 := Finset.sum_le_sum fun j _ => hcol j
      _ = ‖X‖ ^ 2 * ∑ j, ∑ i, B i j ^ 2 := by rw [Finset.mul_sum]
      _ = ‖X‖ ^ 2 * ∑ i, ∑ j, B i j ^ 2 := by rw [Finset.sum_comm]
  unfold matrixHSNorm
  calc Real.sqrt (∑ i, ∑ j, (X * B) i j ^ 2)
      ≤ Real.sqrt (‖X‖ ^ 2 * ∑ i, ∑ j, B i j ^ 2) := Real.sqrt_le_sqrt hsum
    _ = ‖X‖ * Real.sqrt (∑ i, ∑ j, B i j ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem norm_pow_succ_le (B : Matrix ι ι ℝ) (n : ℕ) : ‖B ^ (n + 1)‖ ≤ ‖B‖ ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ B (n + 1), pow_succ ‖B‖ (n + 1)]
    exact (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg _))

theorem hs_pow_succ (B : Matrix ι ι ℝ) (n : ℕ) :
    matrixHSNorm (B ^ (n + 1)) ≤ ‖B‖ ^ n * matrixHSNorm B := by
  cases n with
  | zero => simp
  | succ n =>
    rw [pow_succ B (n + 1)]
    calc matrixHSNorm (B ^ (n + 1) * B) ≤ ‖B ^ (n + 1)‖ * matrixHSNorm B := hs_mul_left _ _
      _ ≤ ‖B‖ ^ (n + 1) * matrixHSNorm B :=
          mul_le_mul_of_nonneg_right (norm_pow_succ_le B n) (hsNonneg B)

end S037Aux

open S037Aux in
theorem trace_power_hs_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (k : ℕ) (hk : 2 ≤ k) :
    |Matrix.trace (B ^ k)| ≤
      operatorNorm B ^ (k - 2) * matrixHSNorm B ^ 2 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  have hk2 : n + 2 - 2 = n := by omega
  rw [hk2]
  rw [show B ^ (n + 2) = B ^ (n + 1) * B from pow_succ B (n + 1)]
  calc |Matrix.trace (B ^ (n + 1) * B)| ≤ matrixHSNorm (B ^ (n + 1)) * matrixHSNorm B :=
        trace_cs _ _
    _ ≤ (‖B‖ ^ n * matrixHSNorm B) * matrixHSNorm B :=
        mul_le_mul_of_nonneg_right (hs_pow_succ B n) (hsNonneg B)
    _ = operatorNorm B ^ n * matrixHSNorm B ^ 2 := by unfold operatorNorm; ring

open S037Aux in
theorem higher_log_trace_terms_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ)
    (hB : operatorNorm B ≤ (1 / 2 : ℝ)) :
    Summable
      (fun j : ℕ =>
        |Matrix.trace (B ^ (j + 2))| / ((j : ℝ) + 2)) ∧
    Summable
      (fun j : ℕ =>
        (-1 : ℝ) ^ (j + 3) *
          Matrix.trace (B ^ (j + 2)) / ((j : ℝ) + 2)) ∧
    (∑' j : ℕ,
      |Matrix.trace (B ^ (j + 2))| / ((j : ℝ) + 2)) ≤
        matrixHSNorm B ^ 2 ∧
    |∑' j : ℕ,
      (-1 : ℝ) ^ (j + 3) *
        Matrix.trace (B ^ (j + 2)) / ((j : ℝ) + 2)| ≤
        matrixHSNorm B ^ 2 := by
  have hop0 : 0 ≤ operatorNorm B := by unfold operatorNorm; exact norm_nonneg _
  have hterm : ∀ j : ℕ, |Matrix.trace (B ^ (j + 2))| / ((j : ℝ) + 2) ≤
      (1 / 2 : ℝ) ^ j * (matrixHSNorm B ^ 2 / 2) := by
    intro j
    have h1 := trace_power_hs_bound B (j + 2) (by omega)
    rw [show j + 2 - 2 = j by omega] at h1
    have h2 : operatorNorm B ^ j ≤ (1 / 2 : ℝ) ^ j := pow_le_pow_left₀ hop0 hB j
    have hA : |Matrix.trace (B ^ (j + 2))| ≤ (1 / 2 : ℝ) ^ j * matrixHSNorm B ^ 2 :=
      h1.trans (mul_le_mul_of_nonneg_right h2 (sq_nonneg _))
    have hpos : (0 : ℝ) < (j : ℝ) + 2 := by positivity
    have hpos2 : 0 ≤ (1 / 2 : ℝ) ^ j * matrixHSNorm B ^ 2 := by positivity
    rw [div_le_iff₀ hpos]
    nlinarith [hA, hpos2, mul_nonneg hpos2 (Nat.cast_nonneg (α := ℝ) j)]
  have hgeo : Summable (fun j : ℕ => (1 / 2 : ℝ) ^ j * (matrixHSNorm B ^ 2 / 2)) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
  have hA : Summable (fun j : ℕ => |Matrix.trace (B ^ (j + 2))| / ((j : ℝ) + 2)) :=
    Summable.of_nonneg_of_le (fun j => by positivity) hterm hgeo
  have hsum_le : (∑' j : ℕ, |Matrix.trace (B ^ (j + 2))| / ((j : ℝ) + 2)) ≤ matrixHSNorm B ^ 2 := by
    calc (∑' j : ℕ, |Matrix.trace (B ^ (j + 2))| / ((j : ℝ) + 2))
        ≤ ∑' j : ℕ, (1 / 2 : ℝ) ^ j * (matrixHSNorm B ^ 2 / 2) := hA.tsum_le_tsum hterm hgeo
      _ = matrixHSNorm B ^ 2 := by
          rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
          ring
  have hnorm_eq : ∀ j : ℕ, ‖(-1 : ℝ) ^ (j + 3) * Matrix.trace (B ^ (j + 2)) / ((j : ℝ) + 2)‖ =
      |Matrix.trace (B ^ (j + 2))| / ((j : ℝ) + 2) := by
    intro j
    rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (j : ℝ) + 2)]
  have hB2 : Summable (fun j : ℕ =>
      (-1 : ℝ) ^ (j + 3) * Matrix.trace (B ^ (j + 2)) / ((j : ℝ) + 2)) :=
    Summable.of_norm_bounded (g := fun j : ℕ => (1 / 2 : ℝ) ^ j * (matrixHSNorm B ^ 2 / 2))
      hgeo (fun j => (hnorm_eq j).trans_le (hterm j))
  refine ⟨hA, hB2, hsum_le, ?_⟩
  have hnsum : Summable (fun j : ℕ =>
      ‖(-1 : ℝ) ^ (j + 3) * Matrix.trace (B ^ (j + 2)) / ((j : ℝ) + 2)‖) :=
    hA.congr (fun j => (hnorm_eq j).symm)
  calc |∑' j : ℕ, (-1 : ℝ) ^ (j + 3) * Matrix.trace (B ^ (j + 2)) / ((j : ℝ) + 2)|
      = ‖∑' j : ℕ, (-1 : ℝ) ^ (j + 3) * Matrix.trace (B ^ (j + 2)) / ((j : ℝ) + 2)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∑' j : ℕ, ‖(-1 : ℝ) ^ (j + 3) * Matrix.trace (B ^ (j + 2)) / ((j : ℝ) + 2)‖ :=
        norm_tsum_le_tsum_norm hnsum
    _ = ∑' j : ℕ, |Matrix.trace (B ^ (j + 2))| / ((j : ℝ) + 2) := tsum_congr hnorm_eq
    _ ≤ matrixHSNorm B ^ 2 := hsum_le

end NlsGge.ThirdConsultation.S
end
