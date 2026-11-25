import Mathlib
import NlsGge.ThirdConsultation.M.M023Host
import NlsGge.ThirdConsultation.M.M023Bridge
import NlsGge.ThirdConsultation.M.M021Real
import NlsGge.ThirdConsultation.M.M021Comp
import NlsGge.Atomic.KST.KST005
import NlsGge.Atomic.DM.DM046

   
                                                                         

                                                                                                     
                                                                                                                   
                                                                                               
  

set_option autoImplicit false

open scoped ENNReal BigOperators BoundedContinuousFunction

namespace NlsGge.ThirdConsultation.MTwoMode.WeightedInverse
noncomputable section

open NlsGge.ThirdConsultation.MTwoMode

/-- Reciprocal distance `1/|l-n|`, set to zero at `l = n`. -/
def eSeq (n l : ℤ) : ℝ := if l = n then 0 else 1 / ((l - n).natAbs : ℝ)

theorem eSeq_nonneg (n l : ℤ) : 0 ≤ eSeq n l := by
  unfold eSeq; split_ifs <;> positivity

theorem eSeq_le_one (n l : ℤ) : eSeq n l ≤ 1 := by
  unfold eSeq
  split_ifs with h
  · norm_num
  · have h1 : (1 : ℝ) ≤ ((l - n).natAbs : ℝ) := by
      have : 0 < (l - n).natAbs := Int.natAbs_pos.mpr (sub_ne_zero.mpr h)
      exact_mod_cast this
    exact div_le_one_of_le₀ h1 (by linarith)

theorem eSeq_sq (n l : ℤ) :
    eSeq n l ^ 2 = if l ≠ n then 1 / ((l - n).natAbs : ℝ) ^ 2 else 0 := by
  unfold eSeq
  by_cases h : l = n
  · simp [h]
  · simp [h, one_div, inv_pow]

theorem eSeq_sq_summable (n : ℤ) : Summable fun l => eSeq n l ^ 2 := by
  have hbase0 : Summable (fun d : ℤ => 1 / (d : ℝ) ^ 2) :=
    (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
  have hbase : Summable (fun d : ℤ => 1 / (Int.natAbs d : ℝ) ^ 2) := by
    convert hbase0 using 1 <;> simp [Nat.cast_natAbs, Int.cast_abs, abs_pow]
  have hshift : Summable (fun l : ℤ => 1 / (Int.natAbs (l - n) : ℝ) ^ 2) :=
    hbase.comp_injective (i := fun l : ℤ => l - n) (fun l l' h => by simpa using h)
  refine Summable.of_nonneg_of_le (fun l => sq_nonneg _) (fun l => ?_) hshift
  rw [eSeq_sq]
  split_ifs with h
  · exact le_refl _
  · positivity

theorem eSeq_sq_sum_le (n : ℤ) : ∑' l, eSeq n l ^ 2 ≤ 4 := by
  have h := lattice_reciprocal_sq_bound_contract n
  refine le_trans (le_of_eq (tsum_congr fun l => eSeq_sq n l)) h

theorem eSeq_neg_sq_summable (n : ℤ) : Summable fun l => eSeq n (-l) ^ 2 := by
  have h := ((Equiv.neg ℤ).summable_iff (f := fun l : ℤ => eSeq n l ^ 2)).2 (eSeq_sq_summable n)
  exact h

theorem eSeq_neg_sq_sum_le (n : ℤ) : ∑' l, eSeq n (-l) ^ 2 ≤ 4 := by
  calc ∑' l, eSeq n (-l) ^ 2 = ∑' l, eSeq n l ^ 2 :=
        (Equiv.neg ℤ).tsum_eq (fun l => eSeq n l ^ 2)
    _ ≤ 4 := eSeq_sq_sum_le n

/-- Generic multiplier facts for `D = E · h` with `E` a fixed square-summable profile. -/
theorem D_core (E : ℤ → ℝ) (hE0 : ∀ l, 0 ≤ E l) (hE1 : ∀ l, E l ≤ 1)
    (hEs : Summable fun l => E l ^ 2) (hE4 : ∑' l, E l ^ 2 ≤ 4)
    (h : ℤ → ℂ) (G : ℝ) (hG : 0 ≤ G) (hh : ∀ l, ‖h l‖ ≤ G) :
    (∀ l, ‖(E l : ℂ) * h l‖ ≤ G) ∧ Summable (fun l => ‖(E l : ℂ) * h l‖ ^ 2) ∧
      ∑' l, ‖(E l : ℂ) * h l‖ ^ 2 ≤ 4 * G ^ 2 := by
  have hn : ∀ l, ‖(E l : ℂ) * h l‖ = E l * ‖h l‖ := fun l => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hE0 l)]
  have hsq : ∀ l, ‖(E l : ℂ) * h l‖ ^ 2 ≤ G ^ 2 * E l ^ 2 := fun l => by
    rw [hn l, mul_pow]
    have h1 : ‖h l‖ ^ 2 ≤ G ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hh l) 2
    nlinarith [sq_nonneg (E l), sq_nonneg (‖h l‖)]
  have hsum : Summable (fun l => ‖(E l : ℂ) * h l‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun l => sq_nonneg _) hsq (hEs.mul_left _)
  refine ⟨fun l => ?_, hsum, ?_⟩
  · rw [hn l]
    calc E l * ‖h l‖ ≤ 1 * G := mul_le_mul (hE1 l) (hh l) (norm_nonneg _) zero_le_one
      _ = G := one_mul G
  · calc ∑' l, ‖(E l : ℂ) * h l‖ ^ 2 ≤ ∑' l, G ^ 2 * E l ^ 2 :=
          Summable.tsum_le_tsum hsq hsum (hEs.mul_left _)
      _ = G ^ 2 * ∑' l, E l ^ 2 := tsum_mul_left
      _ ≤ G ^ 2 * 4 := mul_le_mul_of_nonneg_left hE4 (sq_nonneg _)
      _ = 4 * G ^ 2 := mul_comm _ _

/-- The multiplier attached to a bounded sequence `g`: `e(l) g(l)` on the upper branch, reflected on the lower. -/
def Dm (n : ℤ) (g : ℤ →ᵇ ℂ) (b : Bool) (l : ℤ) : ℂ :=
  if b then (eSeq n l : ℂ) * g l else (eSeq n (-l) : ℂ) * g (-l)

theorem Dm_facts (n : ℤ) (g : ℤ →ᵇ ℂ) (b : Bool) :
    (∀ l, ‖Dm n g b l‖ ≤ ‖g‖) ∧ Summable (fun l => ‖Dm n g b l‖ ^ 2) ∧
      ∑' l, ‖Dm n g b l‖ ^ 2 ≤ 4 * ‖g‖ ^ 2 := by
  cases b
  · exact D_core (fun l => eSeq n (-l)) (fun l => eSeq_nonneg n _) (fun l => eSeq_le_one n _)
      (eSeq_neg_sq_summable n) (eSeq_neg_sq_sum_le n) (fun l => g (-l)) ‖g‖ (norm_nonneg _)
      (fun l => BoundedContinuousFunction.norm_coe_le_norm g _)
  · exact D_core (fun l => eSeq n l) (fun l => eSeq_nonneg n _) (fun l => eSeq_le_one n _)
      (eSeq_sq_summable n) (eSeq_sq_sum_le n) (fun l => g l) ‖g‖ (norm_nonneg _)
      (fun l => BoundedContinuousFunction.norm_coe_le_norm g _)

/-! ### Rescaled `comp_bound` -/

theorem comp_gen (w : ℤ → ℝ) (hw : ∀ k : ℤ, 1 ≤ w k)
    (hwmul : NlsGge.Atomic.DM046.SubmultiplicativeWeight w) (s : ℤ)
    (a x D : ℤ → ℂ) (G : ℝ) (hG0 : 0 ≤ G)
    (hD1 : ∀ l, ‖D l‖ ≤ G) (hDs : Summable fun l => ‖D l‖ ^ 2)
    (hD4 : ∑' l, ‖D l‖ ^ 2 ≤ 4 * G ^ 2)
    (hPa : ∑' l, ENNReal.ofReal (w l ^ 2 * ‖a l‖ ^ 2) ≠ ⊤)
    (hEx : ∑' l, ENNReal.ofReal (w (l + s) ^ 2 * ‖x l‖ ^ 2) ≠ ⊤) :
    ∑' k : ℤ, ENNReal.ofReal (w (k + s) ^ 2 * ‖∑' l, a (k - l) * (D l * x l)‖ ^ 2) ≤
      ENNReal.ofReal (G ^ 2) *
        (4 * (∑' l, ENNReal.ofReal (w l ^ 2 * ‖a l‖ ^ 2)) *
          ∑' l, ENNReal.ofReal (w (l + s) ^ 2 * ‖x l‖ ^ 2)) := by
  rcases hG0.eq_or_lt with h0 | hpos
  · have hD0 : ∀ l, D l = 0 := fun l => by
      have := hD1 l
      rw [← h0] at this
      exact norm_le_zero_iff.mp this
    simp [hD0]
  · have hGc : (G : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    set D' : ℤ → ℂ := fun l => D l / (G : ℂ) with hD'
    have hn' : ∀ l, ‖D' l‖ = ‖D l‖ / G := fun l => by
      rw [hD', norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    have hD1' : ∀ l, ‖D' l‖ ≤ 1 := fun l => by
      rw [hn' l]; exact div_le_one_of_le₀ (hD1 l) hpos.le
    have hsq' : ∀ l, ‖D' l‖ ^ 2 = ‖D l‖ ^ 2 / G ^ 2 := fun l => by rw [hn' l, div_pow]
    have hDs' : Summable fun l => ‖D' l‖ ^ 2 := by
      simp_rw [hsq']; exact hDs.div_const _
    have hD4' : ∑' l, ‖D' l‖ ^ 2 ≤ 4 := by
      simp_rw [hsq']
      rw [tsum_div_const, div_le_iff₀ (by positivity)]
      linarith
    have hb := NlsGge.ThirdConsultation.MTwoMode.Comp21.comp_bound w hw hwmul s a x D' hD1' hDs' hD4' hPa hEx
    have hscale : ∀ k : ℤ, ∑' l, a (k - l) * (D l * x l) = (G : ℂ) * ∑' l, a (k - l) * (D' l * x l) := by
      intro k
      rw [← tsum_mul_left]
      refine tsum_congr fun l => ?_
      simp only [hD']
      field_simp
    have hterm : ∀ k : ℤ, ENNReal.ofReal (w (k + s) ^ 2 * ‖∑' l, a (k - l) * (D l * x l)‖ ^ 2) =
        ENNReal.ofReal (G ^ 2) *
          ENNReal.ofReal (w (k + s) ^ 2 * ‖∑' l, a (k - l) * (D' l * x l)‖ ^ 2) := by
      intro k
      rw [← ENNReal.ofReal_mul (sq_nonneg _), hscale k, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hpos]
      congr 1
      ring
    calc ∑' k : ℤ, ENNReal.ofReal (w (k + s) ^ 2 * ‖∑' l, a (k - l) * (D l * x l)‖ ^ 2)
        = ∑' k : ℤ, ENNReal.ofReal (G ^ 2) *
            ENNReal.ofReal (w (k + s) ^ 2 * ‖∑' l, a (k - l) * (D' l * x l)‖ ^ 2) :=
          tsum_congr hterm
      _ = ENNReal.ofReal (G ^ 2) *
            ∑' k : ℤ, ENNReal.ofReal (w (k + s) ^ 2 * ‖∑' l, a (k - l) * (D' l * x l)‖ ^ 2) :=
          ENNReal.tsum_mul_left
      _ ≤ _ := by
          exact mul_le_mul_right hb _

end
end NlsGge.ThirdConsultation.MTwoMode.WeightedInverse
