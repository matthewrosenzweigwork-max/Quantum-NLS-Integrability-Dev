import NlsGge.ThirdConsultation.M.M021Real
import NlsGge.Atomic.KST.KST004
import NlsGge.Atomic.KST.KST005
import NlsGge.Atomic.DM.DM046

   
                                                                   

                                                                            
                                                                              
                                                                          
                                                                 
  

set_option autoImplicit false

namespace NlsGge.ThirdConsultation.MTwoMode.Comp21

open NlsGge.ThirdConsultation.MTwoMode.Real21
open NlsGge.Atomic.KST004
open scoped ENNReal

noncomputable section

/-- Weighted potential amplitude `w m ‖a m‖`. -/
def A21 (w : ℤ → ℝ) (a : ℤ → ℂ) (m : ℤ) : ℝ := w m * ‖a m‖

/-- Weighted input amplitude `w (l+s) ‖x l‖`. -/
def X21 (w : ℤ → ℝ) (s : ℤ) (x : ℤ → ℂ) (l : ℤ) : ℝ := w (l + s) * ‖x l‖

/-- Kernel-weighted input amplitude `‖D l‖ · w (l+s) ‖x l‖`. -/
def G21 (w : ℤ → ℝ) (s : ℤ) (D : ℤ → ℂ) (x : ℤ → ℂ) (l : ℤ) : ℝ :=
  ‖D l‖ * X21 w s x l

/-- The complementary coefficient is bounded by one, square-summable, with
squared sum at most four (from the KST004 bound and the KST005 lattice bound). -/
theorem D_facts (n : ℤ) (lam : ℂ) (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n) :
    (∀ l : ℤ, ‖complementaryResolventCoeff n lam l‖ ≤ 1) ∧
    Summable (fun l : ℤ => ‖complementaryResolventCoeff n lam l‖ ^ 2) ∧
    ∑' l : ℤ, ‖complementaryResolventCoeff n lam l‖ ^ 2 ≤ 4 := by
  have hone : ∀ l : ℤ, ‖complementaryResolventCoeff n lam l‖ ≤
      1 / (Int.natAbs (l - n) : ℝ) :=
    fun l => complementaryResolventCoeff_bound n l lam hlam
  have hle1 : ∀ l : ℤ, ‖complementaryResolventCoeff n lam l‖ ≤ 1 := by
    intro l
    refine le_trans (hone l) ?_
    rcases Nat.eq_zero_or_pos (Int.natAbs (l - n)) with h | h
    · simp [h]
    · have h1 : (1 : ℝ) ≤ (Int.natAbs (l - n) : ℝ) := Nat.one_le_cast.mpr h
      exact div_le_one_of_le₀ h1 (by linarith)
  have hsq : ∀ l : ℤ, ‖complementaryResolventCoeff n lam l‖ ^ 2 ≤
      (if l ≠ n then 1 / ((l - n).natAbs : ℝ) ^ 2 else 0) := by
    intro l
    by_cases hl : l = n
    · subst hl
      simp [complementaryResolventCoeff]
    · rw [if_pos hl]
      exact le_of_le_of_eq (pow_le_pow_left₀ (norm_nonneg _) (hone l) 2) (one_div_pow _ _)
  have hgs : Summable (fun l : ℤ => if l ≠ n then 1 / ((l - n).natAbs : ℝ) ^ 2 else 0) := by
    have hbase0 : Summable (fun d : ℤ => 1 / (d : ℝ) ^ 2) :=
      (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
    have hbase : Summable (fun d : ℤ => 1 / (Int.natAbs d : ℝ) ^ 2) := by
      convert hbase0 using 1 <;> simp [Nat.cast_natAbs, Int.cast_abs, abs_pow]
    have hshift : Summable (fun l : ℤ => 1 / (Int.natAbs (l - n) : ℝ) ^ 2) :=
      hbase.comp_injective (i := fun l : ℤ => l - n) (fun l l' h => by simpa using h)
    refine Summable.of_nonneg_of_le (fun l => ?_) (fun l => ?_) hshift
    · split_ifs <;> positivity
    · split_ifs with h
      · exact le_refl _
      · positivity
  have hDs : Summable (fun l : ℤ => ‖complementaryResolventCoeff n lam l‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun l => sq_nonneg _) hsq hgs
  have hcmp : ∑' l : ℤ, ‖complementaryResolventCoeff n lam l‖ ^ 2 ≤
      ∑' l : ℤ, (if l ≠ n then 1 / ((l - n).natAbs : ℝ) ^ 2 else 0) :=
    Summable.tsum_le_tsum hsq hDs hgs
  have hlat : ∑' l : ℤ, (if l ≠ n then 1 / ((l - n).natAbs : ℝ) ^ 2 else 0) ≤ 4 :=
    lattice_reciprocal_sq_bound_contract n
  have hD4 : ∑' l : ℤ, ‖complementaryResolventCoeff n lam l‖ ^ 2 ≤ 4 :=
    le_trans hcmp hlat
  exact ⟨hle1, hDs, hD4⟩

/-- The same facts for the reflected kernel `l ↦ d(-l)` used by the lower component. -/
theorem D_facts_neg (n : ℤ) (lam : ℂ) (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n) :
    (∀ l : ℤ, ‖complementaryResolventCoeff n lam (-l)‖ ≤ 1) ∧
    Summable (fun l : ℤ => ‖complementaryResolventCoeff n lam (-l)‖ ^ 2) ∧
    ∑' l : ℤ, ‖complementaryResolventCoeff n lam (-l)‖ ^ 2 ≤ 4 := by
  obtain ⟨h1, h2, h3⟩ := D_facts n lam hlam
  refine ⟨fun l => h1 (-l), (Equiv.neg ℤ).summable_iff.2 h2, ?_⟩
  calc ∑' l : ℤ, ‖complementaryResolventCoeff n lam (-l)‖ ^ 2
      = ∑' l : ℤ, ‖complementaryResolventCoeff n lam l‖ ^ 2 :=
        (Equiv.neg ℤ).tsum_eq (fun l => ‖complementaryResolventCoeff n lam l‖ ^ 2)
    _ ≤ 4 := h3

/-- One-component weighted convolution bound with constant four (two in norm). -/
theorem comp_bound (w : ℤ → ℝ) (hw : ∀ k : ℤ, 1 ≤ w k)
    (hwmul : NlsGge.Atomic.DM046.SubmultiplicativeWeight w) (s : ℤ)
    (a x D : ℤ → ℂ)
    (hD1 : ∀ l, ‖D l‖ ≤ 1) (hDs : Summable fun l => ‖D l‖ ^ 2)
    (hD4 : ∑' l, ‖D l‖ ^ 2 ≤ 4)
    (hPa : ∑' l, ENNReal.ofReal (w l ^ 2 * ‖a l‖ ^ 2) ≠ ⊤)
    (hEx : ∑' l, ENNReal.ofReal (w (l + s) ^ 2 * ‖x l‖ ^ 2) ≠ ⊤) :
    ∑' k : ℤ, ENNReal.ofReal (w (k + s) ^ 2 * ‖∑' l, a (k - l) * (D l * x l)‖ ^ 2) ≤
      4 * (∑' l, ENNReal.ofReal (w l ^ 2 * ‖a l‖ ^ 2)) *
        ∑' l, ENNReal.ofReal (w (l + s) ^ 2 * ‖x l‖ ^ 2) := by
  have hA0 : ∀ m, 0 ≤ A21 w a m := fun m =>
    mul_nonneg (by linarith [hw m]) (norm_nonneg _)
  have hX0 : ∀ l, 0 ≤ X21 w s x l := fun l =>
    mul_nonneg (by linarith [hw (l + s)]) (norm_nonneg _)
  have hG0 : ∀ l, 0 ≤ G21 w s D x l := fun l => mul_nonneg (norm_nonneg _) (hX0 l)
  have hsA : Summable fun m => A21 w a m ^ 2 := by
    refine summable_of_ofReal_tsum_ne_top _ (fun m => sq_nonneg _) ?_
    rw [show (∑' m, ENNReal.ofReal (A21 w a m ^ 2)) =
        ∑' l, ENNReal.ofReal (w l ^ 2 * ‖a l‖ ^ 2) from
      tsum_congr fun m => by rw [A21, mul_pow]]
    exact hPa
  have hsX : Summable fun l => X21 w s x l ^ 2 := by
    refine summable_of_ofReal_tsum_ne_top _ (fun l => sq_nonneg _) ?_
    rw [show (∑' l, ENNReal.ofReal (X21 w s x l ^ 2)) =
        ∑' l, ENNReal.ofReal (w (l + s) ^ 2 * ‖x l‖ ^ 2) from
      tsum_congr fun l => by rw [X21, mul_pow]]
    exact hEx
  have hsG : Summable (G21 w s D x) :=
    (cs_sq (fun l => ‖D l‖) (X21 w s x) (fun l => norm_nonneg _) hX0 hDs hsX).1
  have hsG2 : Summable fun l => G21 w s D x l ^ 2 := by
    refine Summable.of_nonneg_of_le (fun l => sq_nonneg _) (fun l => ?_) hsX
    have hD2 : ‖D l‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (hD1 l)
    show (‖D l‖ * X21 w s x l) ^ 2 ≤ X21 w s x l ^ 2
    rw [mul_pow]
    exact mul_le_of_le_one_left (sq_nonneg _) hD2
  obtain ⟨hYs, hYsum⟩ := young_real (A21 w a) (G21 w s D x) hA0 hG0 hsA hsG
  have hbound : ∀ k : ℤ, w (k + s) * ‖∑' l, a (k - l) * (D l * x l)‖ ≤
      ∑' l, A21 w a (k - l) * G21 w s D x l := by
    intro k
    have hsf : Summable fun l => A21 w a (k - l) ^ 2 :=
      hsA.comp_injective (i := fun l : ℤ => k - l) (fun l l' h => by simpa using h)
    have hcs_k : Summable fun l => A21 w a (k - l) * G21 w s D x l :=
      (cs_sq (fun l => A21 w a (k - l)) (G21 w s D x) (fun l => hA0 _) hG0 hsf hsG2).1
    have hwt : ∀ l, w (k + s) * ‖a (k - l) * (D l * x l)‖ ≤
        A21 w a (k - l) * G21 w s D x l := by
      intro l
      have h1 := hwmul (k - l) (l + s)
      rw [show k - l + (l + s) = k + s by ring] at h1
      have h2 : 0 ≤ ‖a (k - l)‖ * (‖D l‖ * ‖x l‖) := by positivity
      calc w (k + s) * ‖a (k - l) * (D l * x l)‖
          = w (k + s) * (‖a (k - l)‖ * (‖D l‖ * ‖x l‖)) := by rw [norm_mul, norm_mul]
        _ ≤ (w (k - l) * w (l + s)) * (‖a (k - l)‖ * (‖D l‖ * ‖x l‖)) :=
            mul_le_mul_of_nonneg_right h1 h2
        _ = A21 w a (k - l) * G21 w s D x l := by
            simp only [A21, G21, X21]; ring
    have hw_nonneg : ∀ l, 0 ≤ w (k + s) * ‖a (k - l) * (D l * x l)‖ := fun l =>
      mul_nonneg (by linarith [hw (k + s)]) (norm_nonneg _)
    have hwsum : Summable fun l => w (k + s) * ‖a (k - l) * (D l * x l)‖ :=
      Summable.of_nonneg_of_le hw_nonneg hwt hcs_k
    have hnsum : Summable fun l => ‖a (k - l) * (D l * x l)‖ :=
      Summable.of_nonneg_of_le (fun l => norm_nonneg _)
        (fun l => le_trans (le_mul_of_one_le_left (norm_nonneg _) (hw (k + s))) (hwt l)) hcs_k
    calc w (k + s) * ‖∑' l, a (k - l) * (D l * x l)‖
        ≤ w (k + s) * ∑' l, ‖a (k - l) * (D l * x l)‖ :=
          mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hnsum) (by linarith [hw (k + s)])
      _ = ∑' l, w (k + s) * ‖a (k - l) * (D l * x l)‖ := tsum_mul_left.symm
      _ ≤ ∑' l, A21 w a (k - l) * G21 w s D x l := Summable.tsum_le_tsum hwt hwsum hcs_k
  have hsq_summ : Summable fun k : ℤ => (w (k + s) * ‖∑' l, a (k - l) * (D l * x l)‖) ^ 2 :=
    Summable.of_nonneg_of_le (fun k => sq_nonneg _)
      (fun k => pow_le_pow_left₀
        (mul_nonneg (by linarith [hw (k + s)]) (norm_nonneg _)) (hbound k) 2) hYs
  have hXnn : 0 ≤ ∑' l, X21 w s x l ^ 2 := tsum_nonneg fun l => sq_nonneg _
  have hAnn : 0 ≤ ∑' m, A21 w a m ^ 2 := tsum_nonneg fun m => sq_nonneg _
  have hGX : (∑' l, G21 w s D x l) ^ 2 ≤ 4 * ∑' l, X21 w s x l ^ 2 := by
    obtain ⟨_, hcs⟩ := cs_sq (fun l => ‖D l‖) (X21 w s x) (fun l => norm_nonneg _) hX0 hDs hsX
    calc (∑' l, G21 w s D x l) ^ 2 ≤ (∑' l, ‖D l‖ ^ 2) * ∑' l, X21 w s x l ^ 2 := hcs
      _ ≤ 4 * ∑' l, X21 w s x l ^ 2 := mul_le_mul_of_nonneg_right hD4 hXnn
  have hreal : ∑' k : ℤ, (w (k + s) * ‖∑' l, a (k - l) * (D l * x l)‖) ^ 2 ≤
      4 * (∑' l, X21 w s x l ^ 2) * ∑' m, A21 w a m ^ 2 := by
    calc ∑' k : ℤ, (w (k + s) * ‖∑' l, a (k - l) * (D l * x l)‖) ^ 2
        ≤ ∑' k : ℤ, (∑' l, A21 w a (k - l) * G21 w s D x l) ^ 2 :=
          Summable.tsum_le_tsum (fun k => pow_le_pow_left₀
            (mul_nonneg (by linarith [hw (k + s)]) (norm_nonneg _)) (hbound k) 2) hsq_summ hYs
      _ ≤ (∑' l, G21 w s D x l) ^ 2 * ∑' m, A21 w a m ^ 2 := hYsum
      _ ≤ (4 * ∑' l, X21 w s x l ^ 2) * ∑' m, A21 w a m ^ 2 :=
          mul_le_mul_of_nonneg_right hGX hAnn
      _ = 4 * (∑' l, X21 w s x l ^ 2) * ∑' m, A21 w a m ^ 2 := by ring
  have hP : ∑' l, ENNReal.ofReal (w l ^ 2 * ‖a l‖ ^ 2) =
      ENNReal.ofReal (∑' m, A21 w a m ^ 2) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun m => sq_nonneg _) hsA]
    exact tsum_congr fun m => by rw [A21, mul_pow]
  have hE : ∑' l, ENNReal.ofReal (w (l + s) ^ 2 * ‖x l‖ ^ 2) =
      ENNReal.ofReal (∑' l, X21 w s x l ^ 2) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun l => sq_nonneg _) hsX]
    exact tsum_congr fun l => by rw [X21, mul_pow]
  rw [hP, hE]
  calc ∑' k : ℤ, ENNReal.ofReal (w (k + s) ^ 2 * ‖∑' l, a (k - l) * (D l * x l)‖ ^ 2)
      = ∑' k : ℤ, ENNReal.ofReal ((w (k + s) * ‖∑' l, a (k - l) * (D l * x l)‖) ^ 2) :=
        tsum_congr fun k => by rw [mul_pow]
    _ = ENNReal.ofReal (∑' k : ℤ, (w (k + s) * ‖∑' l, a (k - l) * (D l * x l)‖) ^ 2) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) hsq_summ).symm
    _ ≤ ENNReal.ofReal (4 * (∑' l, X21 w s x l ^ 2) * ∑' m, A21 w a m ^ 2) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = 4 * ENNReal.ofReal (∑' m, A21 w a m ^ 2) *
          ENNReal.ofReal (∑' l, X21 w s x l ^ 2) := by
        rw [ENNReal.ofReal_mul (mul_nonneg (by norm_num) hXnn),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
        ring

end
end NlsGge.ThirdConsultation.MTwoMode.Comp21

