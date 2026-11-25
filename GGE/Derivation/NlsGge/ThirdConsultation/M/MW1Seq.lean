import Mathlib
import NlsGge.ThirdConsultation.M.M021Real

/-!
# MW1Seq: smoothing convolution estimate on integer sequences (proof development, AUTHOR; not self-reviewed)

Support for the Pro round 11 section 7.3 weighted-threshold bridge (M-024..026).  Pure real/complex sequence analysis:
for a weight `w >= 1` with the additive splitting `w (k+s) <= w (k-l) + w (l+s)`, a potential coefficient `a` with
`w a` square summable (hence `a` summable when `1/w` is square summable), a kernel `D` with `w(l+s)|D l| <= C`
and `D` square summable, and an input `x` that is only square summable, the weighted convolution
`k |-> w (k+s) * |sum_l a (k-l) * (D l * x l)|` is square summable with an explicit bound.  Every `tsum` is
preceded by `Summable`.  Uses only the landed `young_real` and `cs_sq` of M021Real.
-/

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.MTwoModeW

open NlsGge.ThirdConsultation.MTwoMode.Real21

/-- Young's inequality with the summable factor on the left (reindexed `young_real`). -/
theorem young_real_comm (a Y : ℤ → ℝ) (ha : ∀ m, 0 ≤ a m) (hY : ∀ l, 0 ≤ Y l)
    (hsY : Summable fun m => Y m ^ 2) (ha1 : Summable a) :
    Summable (fun k : ℤ => (∑' l, a (k - l) * Y l) ^ 2) ∧
      ∑' k : ℤ, (∑' l, a (k - l) * Y l) ^ 2 ≤ (∑' l, a l) ^ 2 * ∑' m, Y m ^ 2 := by
  have h := young_real Y a hY ha hsY ha1
  have e : ∀ k : ℤ, ∑' l, a (k - l) * Y l = ∑' l, Y (k - l) * a l := by
    intro k
    have h1 := (Equiv.subLeft k).tsum_eq (fun l => Y (k - l) * a l)
    simp only [Equiv.subLeft_apply, sub_sub_cancel] at h1
    rw [← h1]
    exact tsum_congr fun l => mul_comm _ _
  simpa only [e] using h

/-- Sum of the two Young convolutions, in squared form. -/
theorem smooth_conv (A α G Y : ℤ → ℝ) (hA : ∀ m, 0 ≤ A m) (hα : ∀ m, 0 ≤ α m)
    (hG : ∀ l, 0 ≤ G l) (hY : ∀ l, 0 ≤ Y l)
    (hsA : Summable fun m => A m ^ 2) (hsα : Summable α) (hsG : Summable G)
    (hsY : Summable fun m => Y m ^ 2) :
    Summable (fun k : ℤ => (∑' l, A (k - l) * G l + ∑' l, α (k - l) * Y l) ^ 2) ∧
      ∑' k : ℤ, (∑' l, A (k - l) * G l + ∑' l, α (k - l) * Y l) ^ 2 ≤
        2 * ((∑' l, G l) ^ 2 * ∑' m, A m ^ 2) + 2 * ((∑' l, α l) ^ 2 * ∑' m, Y m ^ 2) := by
  obtain ⟨h1s, h1⟩ := young_real A G hA hG hsA hsG
  obtain ⟨h2s, h2⟩ := young_real_comm α Y hα hY hsY hsα
  have hpt : ∀ k : ℤ, (∑' l, A (k - l) * G l + ∑' l, α (k - l) * Y l) ^ 2 ≤
      2 * (∑' l, A (k - l) * G l) ^ 2 + 2 * (∑' l, α (k - l) * Y l) ^ 2 := by
    intro k
    nlinarith [sq_nonneg ((∑' l, A (k - l) * G l) - ∑' l, α (k - l) * Y l)]
  have hsum : Summable (fun k : ℤ => 2 * (∑' l, A (k - l) * G l) ^ 2 +
      2 * (∑' l, α (k - l) * Y l) ^ 2) := (h1s.mul_left 2).add (h2s.mul_left 2)
  have hs : Summable (fun k : ℤ => (∑' l, A (k - l) * G l + ∑' l, α (k - l) * Y l) ^ 2) :=
    Summable.of_nonneg_of_le (fun k => sq_nonneg _) hpt hsum
  refine ⟨hs, ?_⟩
  calc ∑' k : ℤ, (∑' l, A (k - l) * G l + ∑' l, α (k - l) * Y l) ^ 2
      ≤ ∑' k : ℤ, (2 * (∑' l, A (k - l) * G l) ^ 2 + 2 * (∑' l, α (k - l) * Y l) ^ 2) :=
        Summable.tsum_le_tsum hpt hs hsum
    _ = 2 * ∑' k : ℤ, (∑' l, A (k - l) * G l) ^ 2 + 2 * ∑' k : ℤ, (∑' l, α (k - l) * Y l) ^ 2 := by
        rw [Summable.tsum_add (h1s.mul_left 2) (h2s.mul_left 2), tsum_mul_left, tsum_mul_left]
    _ ≤ 2 * ((∑' l, G l) ^ 2 * ∑' m, A m ^ 2) + 2 * ((∑' l, α l) ^ 2 * ∑' m, Y m ^ 2) := by
        gcongr

/-- The smoothing bound for one component.  `C` bounds `w (l+s) * |D l|`; no weight is placed on the input `x`. -/
theorem smooth_comp (w : ℤ → ℝ) (hw : ∀ k, 1 ≤ w k)
    (hadd : ∀ k l s : ℤ, w (k + s) ≤ w (k - l) + w (l + s))
    (s : ℤ) (a x D : ℤ → ℂ) (C : ℝ)
    (hD1 : ∀ l, ‖D l‖ ≤ 1) (hDs : Summable fun l => ‖D l‖ ^ 2)
    (hD4 : ∑' l, ‖D l‖ ^ 2 ≤ 4) (hDw : ∀ l, w (l + s) * ‖D l‖ ≤ C)
    (hsa : Summable fun m => (w m * ‖a m‖) ^ 2) (hsa1 : Summable fun m => ‖a m‖)
    (hsx : Summable fun l => ‖x l‖ ^ 2) :
    Summable (fun k : ℤ => (w (k + s) * ‖∑' l, a (k - l) * (D l * x l)‖) ^ 2) ∧
      ∑' k : ℤ, (w (k + s) * ‖∑' l, a (k - l) * (D l * x l)‖) ^ 2 ≤
        2 * (4 * ∑' l, ‖x l‖ ^ 2) * ∑' m, (w m * ‖a m‖) ^ 2 +
          2 * (∑' m, ‖a m‖) ^ 2 * (C ^ 2 * ∑' l, ‖x l‖ ^ 2) := by
  have hw0 : ∀ k, 0 ≤ w k := fun k => by linarith [hw k]
  have hA0 : ∀ m, 0 ≤ w m * ‖a m‖ := fun m => mul_nonneg (hw0 m) (norm_nonneg _)
  have hα0 : ∀ m, 0 ≤ ‖a m‖ := fun m => norm_nonneg _
  have hG0 : ∀ l, 0 ≤ ‖D l‖ * ‖x l‖ := fun l => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hY0 : ∀ l, 0 ≤ w (l + s) * ‖D l‖ * ‖x l‖ := fun l =>
    mul_nonneg (mul_nonneg (hw0 _) (norm_nonneg _)) (norm_nonneg _)
  -- square summability of the pieces
  have hsα2 : Summable fun m => ‖a m‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun m => sq_nonneg _) (fun m => ?_) hsa
    rw [mul_pow]
    exact le_mul_of_one_le_left (sq_nonneg _) (by nlinarith [hw m])
  obtain ⟨hsG, hcsG⟩ := cs_sq (fun l => ‖D l‖) (fun l => ‖x l‖) (fun l => norm_nonneg _)
    (fun l => norm_nonneg _) hDs hsx
  have hsG2 : Summable fun l => (‖D l‖ * ‖x l‖) ^ 2 := by
    refine Summable.of_nonneg_of_le (fun l => sq_nonneg _) (fun l => ?_) hsx
    rw [mul_pow]
    exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ (norm_nonneg _) (hD1 l))
  have hY2le : ∀ l, (w (l + s) * ‖D l‖ * ‖x l‖) ^ 2 ≤ C ^ 2 * ‖x l‖ ^ 2 := by
    intro l
    have h1 : w (l + s) * ‖D l‖ * ‖x l‖ ≤ C * ‖x l‖ :=
      mul_le_mul_of_nonneg_right (hDw l) (norm_nonneg _)
    calc (w (l + s) * ‖D l‖ * ‖x l‖) ^ 2 ≤ (C * ‖x l‖) ^ 2 := pow_le_pow_left₀ (hY0 l) h1 2
      _ = C ^ 2 * ‖x l‖ ^ 2 := by ring
  have hsY : Summable fun l => (w (l + s) * ‖D l‖ * ‖x l‖) ^ 2 :=
    Summable.of_nonneg_of_le (fun l => sq_nonneg _) hY2le (hsx.mul_left _)
  have hY2sum : ∑' l, (w (l + s) * ‖D l‖ * ‖x l‖) ^ 2 ≤ C ^ 2 * ∑' l, ‖x l‖ ^ 2 := by
    calc ∑' l, (w (l + s) * ‖D l‖ * ‖x l‖) ^ 2 ≤ ∑' l, C ^ 2 * ‖x l‖ ^ 2 :=
          Summable.tsum_le_tsum hY2le hsY (hsx.mul_left _)
      _ = C ^ 2 * ∑' l, ‖x l‖ ^ 2 := tsum_mul_left
  obtain ⟨hs, hle⟩ := smooth_conv (fun m => w m * ‖a m‖) (fun m => ‖a m‖)
    (fun l => ‖D l‖ * ‖x l‖) (fun l => w (l + s) * ‖D l‖ * ‖x l‖) hA0 hα0 hG0 hY0 hsa hsa1 hsG hsY
  -- pointwise majorant
  have hpt : ∀ k l : ℤ, w (k + s) * ‖a (k - l) * (D l * x l)‖ ≤
      (w (k - l) * ‖a (k - l)‖) * (‖D l‖ * ‖x l‖) +
        ‖a (k - l)‖ * (w (l + s) * ‖D l‖ * ‖x l‖) := by
    intro k l
    have h1 := hadd k l s
    have h2 : 0 ≤ ‖a (k - l)‖ * (‖D l‖ * ‖x l‖) := mul_nonneg (norm_nonneg _) (hG0 l)
    calc w (k + s) * ‖a (k - l) * (D l * x l)‖
        = w (k + s) * (‖a (k - l)‖ * (‖D l‖ * ‖x l‖)) := by rw [norm_mul, norm_mul]
      _ ≤ (w (k - l) + w (l + s)) * (‖a (k - l)‖ * (‖D l‖ * ‖x l‖)) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = _ := by ring
  -- row summability
  have hrow1 : ∀ k : ℤ, Summable fun l => (w (k - l) * ‖a (k - l)‖) * (‖D l‖ * ‖x l‖) := by
    intro k
    have hsf : Summable fun l => (w (k - l) * ‖a (k - l)‖) ^ 2 :=
      hsa.comp_injective (i := fun l : ℤ => k - l) (fun l l' h => by simpa using h)
    exact (cs_sq (fun l => w (k - l) * ‖a (k - l)‖) (fun l => ‖D l‖ * ‖x l‖)
      (fun l => hA0 _) hG0 hsf hsG2).1
  have hrow2 : ∀ k : ℤ, Summable fun l => ‖a (k - l)‖ * (w (l + s) * ‖D l‖ * ‖x l‖) := by
    intro k
    have hsf : Summable fun l => ‖a (k - l)‖ ^ 2 :=
      hsα2.comp_injective (i := fun l : ℤ => k - l) (fun l l' h => by simpa using h)
    exact (cs_sq (fun l => ‖a (k - l)‖) (fun l => w (l + s) * ‖D l‖ * ‖x l‖)
      (fun l => hα0 _) hY0 hsf hsY).1
  have hbound : ∀ k : ℤ, w (k + s) * ‖∑' l, a (k - l) * (D l * x l)‖ ≤
      ∑' l, (w (k - l) * ‖a (k - l)‖) * (‖D l‖ * ‖x l‖) +
        ∑' l, ‖a (k - l)‖ * (w (l + s) * ‖D l‖ * ‖x l‖) := by
    intro k
    have hsum2 : Summable fun l => (w (k - l) * ‖a (k - l)‖) * (‖D l‖ * ‖x l‖) +
        ‖a (k - l)‖ * (w (l + s) * ‖D l‖ * ‖x l‖) := (hrow1 k).add (hrow2 k)
    have hw_nn : ∀ l, 0 ≤ w (k + s) * ‖a (k - l) * (D l * x l)‖ := fun l =>
      mul_nonneg (hw0 _) (norm_nonneg _)
    have hwsum : Summable fun l => w (k + s) * ‖a (k - l) * (D l * x l)‖ :=
      Summable.of_nonneg_of_le hw_nn (hpt k) hsum2
    have hnsum : Summable fun l => ‖a (k - l) * (D l * x l)‖ := by
      refine Summable.of_nonneg_of_le (fun l => norm_nonneg _) (fun l => ?_) hwsum
      exact le_mul_of_one_le_left (norm_nonneg _) (hw (k + s))
    calc w (k + s) * ‖∑' l, a (k - l) * (D l * x l)‖
        ≤ w (k + s) * ∑' l, ‖a (k - l) * (D l * x l)‖ :=
          mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hnsum) (hw0 _)
      _ = ∑' l, w (k + s) * ‖a (k - l) * (D l * x l)‖ := tsum_mul_left.symm
      _ ≤ ∑' l, ((w (k - l) * ‖a (k - l)‖) * (‖D l‖ * ‖x l‖) +
            ‖a (k - l)‖ * (w (l + s) * ‖D l‖ * ‖x l‖)) :=
          Summable.tsum_le_tsum (hpt k) hwsum hsum2
      _ = _ := Summable.tsum_add (hrow1 k) (hrow2 k)
  have hnn : ∀ k : ℤ, 0 ≤ w (k + s) * ‖∑' l, a (k - l) * (D l * x l)‖ := fun k =>
    mul_nonneg (hw0 _) (norm_nonneg _)
  have hsq : Summable fun k : ℤ => (w (k + s) * ‖∑' l, a (k - l) * (D l * x l)‖) ^ 2 :=
    Summable.of_nonneg_of_le (fun k => sq_nonneg _)
      (fun k => pow_le_pow_left₀ (hnn k) (hbound k) 2) hs
  refine ⟨hsq, ?_⟩
  have hGX : (∑' l, ‖D l‖ * ‖x l‖) ^ 2 ≤ 4 * ∑' l, ‖x l‖ ^ 2 := by
    calc (∑' l, ‖D l‖ * ‖x l‖) ^ 2 ≤ (∑' l, ‖D l‖ ^ 2) * ∑' l, ‖x l‖ ^ 2 := hcsG
      _ ≤ 4 * ∑' l, ‖x l‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hD4 (tsum_nonneg fun l => sq_nonneg _)
  have hAn : 0 ≤ ∑' m, (w m * ‖a m‖) ^ 2 := tsum_nonneg fun m => sq_nonneg _
  calc ∑' k : ℤ, (w (k + s) * ‖∑' l, a (k - l) * (D l * x l)‖) ^ 2
      ≤ ∑' k : ℤ, (∑' l, (w (k - l) * ‖a (k - l)‖) * (‖D l‖ * ‖x l‖) +
          ∑' l, ‖a (k - l)‖ * (w (l + s) * ‖D l‖ * ‖x l‖)) ^ 2 :=
        Summable.tsum_le_tsum (fun k => pow_le_pow_left₀ (hnn k) (hbound k) 2) hsq hs
    _ ≤ 2 * ((∑' l, ‖D l‖ * ‖x l‖) ^ 2 * ∑' m, (w m * ‖a m‖) ^ 2) +
          2 * ((∑' m, ‖a m‖) ^ 2 * ∑' l, (w (l + s) * ‖D l‖ * ‖x l‖) ^ 2) := hle
    _ ≤ 2 * (4 * ∑' l, ‖x l‖ ^ 2) * ∑' m, (w m * ‖a m‖) ^ 2 +
          2 * (∑' m, ‖a m‖) ^ 2 * (C ^ 2 * ∑' l, ‖x l‖ ^ 2) := by
        have h1 : (∑' l, ‖D l‖ * ‖x l‖) ^ 2 * ∑' m, (w m * ‖a m‖) ^ 2 ≤
            (4 * ∑' l, ‖x l‖ ^ 2) * ∑' m, (w m * ‖a m‖) ^ 2 :=
          mul_le_mul_of_nonneg_right hGX hAn
        have h2 : (∑' m, ‖a m‖) ^ 2 * ∑' l, (w (l + s) * ‖D l‖ * ‖x l‖) ^ 2 ≤
            (∑' m, ‖a m‖) ^ 2 * (C ^ 2 * ∑' l, ‖x l‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hY2sum (sq_nonneg _)
        nlinarith [h1, h2]

end NlsGge.ThirdConsultation.MTwoModeW

end
