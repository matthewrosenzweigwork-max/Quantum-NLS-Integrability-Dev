import Mathlib

   
                                                             

                                                                      
                                                                      
                                                                                
  

set_option autoImplicit false

namespace NlsGge.ThirdConsultation.MTwoMode.Real21

/-- Cauchy-Schwarz for nonnegative square-summable sequences on `ℤ`. -/
theorem cs_sq (f g : ℤ → ℝ) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hsf : Summable fun i => f i ^ 2) (hsg : Summable fun i => g i ^ 2) :
    Summable (fun i => f i * g i) ∧
      (∑' i, f i * g i) ^ 2 ≤ (∑' i, f i ^ 2) * (∑' i, g i ^ 2) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hsf' : Summable fun i => f i ^ (2 : ℝ) := by
    simpa only [Real.rpow_two] using hsf
  have hsg' : Summable fun i => g i ^ (2 : ℝ) := by
    simpa only [Real.rpow_two] using hsg
  obtain ⟨hs, hle⟩ :=
    Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hpq hf hg hsf' hsg'
  simp only [Real.rpow_two] at hle
  have hS : 0 ≤ ∑' i, f i ^ 2 := tsum_nonneg fun i => sq_nonneg _
  have hT : 0 ≤ ∑' i, g i ^ 2 := tsum_nonneg fun i => sq_nonneg _
  have hX : 0 ≤ ∑' i, f i * g i := tsum_nonneg fun i => mul_nonneg (hf i) (hg i)
  have hsqrt : ∀ S : ℝ, 0 ≤ S → (S ^ (1 / (2 : ℝ))) ^ 2 = S := by
    intro S hS0
    rw [← Real.rpow_natCast, ← Real.rpow_mul hS0]
    norm_num
  refine ⟨hs, ?_⟩
  calc (∑' i, f i * g i) ^ 2
      ≤ ((∑' i, f i ^ 2) ^ (1 / (2 : ℝ)) * (∑' i, g i ^ 2) ^ (1 / (2 : ℝ))) ^ 2 :=
        pow_le_pow_left₀ hX hle 2
    _ = (∑' i, f i ^ 2) * (∑' i, g i ^ 2) := by
        rw [mul_pow, hsqrt _ hS, hsqrt _ hT]

/-- A nonnegative real series whose `ENNReal` image has finite total is summable. -/
theorem summable_of_ofReal_tsum_ne_top (g : ℤ → ℝ) (hg : ∀ l, 0 ≤ g l)
    (h : ∑' l, ENNReal.ofReal (g l) ≠ ⊤) : Summable g := by
  have h1 := ENNReal.summable_toReal h
  have h2 : (fun l => (ENNReal.ofReal (g l)).toReal) = g :=
    funext fun l => ENNReal.toReal_ofReal (hg l)
  rw [h2] at h1
  exact h1

/-- The shear `(m, l) ↦ (m + l, l)` of `ℤ × ℤ`. -/
def shear : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (p.1 + p.2, p.2)
  invFun q := (q.1 - q.2, q.2)
  left_inv p := by simp
  right_inv q := by simp

/-- Young's inequality in squared form: `∑_k (∑_l A(k-l) G(l))² ≤ (∑ G)² ∑ A²`
for nonnegative `A` with summable squares and `G` summable. -/
theorem young_real (A G : ℤ → ℝ) (hA : ∀ m, 0 ≤ A m) (hG : ∀ l, 0 ≤ G l)
    (hsA : Summable fun m => A m ^ 2) (hG1 : Summable G) :
    Summable (fun k : ℤ => (∑' l, A (k - l) * G l) ^ 2) ∧
      ∑' k : ℤ, (∑' l, A (k - l) * G l) ^ 2 ≤
        (∑' l, G l) ^ 2 * ∑' m, A m ^ 2 := by
  let F : ℤ × ℤ → ℝ := fun p => G p.2 * A (p.1 - p.2) ^ 2
  have hF0 : 0 ≤ F := fun p => mul_nonneg (hG _) (sq_nonneg _)
  have hprod : Summable fun p : ℤ × ℤ => A p.1 ^ 2 * G p.2 :=
    Summable.mul_of_nonneg hsA hG1 (fun m => sq_nonneg _) hG
  have hshear : Summable (F ∘ shear) :=
    hprod.congr fun p => by simp [F, shear]; ring
  have hFs : Summable F := shear.summable_iff.mp hshear
  have hrow : ∀ k : ℤ, Summable fun l => G l * A (k - l) ^ 2 := fun k =>
    ((summable_prod_of_nonneg hF0).1 hFs).1 k
  have hR : Summable fun k : ℤ => ∑' l, G l * A (k - l) ^ 2 :=
    ((summable_prod_of_nonneg hF0).1 hFs).2
  have hsA_norm : Summable fun m => ‖A m ^ 2‖ :=
    hsA.congr fun m => (Real.norm_of_nonneg (sq_nonneg _)).symm
  have hG_norm : Summable fun l => ‖G l‖ :=
    hG1.congr fun l => (Real.norm_of_nonneg (hG l)).symm
  have hsum : ∑' k : ℤ, ∑' l : ℤ, G l * A (k - l) ^ 2 =
      (∑' l, G l) * ∑' m, A m ^ 2 := by
    have e1 : ∑' p : ℤ × ℤ, F p = ∑' k : ℤ, ∑' l : ℤ, G l * A (k - l) ^ 2 :=
      hFs.tsum_prod' hrow
    have e2 : ∑' p : ℤ × ℤ, F p = ∑' p : ℤ × ℤ, A p.1 ^ 2 * G p.2 := by
      rw [← shear.tsum_eq F]
      exact tsum_congr fun p => by simp [F, shear]; ring
    have e3 := tsum_mul_tsum_of_summable_norm hsA_norm hG_norm
    calc ∑' k : ℤ, ∑' l : ℤ, G l * A (k - l) ^ 2
        = ∑' p : ℤ × ℤ, F p := e1.symm
      _ = ∑' p : ℤ × ℤ, A p.1 ^ 2 * G p.2 := e2
      _ = (∑' m, A m ^ 2) * ∑' l, G l := e3.symm
      _ = (∑' l, G l) * ∑' m, A m ^ 2 := mul_comm _ _
  have hpt : ∀ k : ℤ, (∑' l, A (k - l) * G l) ^ 2 ≤
      (∑' l, G l) * ∑' l, G l * A (k - l) ^ 2 := by
    intro k
    obtain ⟨_, hcs⟩ := cs_sq (fun l => Real.sqrt (G l))
      (fun l => Real.sqrt (G l) * A (k - l))
      (fun l => Real.sqrt_nonneg _) (fun l => mul_nonneg (Real.sqrt_nonneg _) (hA _))
      (hG1.congr fun l => (Real.sq_sqrt (hG l)).symm)
      ((hrow k).congr fun l => by rw [mul_pow, Real.sq_sqrt (hG l)])
    have e_fg : ∑' l, Real.sqrt (G l) * (Real.sqrt (G l) * A (k - l)) =
        ∑' l, A (k - l) * G l :=
      tsum_congr fun l => by rw [← mul_assoc, Real.mul_self_sqrt (hG l)]; ring
    have e_f2 : ∑' l, Real.sqrt (G l) ^ 2 = ∑' l, G l :=
      tsum_congr fun l => Real.sq_sqrt (hG l)
    have e_g2 : ∑' l, (Real.sqrt (G l) * A (k - l)) ^ 2 =
        ∑' l, G l * A (k - l) ^ 2 :=
      tsum_congr fun l => by rw [mul_pow, Real.sq_sqrt (hG l)]
    rw [e_fg, e_f2, e_g2] at hcs
    exact hcs
  have hY : Summable fun k : ℤ => (∑' l, A (k - l) * G l) ^ 2 :=
    Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => hpt k) (hR.mul_left _)
  refine ⟨hY, ?_⟩
  calc ∑' k : ℤ, (∑' l, A (k - l) * G l) ^ 2
      ≤ ∑' k : ℤ, (∑' l, G l) * ∑' l, G l * A (k - l) ^ 2 :=
        Summable.tsum_le_tsum (fun k => hpt k) hY (hR.mul_left _)
    _ = (∑' l, G l) * ∑' k : ℤ, ∑' l : ℤ, G l * A (k - l) ^ 2 := tsum_mul_left
    _ = (∑' l, G l) * ((∑' l, G l) * ∑' m, A m ^ 2) := by rw [hsum]
    _ = (∑' l, G l) ^ 2 * ∑' m, A m ^ 2 := by ring

end NlsGge.ThirdConsultation.MTwoMode.Real21

