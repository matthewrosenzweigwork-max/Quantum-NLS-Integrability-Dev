import Mathlib

                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace NlsGge.ThirdConsultation.S


def normalizerModes (N : ℕ) : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)

def normalizerLow (M N : ℕ) : Finset ℤ :=
  (normalizerModes N).filter (fun n => n.natAbs ≤ M)

def normalizerHigh (M N : ℕ) : Finset ℤ :=
  (normalizerModes N).filter (fun n => M < n.natAbs)

def mixedProduct (M N : ℕ) (R : ℝ) (ρ a : ℤ → ℝ) : ℝ :=
  (∏ n ∈ normalizerLow M N, Real.pi * R ^ 2) *
    ∏ n ∈ normalizerHigh M N, Real.pi / (ρ n * a n)

def freeNormalizer (N : ℕ) (a : ℤ → ℝ) : ℝ :=
  ∏ n ∈ normalizerModes N, Real.pi / a n

theorem mixed_product_normalizer_cancel
    (M N : ℕ) (R : ℝ) (ρ a : ℤ → ℝ)
    (ha : ∀ n : ℤ, 0 < a n) (hρ : ∀ n : ℤ, 0 < ρ n) :
    mixedProduct M N R ρ a / freeNormalizer N a =
      (∏ n ∈ normalizerLow M N, R ^ 2 * a n) *
        ∏ n ∈ normalizerHigh M N, (ρ n)⁻¹ := by
  have hsplit : ∀ f : ℤ → ℝ, ∏ n ∈ normalizerModes N, f n =
      (∏ n ∈ normalizerLow M N, f n) * ∏ n ∈ normalizerHigh M N, f n := by
    intro f
    unfold normalizerLow normalizerHigh
    rw [← Finset.prod_filter_mul_prod_filter_not (normalizerModes N) (fun n => n.natAbs ≤ M)]
    congr 1
    exact Finset.prod_congr (Finset.filter_congr (fun n _ => by simp)) (fun _ _ => rfl)
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hfpos : 0 < freeNormalizer N a :=
    Finset.prod_pos (fun n _ => div_pos Real.pi_pos (ha n))
  have hlow : ∏ n ∈ normalizerLow M N, Real.pi * R ^ 2 =
      (∏ n ∈ normalizerLow M N, Real.pi / a n) * ∏ n ∈ normalizerLow M N, R ^ 2 * a n := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun n _ => ?_)
    have := (ha n).ne'
    field_simp
  have hhigh : ∏ n ∈ normalizerHigh M N, Real.pi / (ρ n * a n) =
      (∏ n ∈ normalizerHigh M N, Real.pi / a n) * ∏ n ∈ normalizerHigh M N, (ρ n)⁻¹ := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun n _ => ?_)
    have := (ha n).ne'
    have := (hρ n).ne'
    field_simp
  rw [div_eq_iff hfpos.ne']
  unfold mixedProduct
  rw [hlow, hhigh]
  unfold freeNormalizer
  rw [hsplit (fun n => Real.pi / a n)]
  ring

theorem mixed_product_normalizer_cancel_of_le
    (M N : ℕ) (hNM : N ≤ M) (R : ℝ) (ρ a : ℤ → ℝ)
    (ha : ∀ n : ℤ, 0 < a n) (hρ : ∀ n : ℤ, 0 < ρ n) :
    mixedProduct M N R ρ a / freeNormalizer N a =
      ∏ n ∈ normalizerModes N, R ^ 2 * a n := by
  have h := mixed_product_normalizer_cancel M N R ρ a ha hρ
  have hhigh : normalizerHigh M N = ∅ := by
    unfold normalizerHigh normalizerModes
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false, not_and, not_lt]
    intro hn
    have : n.natAbs ≤ N := by omega
    omega
  have hlow : normalizerLow M N = normalizerModes N := by
    unfold normalizerLow
    apply Finset.filter_true_of_mem
    intro n hn
    unfold normalizerModes at hn
    simp only [Finset.mem_Icc] at hn
    omega
  rw [h, hhigh, hlow]
  simp

end NlsGge.ThirdConsultation.S
