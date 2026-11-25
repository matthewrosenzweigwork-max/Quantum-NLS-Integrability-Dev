import Mathlib
import NlsGge.ThirdConsultation.G1.Round5
import NlsGge.ThirdConsultation.G1.ProductBounds
import NlsGge.ThirdConsultation.G1.NormCalculus
import NlsGge.ThirdConsultation.G1.WkbStructure

                                                                                                                                  
                                                                                                   
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38

namespace NlsGge.GKDefinitionDesign
attribute [local instance] Classical.propDecidable

def WkbBound (N n : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ p : ℕ, ∀ φ : PotPair, pairSobolev (N : ℝ) φ → ∀ k : ℕ, 1 ≤ k → k ≤ n →
    physicalSobolev ((N + 1 - k : ℕ) : ℝ) (wkbR φ k) ∧
      physicalSobolevNorm ((N + 1 - k : ℕ) : ℝ) (wkbR φ k) ≤
        C * (1 + pairSobolevNorm (N : ℝ) φ) ^ p

theorem pairSobolevNorm_ge (N : ℕ) (φ : PotPair) :
    0 ≤ pairSobolevNorm (N : ℝ) φ ∧ physicalSobolevNorm (N : ℝ) φ.1 ≤ pairSobolevNorm (N : ℝ) φ ∧
      physicalSobolevNorm (N : ℝ) φ.2 ≤ pairSobolevNorm (N : ℝ) φ := by
  unfold pairSobolevNorm
  refine ⟨Real.sqrt_nonneg _, ?_, ?_⟩
  · apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (physicalSobolevNorm (N : ℝ) φ.2)]
  · apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (physicalSobolevNorm (N : ℝ) φ.1)]

theorem wkb_bound (N : ℕ) : ∀ n : ℕ, 1 ≤ n → n ≤ N → WkbBound N n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro _
    refine ⟨1, one_pos, 1, fun φ hφ k hk1 hk2 => ?_⟩
    have hk : k = 1 := by omega
    subst hk
    have e : N + 1 - 1 = N := by omega
    rw [e, wkbR_one]
    obtain ⟨h1, h2⟩ := psn_neg N hφ.2
    obtain ⟨-, -, h3⟩ := pairSobolevNorm_ge N φ
    refine ⟨h1, ?_⟩
    rw [h2]
    have hx := (pairSobolevNorm_ge N φ).1
    nlinarith
  | succ n hn ih =>
    intro hN
    obtain ⟨C, hC, p, h⟩ := ih (by omega)
    obtain ⟨Cm, hCm, hprod⟩ := psn_prod (N - n) (by omega)
    refine ⟨C + 2 * Real.pi * C + Cm * Cm * ((n - 1 : ℕ) : ℝ) * C * C, by positivity, 2 * p + 1, ?_⟩
    intro φ hφ k hk1 hk2
    obtain ⟨hx0, hxφ1, -⟩ := pairSobolevNorm_ge N φ
    set x := pairSobolevNorm (N : ℝ) φ with hxdef
    have hy : 1 ≤ 1 + x := by linarith
    set y := 1 + x with hydef
    have hY : 1 ≤ y ^ p := one_le_pow₀ hy
    have hp' : y ^ (2 * p + 1) = y * (y ^ p) ^ 2 := by ring
    have hYY : y ^ p ≤ y * (y ^ p) ^ 2 := by nlinarith
    have hxy : x ≤ y := by linarith
    have hpi : 0 < Real.pi := Real.pi_pos
    by_cases hk : k ≤ n
    · obtain ⟨h1, h2⟩ := h φ hφ k hk1 hk
      refine ⟨h1, h2.trans ?_⟩
      rw [hp']
      have h3 : C * y ^ p ≤ C * (y * (y ^ p) ^ 2) := mul_le_mul_of_nonneg_left hYY hC.le
      have h4 : 0 ≤ 2 * Real.pi * C + Cm * Cm * ((n - 1 : ℕ) : ℝ) * C * C := by positivity
      nlinarith [mul_nonneg h4 (by positivity : (0:ℝ) ≤ y * (y ^ p) ^ 2)]
    · have hk' : k = n + 1 := by omega
      subst hk'
      have e : N + 1 - (n + 1) = N - n := by omega
      rw [e, wkbR_succ φ n hn]
      set m := N - n with hm
      have hmN : m ≤ N := by omega
      set B := C * y ^ p with hB
      have hr : ∀ j, 1 ≤ j → j ≤ n → physicalSobolev (m : ℝ) (wkbR φ j) ∧
          physicalSobolevNorm (m : ℝ) (wkbR φ j) ≤ B := by
        intro j hj1 hj2
        obtain ⟨h1, h2⟩ := h φ hφ j hj1 hj2
        obtain ⟨h3, h4⟩ := psn_mono (show m ≤ N + 1 - j by omega) h1
        exact ⟨h3, h4.trans h2⟩
      have hBnn : 0 ≤ B := by positivity
      have hterm : ∀ j ∈ Finset.Icc 1 (n - 1),
          physicalSobolev (m : ℝ) (physicalProduct (wkbR φ j) (wkbR φ (n - j))) ∧
          physicalSobolevNorm (m : ℝ) (physicalProduct (wkbR φ j) (wkbR φ (n - j))) ≤ Cm * B * B := by
        intro j hj
        rw [Finset.mem_Icc] at hj
        obtain ⟨a1, a2⟩ := hr j hj.1 (by omega)
        obtain ⟨b1, b2⟩ := hr (n - j) (by omega) (by omega)
        obtain ⟨c1, c2⟩ := hprod _ _ a1 b1
        refine ⟨c1, c2.trans ?_⟩
        have := psn_nonneg m (wkbR φ j)
        have := psn_nonneg m (wkbR φ (n - j))
        gcongr
      obtain ⟨s1, s2⟩ := psn_sum m (Finset.Icc 1 (n - 1))
        (fun j => physicalProduct (wkbR φ j) (wkbR φ (n - j))) (fun j hj => (hterm j hj).1)
      have s3 : physicalSobolevNorm (m : ℝ) (∑ j ∈ Finset.Icc 1 (n - 1),
          physicalProduct (wkbR φ j) (wkbR φ (n - j))) ≤ ((n - 1 : ℕ) : ℝ) * (Cm * B * B) := by
        refine s2.trans ?_
        refine (Finset.sum_le_sum (fun j hj => (hterm j hj).2)).trans ?_
        simp
      obtain ⟨f1, f2⟩ := psn_mono hmN hφ.1
      have f3 : physicalSobolevNorm (m : ℝ) φ.1 ≤ x := f2.trans hxφ1
      obtain ⟨g1, g2⟩ := hprod _ _ f1 s1
      have g3 : physicalSobolevNorm (m : ℝ) (physicalProduct φ.1 (∑ j ∈ Finset.Icc 1 (n - 1),
          physicalProduct (wkbR φ j) (wkbR φ (n - j)))) ≤ Cm * x * (((n - 1 : ℕ) : ℝ) * (Cm * B * B)) := by
        refine g2.trans ?_
        have := psn_nonneg m φ.1
        have := psn_nonneg m (∑ j ∈ Finset.Icc 1 (n - 1), physicalProduct (wkbR φ j) (wkbR φ (n - j)))
        gcongr
      obtain ⟨hn1, hn2⟩ := h φ hφ n hn le_rfl
      have e2 : N + 1 - n = m + 1 := by omega
      rw [e2] at hn1 hn2
      obtain ⟨d1, d2⟩ := psn_deriv m hn1
      obtain ⟨t1, t2⟩ := psn_add m d1 g1
      refine ⟨t1, t2.trans ?_⟩
      have d3 : physicalSobolevNorm (m : ℝ) (weakDerivative (wkbR φ n)) ≤ 2 * Real.pi * B :=
        d2.trans (mul_le_mul_of_nonneg_left hn2 (by positivity))
      rw [hp']
      have hn1' : 0 ≤ ((n - 1 : ℕ) : ℝ) := by positivity
      have hb : 0 ≤ Cm * Cm * ((n - 1 : ℕ) : ℝ) * C * C := by positivity
      have h5 : Cm * x * (((n - 1 : ℕ) : ℝ) * (Cm * B * B)) =
          (Cm * Cm * ((n - 1 : ℕ) : ℝ) * C * C) * x * (y ^ p) ^ 2 := by rw [hB]; ring
      have h6 : 2 * Real.pi * B = (2 * Real.pi * C) * y ^ p := by rw [hB]; ring
      have h7 : (2 * Real.pi * C) * y ^ p ≤ (2 * Real.pi * C) * (y * (y ^ p) ^ 2) :=
        mul_le_mul_of_nonneg_left hYY (by positivity)
      have h8 : (Cm * Cm * ((n - 1 : ℕ) : ℝ) * C * C) * x * (y ^ p) ^ 2 ≤
          (Cm * Cm * ((n - 1 : ℕ) : ℝ) * C * C) * (y * (y ^ p) ^ 2) := by
        have : x * (y ^ p) ^ 2 ≤ y * (y ^ p) ^ 2 := mul_le_mul_of_nonneg_right hxy (by positivity)
        nlinarith [mul_le_mul_of_nonneg_left this hb]
      have h9 : 0 ≤ C * (y * (y ^ p) ^ 2) := by positivity
      nlinarith [d3, g3, h5, h6, h7, h8, h9]

theorem G1_034 (N : ℕ) (hN : 1 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∃ p : ℕ, ∀ φ : PotPair,
      pairSobolev (N : ℝ) φ →
      wkbR φ 1 = -φ.2 ∧ wkbR φ 2 = -weakDerivative φ.2 ∧
      (∀ n : ℕ, 1 ≤ n → n ≤ N →
        physicalSobolev ((N + 1 - n : ℕ) : ℝ) (wkbR φ n) ∧
        physicalSobolevNorm ((N + 1 - n : ℕ) : ℝ) (wkbR φ n) ≤
          C * (1 + pairSobolevNorm (N : ℝ) φ) ^ p) ∧
      (∀ n : ℕ, 1 ≤ n → n ≤ N →
        wkbR φ (n + 1) = weakDerivative (wkbR φ n) +
          physicalProduct φ.1
            (∑ k ∈ Finset.Icc 1 (n - 1),
              physicalProduct (wkbR φ k) (wkbR φ (n - k)))) := by
  obtain ⟨C, hC, p, h⟩ := wkb_bound N N hN le_rfl
  refine ⟨C, hC, p, fun φ hφ => ⟨wkbR_one φ, wkbR_two φ, fun n h1 h2 => h φ hφ n h1 h2,
    fun n h1 _ => wkbR_succ φ n h1⟩⟩

end NlsGge.GKDefinitionDesign
end
