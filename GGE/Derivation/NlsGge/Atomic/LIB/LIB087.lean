import Mathlib
import NlsGge.Atomic.LIB.LIB006

/- LIB-087 PRODUCTION01 (proof development, AUTHOR). Target NlsGge/Atomic/LIB/LIB087.lean, namespace NlsGge.Atomic.LIB087.
   Head verbatim from STATEMENTS/LIB.md LIB-087.  Route: Fourier coefficients of the product are the convolution
   (LIB006.h1MulL2_fourier_hasSum); weight (1+n^2)^m via q n = sqrt(1+n^2)^m <= 2^m (q k + q (n-k)); two l2*l1 Young bounds
   (LIB006.young_sq_bound) with l1 norms controlled by the H^1 weight (LIB006.summable_and_sq_le_of_weighted).
   Constant C = 2^(m+1) * sqrt(sum 1/(1+k^2)), chosen before the fields. -/
set_option autoImplicit false

noncomputable section

namespace NlsGge.Atomic.LIB087

open NlsGge.Pilot NlsGge.Atomic.LIB005 NlsGge.Atomic.LIB006

lemma jb_sq (n : ℤ) : japaneseBracket n ^ 2 = 1 + (n : ℝ) ^ 2 :=
  Real.sq_sqrt (by positivity)

lemma wt (m : ℕ) (n : ℤ) : Real.rpow (japaneseBracket n) (2 * (m : ℝ)) = (1 + (n : ℝ) ^ 2) ^ m := by
  show japaneseBracket n ^ (2 * (m : ℝ)) = _
  rw [show (2 * (m : ℝ)) = ((2 * m : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, pow_mul, jb_sq]

lemma q_le (m : ℕ) (n k : ℤ) :
    Real.sqrt (1 + (n : ℝ) ^ 2) ^ m ≤
      2 ^ m * (Real.sqrt (1 + (k : ℝ) ^ 2) ^ m + Real.sqrt (1 + ((n - k : ℤ) : ℝ) ^ 2) ^ m) := by
  set x := Real.sqrt (1 + (k : ℝ) ^ 2) with hx
  set y := Real.sqrt (1 + ((n - k : ℤ) : ℝ) ^ 2) with hy
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hxy : |(k : ℝ) * ((n - k : ℤ) : ℝ)| ≤ x * y := by
    rw [hx, hy, ← Real.sqrt_mul (by positivity)]
    rw [← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg ((k : ℝ)), sq_nonneg (((n - k : ℤ) : ℝ))]
  have hz : Real.sqrt (1 + (n : ℝ) ^ 2) ≤ x + y := by
    rw [Real.sqrt_le_left (by positivity)]
    have h1 : x ^ 2 = 1 + (k : ℝ) ^ 2 := Real.sq_sqrt (by positivity)
    have h2 : y ^ 2 = 1 + ((n - k : ℤ) : ℝ) ^ 2 := Real.sq_sqrt (by positivity)
    have hn : (n : ℝ) = (k : ℝ) + ((n - k : ℤ) : ℝ) := by push_cast; ring
    have := neg_abs_le ((k : ℝ) * ((n - k : ℤ) : ℝ))
    have := le_abs_self ((k : ℝ) * ((n - k : ℤ) : ℝ))
    rw [hn]
    nlinarith
  have hxy2 : x + y ≤ 2 * max x y := by
    have := le_max_left x y; have := le_max_right x y; linarith
  have hm : max x y ^ m ≤ x ^ m + y ^ m := by
    rcases le_total x y with h | h
    · rw [max_eq_right h]; have := pow_nonneg hx0 m; linarith
    · rw [max_eq_left h]; have := pow_nonneg hy0 m; linarith
  calc Real.sqrt (1 + (n : ℝ) ^ 2) ^ m ≤ (x + y) ^ m := pow_le_pow_left₀ (Real.sqrt_nonneg _) hz m
    _ ≤ (2 * max x y) ^ m := pow_le_pow_left₀ (by positivity) hxy2 m
    _ = 2 ^ m * max x y ^ m := mul_pow _ _ _
    _ ≤ 2 ^ m * (x ^ m + y ^ m) := mul_le_mul_of_nonneg_left hm (by positivity)

theorem core (m : ℕ) (hm : 1 ≤ m) (a b γ : ℤ → ℝ) (ha0 : ∀ k, 0 ≤ a k) (hb0 : ∀ k, 0 ≤ b k)
    (hγ0 : ∀ k, 0 ≤ γ k)
    (hWa : Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2) ^ m * a n ^ 2))
    (hWb : Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2) ^ m * b n ^ 2))
    (hγ : ∀ n, Summable (fun k : ℤ => a k * b (n - k)) → γ n ≤ ∑' k : ℤ, a k * b (n - k)) :
    Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2) ^ m * γ n ^ 2) ∧
      ∑' n : ℤ, (1 + (n : ℝ) ^ 2) ^ m * γ n ^ 2 ≤
        (4 ^ (m + 1) * ∑' k : ℤ, 1 / (1 + (k : ℝ) ^ 2)) *
          (∑' n : ℤ, (1 + (n : ℝ) ^ 2) ^ m * a n ^ 2) *
            (∑' n : ℤ, (1 + (n : ℝ) ^ 2) ^ m * b n ^ 2) := by
  set S : ℝ := ∑' k : ℤ, 1 / (1 + (k : ℝ) ^ 2) with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun k => by positivity
  set q : ℤ → ℝ := fun k => Real.sqrt (1 + (k : ℝ) ^ 2) ^ m with hq
  have hq0 : ∀ k, 0 ≤ q k := fun k => by simp only [hq]; positivity
  have hq2 : ∀ k, q k ^ 2 = (1 + (k : ℝ) ^ 2) ^ m := fun k => by
    simp only [hq]; rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by positivity)]
  have hqle : ∀ n k : ℤ, q n ≤ 2 ^ m * (q k + q (n - k)) := fun n k => q_le m n k
  set A : ℤ → ℝ := fun k => q k * a k with hA
  set B : ℤ → ℝ := fun k => q k * b k with hB
  have hA0 : ∀ k, 0 ≤ A k := fun k => mul_nonneg (hq0 k) (ha0 k)
  have hB0 : ∀ k, 0 ≤ B k := fun k => mul_nonneg (hq0 k) (hb0 k)
  have hA2e : ∀ k, A k ^ 2 = (1 + (k : ℝ) ^ 2) ^ m * a k ^ 2 := fun k => by
    simp only [hA]; rw [mul_pow, hq2]
  have hB2e : ∀ k, B k ^ 2 = (1 + (k : ℝ) ^ 2) ^ m * b k ^ 2 := fun k => by
    simp only [hB]; rw [mul_pow, hq2]
  have hA2 : Summable (fun k => A k ^ 2) := hWa.congr fun k => (hA2e k).symm
  have hB2 : Summable (fun k => B k ^ 2) := hWb.congr fun k => (hB2e k).symm
  have hlow : ∀ k : ℤ, (1 + (k : ℝ) ^ 2) ≤ (1 + (k : ℝ) ^ 2) ^ m := fun k =>
    le_self_pow₀ (by nlinarith [sq_nonneg (k : ℝ)]) (by omega)
  have hW1 : ∀ (c : ℤ → ℝ), Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2) ^ m * c n ^ 2) →
      Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2) * c n ^ 2) ∧
        ∑' n : ℤ, (1 + (n : ℝ) ^ 2) * c n ^ 2 ≤ ∑' n : ℤ, (1 + (n : ℝ) ^ 2) ^ m * c n ^ 2 := by
    intro c hc
    have hs : Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2) * c n ^ 2) :=
      Summable.of_nonneg_of_le (fun n => by positivity)
        (fun n => mul_le_mul_of_nonneg_right (hlow n) (sq_nonneg _)) hc
    exact ⟨hs, hs.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_right (hlow n) (sq_nonneg _)) hc⟩
  obtain ⟨hWa1, hWa1le⟩ := hW1 a hWa
  obtain ⟨hWb1, hWb1le⟩ := hW1 b hWb
  obtain ⟨has, hasq⟩ := summable_and_sq_le_of_weighted a ha0 hWa1
  obtain ⟨hbs, hbsq⟩ := summable_and_sq_le_of_weighted b hb0 hWb1
  set Pa : ℝ := ∑' n : ℤ, (1 + (n : ℝ) ^ 2) ^ m * a n ^ 2 with hPa
  set Pb : ℝ := ∑' n : ℤ, (1 + (n : ℝ) ^ 2) ^ m * b n ^ 2 with hPb
  have hPa0 : 0 ≤ Pa := tsum_nonneg fun n => by positivity
  have hPb0 : 0 ≤ Pb := tsum_nonneg fun n => by positivity
  have hsa : (∑' k, a k) ^ 2 ≤ S * Pa := hasq.trans (mul_le_mul_of_nonneg_left hWa1le hS0)
  have hsb : (∑' k, b k) ^ 2 ≤ S * Pb := hbsq.trans (mul_le_mul_of_nonneg_left hWb1le hS0)
  have hAs : ∑' k, A k ^ 2 = Pa := tsum_congr hA2e
  have hBs : ∑' k, B k ^ 2 = Pb := tsum_congr hB2e
  obtain ⟨hD1, hD2, hD3⟩ := young_sq_bound A b hA0 hb0 hbs hA2
  obtain ⟨hE1, hE2, hE3⟩ := young_sq_bound B a hB0 ha0 has hB2
  have ha2 : Summable (fun k => a k ^ 2) := sq_summable_of_weighted a hWa1
  obtain ⟨hab1, -, -⟩ := young_sq_bound a b ha0 hb0 hbs ha2
  have hEflip : ∀ n, Summable (fun k => a k * B (n - k)) := by
    intro n
    have := (Equiv.subLeft n).summable_iff.2 (hE1 n)
    refine this.congr fun k => ?_
    simp only [Function.comp, Equiv.subLeft_apply, sub_sub_cancel]
    ring
  have hDE : ∀ n, q n * γ n ≤ 2 ^ m * ((∑' k, A k * b (n - k)) + ∑' k, B k * a (n - k)) := by
    intro n
    have hE' : ∑' k, a k * B (n - k) = ∑' k, B k * a (n - k) := conv_flip a B n
    calc q n * γ n ≤ q n * ∑' k, a k * b (n - k) :=
          mul_le_mul_of_nonneg_left (hγ n (hab1 n)) (hq0 n)
      _ = ∑' k, q n * (a k * b (n - k)) := tsum_mul_left.symm
      _ ≤ ∑' k, 2 ^ m * (A k * b (n - k) + a k * B (n - k)) := by
          refine Summable.tsum_le_tsum (fun k => ?_) ((hab1 n).mul_left _)
            (((hD1 n).add (hEflip n)).mul_left _)
          have h1 := hqle n k
          have h0 : 0 ≤ a k * b (n - k) := mul_nonneg (ha0 _) (hb0 _)
          calc q n * (a k * b (n - k)) ≤ 2 ^ m * (q k + q (n - k)) * (a k * b (n - k)) :=
                mul_le_mul_of_nonneg_right h1 h0
            _ = _ := by simp only [hA, hB]; ring
      _ = 2 ^ m * ((∑' k, A k * b (n - k)) + ∑' k, B k * a (n - k)) := by
          rw [tsum_mul_left, (hD1 n).tsum_add (hEflip n), hE']
  have hpt : ∀ n : ℤ, (1 + (n : ℝ) ^ 2) ^ m * γ n ^ 2 ≤
      (2 * 4 ^ m) * ((∑' k, A k * b (n - k)) ^ 2 + (∑' k, B k * a (n - k)) ^ 2) := by
    intro n
    have h := hDE n
    have h0 : 0 ≤ q n * γ n := mul_nonneg (hq0 n) (hγ0 n)
    have hD0 : 0 ≤ ∑' k, A k * b (n - k) := tsum_nonneg fun k => mul_nonneg (hA0 _) (hb0 _)
    have hE0 : 0 ≤ ∑' k, B k * a (n - k) := tsum_nonneg fun k => mul_nonneg (hB0 _) (ha0 _)
    calc (1 + (n : ℝ) ^ 2) ^ m * γ n ^ 2 = (q n * γ n) ^ 2 := by rw [mul_pow, hq2]
      _ ≤ (2 ^ m * ((∑' k, A k * b (n - k)) + ∑' k, B k * a (n - k))) ^ 2 :=
          pow_le_pow_left₀ h0 h 2
      _ = 4 ^ m * ((∑' k, A k * b (n - k)) + ∑' k, B k * a (n - k)) ^ 2 := by
          rw [mul_pow, ← pow_mul, mul_comm m 2, pow_mul]; norm_num
      _ ≤ 4 ^ m * (2 * ((∑' k, A k * b (n - k)) ^ 2 + (∑' k, B k * a (n - k)) ^ 2)) := by
          gcongr
          nlinarith [sq_nonneg ((∑' k, A k * b (n - k)) - ∑' k, B k * a (n - k))]
      _ = _ := by ring
  have hsumF : Summable (fun n : ℤ => (2 * 4 ^ m) *
      ((∑' k, A k * b (n - k)) ^ 2 + (∑' k, B k * a (n - k)) ^ 2)) :=
    (hD2.add hE2).mul_left _
  have hsum : Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2) ^ m * γ n ^ 2) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (by positivity) (sq_nonneg _)) hpt hsumF
  refine ⟨hsum, ?_⟩
  have h1 : ∑' n : ℤ, (∑' k, A k * b (n - k)) ^ 2 ≤ S * Pb * Pa :=
    hD3.trans (by rw [hAs]; exact mul_le_mul_of_nonneg_right hsb hPa0)
  have h2 : ∑' n : ℤ, (∑' k, B k * a (n - k)) ^ 2 ≤ S * Pa * Pb :=
    hE3.trans (by rw [hBs]; exact mul_le_mul_of_nonneg_right hsa hPb0)
  calc ∑' n : ℤ, (1 + (n : ℝ) ^ 2) ^ m * γ n ^ 2
      ≤ ∑' n : ℤ, (2 * 4 ^ m) *
          ((∑' k, A k * b (n - k)) ^ 2 + (∑' k, B k * a (n - k)) ^ 2) :=
        hsum.tsum_le_tsum hpt hsumF
    _ = (2 * 4 ^ m) * ((∑' n : ℤ, (∑' k, A k * b (n - k)) ^ 2) +
          ∑' n : ℤ, (∑' k, B k * a (n - k)) ^ 2) := by
        rw [tsum_mul_left, hD2.tsum_add hE2]
    _ ≤ (2 * 4 ^ m) * (S * Pb * Pa + S * Pa * Pb) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity)
    _ = (4 ^ (m + 1) * S) * Pa * Pb := by ring

theorem sobolev_mul_norm_le (m : ℕ) (hm : 1 ≤ m) :
  ∃ C : ℝ, 0 < C ∧ ∀ (u v : PhysicalL2)
    (hu : SobolevSquareSummable (m : ℝ) (physicalFourier u))
    (hv : SobolevSquareSummable (m : ℝ) (physicalFourier v)),
    ∃ hu1 : SobolevSquareSummable 1 (physicalFourier u),
    ∃ hp : SobolevSquareSummable (m : ℝ) (physicalFourier (h1MulL2 u hu1 v)),
      ‖physicalSobolevL2 (m : ℝ) (h1MulL2 u hu1 v) hp‖ ≤
        C * ‖physicalSobolevL2 (m : ℝ) u hu‖ *
          ‖physicalSobolevL2 (m : ℝ) v hv‖ := by
  set S : ℝ := ∑' k : ℤ, 1 / (1 + (k : ℝ) ^ 2) with hS
  have hSpos : 0 < S := summable_inv_one_add_sq.tsum_pos (fun k => by positivity) 0 (by norm_num)
  refine ⟨2 ^ (m + 1) * Real.sqrt S, by positivity, fun u v hu hv => ?_⟩
  have hu' : Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2) ^ m * ‖physicalFourier u n‖ ^ 2) := by
    have := hu
    unfold SobolevSquareSummable at this
    simpa only [wt] using this
  have hv' : Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2) ^ m * ‖physicalFourier v n‖ ^ 2) := by
    have := hv
    unfold SobolevSquareSummable at this
    simpa only [wt] using this
  have hlow : ∀ k : ℤ, (1 + (k : ℝ) ^ 2) ≤ (1 + (k : ℝ) ^ 2) ^ m := fun k =>
    le_self_pow₀ (by nlinarith [sq_nonneg (k : ℝ)]) (by omega)
  have hu1 : SobolevSquareSummable 1 (physicalFourier u) :=
    (sobolev_one_iff' _).mpr (Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => mul_le_mul_of_nonneg_right (hlow n) (sq_nonneg _)) hu')
  obtain ⟨hs, hbd⟩ := core m hm (fun k => ‖physicalFourier u k‖) (fun k => ‖physicalFourier v k‖)
    (fun n => ‖physicalFourier (h1MulL2 u hu1 v) n‖) (fun k => norm_nonneg _)
    (fun k => norm_nonneg _) (fun k => norm_nonneg _) hu' hv' (by
      intro n hsm
      have hf : Summable (fun k => ‖physicalFourier u k * physicalFourier v (n - k)‖) :=
        hsm.congr (fun k => (norm_mul _ _).symm)
      have hH := h1MulL2_fourier_hasSum u v hu1 n
      calc ‖physicalFourier (h1MulL2 u hu1 v) n‖
          = ‖∑' k, physicalFourier u k * physicalFourier v (n - k)‖ := by rw [hH.tsum_eq]
        _ ≤ ∑' k, ‖physicalFourier u k * physicalFourier v (n - k)‖ := norm_tsum_le_tsum_norm hf
        _ = _ := tsum_congr (fun k => norm_mul _ _))
  have hp : SobolevSquareSummable (m : ℝ) (physicalFourier (h1MulL2 u hu1 v)) := by
    unfold SobolevSquareSummable
    simpa only [wt] using hs
  refine ⟨hu1, hp, ?_⟩
  have nu := physicalSobolevL2_norm_sq (m : ℝ) u hu
  have nv := physicalSobolevL2_norm_sq (m : ℝ) v hv
  have np := physicalSobolevL2_norm_sq (m : ℝ) (h1MulL2 u hu1 v) hp
  simp only [wt] at nu nv np
  have hsq : ‖physicalSobolevL2 (m : ℝ) (h1MulL2 u hu1 v) hp‖ ^ 2 ≤
      (2 ^ (m + 1) * Real.sqrt S * ‖physicalSobolevL2 (m : ℝ) u hu‖ *
        ‖physicalSobolevL2 (m : ℝ) v hv‖) ^ 2 := by
    rw [np, mul_pow, mul_pow, mul_pow, nu, nv, Real.sq_sqrt hSpos.le]
    have e : ((2 : ℝ) ^ (m + 1)) ^ 2 = 4 ^ (m + 1) := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [e]
    exact hbd
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

end NlsGge.Atomic.LIB087
