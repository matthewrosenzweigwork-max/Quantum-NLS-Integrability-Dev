import Mathlib

/- M049 CORE PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Proposed target
   NlsGge/Atomic/M/M049Core.lean. Mathlib only. Generic algebra for M-049 `molnar_inverse_birkhoff` and the PDE
   consumer `actualBirkhoffTop38_inverse_polynomial` (Pro r16 L609-631, L1185, L1452-1458):
   * inverse_bound_of: from an M-048-shaped estimate ‖u‖² ≤ d²(A_m + (1+A_1)^p A_0) with ONE constant d before every u,
     and A_m(Tz) ≤ K_m a², A_1(Tz) ≤ K_1 b², A_0(Tz) ≤ c², derive ‖Tz‖ ≤ D (a + (1+b)^p c) with D = d √(K_m + K_1^p)
     chosen BEFORE z (r16 Q2: uniform constant, quantifier order ∃ D ∀ z).
   * poly_alg: a + (1+b)^p c ≤ 2 (1+a)^(p+1) for 0 ≤ b, c ≤ a (the C = 2D step). -/

set_option autoImplicit false

namespace NlsGge.ThirdConsultation.M049Aux

theorem inverse_bound_of (p : ℕ) {Z X : Type*} [NormedAddCommGroup X] (T : Z → X) (A : ℕ → X → ℝ)
    (i : ℕ) (a b c : Z → ℝ) (ha : ∀ z, 0 ≤ a z) (hb : ∀ z, 0 ≤ b z) (hc : ∀ z, 0 ≤ c z)
    (Km K1 : ℝ) (hKm : 0 ≤ Km) (hK1 : 1 ≤ K1)
    (h48 : ∃ d : ℝ, 0 < d ∧ ∀ u : X, ‖u‖ ^ 2 ≤ d ^ 2 * (A i u + (1 + A 1 u) ^ p * A 0 u))
    (hAm : ∀ z, A i (T z) ≤ Km * a z ^ 2) (hA1 : ∀ z, A 1 (T z) ≤ K1 * b z ^ 2)
    (hA0 : ∀ z, A 0 (T z) ≤ c z ^ 2) (hA1n : ∀ z, 0 ≤ A 1 (T z)) (hA0n : ∀ z, 0 ≤ A 0 (T z)) :
    ∃ D : ℝ, 0 < D ∧ ∀ z, ‖T z‖ ≤ D * (a z + (1 + b z) ^ p * c z) := by
  obtain ⟨d, hd, hdu⟩ := h48
  set K : ℝ := Km + K1 ^ p with hK
  have hK1p : 1 ≤ K1 ^ p := one_le_pow₀ hK1
  have hKpos : 0 < K := by linarith
  refine ⟨d * Real.sqrt K, mul_pos hd (Real.sqrt_pos.2 hKpos), fun z => ?_⟩
  have hu := hdu (T z)
  have hbz := hb z
  have hcz := hc z
  have haz := ha z
  have hy0 : 0 ≤ (1 + b z) ^ p * c z := mul_nonneg (pow_nonneg (by linarith) _) hcz
  -- (1 + A1) ≤ K1 (1+b)²
  have h1 : 1 + A 1 (T z) ≤ K1 * (1 + b z) ^ 2 := by
    have := hA1 z
    nlinarith
  have h2 : (1 + A 1 (T z)) ^ p ≤ K1 ^ p * ((1 + b z) ^ p) ^ 2 := by
    have := pow_le_pow_left₀ (by linarith [hA1n z]) h1 p
    calc (1 + A 1 (T z)) ^ p ≤ (K1 * (1 + b z) ^ 2) ^ p := this
      _ = K1 ^ p * ((1 + b z) ^ p) ^ 2 := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 p]
  have h3 : (1 + A 1 (T z)) ^ p * A 0 (T z) ≤ K1 ^ p * ((1 + b z) ^ p * c z) ^ 2 := by
    have hpow0 : 0 ≤ (1 + A 1 (T z)) ^ p := pow_nonneg (by linarith [hA1n z]) _
    calc (1 + A 1 (T z)) ^ p * A 0 (T z) ≤ (K1 ^ p * ((1 + b z) ^ p) ^ 2) * c z ^ 2 :=
          mul_le_mul h2 (hA0 z) (hA0n z) (by positivity)
      _ = K1 ^ p * ((1 + b z) ^ p * c z) ^ 2 := by ring
  have h4 : ‖T z‖ ^ 2 ≤ (d * Real.sqrt K * (a z + (1 + b z) ^ p * c z)) ^ 2 := by
    have hsq : (d * Real.sqrt K * (a z + (1 + b z) ^ p * c z)) ^ 2 =
        d ^ 2 * (K * (a z + (1 + b z) ^ p * c z) ^ 2) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hKpos.le]; ring
    rw [hsq]
    refine le_trans hu (mul_le_mul_of_nonneg_left ?_ (sq_nonneg d))
    have hm := hAm z
    have hy := hy0
    nlinarith [mul_nonneg haz hy, sq_nonneg (a z), sq_nonneg ((1 + b z) ^ p * c z)]
  have h5 := Real.sqrt_le_sqrt h4
  rwa [Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (mul_nonneg (mul_nonneg hd.le (Real.sqrt_nonneg _)) (by linarith))] at h5

theorem poly_alg (a b c : ℝ) (p : ℕ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hba : b ≤ a) (hca : c ≤ a) :
    a + (1 + b) ^ p * c ≤ 2 * (1 + a) ^ (p + 1) := by
  have ha : 0 ≤ a := le_trans hb hba
  have h1a : 1 ≤ 1 + a := by linarith
  have hA : a ≤ (1 + a) ^ (p + 1) := by
    calc a ≤ 1 + a := by linarith
      _ = (1 + a) ^ 1 := (pow_one _).symm
      _ ≤ (1 + a) ^ (p + 1) := pow_le_pow_right₀ h1a (by omega)
  have hB : (1 + b) ^ p * c ≤ (1 + a) ^ (p + 1) := by
    calc (1 + b) ^ p * c ≤ (1 + a) ^ p * (1 + a) :=
          mul_le_mul (pow_le_pow_left₀ (by linarith) (by linarith) p) (by linarith) hc
            (pow_nonneg (by linarith) _)
      _ = (1 + a) ^ (p + 1) := (pow_succ _ _).symm
  linarith

end NlsGge.ThirdConsultation.M049Aux
