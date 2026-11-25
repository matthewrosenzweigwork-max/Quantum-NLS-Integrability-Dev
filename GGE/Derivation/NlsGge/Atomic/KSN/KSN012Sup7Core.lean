import Mathlib

/- KSN012 SUP7 CORE PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/KSN/KSN012Sup7Core.lean. Pure real/complex/ENNReal lemmas for the ball-uniform reduction of
   KSN012_missingA (Sup7): the good-index estimate (difference of the KSPS-023 and KSPS-024 tail identities, KST route
   g(mu) - g(lamDot) with g(lam) = lam + P(1/lam)), the bad-index estimate (rough localization only), the constant
   aggregation, and the ENNReal partial-sum criterion. No NLS objects; nothing assumed. -/
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.KSN012U
noncomputable section

theorem sup7_sq3 (p q r : ℝ) : (p + q + r) ^ 2 ≤ 3 * (p ^ 2 + q ^ 2 + r ^ 2) := by
  nlinarith [sq_nonneg (p - q), sq_nonneg (q - r), sq_nonneg (p - r)]

theorem sup7_sq2 (p q : ℝ) : (p + q) ^ 2 ≤ 2 * (p ^ 2 + q ^ 2) := by
  nlinarith [sq_nonneg (p - q)]

theorem sup7_sq4 (p q r t : ℝ) : (p + q + r + t) ^ 2 ≤ 4 * (p ^ 2 + q ^ 2 + r ^ 2 + t ^ 2) := by
  nlinarith [sq_nonneg (p - q), sq_nonneg (q - r), sq_nonneg (p - r), sq_nonneg (p - t), sq_nonneg (q - t),
    sq_nonneg (r - t)]

/-- `‖x⁻¹ - y⁻¹‖ ≤ ‖x - y‖ / ν^2` when both norms are at least `ν > 0`. -/
theorem sup7_inv_sub_le (x y : ℂ) (ν : ℝ) (hν : 0 < ν) (hx : ν ≤ ‖x‖) (hy : ν ≤ ‖y‖) :
    ‖x⁻¹ - y⁻¹‖ ≤ ‖x - y‖ / ν ^ 2 := by
  have hx0 : x ≠ 0 := by intro h; rw [h, norm_zero] at hx; linarith
  have hy0 : y ≠ 0 := by intro h; rw [h, norm_zero] at hy; linarith
  rw [inv_sub_inv hx0 hy0, norm_div, norm_mul, norm_sub_rev]
  apply div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hν 2)
  rw [pow_two]
  exact mul_le_mul hx hy hν.le (norm_nonneg _)

/-- Good index: the two tail identities subtracted. -/
theorem sup7_good_pure (w ν L ψ ψc : ℝ) (m c F r2 r2' Pm Pc z : ℂ)
    (hw : 1 ≤ w) (hν : 0 < ν) (hL0 : 0 ≤ L) (hL : 2 * L ≤ ν ^ 2)
    (hm : m + Pm - z = F / 2 + r2) (hc : c + Pc - z = r2')
    (hP : ‖Pm - Pc‖ ≤ L * (‖m - c‖ / ν ^ 2))
    (hr : w ^ 2 * ‖r2‖ ≤ ψ) (hr' : w ^ 2 * ‖r2'‖ ≤ ψc) :
    w ^ 2 * ‖m - c‖ ^ 2 ≤ 3 * (w ^ 2 * ‖F‖ ^ 2 + 4 * ψ ^ 2 + 4 * ψc ^ 2) := by
  have e : m - c = F / 2 + r2 - r2' - (Pm - Pc) := by linear_combination hm - hc
  have hF2 : ‖F / 2‖ = ‖F‖ / 2 := by rw [norm_div, Complex.norm_ofNat]
  have h1 : ‖m - c‖ ≤ ‖F‖ / 2 + ‖r2‖ + ‖r2'‖ + ‖Pm - Pc‖ := by
    rw [e]
    calc ‖F / 2 + r2 - r2' - (Pm - Pc)‖ ≤ ‖F / 2 + r2 - r2'‖ + ‖Pm - Pc‖ := norm_sub_le _ _
      _ ≤ ‖F / 2 + r2‖ + ‖r2'‖ + ‖Pm - Pc‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ ‖F / 2‖ + ‖r2‖ + ‖r2'‖ + ‖Pm - Pc‖ := by gcongr; exact norm_add_le _ _
      _ = ‖F‖ / 2 + ‖r2‖ + ‖r2'‖ + ‖Pm - Pc‖ := by rw [hF2]
  have hν2 : 0 < ν ^ 2 := by positivity
  have hq : L * (‖m - c‖ / ν ^ 2) ≤ ‖m - c‖ / 2 := by
    rw [← mul_div_assoc, div_le_div_iff₀ hν2 (by norm_num : (0 : ℝ) < 2)]
    have := norm_nonneg (m - c)
    nlinarith
  have h2 : ‖m - c‖ ≤ ‖F‖ + 2 * ‖r2‖ + 2 * ‖r2'‖ := by linarith
  have hw0 : 0 ≤ w := by linarith
  have hww : w ≤ w ^ 2 := by nlinarith
  have hr1 : w * ‖r2‖ ≤ ψ := le_trans (mul_le_mul_of_nonneg_right hww (norm_nonneg _)) hr
  have hr1' : w * ‖r2'‖ ≤ ψc := le_trans (mul_le_mul_of_nonneg_right hww (norm_nonneg _)) hr'
  have h3 : w * ‖m - c‖ ≤ w * ‖F‖ + 2 * ψ + 2 * ψc := by
    have := mul_le_mul_of_nonneg_left h2 hw0
    nlinarith
  have hX : 0 ≤ w * ‖m - c‖ := mul_nonneg hw0 (norm_nonneg _)
  have h4 := pow_le_pow_left₀ hX h3 2
  have h5 := sup7_sq3 (w * ‖F‖) (2 * ψ) (2 * ψc)
  have e1 : (w * ‖m - c‖) ^ 2 = w ^ 2 * ‖m - c‖ ^ 2 := by ring
  have e2 : 3 * ((w * ‖F‖) ^ 2 + (2 * ψ) ^ 2 + (2 * ψc) ^ 2) =
      3 * (w ^ 2 * ‖F‖ ^ 2 + 4 * ψ ^ 2 + 4 * ψc ^ 2) := by ring
  linarith

/-- Bad index: only the rough localization is used. -/
theorem sup7_bad_pure (w a t : ℝ) (m c z : ℂ) (hw : 0 < w) (ha : 0 ≤ a) (ht : 1 ≤ t)
    (hm : ‖m - z‖ ≤ a / w) (hc : ‖c - z‖ ≤ a / w) :
    w ^ 2 * ‖m - c‖ ^ 2 ≤ 4 * a ^ 2 * t ^ 2 := by
  have h1 : ‖m - c‖ ≤ 2 * a / w := by
    have e : m - c = (m - z) - (c - z) := by ring
    rw [e]
    calc ‖(m - z) - (c - z)‖ ≤ ‖m - z‖ + ‖c - z‖ := norm_sub_le _ _
      _ ≤ a / w + a / w := add_le_add hm hc
      _ = 2 * a / w := by ring
  have h2 : w * ‖m - c‖ ≤ 2 * a := by
    rw [le_div_iff₀ hw] at h1
    linarith
  have hX : 0 ≤ w * ‖m - c‖ := mul_nonneg hw.le (norm_nonneg _)
  have h3 := pow_le_pow_left₀ hX h2 2
  have ht2 : 1 ≤ t ^ 2 := one_le_pow₀ ht
  have h4 : 4 * a ^ 2 ≤ 4 * a ^ 2 * t ^ 2 := by
    have := mul_le_mul_of_nonneg_left ht2 (by positivity : (0 : ℝ) ≤ 4 * a ^ 2)
    linarith
  have e1 : (w * ‖m - c‖) ^ 2 = w ^ 2 * ‖m - c‖ ^ 2 := by ring
  nlinarith

/-- The aggregated constant (a literal abbreviation). -/
def sup7K (a C1b C2b J : ℝ) : ℝ :=
  3 * (2 + 4 * (8 * C1b ^ 2 * (1 + 2 * Real.pi + 2 * J) ^ 2 + 2) +
      4 * (4 * C2b ^ 2 * (1 + 2 * Real.pi + 2 * J) ^ 2 + 2)) +
    4 * a ^ 2 * (6 * (1 + 2 * Real.pi + 2 * J) ^ 2)

theorem sup7K_nonneg (a C1b C2b J : ℝ) : 0 ≤ sup7K a C1b C2b J := by
  unfold sup7K
  positivity

/-- Aggregation of the per-index bounds into one master sequence `Q = d²+e²+u²+x1²+x2²`. -/
theorem sup7_aggregate (a c1 c2 C1b C2b J d e f1 f2 i x1 x2 u wF : ℝ)
    (hc1 : 0 ≤ c1) (hc1b : c1 ≤ C1b) (hc2 : 0 ≤ c2) (hc2b : c2 ≤ C2b) (hJ : 0 ≤ J)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hf1 : 0 ≤ f1) (hf2 : 0 ≤ f2) (hi : 0 ≤ i)
    (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2) (hu : 0 ≤ u) (hwF : 0 ≤ wF)
    (hf1x : f1 ≤ 2 * Real.pi * x1) (hf2x : f2 ≤ 2 * Real.pi * x2) (hiu : i ≤ 2 * J * u)
    (hwFx : wF ≤ x1 + x2) :
    3 * (wF ^ 2 + 4 * (c1 * (d + f1 + f2 + i) + d / 2) ^ 2 + 4 * (c2 * (e + i) + e / 2) ^ 2) +
        4 * a ^ 2 * ((d + f1 + f2 + i) ^ 2 + (e + i) ^ 2) ≤
      sup7K a C1b C2b J * (d ^ 2 + e ^ 2 + u ^ 2 + x1 ^ 2 + x2 ^ 2) := by
  have hpi := Real.pi_pos
  set s : ℝ := 1 + 2 * Real.pi + 2 * J with hs
  set Q : ℝ := d ^ 2 + e ^ 2 + u ^ 2 + x1 ^ 2 + x2 ^ 2 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hs1 : 1 ≤ s := by rw [hs]; linarith
  have hs0 : 0 ≤ s := by linarith
  -- tau
  set τ : ℝ := d + f1 + f2 + i with hτ
  set τc : ℝ := e + i with hτc
  have hτ0 : 0 ≤ τ := by positivity
  have hτc0 : 0 ≤ τc := by positivity
  have hτs : τ ≤ s * (d + x1 + x2 + u) := by
    have a1 : d ≤ s * d := le_mul_of_one_le_left hd hs1
    have a2 : 2 * Real.pi * x1 ≤ s * x1 := mul_le_mul_of_nonneg_right (by rw [hs]; linarith) hx1
    have a3 : 2 * Real.pi * x2 ≤ s * x2 := mul_le_mul_of_nonneg_right (by rw [hs]; linarith) hx2
    have a4 : 2 * J * u ≤ s * u := mul_le_mul_of_nonneg_right (by rw [hs]; linarith) hu
    have e : s * (d + x1 + x2 + u) = s * d + s * x1 + s * x2 + s * u := by ring
    rw [e, hτ]; linarith
  have hτcs : τc ≤ s * (e + u) := by
    have a1 : e ≤ s * e := le_mul_of_one_le_left he hs1
    have a4 : 2 * J * u ≤ s * u := mul_le_mul_of_nonneg_right (by rw [hs]; linarith) hu
    have e' : s * (e + u) = s * e + s * u := by ring
    rw [e', hτc]; linarith
  have hτ2 : τ ^ 2 ≤ 4 * s ^ 2 * Q := by
    have b4 : d ^ 2 + x1 ^ 2 + x2 ^ 2 + u ^ 2 ≤ Q := by rw [hQ]; linarith [sq_nonneg e]
    calc τ ^ 2 ≤ (s * (d + x1 + x2 + u)) ^ 2 := pow_le_pow_left₀ hτ0 hτs 2
      _ = s ^ 2 * (d + x1 + x2 + u) ^ 2 := by ring
      _ ≤ s ^ 2 * (4 * (d ^ 2 + x1 ^ 2 + x2 ^ 2 + u ^ 2)) :=
          mul_le_mul_of_nonneg_left (sup7_sq4 d x1 x2 u) (sq_nonneg s)
      _ = 4 * s ^ 2 * (d ^ 2 + x1 ^ 2 + x2 ^ 2 + u ^ 2) := by ring
      _ ≤ 4 * s ^ 2 * Q := mul_le_mul_of_nonneg_left b4 (by positivity)
  have hτc2 : τc ^ 2 ≤ 2 * s ^ 2 * Q := by
    have b4 : e ^ 2 + u ^ 2 ≤ Q := by rw [hQ]; linarith [sq_nonneg d, sq_nonneg x1, sq_nonneg x2]
    calc τc ^ 2 ≤ (s * (e + u)) ^ 2 := pow_le_pow_left₀ hτc0 hτcs 2
      _ = s ^ 2 * (e + u) ^ 2 := by ring
      _ ≤ s ^ 2 * (2 * (e ^ 2 + u ^ 2)) := mul_le_mul_of_nonneg_left (sup7_sq2 e u) (sq_nonneg s)
      _ = 2 * s ^ 2 * (e ^ 2 + u ^ 2) := by ring
      _ ≤ 2 * s ^ 2 * Q := mul_le_mul_of_nonneg_left b4 (by positivity)
  -- psi
  have hψ0 : 0 ≤ c1 * τ + d / 2 := by positivity
  have hψ : c1 * τ + d / 2 ≤ C1b * τ + d := by
    have := mul_le_mul_of_nonneg_right hc1b hτ0
    linarith
  have hψ2 : (c1 * τ + d / 2) ^ 2 ≤ (8 * C1b ^ 2 * s ^ 2 + 2) * Q := by
    have b4 := mul_le_mul_of_nonneg_left hτ2 (sq_nonneg C1b)
    have b5 : d ^ 2 ≤ Q := by rw [hQ]; linarith [sq_nonneg e, sq_nonneg u, sq_nonneg x1, sq_nonneg x2]
    calc (c1 * τ + d / 2) ^ 2 ≤ (C1b * τ + d) ^ 2 := pow_le_pow_left₀ hψ0 hψ 2
      _ ≤ 2 * ((C1b * τ) ^ 2 + d ^ 2) := sup7_sq2 _ _
      _ = 2 * (C1b ^ 2 * τ ^ 2) + 2 * d ^ 2 := by ring
      _ ≤ 2 * (C1b ^ 2 * (4 * s ^ 2 * Q)) + 2 * Q := by linarith
      _ = (8 * C1b ^ 2 * s ^ 2 + 2) * Q := by ring
  have hψc0 : 0 ≤ c2 * τc + e / 2 := by positivity
  have hψc : c2 * τc + e / 2 ≤ C2b * τc + e := by
    have := mul_le_mul_of_nonneg_right hc2b hτc0
    linarith
  have hψc2 : (c2 * τc + e / 2) ^ 2 ≤ (4 * C2b ^ 2 * s ^ 2 + 2) * Q := by
    have b4 := mul_le_mul_of_nonneg_left hτc2 (sq_nonneg C2b)
    have b5 : e ^ 2 ≤ Q := by rw [hQ]; linarith [sq_nonneg d, sq_nonneg u, sq_nonneg x1, sq_nonneg x2]
    calc (c2 * τc + e / 2) ^ 2 ≤ (C2b * τc + e) ^ 2 := pow_le_pow_left₀ hψc0 hψc 2
      _ ≤ 2 * ((C2b * τc) ^ 2 + e ^ 2) := sup7_sq2 _ _
      _ = 2 * (C2b ^ 2 * τc ^ 2) + 2 * e ^ 2 := by ring
      _ ≤ 2 * (C2b ^ 2 * (2 * s ^ 2 * Q)) + 2 * Q := by linarith
      _ = (4 * C2b ^ 2 * s ^ 2 + 2) * Q := by ring
  -- Fourier part
  have hwF2 : wF ^ 2 ≤ 2 * Q := by
    have b1 := pow_le_pow_left₀ hwF hwFx 2
    have b2 := sup7_sq2 x1 x2
    have b4 : x1 ^ 2 + x2 ^ 2 ≤ Q := by rw [hQ]; linarith [sq_nonneg d, sq_nonneg u, sq_nonneg e]
    linarith
  have ha2 : 0 ≤ 4 * a ^ 2 := by positivity
  have hsum := mul_le_mul_of_nonneg_left (add_le_add hτ2 hτc2) ha2
  have eK : sup7K a C1b C2b J * Q =
      3 * (2 * Q + 4 * ((8 * C1b ^ 2 * s ^ 2 + 2) * Q) + 4 * ((4 * C2b ^ 2 * s ^ 2 + 2) * Q)) +
        4 * a ^ 2 * (4 * s ^ 2 * Q + 2 * s ^ 2 * Q) := by
    unfold sup7K; rw [hs]; ring
  rw [eK]
  linarith

/-- ENNReal tsum bound from uniformly bounded finite partial sums of a nonnegative real sequence. -/
theorem sup7_tsum_ofReal_le (f : ℤ → ℝ) (hf : ∀ n, 0 ≤ f n) (c : ℝ)
    (h : ∀ F : Finset ℤ, ∑ n ∈ F, f n ≤ c) :
    ∑' n : ℤ, ENNReal.ofReal (f n) ≤ ENNReal.ofReal c := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le (fun F => ?_)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => hf n)]
  exact ENNReal.ofReal_le_ofReal (h F)

end
end NlsGge.ThirdConsultation.KSN012U
