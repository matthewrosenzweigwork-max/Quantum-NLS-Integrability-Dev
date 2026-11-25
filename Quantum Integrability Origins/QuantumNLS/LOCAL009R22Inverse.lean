import QuantumNLS.LOCAL009R22Cauchy

/-! Quantitative scalar inversion for the literal exponential map. No
inverse expansion is an input: the inverse is the accepted GP-03 selection,
and the transfer remainder is supplied by the proved separated-root estimate.
The target-disk and geometric margins remain explicit at this boundary. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Complex Set Filter Topology Metric
namespace QuantumNLS.LOCAL009R22Inverse
open QuantumNLS.Ext025A7 QuantumNLS.LOCAL009R22Transfer
  QuantumNLS.LOCAL009R22Cauchy QuantumNLS.TransferProductCorrection

theorem spectralMap_norm_le {κ L R B : ℝ} (hκ : 0 ≤ κ)
    {z w : ℂ} (hw : ‖w‖ ≤ R) (hB : 0 ≤ B)
    (hz : ‖Complex.exp (Complex.I * z * L)‖ ≤ B) :
    ‖spectralMap κ L z w‖ ≤ (1 + B) * Real.exp (κ * R) := by
  have hp : ‖Complex.exp (I * κ * w)‖ ≤ Real.exp (κ * R) := by
    apply (Complex.norm_exp_le_exp_norm _).trans
    apply Real.exp_le_exp.mpr
    simpa [abs_of_nonneg hκ] using mul_le_mul_of_nonneg_left hw hκ
  have hm : ‖Complex.exp (-I * κ * w)‖ ≤ Real.exp (κ * R) := by
    apply (Complex.norm_exp_le_exp_norm _).trans
    apply Real.exp_le_exp.mpr
    simpa [abs_of_nonneg hκ] using mul_le_mul_of_nonneg_left hw hκ
  calc
    ‖spectralMap κ L z w‖ ≤ ‖Complex.exp (I * κ * w)‖ +
        ‖Complex.exp (I * z * L)‖ * ‖Complex.exp (-I * κ * w)‖ := by
      simpa only [spectralMap, norm_mul] using norm_add_le
        (Complex.exp (I * κ * w))
        (Complex.exp (I * z * L) * Complex.exp (-I * κ * w))
    _ ≤ Real.exp (κ * R) + B * Real.exp (κ * R) := by gcongr
    _ = _ := by ring

/-- Explicit quadratic Taylor error; it applies also when the endpoints
depend on the spectral parameter. -/
theorem spectral_taylor_remainder {κ L R B : ℝ} (hκ : 0 ≤ κ)
    (hsmall : κ * R ≤ 1 / 2) {z w v : ℂ}
    (hw : ‖w‖ ≤ R) (hv : ‖v‖ ≤ R) (hB : 0 ≤ B)
    (hz : ‖Complex.exp (Complex.I * z * L)‖ ≤ B) :
    ‖spectralMap κ L z w - spectralMap κ L z v -
        spectralDerivative κ L z v * (w - v)‖ ≤
      ((1 + B) * Real.exp (κ * R) * κ^2) * ‖w-v‖^2 := by
  have hd : κ * ‖w - v‖ ≤ 1 := by
    have hn := norm_sub_le w v
    have hh := mul_le_mul_of_nonneg_left (hn.trans (add_le_add hw hv)) hκ
    nlinarith
  have hnp : ‖I * κ * (w-v)‖ = κ * ‖w-v‖ := by simp [abs_of_nonneg hκ]
  have hnm : ‖-I * κ * (w-v)‖ = κ * ‖w-v‖ := by simp [abs_of_nonneg hκ]
  have hp := Complex.norm_exp_sub_one_sub_id_le (x := I * κ * (w-v))
    (by rw [hnp]; exact hd)
  have hm := Complex.norm_exp_sub_one_sub_id_le (x := -I * κ * (w-v))
    (by rw [hnm]; exact hd)
  rw [hnp] at hp
  rw [hnm] at hm
  have hep : ‖Complex.exp (I * κ * v)‖ ≤ Real.exp (κ * R) := by
    apply (Complex.norm_exp_le_exp_norm _).trans
    apply Real.exp_le_exp.mpr
    simpa [abs_of_nonneg hκ] using mul_le_mul_of_nonneg_left hv hκ
  have hem : ‖Complex.exp (-I * κ * v)‖ ≤ Real.exp (κ * R) := by
    apply (Complex.norm_exp_le_exp_norm _).trans
    apply Real.exp_le_exp.mpr
    simpa [abs_of_nonneg hκ] using mul_le_mul_of_nonneg_left hv hκ
  have hep' : Complex.exp (I * κ * w) =
      Complex.exp (I * κ * v) * Complex.exp (I * κ * (w-v)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hem' : Complex.exp (-I * κ * w) =
      Complex.exp (-I * κ * v) * Complex.exp (-I * κ * (w-v)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have heq : spectralMap κ L z w - spectralMap κ L z v -
        spectralDerivative κ L z v * (w-v) =
      Complex.exp (I * κ * v) *
          (Complex.exp (I * κ * (w-v)) - 1 - I * κ * (w-v)) +
        (Complex.exp (I * z * L) * Complex.exp (-I * κ * v)) *
          (Complex.exp (-I * κ * (w-v)) - 1 - -I * κ * (w-v)) := by
    unfold spectralMap spectralDerivative
    rw [hep', hem']
    ring
  rw [heq]
  calc
    _ ≤ ‖Complex.exp (I * κ * v)‖ *
          ‖Complex.exp (I * κ * (w-v)) - 1 - I * κ * (w-v)‖ +
        (‖Complex.exp (I * z * L)‖ * ‖Complex.exp (-I * κ * v)‖) *
          ‖Complex.exp (-I * κ * (w-v)) - 1 - -I * κ * (w-v)‖ := by
      simpa only [norm_mul] using norm_add_le
        (Complex.exp (I * κ * v) *
          (Complex.exp (I * κ * (w-v)) - 1 - I * κ * (w-v)))
        ((Complex.exp (I * z * L) * Complex.exp (-I * κ * v)) *
          (Complex.exp (-I * κ * (w-v)) - 1 - -I * κ * (w-v)))
    _ ≤ Real.exp (κ * R) * (κ * ‖w-v‖)^2 +
        (B * Real.exp (κ * R)) * (κ * ‖w-v‖)^2 := by gcongr
    _ = _ := by ring

/-- The accepted inverse is quantitatively stable against the actual root
Cauchy sum. Its existence and right-inverse identity come from GP-03. -/
theorem inverse_distance {κ L R : ℝ} {U : Set ℂ}
    (hκ : 0 < κ) (hR : 0 < R) (hsmall : κ * R ≤ 1 / 1000)
    (hU : IsOpen U)
    (hexp : ∀ z ∈ U, ‖Complex.exp (I * z * L)‖ ≤ 8)
    (hgap : ∀ z ∈ U, 1 / 2 ≤ ‖1 - Complex.exp (I * z * L)‖)
    {z y v : ℂ} (hz : z ∈ U) (hv : ‖v‖ ≤ R)
    (hy : ‖y - spectralMap κ L z 0‖ < 3 / 4 * ‖spectralLinear κ L z‖ * R) :
    (3 * κ / 8) * ‖spectralInverse κ L R z y - v‖ ≤
      ‖y - spectralMap κ L z v‖ := by
  obtain ⟨hw, he, _, _⟩ := local009_application κ L hκ hR hsmall hU hexp hgap hz hy
  have hDpos : κ / 2 ≤ ‖spectralLinear κ L z‖ := by
    rw [spectralLinear_norm, abs_of_pos hκ]
    nlinarith [hgap z hz]
  have hD : spectralLinear κ L z ≠ 0 := by
    apply norm_ne_zero_iff.mp
    linarith
  have hb : ∀ w ∈ closedBall (0 : ℂ) R,
      ‖spectralDerivative κ L z w - spectralLinear κ L z‖ ≤
        ‖spectralLinear κ L z‖ / 4 := fun w hw => local009_quarter_from_source hκ hsmall
    (hexp z hz) (hgap z hz) hw
  have hn := normalizedSpectral_lower κ L hD hb
    (ball_subset_closedBall hw) (show v ∈ closedBall (0 : ℂ) R by simpa using hv)
  have hdiff : normalizedSpectral κ L z (spectralInverse κ L R z y) -
      normalizedSpectral κ L z v = (y - spectralMap κ L z v) / spectralLinear κ L z := by
    unfold normalizedSpectral
    rw [he]
    ring
  rw [hdiff, norm_div] at hn
  have hn' := (le_div_iff₀ (norm_pos_iff.mpr hD)).mp hn
  nlinarith [norm_nonneg (spectralInverse κ L R z y - v)]

/-- Algebraic inversion of the *proved* second-order transfer expansion.
The output retains the inverse displacement, so that later uniform
first-order and Cauchy estimates can be inserted without changing its sign. -/
theorem inverse_transfer_remainder
    {κ L M d ε R : ℝ} {U : Set ℂ}
    (hκ : 0 < κ) (hM : 0 < M) (hd : 0 < d)
    (hsmall : κ * M / d ≤ 1 / 10)
    (hR : 0 < R) (hradius : κ * R ≤ 1 / 1000) (hU : IsOpen U)
    (hexp : ∀ z ∈ U, ‖Complex.exp (I * z * L)‖ ≤ 8)
    (hgap : ∀ z ∈ U, 1 / 2 ≤ ‖1 - Complex.exp (I * z * L)‖)
    {N : ℕ} (hN : 0 < N) (hε : 0 ≤ ε) (hbudget : ε * N ≤ M)
    (q : Fin N → ℝ) {z : ℂ} (hz : z ∈ U)
    (hsep : ∀ j, d ≤ ‖z - (q j : ℂ)‖)
    (hG : ‖sourceG ε q z‖ ≤ R)
    (htarget : ‖transferS (κ * ε) L q z - spectralMap κ L z 0‖ <
      3 / 4 * ‖spectralLinear κ L z‖ * R) :
    let T := spectralInverse κ L R z (transferS (κ * ε) L q z)
    (3 * κ / 8) * ‖T - sourceG ε q z +
      (κ^2 * ε / 2 : ℝ) *
        (spectralMap κ L z (sourceG ε q z) /
          spectralDerivative κ L z (sourceG ε q z)) * deriv (sourceG ε q) z‖ ≤
      Real.exp (1 / 10) * 9 * ((κ / d)^4 * M^2 + (κ / d)^3 * M) * ε^2 +
        (9 * Real.exp (κ * R) * κ^2) * ‖T - sourceG ε q z‖^2 := by
  dsimp only
  let T := spectralInverse κ L R z (transferS (κ * ε) L q z)
  let G := sourceG ε q z
  let D := spectralDerivative κ L z G
  obtain ⟨hT, he, _, _⟩ := local009_application κ L hκ hR hradius hU hexp hgap hz htarget
  have hquarter := local009_quarter_from_source hκ hradius (hexp z hz) (hgap z hz)
    (show G ∈ closedBall (0 : ℂ) R by simpa using hG)
  have hDlow : 3 * κ / 8 ≤ ‖D‖ := by
    have hl := spectralDerivative_lower κ L hquarter
    have hn : κ / 2 ≤ ‖spectralLinear κ L z‖ := by
      rw [spectralLinear_norm, abs_of_pos hκ]
      nlinarith [hgap z hz]
    dsimp [D]
    linarith
  have hD : D ≠ 0 := norm_ne_zero_iff.mp (by linarith)
  have hprod := transfer_second_order_separated hκ.le hM hd hsmall hN hε hbudget q hsep
    (by norm_num : (0 : ℝ) ≤ 8) (hexp z hz)
  have hTaylor := spectral_taylor_remainder hκ.le
    (by linarith : κ * R ≤ 1 / 2)
    (show ‖T‖ ≤ R by simpa [T] using (mem_ball_zero_iff.mp hT).le)
    hG (by norm_num : (0 : ℝ) ≤ 8) (hexp z hz)
  have hid : D * (T - G + (κ^2 * ε / 2 : ℝ) *
        (spectralMap κ L z G / D) * deriv (sourceG ε q) z) =
      (transferS (κ * ε) L q z - (spectralMap κ L z G -
        (κ^2 * ε / 2 : ℝ) * spectralMap κ L z G * deriv (sourceG ε q) z)) -
      (spectralMap κ L z T - spectralMap κ L z G - D * (T-G)) := by
    change spectralMap κ L z T = transferS (κ * ε) L q z at he
    rw [he]
    field_simp [hD]
    ring
  have hnorm := norm_sub_le
    (transferS (κ * ε) L q z - (spectralMap κ L z G -
      (κ^2 * ε / 2 : ℝ) * spectralMap κ L z G * deriv (sourceG ε q) z))
    (spectralMap κ L z T - spectralMap κ L z G - D * (T-G))
  rw [← hid, norm_mul] at hnorm
  have hm := mul_le_mul_of_nonneg_right hDlow
    (norm_nonneg (T - G + (κ^2 * ε / 2 : ℝ) *
      (spectralMap κ L z G / D) * deriv (sourceG ε q) z))
  simp only [show (1 + 8 : ℝ) = 9 by norm_num] at hprod hTaylor
  exact hm.trans (hnorm.trans (add_le_add hprod hTaylor))

def transferConstant (κ M d : ℝ) : ℝ :=
  Real.exp (1 / 10) * 9 * ((κ / d)^4 * M^2 + (κ / d)^3 * M)

def displacementConstant (κ M d : ℝ) : ℝ :=
  (transferConstant κ M d * M +
    (κ^2 / 2) * (9 * Real.exp (κ * (M/d))) * (M/d^2)) / (3 * κ / 8)

/-- First-order displacement of the *actual selected inverse*. The only
unproved application margin at this boundary is membership in its specified
target disk; no displacement or inverse remainder is assumed. -/
theorem inverse_transfer_linear
    {κ L M d ε R : ℝ} {U : Set ℂ}
    (hκ : 0 < κ) (hM : 0 < M) (hd : 0 < d)
    (hsmall : κ * M / d ≤ 1 / 10)
    (hR : 0 < R) (hradius : κ * R ≤ 1 / 1000) (hU : IsOpen U)
    (hexp : ∀ z ∈ U, ‖Complex.exp (I * z * L)‖ ≤ 8)
    (hgap : ∀ z ∈ U, 1 / 2 ≤ ‖1 - Complex.exp (I * z * L)‖)
    {N : ℕ} (hN : 0 < N) (hε : 0 ≤ ε) (hεM : ε ≤ M)
    (hbudget : ε * N ≤ M) (q : Fin N → ℝ) {z : ℂ} (hz : z ∈ U)
    (hsep : ∀ j, d ≤ ‖z - (q j : ℂ)‖)
    (hG : ‖sourceG ε q z‖ ≤ R)
    (htarget : ‖transferS (κ * ε) L q z - spectralMap κ L z 0‖ <
      3 / 4 * ‖spectralLinear κ L z‖ * R) :
    ‖spectralInverse κ L R z (transferS (κ * ε) L q z) - sourceG ε q z‖ ≤
      displacementConstant κ M d * ε := by
  let G := sourceG ε q z
  let F := spectralMap κ L z G
  let P := deriv (sourceG ε q) z
  let S := transferS (κ * ε) L q z
  let m := 3 * κ / 8
  have hm : 0 < m := by dsimp [m]; positivity
  have hF : ‖F‖ ≤ 9 * Real.exp (κ * (M/d)) := by
    simpa only [show (1 + 8 : ℝ) = 9 by norm_num] using
      spectralMap_norm_le hκ.le (norm_sourceG_le hε hd hbudget q hsep)
        (by norm_num) (hexp z hz)
  have hP : ‖P‖ ≤ M/d^2 := norm_deriv_sourceG_le hε hd hbudget q hsep
  have hp := transfer_second_order_separated hκ.le hM hd hsmall hN hε hbudget q hsep
    (by norm_num : (0 : ℝ) ≤ 8) (hexp z hz)
  simp only [show (1 + 8 : ℝ) = 9 by norm_num] at hp
  change ‖S - (F - (κ^2 * ε / 2 : ℝ) * F * P)‖ ≤
    transferConstant κ M d * ε^2 at hp
  have ha : 0 ≤ κ^2 * ε / 2 := by positivity
  have hSF : ‖S-F‖ ≤ (transferConstant κ M d * M +
      (κ^2/2) * (9 * Real.exp (κ * (M/d))) * (M/d^2)) * ε := by
    calc
      ‖S-F‖ = ‖(S - (F - (κ^2 * ε / 2 : ℝ) * F * P)) -
          (κ^2 * ε / 2 : ℝ) * F * P‖ := by congr 1; ring
      _ ≤ ‖S - (F - (κ^2 * ε / 2 : ℝ) * F * P)‖ +
          ‖(κ^2 * ε / 2 : ℝ) * F * P‖ := norm_sub_le _ _
      _ ≤ transferConstant κ M d * ε^2 +
          (κ^2 * ε / 2) * (9 * Real.exp (κ * (M/d))) * (M/d^2) := by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
        exact add_le_add hp (mul_le_mul (mul_le_mul_of_nonneg_left hF ha) hP
          (norm_nonneg _) (by positivity))
      _ ≤ transferConstant κ M d * (M * ε) +
          (κ^2 * ε / 2) * (9 * Real.exp (κ * (M/d))) * (M/d^2) := by
        gcongr
        · unfold transferConstant
          positivity
        · nlinarith
      _ = _ := by ring
  have hdist := inverse_distance hκ hR hradius hU hexp hgap hz hG htarget
  have hle := hdist.trans hSF
  rw [mul_comm] at hle
  have hdiv := (le_div_iff₀ hm).mpr hle
  simpa only [displacementConstant, m, mul_div_assoc, div_mul_eq_mul_div,
    G, S, F] using hdiv

def inverseRemainderConstant (κ M d R : ℝ) : ℝ :=
  (transferConstant κ M d + (9 * Real.exp (κ * R) * κ^2) *
    (displacementConstant κ M d)^2) / (3 * κ / 8)

/-- The literal inverse expansion, with a common explicit O(ε²) constant.
This is a pointwise analytic constituent, before the z-derivative replacement
and before the scalar contour integral. -/
theorem inverse_transfer_second_order
    {κ L M d ε R : ℝ} {U : Set ℂ}
    (hκ : 0 < κ) (hM : 0 < M) (hd : 0 < d)
    (hsmall : κ * M / d ≤ 1 / 10)
    (hR : 0 < R) (hradius : κ * R ≤ 1 / 1000) (hU : IsOpen U)
    (hexp : ∀ z ∈ U, ‖Complex.exp (I * z * L)‖ ≤ 8)
    (hgap : ∀ z ∈ U, 1 / 2 ≤ ‖1 - Complex.exp (I * z * L)‖)
    {N : ℕ} (hN : 0 < N) (hε : 0 ≤ ε) (hεM : ε ≤ M)
    (hbudget : ε * N ≤ M) (q : Fin N → ℝ) {z : ℂ} (hz : z ∈ U)
    (hsep : ∀ j, d ≤ ‖z - (q j : ℂ)‖)
    (hG : ‖sourceG ε q z‖ ≤ R)
    (htarget : ‖transferS (κ * ε) L q z - spectralMap κ L z 0‖ <
      3 / 4 * ‖spectralLinear κ L z‖ * R) :
    let T := spectralInverse κ L R z (transferS (κ * ε) L q z)
    ‖T - sourceG ε q z + (κ^2 * ε / 2 : ℝ) *
      (spectralMap κ L z (sourceG ε q z) /
        spectralDerivative κ L z (sourceG ε q z)) * deriv (sourceG ε q) z‖ ≤
      inverseRemainderConstant κ M d R * ε^2 := by
  have hlin := inverse_transfer_linear hκ hM hd hsmall hR hradius hU hexp hgap
    hN hε hεM hbudget q hz hsep hG htarget
  have hrem := inverse_transfer_remainder hκ hM hd hsmall hR hradius hU hexp hgap
    hN hε hbudget q hz hsep hG htarget
  dsimp only at hrem ⊢
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hlin 2
  have hm : 0 < 3 * κ / 8 := by positivity
  rw [mul_pow] at hsq
  have hbound := hrem.trans (add_le_add_right
    (mul_le_mul_of_nonneg_left hsq
      (by positivity : 0 ≤ 9 * Real.exp (κ * R) * κ^2)) _)
  rw [mul_comm] at hbound
  have hdiv := (le_div_iff₀ hm).mpr hbound
  convert hdiv using 1
  unfold inverseRemainderConstant transferConstant
  ring

end QuantumNLS.LOCAL009R22Inverse
#print axioms QuantumNLS.LOCAL009R22Inverse.spectralMap_norm_le
#print axioms QuantumNLS.LOCAL009R22Inverse.spectral_taylor_remainder
#print axioms QuantumNLS.LOCAL009R22Inverse.inverse_distance
#print axioms QuantumNLS.LOCAL009R22Inverse.inverse_transfer_remainder
#print axioms QuantumNLS.LOCAL009R22Inverse.inverse_transfer_linear
#print axioms QuantumNLS.LOCAL009R22Inverse.inverse_transfer_second_order
