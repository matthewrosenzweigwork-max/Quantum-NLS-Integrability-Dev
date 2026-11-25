import QuantumNLS.ResetMoserCone

/-!
# `thm:reset-moser` (LOCAL-017), stage 2c: bound on the Hamiltonian field and the angular velocity of the flow

Source: `symplectic_correction.tex`, "The periods of a radial primitive": the loop `s ↦ φ_j^s(z)` has winding vector `−e_j`; "The
linearization of the field at zero is `−i z_j e_j`, by `Ω_0 = ω` and the quadratic formula for `q_j`." Here the winding is computed
directly from the identity `ι_{X_j}Ω = dq_j` paired with the radial vector `z_k e_k`, which gives the angular velocity of the `k`th
coordinate exactly:

* `norm_fderiv_q_le`: `‖dq_n(z)‖ ≤ 2|z_n|`; `norm_Ycov_le`: `‖Ycov D b‖ ≤ ‖b‖` for `‖D‖ < 1`; `norm_Xn_le`: `‖X_j(w)‖ ≤ 2|w_j|`;
* `ang_identity`: `Im(conj(w_k) (X_j)_k(w)) = ½ (Ω_w − ω)(X_j(w), w_k e_k) − δ_{jk}|w_j|²` (exact);
* `ang_bound`: on `B_ρ` (`Loc`), if `w_k ≠ 0`, `|Im(conj(w_k)(X_j)_k(w))/|w_k|² + δ_{jk}| ≤ M‖w‖²|w_j|/|w_k|`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology ENNReal
open Filter Set Metric

namespace QuantumNLS.ResetMoser

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.RealAnalyticDef

theorem norm_fderiv_q_le (n : ℤ) (z : K) : ‖fderiv ℝ (q n) z‖ ≤ 2 * ‖z n‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  rw [fderiv_q_apply, Real.norm_eq_abs]
  have h1 : |(conj (z n) * h n).re| ≤ ‖conj (z n) * h n‖ := Complex.abs_re_le_norm _
  have h2 : ‖conj (z n) * h n‖ = ‖z n‖ * ‖h n‖ := by rw [norm_mul, Complex.norm_conj]
  have h3 : ‖h n‖ ≤ ‖h‖ := lp.norm_apply_le_norm (by norm_num) h n
  have h4 : |2 * (conj (z n) * h n).re| = 2 * |(conj (z n) * h n).re| := by
    rw [abs_mul, abs_two]
  rw [h4]
  have : ‖z n‖ * ‖h n‖ ≤ ‖z n‖ * ‖h‖ := mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
  nlinarith [norm_nonneg (z n)]

theorem norm_Ycov_le {D : Form} (hD : ‖D‖ < 1) (b : Cov) : ‖Ycov D b‖ ≤ ‖b‖ := by
  set Y := Ycov D b with hY
  have hio := iota_Ycov hD b (Complex.I • Y)
  rw [omega_I_smul] at hio
  have hn : ‖Complex.I • Y‖ = ‖Y‖ := by rw [norm_smul, Complex.norm_I, one_mul]
  have h1 : |D Y (Complex.I • Y)| ≤ ‖D‖ * ‖Y‖ * ‖Y‖ := by
    have := D.le_opNorm₂ Y (Complex.I • Y)
    rw [Real.norm_eq_abs, hn] at this
    exact this
  have h2 : |b (Complex.I • Y)| ≤ ‖b‖ * ‖Y‖ := by
    have := b.le_opNorm (Complex.I • Y)
    rw [Real.norm_eq_abs, hn] at this
    exact this
  have h3 : 2 * ‖Y‖ ^ 2 ≤ ‖D‖ * ‖Y‖ * ‖Y‖ + ‖b‖ * ‖Y‖ := by
    have e : 2 * ‖Y‖ ^ 2 = -(D Y (Complex.I • Y)) - b (Complex.I • Y) := by linarith
    rw [e]
    have := neg_abs_le (D Y (Complex.I • Y))
    have := le_abs_self (-(D Y (Complex.I • Y)))
    have := abs_neg (D Y (Complex.I • Y))
    have := neg_abs_le (b (Complex.I • Y))
    have := le_abs_self (-(b (Complex.I • Y)))
    have := abs_neg (b (Complex.I • Y))
    linarith [abs_nonneg (D Y (Complex.I • Y)), abs_nonneg (b (Complex.I • Y)), neg_le_abs (D Y (Complex.I • Y)),
      neg_le_abs (b (Complex.I • Y)), le_abs_self (D Y (Complex.I • Y)), le_abs_self (b (Complex.I • Y))]
  have h0 : 0 ≤ ‖Y‖ := norm_nonneg _
  rcases h0.eq_or_lt with h | h
  · rw [← h]; exact norm_nonneg _
  · have h4 : (2 - ‖D‖) * ‖Y‖ ≤ ‖b‖ := by
      have : (2 - ‖D‖) * ‖Y‖ * ‖Y‖ ≤ ‖b‖ * ‖Y‖ := by nlinarith
      exact le_of_mul_le_mul_right this h
    nlinarith [norm_nonneg D]

theorem norm_Xn_le (S : Hyp) {w : K} (hw : w ∈ ball (0 : K) S.R) (j : ℤ) : ‖Xn S.Ω j w‖ ≤ 2 * ‖w j‖ := by
  unfold Xn
  refine (norm_Ycov_le (S.Ω_lt w hw) _).trans ?_
  rw [norm_neg]
  exact norm_fderiv_q_le j w

/-- **The angular velocity of the `k`th coordinate along `φ_j`**, exactly. -/
theorem ang_identity (S : Hyp) {w : K} (hw : w ∈ ball (0 : K) S.R) (j k : ℤ) :
    (conj (w k) * (Xn S.Ω j w) k).im =
      (1 / 2) * Dl S w (Xn S.Ω j w) (lp.single (E := fun _ : ℤ => ℂ) 2 k (w k)) -
        (if k = j then ‖w j‖ ^ 2 else 0) := by
  set X := Xn S.Ω j w with hX
  set e : K := lp.single (E := fun _ : ℤ => ℂ) 2 k (w k) with he
  have h1 : S.Ω w X e = fderiv ℝ (q j) w e := Xn_spec (S.Ω_lt w hw) j e
  have h2 : S.Ω w X e = Dl S w X e + omega X e := by
    simp only [Dl, ContinuousLinearMap.sub_apply, omegaF_apply]; ring
  have h3 : omega X e = -2 * (conj (w k) * X k).im := by
    rw [omega, he, lp.inner_single_right, RCLike.inner_apply]
    simp [Complex.mul_im]
    ring
  have h4 : fderiv ℝ (q j) w e = 2 * (if k = j then ‖w j‖ ^ 2 else 0) := by
    rw [fderiv_q_apply, he, lp.single_apply]
    by_cases hk : k = j
    · subst hk
      simp [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sq_norm, Complex.normSq_apply]
    · have : j ≠ k := fun h => hk h.symm
      simp [hk, this]
  have h5 := h1.symm.trans h2
  rw [h3, h4] at h5
  linarith

theorem ang_bound (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) {w : K} (hw : w ∈ ball (0 : K) ρ) (j k : ℤ)
    (hk : w k ≠ 0) :
    |(conj (w k) * (Xn S.Ω j w) k).im / ‖w k‖ ^ 2 + (if k = j then 1 else 0)| ≤
      M * ‖w‖ ^ 2 * ‖w j‖ / ‖w k‖ := by
  have hwR := ball_mono_R hL hw
  have hid := ang_identity S hwR j k
  have hk0 : 0 < ‖w k‖ := norm_pos_iff.2 hk
  set X := Xn S.Ω j w with hX
  set e : K := lp.single (E := fun _ : ℤ => ℂ) 2 k (w k) with he
  have hne : ‖e‖ = ‖w k‖ := by rw [he, lp.norm_single (by norm_num)]
  have hXb : ‖X‖ ≤ 2 * ‖w j‖ := norm_Xn_le S hwR j
  have hDl : ‖Dl S w‖ ≤ M * ‖w‖ ^ 2 := hL.b2 w hw
  have hbd : |Dl S w X e| ≤ M * ‖w‖ ^ 2 * (2 * ‖w j‖) * ‖w k‖ := by
    have h1 := (Dl S w).le_opNorm₂ X e
    rw [Real.norm_eq_abs] at h1
    refine h1.trans ?_
    rw [hne]
    have h0 := hL.M0
    gcongr
  have heq : (conj (w k) * X k).im / ‖w k‖ ^ 2 + (if k = j then 1 else 0) =
      (1 / 2) * Dl S w X e / ‖w k‖ ^ 2 := by
    rw [hid]
    by_cases hkj : k = j
    · subst hkj
      simp only [if_true]
      field_simp
      ring
    · simp only [hkj, if_false]
      field_simp
      ring
  rw [heq, abs_div, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2), abs_of_pos (by positivity : 0 < ‖w k‖ ^ 2)]
  rw [div_le_div_iff₀ (by positivity) hk0]
  have : (1 / 2) * |Dl S w X e| ≤ (1 / 2) * (M * ‖w‖ ^ 2 * (2 * ‖w j‖) * ‖w k‖) :=
    mul_le_mul_of_nonneg_left hbd (by norm_num)
  nlinarith [this, norm_nonneg (w k), hk0]

end QuantumNLS.ResetMoser

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoser.norm_Ycov_le
#print axioms QuantumNLS.ResetMoser.norm_Xn_le
#print axioms QuantumNLS.ResetMoser.ang_identity
#print axioms QuantumNLS.ResetMoser.ang_bound
