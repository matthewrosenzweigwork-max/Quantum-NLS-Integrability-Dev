import Mathlib

/-!
# PROP-006 `thm:B3-period-reconstruction`, pointwise core (label_periods.tex:308-337, 368-442)

Pointwise objects of the two-term reconstruction, for roots `q : Fin N → ℝ`, coupling `c`, and a
background function `G` (later `G_μ`, the Cauchy transform of `μ`):
* `ANf c q z = ∏_j (1 + ic/(z − q_j))` (`A_N`, eq:B3-multiplier; `ANf (−c) q = B_N`),
  `ellf c q z = Σ_j log(1 + ic/(z − q_j))` (`ℓ_N`, principal branch = Taylor branch for
  `|ic/(z−q_j)| < 1`), `dellf` (its derivative `ℓ_N'`), `ef L z = e^{izL}`,
  `sNf = A_N + e^{izL} B_N` (the exact transfer formula);
* background (eq:B3-classical-multiplier): `Af = e^{iκG}`, `sf = A + e^{izL}/A`, `Df = A − e^{izL}/A`;
* eq:B3-reconstructed-multiplier and eq:B3-reconstructed-log: `Wf = (s_N² − s²)/D²`, `DNf = D (1 + W)^{1/2}` (principal
  power, i.e. `exp(½ log(1+W))` with the Taylor logarithm for `|W| < 1`), `aNf = (s_N + D_N)/2`,
  `logaNf = iκG + log(a_N/A)`.

Proved (pointwise, exact):
* `DN_sq`, `quad` (`a_N² − s_N a_N + e^{izL} = 0`), `aD` (`a_N D_N = a_N² − e^{izL}`),
  `residual_eq` (eq:B3-multiplier-residual: `ε² + D_N ε + e^{izL}(A_N B_N − 1) = 0`, `ε = A_N − a_N`);
* `hasDerivAt_log_term`, `hasDerivAt_ell`, `AN_eq_exp`, `hasDerivAt_AN` (away from the roots);
* `differentiableAt_aN`, `deriv_aN_mul_DN` (`a_N' D_N = s_N' a_N − (e^{izL})'`, implicit
  differentiation of the quadratic).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open Complex Filter Topology

namespace QuantumNLS.PeriodReconstructionCore

variable {N : ℕ}

/-- `A_N(z) = ∏_j (1 + ic/(z − q_j))`. -/
def ANf (c : ℝ) (q : Fin N → ℝ) (z : ℂ) : ℂ := ∏ j, (1 + I * c / (z - q j))

/-- `ℓ_N(z) = Σ_j log(1 + ic/(z − q_j))`. -/
def ellf (c : ℝ) (q : Fin N → ℝ) (z : ℂ) : ℂ := ∑ j, log (1 + I * c / (z - q j))

/-- `ℓ_N'(z) = Σ_j −ic/((z − q_j)(z − q_j + ic))`. -/
def dellf (c : ℝ) (q : Fin N → ℝ) (z : ℂ) : ℂ :=
  ∑ j, -(I * c) / ((z - q j) * (z - q j + I * c))

/-- `e^{izL}`. -/
def ef (L : ℝ) (z : ℂ) : ℂ := exp (I * L * z)

/-- The exact transfer formula `s_N = A_N + e^{izL} B_N`, `B_N = ∏(1 − ic/(z − q_j))`. -/
def sNf (L c : ℝ) (q : Fin N → ℝ) (z : ℂ) : ℂ := ANf c q z + ef L z * ANf (-c) q z

/-- `A = e^{iκG}`. -/
def Af (κ : ℝ) (G : ℂ → ℂ) (z : ℂ) : ℂ := exp (I * κ * G z)

/-- `s = A + e^{izL}/A`. -/
def sf (L κ : ℝ) (G : ℂ → ℂ) (z : ℂ) : ℂ := Af κ G z + ef L z / Af κ G z

/-- `D = A − e^{izL}/A`. -/
def Df (L κ : ℝ) (G : ℂ → ℂ) (z : ℂ) : ℂ := Af κ G z - ef L z / Af κ G z

/-- `W = (s_N² − s²)/D²`. -/
def Wf (L κ c : ℝ) (G : ℂ → ℂ) (q : Fin N → ℝ) (z : ℂ) : ℂ :=
  (sNf L c q z ^ 2 - sf L κ G z ^ 2) / Df L κ G z ^ 2

/-- `D_N = D (1 + W)^{1/2}`. -/
def DNf (L κ c : ℝ) (G : ℂ → ℂ) (q : Fin N → ℝ) (z : ℂ) : ℂ :=
  Df L κ G z * (1 + Wf L κ c G q z) ^ ((2 : ℂ)⁻¹)

/-- `a_N = (s_N + D_N)/2`. -/
def aNf (L κ c : ℝ) (G : ℂ → ℂ) (q : Fin N → ℝ) (z : ℂ) : ℂ :=
  (sNf L c q z + DNf L κ c G q z) / 2

/-- `log a_N = iκG + log(a_N/A)`. -/
def logaNf (L κ c : ℝ) (G : ℂ → ℂ) (q : Fin N → ℝ) (z : ℂ) : ℂ :=
  I * κ * G z + log (aNf L κ c G q z / Af κ G z)

/-! ## Exact algebra -/

lemma DN_sq (L κ c : ℝ) (G : ℂ → ℂ) (q : Fin N → ℝ) {z : ℂ} (hD : Df L κ G z ≠ 0) :
    DNf L κ c G q z ^ 2 = sNf L c q z ^ 2 - 4 * ef L z := by
  have hA : Af κ G z ≠ 0 := exp_ne_zero _
  unfold DNf
  rw [mul_pow, Complex.cpow_ofNat_inv_pow]
  unfold Wf
  have h4 : sf L κ G z ^ 2 - Df L κ G z ^ 2 = 4 * ef L z := by
    unfold sf Df; field_simp; ring
  rw [mul_add, mul_one, mul_div_cancel₀ _ (pow_ne_zero 2 hD)]
  linear_combination -h4

lemma quad (L κ c : ℝ) (G : ℂ → ℂ) (q : Fin N → ℝ) {z : ℂ} (hD : Df L κ G z ≠ 0) :
    aNf L κ c G q z ^ 2 - sNf L c q z * aNf L κ c G q z + ef L z = 0 := by
  have h := DN_sq L κ c G q hD
  unfold aNf
  linear_combination h / 4

lemma DN_eq (L κ c : ℝ) (G : ℂ → ℂ) (q : Fin N → ℝ) (z : ℂ) :
    DNf L κ c G q z = 2 * aNf L κ c G q z - sNf L c q z := by unfold aNf; ring

lemma aD (L κ c : ℝ) (G : ℂ → ℂ) (q : Fin N → ℝ) {z : ℂ} (hD : Df L κ G z ≠ 0) :
    aNf L κ c G q z * DNf L κ c G q z = aNf L κ c G q z ^ 2 - ef L z := by
  have h := quad L κ c G q hD
  rw [DN_eq]; linear_combination h

/-- eq:B3-multiplier-residual. -/
lemma residual_eq (L κ c : ℝ) (G : ℂ → ℂ) (q : Fin N → ℝ) {z : ℂ} (hD : Df L κ G z ≠ 0) :
    (ANf c q z - aNf L κ c G q z) ^ 2 + DNf L κ c G q z * (ANf c q z - aNf L κ c G q z) +
      ef L z * (ANf c q z * ANf (-c) q z - 1) = 0 := by
  have h := quad L κ c G q hD
  rw [DN_eq]
  unfold sNf at h ⊢
  linear_combination -h

/-! ## Derivatives away from the roots -/

lemma ne_zero_term {c q : ℝ} {z : ℂ} (hz : 2 * |c| < ‖z - q‖) : 1 + I * c / (z - q) ≠ 0 := by
  have hw : z - q ≠ 0 := by intro h; rw [h, norm_zero] at hz; linarith [abs_nonneg c]
  intro h
  have : I * c / (z - q) = -1 := by linear_combination h
  have h2 := congrArg norm this
  rw [norm_neg, norm_one, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, div_eq_one_iff_eq (norm_ne_zero_iff.2 hw)] at h2
  linarith [abs_nonneg c]

lemma hasDerivAt_log_term {c q : ℝ} {z : ℂ} (hz : 2 * |c| < ‖z - q‖) :
    HasDerivAt (fun w => log (1 + I * c / (w - q)))
      (-(I * c) / ((z - q) * (z - q + I * c))) z := by
  have hw : z - q ≠ 0 := by intro h; rw [h, norm_zero] at hz; linarith [abs_nonneg c]
  have hnw : 0 < ‖z - q‖ := norm_pos_iff.2 hw
  have hu : ‖I * c / (z - q)‖ < 1 / 2 := by
    rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      div_lt_iff₀ hnw]; linarith
  have hre : 0 < (1 + I * c / (z - q)).re := by
    have := Complex.abs_re_le_norm (I * c / (z - q))
    simp only [add_re, one_re]
    linarith [neg_abs_le (I * c / (z - q)).re]
  have hslit : 1 + I * c / (z - q) ∈ slitPlane := Or.inl hre
  have hne1 : 1 + I * c / (z - q) ≠ 0 := slitPlane_ne_zero hslit
  have hw2 : z - q + I * c ≠ 0 := by
    intro h
    have e1 : 1 + I * c / (z - q) = (z - q + I * c) / (z - q) := by field_simp
    rw [e1, h, zero_div] at hne1; exact hne1 rfl
  have hg : HasDerivAt (fun z => 1 + I * c / (z - q)) (-(I * c) / (z - q) ^ 2) z := by
    have h1 := (((hasDerivAt_id' z).sub_const (q : ℂ)).inv hw).const_mul (I * c)
    have h2 := h1.const_add 1
    convert h2 using 1
    · funext w; simp [div_eq_mul_inv]
    · ring
  refine (hg.clog hslit).congr_deriv ?_
  have e1 : 1 + I * c / (z - q) = (z - q + I * c) / (z - q) := by field_simp
  rw [e1]
  field_simp

lemma hasDerivAt_ell {c : ℝ} {q : Fin N → ℝ} {z : ℂ} (hz : ∀ j, 2 * |c| < ‖z - q j‖) :
    HasDerivAt (ellf c q) (dellf c q z) z := by
  unfold ellf dellf
  exact HasDerivAt.fun_sum fun j _ => hasDerivAt_log_term (hz j)

lemma AN_eq_exp {c : ℝ} {q : Fin N → ℝ} {z : ℂ} (hz : ∀ j, 2 * |c| < ‖z - q j‖) :
    ANf c q z = exp (ellf c q z) := by
  unfold ANf ellf
  rw [exp_sum]
  exact Finset.prod_congr rfl fun j _ => (exp_log (ne_zero_term (hz j))).symm

lemma ev_dist {c : ℝ} {q : Fin N → ℝ} {z : ℂ} (hz : ∀ j, 2 * |c| < ‖z - q j‖) :
    ∀ᶠ w : ℂ in 𝓝 z, ∀ j, 2 * |c| < ‖w - q j‖ :=
  Filter.eventually_all.2 fun j =>
    (continuous_norm.comp (continuous_id.sub continuous_const)).continuousAt.eventually
      (lt_mem_nhds (hz j))

lemma hasDerivAt_AN {c : ℝ} {q : Fin N → ℝ} {z : ℂ} (hz : ∀ j, 2 * |c| < ‖z - q j‖) :
    HasDerivAt (ANf c q) (ANf c q z * dellf c q z) z := by
  have heq : (fun w => exp (ellf c q w)) =ᶠ[𝓝 z] ANf c q :=
    (ev_dist hz).mono fun w hw => (AN_eq_exp hw).symm
  rw [AN_eq_exp hz]
  exact ((hasDerivAt_ell hz).cexp).congr_of_eventuallyEq heq.symm

lemma hasDerivAt_ef (L : ℝ) (z : ℂ) : HasDerivAt (ef L) (I * L * ef L z) z := by
  unfold ef
  have := ((hasDerivAt_id' z).const_mul (I * L)).cexp
  simpa [mul_comm] using this

/-- The exact transfer formula and its derivative away from the roots. -/
lemma hasDerivAt_sN (L : ℝ) {c : ℝ} {q : Fin N → ℝ} {z : ℂ} (hz : ∀ j, 2 * |c| < ‖z - q j‖) :
    HasDerivAt (sNf L c q) (ANf c q z * dellf c q z +
      (I * L * ef L z * ANf (-c) q z + ef L z * (ANf (-c) q z * dellf (-c) q z))) z := by
  have hz' : ∀ j, 2 * |(-c)| < ‖z - q j‖ := fun j => by rw [abs_neg]; exact hz j
  exact (hasDerivAt_AN hz).add ((hasDerivAt_ef L z).mul (hasDerivAt_AN hz'))

/-- `a_N` is differentiable where the background is differentiable, `D ≠ 0`, `1 + W` lies in the
slit plane and `z` is away from the roots. -/
lemma differentiableAt_aN (L κ c : ℝ) {G : ℂ → ℂ} {q : Fin N → ℝ} {z : ℂ}
    (hG : DifferentiableAt ℂ G z) (hD : Df L κ G z ≠ 0) (hz : ∀ j, 2 * |c| < ‖z - q j‖)
    (hW : 1 + Wf L κ c G q z ∈ slitPlane) : DifferentiableAt ℂ (aNf L κ c G q) z := by
  have hA : DifferentiableAt ℂ (Af κ G) z := (hG.const_mul (I * κ)).cexp
  have he : DifferentiableAt ℂ (ef L) z := (hasDerivAt_ef L z).differentiableAt
  have hAne : Af κ G z ≠ 0 := exp_ne_zero _
  have hs : DifferentiableAt ℂ (sf L κ G) z := hA.add (he.div hA hAne)
  have hDd : DifferentiableAt ℂ (Df L κ G) z := hA.sub (he.div hA hAne)
  have hsN : DifferentiableAt ℂ (sNf L c q) z := (hasDerivAt_sN L hz).differentiableAt
  have hWd : DifferentiableAt ℂ (Wf L κ c G q) z :=
    ((hsN.pow 2).sub (hs.pow 2)).div (hDd.pow 2) (pow_ne_zero 2 hD)
  have hDN : DifferentiableAt ℂ (DNf L κ c G q) z :=
    hDd.mul ((differentiableAt_const _ |>.add hWd).cpow_const hW)
  exact (hsN.add hDN).div_const 2

/-- **Implicit differentiation**: `a_N' D_N = s_N' a_N − (e^{izL})'`. -/
lemma deriv_aN_mul_DN (L κ c : ℝ) {G : ℂ → ℂ} {q : Fin N → ℝ} {z : ℂ}
    (hG : DifferentiableAt ℂ G z) (hGc : ∀ᶠ w in 𝓝 z, Df L κ G w ≠ 0)
    (hz : ∀ j, 2 * |c| < ‖z - q j‖) (hW : 1 + Wf L κ c G q z ∈ slitPlane) :
    deriv (aNf L κ c G q) z * DNf L κ c G q z =
      (ANf c q z * dellf c q z +
        (I * L * ef L z * ANf (-c) q z + ef L z * (ANf (-c) q z * dellf (-c) q z))) *
          aNf L κ c G q z - I * L * ef L z := by
  have ha := (differentiableAt_aN L κ c hG hGc.self_of_nhds hz hW).hasDerivAt
  have hsN := hasDerivAt_sN L hz
  have he := hasDerivAt_ef L z
  set a' := deriv (aNf L κ c G q) z
  have hf : HasDerivAt (fun w => aNf L κ c G q w ^ 2 - sNf L c q w * aNf L κ c G q w + ef L w)
      (2 * aNf L κ c G q z * a' - ((ANf c q z * dellf c q z +
        (I * L * ef L z * ANf (-c) q z + ef L z * (ANf (-c) q z * dellf (-c) q z))) *
          aNf L κ c G q z + sNf L c q z * a') + I * L * ef L z) z := by
    have h1 := (ha.pow 2).sub (hsN.mul ha)
    have h2 := h1.add he
    convert h2 using 1
    simp only [Nat.cast_ofNat]; ring
  have h0 : HasDerivAt (fun w => aNf L κ c G q w ^ 2 - sNf L c q w * aNf L κ c G q w + ef L w)
      0 z :=
    (hasDerivAt_const z (0 : ℂ)).congr_of_eventuallyEq (hGc.mono fun w hw => quad L κ c G q hw)
  have heq := hf.unique h0
  rw [DN_eq]
  linear_combination heq

end QuantumNLS.PeriodReconstructionCore

#print axioms QuantumNLS.PeriodReconstructionCore.quad
#print axioms QuantumNLS.PeriodReconstructionCore.residual_eq
#print axioms QuantumNLS.PeriodReconstructionCore.aD
#print axioms QuantumNLS.PeriodReconstructionCore.hasDerivAt_AN
#print axioms QuantumNLS.PeriodReconstructionCore.differentiableAt_aN
#print axioms QuantumNLS.PeriodReconstructionCore.deriv_aN_mul_DN
