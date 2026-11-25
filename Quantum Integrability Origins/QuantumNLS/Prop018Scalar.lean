import QuantumNLS.Prop018Phase

/-!
# PROP-018 (`Q7A:prop:reconstruct`), `eq:scalarerror`, and the assembled proposition

Source: `window_reconstruction.tex`, `Q7A:eq:scalar` and the last paragraph of the proof of `Q7A:prop:reconstruct`:
"By `eq:derivative`, the transfer and its first derivative differ from the background by at most `C(ε+R^{−b}+N^{−1})`.
The uniform smoothness of `q̃_z` and `q(z,s,s') = eA'/[A(A²−e)]` therefore give `eq:scalarerror` after integration."

* `qch_bg`: `q(z, s, s') = e A'/(A(A² − e))` (the scalar integrand of `Q7A:eq:scalar`);
* `lip_q`, `norm_DN_sub_D`, `qch_diff_le`: the uniform Lipschitz bound of `q` near the background, with explicit constants,
  using `|D_N − D| ≤ |s_N² − s²|/|D|` (principal square root has nonnegative real part);
* `scalar_of_bundle`: `|C_{1,N,p}(m) − c_{N,p}| ≤ Cs Σ_r|p_r| (1+a)^{d+1} (ε_N + R_N^{−b} + N^{−1})` on the event;
* **`prop018_reconstruct`**: `eq:phase` and `eq:scalarerror` together, on one event `𝓔_N` with one packet radius, for all
  extensions `f`, `q̃` agreeing with `λ`, `q` near the background, uniformly in the polynomial and the label.
`RootSpectralInputs` is carried as an explicit hypothesis.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology Complex Set
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace QuantumNLS.Prop018Scalar

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheLabels (MArr arrRoots)
open QuantumNLS.EmpiricalRapidity (bornMeasure)
open QuantumNLS.BulkResponseActual (physBasis IsLimitingRapidityMeasure)
open QuantumNLS.Extrapolation (Gfull GN)
open QuantumNLS.RootEvent (EN)
open QuantumNLS.ResolventNeighborhood (GammaN NbhdN sNsrc sLimsrc)
open QuantumNLS.PROP018Probability (cutN regime_eventually)
open QuantumNLS.Prop017Quantum (qAct eta0)
open QuantumNLS.Prop017Physical (RootSpectralInputs)
open QuantumNLS.PeriodReconstructionCore QuantumNLS.PeriodTwoTerm
open QuantumNLS.PeriodReconstruction (Gam)
open QuantumNLS.LabelExactPeriod (rectIntegral)
open QuantumNLS.Prop018Period (poly continuous_poly)
open QuantumNLS.Prop018Bundle (moving_contour_bundle)
open QuantumNLS.HaarSummableReconstruction (contAt_gen)
open QuantumNLS.BetheSpectralCharges (eigenvalue)
open QuantumNLS.Prop018Phase (dch ach lam qch corrf_eq_qch sNsrc_eq sLimsrc_eq C0ev C1ev gam_sub_nbhd norm_le_of_gam
  norm_poly_le phase_of_bundle)

/-! ## 1. Elementary norm estimates -/

lemma norm_inv_sub_inv_le {x y : ℂ} {m : ℝ} (hm : 0 < m) (hx : m ≤ ‖x‖) (hy : m ≤ ‖y‖) :
    ‖x⁻¹ - y⁻¹‖ ≤ ‖x - y‖ / m ^ 2 := by
  have hx0 : x ≠ 0 := fun h => by rw [h, norm_zero] at hx; linarith
  have hy0 : y ≠ 0 := fun h => by rw [h, norm_zero] at hy; linarith
  rw [inv_sub_inv hx0 hy0, norm_div, norm_mul, norm_sub_rev y x]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  exact mul_le_mul_of_nonneg_left (by nlinarith) (norm_nonneg _)

lemma norm_sq_sub_sq_le {x y : ℂ} {B : ℝ} (hx : ‖x‖ ≤ B) (hy : ‖y‖ ≤ B) :
    ‖x ^ 2 - y ^ 2‖ ≤ 2 * B * ‖x - y‖ := by
  rw [sq_sub_sq, norm_mul]
  have h := norm_add_le x y
  exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

lemma norm_mul_sub_mul_le {x1 x0 y1 y0 : ℂ} {X Y : ℝ} (hx : ‖x0‖ ≤ X) (hy : ‖y1‖ ≤ Y) :
    ‖x1 * y1 - x0 * y0‖ ≤ ‖x1 - x0‖ * Y + X * ‖y1 - y0‖ := by
  have e : x1 * y1 - x0 * y0 = (x1 - x0) * y1 + x0 * (y1 - y0) := by ring
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_mul]
  · exact mul_le_mul_of_nonneg_left hy (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

lemma norm_inv_le {x : ℂ} {m : ℝ} (hm : 0 < m) (hx : m ≤ ‖x‖) : ‖x⁻¹‖ ≤ 1 / m := by
  rw [norm_inv, one_div]; exact inv_anti₀ hm hx

lemma norm_inv_sq_le {x : ℂ} {m : ℝ} (hm : 0 < m) (hx : m ≤ ‖x‖) : ‖(x⁻¹) ^ 2‖ ≤ 1 / m ^ 2 := by
  rw [norm_pow]
  have := pow_le_pow_left₀ (norm_nonneg _) (norm_inv_le hm hx) 2
  simpa only [div_pow, one_pow] using this

/-- Lipschitz bound for `(a, v, d) ↦ E (a v − c)/(a² d²)` away from `a = 0`, `d = 0`. -/
lemma lip_q {E c a1 a0 v1 v0 d1 d0 : ℂ} {M V ma md Da Dv Dd : ℝ} (hma : 0 < ma) (hmd : 0 < md)
    (hE : ‖E‖ ≤ M) (hc : ‖c‖ ≤ M) (ha1 : ma ≤ ‖a1‖) (ha0 : ma ≤ ‖a0‖) (ha0u : ‖a0‖ ≤ M)
    (hd1 : md ≤ ‖d1‖) (hd0 : md ≤ ‖d0‖) (hv1 : ‖v1‖ ≤ V) (hv0 : ‖v0‖ ≤ V)
    (hDa : ‖a1 - a0‖ ≤ Da) (hDv : ‖v1 - v0‖ ≤ Dv) (hDd : ‖d1 - d0‖ ≤ Dd) :
    ‖E * (a1 * v1 - c) / (a1 ^ 2 * d1 ^ 2) - E * (a0 * v0 - c) / (a0 ^ 2 * d0 ^ 2)‖ ≤
      M * ((Da * V + M * Dv) * (1 / ma ^ 2 * (1 / md ^ 2)) +
        (M * V + M) * (2 * (1 / ma) * (Da / ma ^ 2) * (1 / md ^ 2) +
          1 / ma ^ 2 * (2 * (1 / md) * (Dd / md ^ 2)))) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans hE
  have hV : 0 ≤ V := (norm_nonneg _).trans hv0
  have ha10 : a1 ≠ 0 := fun h => by rw [h, norm_zero] at ha1; linarith
  have ha00 : a0 ≠ 0 := fun h => by rw [h, norm_zero] at ha0; linarith
  have hd10 : d1 ≠ 0 := fun h => by rw [h, norm_zero] at hd1; linarith
  have hd00 : d0 ≠ 0 := fun h => by rw [h, norm_zero] at hd0; linarith
  have e : E * (a1 * v1 - c) / (a1 ^ 2 * d1 ^ 2) - E * (a0 * v0 - c) / (a0 ^ 2 * d0 ^ 2) =
      E * ((a1 * v1 - c) * ((a1⁻¹) ^ 2 * (d1⁻¹) ^ 2) - (a0 * v0 - c) * ((a0⁻¹) ^ 2 * (d0⁻¹) ^ 2)) := by
    field_simp
  rw [e, norm_mul]
  refine mul_le_mul hE ?_ (norm_nonneg _) hM
  have hX0 : ‖a0 * v0 - c‖ ≤ M * V + M := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ hc)
    rw [norm_mul]; exact mul_le_mul ha0u hv0 (norm_nonneg _) hM
  have hY1 : ‖(a1⁻¹) ^ 2 * (d1⁻¹) ^ 2‖ ≤ 1 / ma ^ 2 * (1 / md ^ 2) := by
    rw [norm_mul]
    exact mul_le_mul (norm_inv_sq_le hma ha1) (norm_inv_sq_le hmd hd1) (norm_nonneg _) (by positivity)
  have hYd : ‖(a1⁻¹) ^ 2 * (d1⁻¹) ^ 2 - (a0⁻¹) ^ 2 * (d0⁻¹) ^ 2‖ ≤
      2 * (1 / ma) * (Da / ma ^ 2) * (1 / md ^ 2) +
        1 / ma ^ 2 * (2 * (1 / md) * (Dd / md ^ 2)) := by
    refine (norm_mul_sub_mul_le (norm_inv_sq_le hma ha0) (norm_inv_sq_le hmd hd1)).trans (add_le_add ?_ ?_)
    · refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      refine (norm_sq_sub_sq_le (norm_inv_le hma ha1) (norm_inv_le hma ha0)).trans ?_
      refine mul_le_mul_of_nonneg_left ((norm_inv_sub_inv_le hma ha1 ha0).trans ?_) (by positivity)
      exact div_le_div_of_nonneg_right hDa (by positivity)
    · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine (norm_sq_sub_sq_le (norm_inv_le hmd hd1) (norm_inv_le hmd hd0)).trans ?_
      refine mul_le_mul_of_nonneg_left ((norm_inv_sub_inv_le hmd hd1 hd0).trans ?_) (by positivity)
      exact div_le_div_of_nonneg_right hDd (by positivity)
  have hXd : ‖(a1 * v1 - c) - (a0 * v0 - c)‖ ≤ Da * V + M * Dv := by
    rw [sub_sub_sub_cancel_right]
    refine (norm_mul_sub_mul_le ha0u hv1).trans (add_le_add ?_ ?_)
    · exact mul_le_mul_of_nonneg_right hDa hV
    · exact mul_le_mul_of_nonneg_left hDv hM
  refine (norm_mul_sub_mul_le hX0 hY1).trans (add_le_add ?_ ?_)
  · exact mul_le_mul_of_nonneg_right hXd (by positivity)
  · exact mul_le_mul_of_nonneg_left hYd (add_nonneg (mul_nonneg hM hV) hM)

/-- `|(1 + W)^{1/2} − 1| ≤ |W|` for the principal square root (its real part is nonnegative). -/
lemma norm_sqrt_sub_one_le (W : ℂ) : ‖(1 + W) ^ ((2 : ℂ)⁻¹) - 1‖ ≤ ‖W‖ := by
  set ζ := (1 + W) ^ ((2 : ℂ)⁻¹) with hζ
  have hsq : ζ ^ 2 = 1 + W := by rw [hζ]; exact Complex.cpow_ofNat_inv_pow _ _
  have hre : 0 ≤ ζ.re := by rw [hζ, Complex.cpow_inv_two_re]; exact Real.sqrt_nonneg _
  have h1 : 1 ≤ ‖ζ + 1‖ := by
    have := Complex.re_le_norm (ζ + 1)
    simp only [add_re, one_re] at this
    linarith
  have e : (ζ - 1) * (ζ + 1) = W := by linear_combination hsq
  have : ‖ζ - 1‖ * ‖ζ + 1‖ = ‖W‖ := by rw [← norm_mul, e]
  nlinarith [norm_nonneg (ζ - 1)]

/-! ## 2. The background chart values -/

lemma dch_bg (L κ : ℝ) (G : ℂ → ℂ) (z : ℂ) : dch L κ G z (sf L κ G z) = Df L κ G z := by
  unfold dch; simp

lemma ach_bg (L κ : ℝ) (G : ℂ → ℂ) (z : ℂ) : ach L κ G z (sf L κ G z) = Af κ G z := by
  unfold ach; rw [dch_bg]; unfold sf Df; ring

/-- `q(z, s, s') = e A'/(A(A² − e))`: the integrand of the scalar `c_{N,p}` (`Q7A:eq:scalar`). -/
lemma qch_bg {L κ : ℝ} {G : ℂ → ℂ} {z : ℂ} (hG : DifferentiableAt ℂ G z) (hD : Df L κ G z ≠ 0) :
    qch L κ G z (sf L κ G z) (deriv (sf L κ G) z) =
      ef L z * deriv (Af κ G) z / (Af κ G z * (Af κ G z ^ 2 - ef L z)) := by
  have hAd : DifferentiableAt ℂ (Af κ G) z := (hG.const_mul (I * κ)).cexp
  have hA := hAd.hasDerivAt
  have hA0 : Af κ G z ≠ 0 := exp_ne_zero _
  have hs : HasDerivAt (sf L κ G) (deriv (Af κ G) z +
      (I * L * ef L z * Af κ G z - ef L z * deriv (Af κ G) z) / Af κ G z ^ 2) z :=
    hA.add ((hasDerivAt_ef L z).div hA hA0)
  rw [hs.deriv]
  unfold qch
  rw [ach_bg, dch_bg]
  have hA2 : Af κ G z ^ 2 - ef L z ≠ 0 := by
    intro h0; apply hD; unfold Df; field_simp; linear_combination h0
  have hD' : Df L κ G z = (Af κ G z ^ 2 - ef L z) / Af κ G z := by unfold Df; field_simp
  rw [hD']
  field_simp
  ring

/-- `|D_N − D| ≤ |s_N² − s²|/|D|`. -/
lemma norm_DN_sub_D (L κ c : ℝ) (G : ℂ → ℂ) {N : ℕ} (q : Fin N → ℝ) {z : ℂ} (hD : Df L κ G z ≠ 0) :
    ‖DNf L κ c G q z - Df L κ G z‖ ≤ ‖sNf L c q z ^ 2 - sf L κ G z ^ 2‖ / ‖Df L κ G z‖ := by
  have hDn : 0 < ‖Df L κ G z‖ := norm_pos_iff.2 hD
  have hDn' : ‖Df L κ G z‖ ≠ 0 := hDn.ne'
  unfold DNf
  rw [show Df L κ G z * (1 + Wf L κ c G q z) ^ ((2 : ℂ)⁻¹) - Df L κ G z =
      Df L κ G z * ((1 + Wf L κ c G q z) ^ ((2 : ℂ)⁻¹) - 1) by ring, norm_mul]
  refine (mul_le_mul_of_nonneg_left (norm_sqrt_sub_one_le _) (norm_nonneg _)).trans (le_of_eq ?_)
  unfold Wf
  rw [norm_div, norm_pow]
  field_simp

lemma A_eq_half (L κ : ℝ) (G : ℂ → ℂ) (z : ℂ) : Af κ G z = (sf L κ G z + Df L κ G z) / 2 := by
  unfold sf Df; ring

lemma norm_sf_le {L κ : ℝ} {G : ℂ → ℂ} {z : ℂ} {M : ℝ} (hA : ‖Af κ G z‖ ≤ M) (hAi : ‖(Af κ G z)⁻¹‖ ≤ M)
    (he : ‖ef L z‖ ≤ M) : ‖sf L κ G z‖ ≤ M + M * M := by
  unfold sf
  rw [div_eq_mul_inv]
  refine (norm_add_le _ _).trans (add_le_add hA ?_)
  rw [norm_mul]
  exact mul_le_mul he hAi (norm_nonneg _) ((norm_nonneg _).trans he)

/-! ## 3. The pointwise Lipschitz estimate on the moving contour -/

/-- The explicit pointwise constant. -/
def Lbd (M η L Vs δs δv : ℝ) : ℝ :=
  M * (1 + |L|) * (((1 + 2 * (M + M * M + 1) / η) / 2 * δs * (Vs + 1) + M * (1 + |L|) * δv) *
      (1 / (1 / (2 * M)) ^ 2 * (1 / (η / 2) ^ 2)) +
    (M * (1 + |L|) * (Vs + 1) + M * (1 + |L|)) *
      (2 * (1 / (1 / (2 * M))) * ((1 + 2 * (M + M * M + 1) / η) / 2 * δs / (1 / (2 * M)) ^ 2) *
          (1 / (η / 2) ^ 2) +
        1 / (1 / (2 * M)) ^ 2 * (2 * (1 / (η / 2)) * (2 * (M + M * M + 1) / η * δs / (η / 2) ^ 2))))

lemma Lbd_scale (M η L Vs k δ ρ : ℝ) :
    Lbd M η L Vs (k * δ) (k * δ / (ρ / 2)) = Lbd M η L Vs k (k / (ρ / 2)) * δ := by
  unfold Lbd; ring

lemma Lbd_nonneg {M η L Vs k ρ : ℝ} (hM : 1 ≤ M) (hη : 0 < η) (hVs : 0 ≤ Vs) (hk : 0 ≤ k) (hρ : 0 < ρ) :
    0 ≤ Lbd M η L Vs k (k / (ρ / 2)) := by
  have hM0 : 0 < M := by linarith
  unfold Lbd; positivity

/-- **Pointwise `eq:scalarerror` integrand bound**: `|q(z,s_N,s_N') − q(z,s,s')| ≤ Lbd(δs, δv)` where `δs`, `δv` bound
`|s_N − s|`, `|s_N' − s'|` (both `≤ 1`). -/
lemma qch_diff_le {L κ c : ℝ} {G : ℂ → ℂ} {N : ℕ} {q : Fin N → ℝ} {z : ℂ} {M η Vs δs δv : ℝ}
    (hM1 : 1 ≤ M) (hη : 0 < η)
    (hA : ‖Af κ G z‖ ≤ M) (hAi : ‖(Af κ G z)⁻¹‖ ≤ M) (he : ‖ef L z‖ ≤ M) (hD : η ≤ ‖Df L κ G z‖)
    (ha : 1 / (2 * M) ≤ ‖aNf L κ c G q z‖) (hDN : 3 * η / 4 ≤ ‖DNf L κ c G q z‖)
    (hv : ‖deriv (sf L κ G) z‖ ≤ Vs)
    (hds : ‖sNf L c q z - sf L κ G z‖ ≤ δs) (hdv : ‖deriv (sNf L c q) z - deriv (sf L κ G) z‖ ≤ δv)
    (hδs1 : δs ≤ 1) (hδv1 : δv ≤ 1) :
    ‖qch L κ G z (sNf L c q z) (deriv (sNf L c q) z) - qch L κ G z (sf L κ G z) (deriv (sf L κ G) z)‖ ≤
      Lbd M η L Vs δs δv := by
  have hM0 : 0 < M := by linarith
  have hD0 : Df L κ G z ≠ 0 := fun h0 => by rw [h0, norm_zero] at hD; linarith
  have hDpos : 0 < ‖Df L κ G z‖ := by linarith
  set Ks : ℝ := M + M * M with hKs
  have hs : ‖sf L κ G z‖ ≤ Ks := norm_sf_le hA hAi he
  have hsN : ‖sNf L c q z‖ ≤ Ks + 1 := by
    have := norm_add_le (sNf L c q z - sf L κ G z) (sf L κ G z)
    rw [sub_add_cancel] at this; linarith
  have hδs0 : 0 ≤ δs := (norm_nonneg _).trans hds
  -- `|D_N − D|`
  have hDD : ‖DNf L κ c G q z - Df L κ G z‖ ≤ 2 * (Ks + 1) / η * δs := by
    refine (norm_DN_sub_D L κ c G q hD0).trans ?_
    have h1 : ‖sNf L c q z ^ 2 - sf L κ G z ^ 2‖ ≤ 2 * (Ks + 1) * δs :=
      (norm_sq_sub_sq_le hsN (by linarith)).trans (mul_le_mul_of_nonneg_left hds (by positivity))
    calc ‖sNf L c q z ^ 2 - sf L κ G z ^ 2‖ / ‖Df L κ G z‖
        ≤ 2 * (Ks + 1) * δs / ‖Df L κ G z‖ := div_le_div_of_nonneg_right h1 hDpos.le
      _ ≤ 2 * (Ks + 1) * δs / η := div_le_div_of_nonneg_left (by positivity) hη hD
      _ = 2 * (Ks + 1) / η * δs := by ring
  -- `|a_N − A|`
  have haA : ‖aNf L κ c G q z - Af κ G z‖ ≤ (1 + 2 * (Ks + 1) / η) / 2 * δs := by
    have e : aNf L κ c G q z - Af κ G z =
        ((sNf L c q z - sf L κ G z) + (DNf L κ c G q z - Df L κ G z)) / 2 := by
      rw [A_eq_half L κ G z]; unfold aNf; ring
    rw [e, norm_div, Complex.norm_two]
    have := norm_add_le (sNf L c q z - sf L κ G z) (DNf L κ c G q z - Df L κ G z)
    have h2 : ‖sNf L c q z - sf L κ G z‖ + ‖DNf L κ c G q z - Df L κ G z‖ ≤ δs + 2 * (Ks + 1) / η * δs :=
      add_le_add hds hDD
    have : (1 + 2 * (Ks + 1) / η) / 2 * δs = (δs + 2 * (Ks + 1) / η * δs) / 2 := by ring
    rw [this]
    exact div_le_div_of_nonneg_right (by linarith) (by norm_num)
  -- the inputs of `lip_q`
  have hA0 : Af κ G z ≠ 0 := exp_ne_zero _
  have hAlow : 1 / (2 * M) ≤ ‖Af κ G z‖ := by
    have hAn : 0 < ‖Af κ G z‖ := norm_pos_iff.2 hA0
    rw [norm_inv] at hAi
    have h1 : 1 / M ≤ ‖Af κ G z‖ := (one_div_le hM0 hAn).2 (by rw [one_div]; exact hAi)
    have h2 : 1 / (2 * M) ≤ 1 / M := one_div_le_one_div_of_le hM0 (by linarith)
    linarith
  have hMq : M ≤ M * (1 + |L|) := by nlinarith [abs_nonneg L]
  have hc : ‖I * (L : ℂ) * ef L z‖ ≤ M * (1 + |L|) := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [abs_nonneg L, norm_nonneg (ef L z)]
  have hvN : ‖deriv (sNf L c q) z‖ ≤ Vs + 1 := by
    have := norm_add_le (deriv (sNf L c q) z - deriv (sf L κ G) z) (deriv (sf L κ G) z)
    rw [sub_add_cancel] at this; linarith
  have hlip := lip_q (E := ef L z) (c := I * (L : ℂ) * ef L z) (a1 := aNf L κ c G q z) (a0 := Af κ G z)
    (v1 := deriv (sNf L c q) z) (v0 := deriv (sf L κ G) z) (d1 := DNf L κ c G q z) (d0 := Df L κ G z)
    (M := M * (1 + |L|)) (V := Vs + 1) (ma := 1 / (2 * M)) (md := η / 2)
    (by positivity) (by positivity) (he.trans hMq) hc ha hAlow (hA.trans hMq) (by linarith) (by linarith)
    hvN (by linarith) haA hdv hDD
  have e1 : qch L κ G z (sNf L c q z) (deriv (sNf L c q) z) = ef L z * (aNf L κ c G q z * deriv (sNf L c q) z -
      I * (L : ℂ) * ef L z) / (aNf L κ c G q z ^ 2 * DNf L κ c G q z ^ 2) := rfl
  have e0 : qch L κ G z (sf L κ G z) (deriv (sf L κ G) z) = ef L z * (Af κ G z * deriv (sf L κ G) z -
      I * (L : ℂ) * ef L z) / (Af κ G z ^ 2 * Df L κ G z ^ 2) := by
    unfold qch; rw [ach_bg, dch_bg]
  rw [e1, e0]
  refine hlip.trans (le_of_eq ?_)
  unfold Lbd
  rw [hKs]

/-! ## 4. The scalar -/

/-- The scalar `c_{N,p} = Re (i/2π) ∮_{Γ_N} p(z) e(z)A'(z)/(A(z)(A(z)² − e(z))) dz` (`Q7A:eq:scalar`). -/
def cscal (L κ : ℝ) (μ : Measure ℝ) (θ h : ℝ) (p : ℕ → ℝ) (d N : ℕ) : ℝ :=
  ((I / (2 * Real.pi)) * rectIntegral (fun z => poly p d z * (ef L z * deriv (Af κ (Gfull μ)) z /
    (Af κ (Gfull μ) z * (Af κ (Gfull μ) z ^ 2 - ef L z)))) (-cutN L θ N) (cutN L θ N) h).re

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-- **`eq:scalarerror` from the moving-contour bundle**. -/
theorem scalar_of_bundle (μ : Measure ℝ) {h ρ C M η r K Kd θ γ : ℝ} {b : ℕ} (hh : 0 < h)
    (hρ0 : 0 < ρ) (hM1 : 1 ≤ M) (hη : 0 < η) (hθ : 0 < θ) (hγ : 0 < γ) (hb : 1 ≤ b)
    (E : (N : ℕ) → Set (MArr N))
    (hev : ∀ᶠ N : ℕ in atTop, ∀ m ∈ E N, ∀ z ∈ NbhdN (cutN L θ N) h (ρ / 8),
          ((∀ j, 2 * |κ / (N : ℝ)| < ‖z - (qAct L κ N m j : ℂ)‖) ∧
          ‖Wf L κ (κ / N) (Gfull μ) (qAct L κ N m) z‖ ≤ 1 / 2 ∧
          1 / (2 * M) ≤ ‖aNf L κ (κ / N) (Gfull μ) (qAct L κ N m) z‖ ∧
          3 * η / 4 ≤ ‖DNf L κ (κ / N) (Gfull μ) (qAct L κ N m) z‖ ∧
          ‖aNf L κ (κ / N) (Gfull μ) (qAct L κ N m) z - Af κ (Gfull μ) z‖ ≤ 1 / (2 * M) ∧
          ‖ellf (κ / N) (qAct L κ N m) z - logaNf L κ (κ / N) (Gfull μ) (qAct L κ N m) z +
              I * κ / (N : ℂ) * corrf L κ (κ / N) (Gfull μ) (qAct L κ N m) z‖ ≤ C / (N : ℝ) ^ 2) ∧
          (∀ j, |qAct L κ N m j| ≤ (N : ℝ) ^ θ) ∧
          ‖Gfull μ z - GN (qAct L κ N m) z‖ ≤ K * ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b) ∧
          (∀ j, r ≤ ‖z - (qAct L κ N m j : ℂ)‖) ∧
          DifferentiableAt ℂ (Gfull μ) z ∧
          η ≤ ‖Df L κ (Gfull μ) z‖ ∧
          ‖Af κ (Gfull μ) z‖ ≤ M ∧ ‖(Af κ (Gfull μ) z)⁻¹‖ ≤ M ∧ ‖ef L z‖ ≤ M ∧
          ∀ n : ℕ, ‖iteratedDeriv n (fun w => sNsrc κ L (qAct L κ N m) w - sLimsrc κ L μ w) z‖ ≤
            n.factorial * (Kd * ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b + 1 / (N : ℝ))) / (ρ / 2) ^ n)
    (d : ℕ) (r0 : ℝ) (hr0' : 0 < r0) (qt : ℂ → ℂ → ℂ → ℂ)
    (hqt : ∀ z w v, ‖w - sf L κ (Gfull μ) z‖ < r0 →
      ‖v - deriv (sf L κ (Gfull μ)) z‖ < r0 → qt z w v = qch L κ (Gfull μ) z w v) :
    ∀ᶠ N : ℕ in atTop, ∀ p : ℕ → ℝ, ∀ m ∈ E N,
      |C1ev L κ qt θ h p d N m - cscal L κ μ θ h p d N| ≤
        4 * Lbd M η L ((M + M * M) / (ρ / 16)) (max Kd 0) (max Kd 0 / (ρ / 2)) * (1 + h) ^ (d + 1) /
            (2 * Real.pi) * (∑ r ∈ Finset.range (d + 1), |p r|) * (1 + cutN L θ N) ^ (d + 1) *
          ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b + 1 / (N : ℝ)) := by
  have hL : 0 < L := Fact.out
  have hpi : 0 < Real.pi := Real.pi_pos
  have hM0 : 0 < M := by linarith
  set Kd' : ℝ := max Kd 0 with hKd'
  have hKd'0 : 0 ≤ Kd' := le_max_right _ _
  set Vs : ℝ := (M + M * M) / (ρ / 16) with hVs
  have hVs0 : 0 ≤ Vs := by rw [hVs]; positivity
  set Lq : ℝ := Lbd M η L Vs Kd' (Kd' / (ρ / 2)) with hLq
  have hLq0 : 0 ≤ Lq := Lbd_nonneg hM1 hη hVs0 hKd'0 hρ0
  -- `δ_N → 0`
  have hδN : Tendsto (fun N : ℕ => Kd' * ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b + 1 / (N : ℝ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-γ)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hγ).comp tendsto_natCast_atTop_atTop
    have hR' : Tendsto (fun N : ℕ => (N : ℝ) ^ θ) atTop atTop :=
      (tendsto_rpow_atTop hθ).comp tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun N : ℕ => 1 / ((N : ℝ) ^ θ) ^ b) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by omega)).comp hR')
    have h3 : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa using ((h1.add h2).add h3).const_mul Kd'
  have hδN2 : Tendsto (fun N : ℕ => Kd' * ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b + 1 / (N : ℝ)) / (ρ / 2))
      atTop (𝓝 0) := by simpa using hδN.div_const (ρ / 2)
  have hsm : ∀ᶠ N : ℕ in atTop,
      (Kd' * ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b + 1 / (N : ℝ)) < r0 ∧
        Kd' * ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b + 1 / (N : ℝ)) / (ρ / 2) < r0) ∧
      (Kd' * ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b + 1 / (N : ℝ)) < 1 ∧
        Kd' * ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b + 1 / (N : ℝ)) / (ρ / 2) < 1) :=
    ((hδN.eventually (gt_mem_nhds hr0')).and (hδN2.eventually (gt_mem_nhds hr0'))).and
      ((hδN.eventually (gt_mem_nhds one_pos)).and (hδN2.eventually (gt_mem_nhds one_pos)))
  filter_upwards [hev, hsm, regime_eventually hL hθ hγ 1 0, eventually_ge_atTop 1]
    with N hevN hsmN hreg hN1
  intro p m hm
  have hN : 0 < N := hN1
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ha2 : 2 ≤ cutN L θ N := by linarith [hreg.1, hreg.2.2.1]
  have hρ8 : 0 < ρ / 8 := by positivity
  set δN : ℝ := (N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b + 1 / (N : ℝ) with hδNdef
  have hδN0 : 0 ≤ δN := by
    have : 0 < (N : ℝ) ^ θ := Real.rpow_pos_of_pos hNr θ
    have : 0 < (N : ℝ) ^ (-γ) := Real.rpow_pos_of_pos hNr _
    rw [hδNdef]; positivity
  have hzN : ∀ z ∈ Gam (-(cutN L θ N)) (cutN L θ N) h, z ∈ NbhdN (cutN L θ N) h (ρ / 8) := fun z hz =>
    gam_sub_nbhd hz (by rw [sub_self, norm_zero]; exact hρ8.le)
  have hball : ∀ z ∈ Gam (-(cutN L θ N)) (cutN L θ N) h, Metric.ball z (ρ / 8) ⊆ NbhdN (cutN L θ N) h (ρ / 8) :=
    fun z hz w hw => gam_sub_nbhd hz (by rw [Metric.mem_ball, dist_eq_norm] at hw; exact hw.le)
  have hsfd : ∀ z ∈ NbhdN (cutN L θ N) h (ρ / 8), DifferentiableAt ℂ (sf L κ (Gfull μ)) z := fun z hz => by
    have hG := (hevN m hm z hz).2.2.2.2.1
    have hA : DifferentiableAt ℂ (Af κ (Gfull μ)) z := (hG.const_mul (I * κ)).cexp
    have he : DifferentiableAt ℂ (ef L) z := (hasDerivAt_ef L z).differentiableAt
    exact hA.add (he.div hA (exp_ne_zero _))
  -- the transfer deviations on `Γ_N`
  have hdev : ∀ z ∈ Gam (-(cutN L θ N)) (cutN L θ N) h,
      ‖sNf L (κ / N) (qAct L κ N m) z - sf L κ (Gfull μ) z‖ ≤ Kd' * δN ∧
      ‖deriv (sNf L (κ / N) (qAct L κ N m)) z - deriv (sf L κ (Gfull μ)) z‖ ≤ Kd' * δN / (ρ / 2) := by
    intro z hz
    have hP := hevN m hm z (hzN z hz)
    have hder := hP.2.2.2.2.2.2.2.2.2
    rw [sNsrc_eq, sLimsrc_eq] at hder
    have hroot : ∀ j, 2 * |κ / (N : ℝ)| < ‖z - (qAct L κ N m j : ℂ)‖ := hP.1.1
    have hd1 : DifferentiableAt ℂ (sNf L (κ / N) (qAct L κ N m)) z := (hasDerivAt_sN L hroot).differentiableAt
    have hKK : Kd * δN ≤ Kd' * δN := mul_le_mul_of_nonneg_right (le_max_left _ _) hδN0
    constructor
    · have h0 := hder 0
      simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, pow_zero, div_one, one_mul] at h0
      exact h0.trans hKK
    · have h1 := hder 1
      rw [iteratedDeriv_one, deriv_fun_sub hd1 (hsfd z (hzN z hz))] at h1
      simp only [Nat.factorial_one, Nat.cast_one, pow_one, one_mul] at h1
      exact h1.trans (div_le_div_of_nonneg_right hKK (by positivity))
  -- the background derivative is bounded (Cauchy estimate on a ball of radius `ρ/16`)
  have hsbd : ∀ w ∈ NbhdN (cutN L θ N) h (ρ / 8), ‖sf L κ (Gfull μ) w‖ ≤ M + M * M := fun w hw => by
    have hP := hevN m hm w hw
    exact norm_sf_le hP.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.2.1
  have hvbd : ∀ z ∈ Gam (-(cutN L θ N)) (cutN L θ N) h, ‖deriv (sf L κ (Gfull μ)) z‖ ≤ Vs := by
    intro z hz
    have hρ16 : 0 < ρ / 16 := by positivity
    have hcl : ∀ w ∈ Metric.closedBall z (ρ / 16), w ∈ NbhdN (cutN L θ N) h (ρ / 8) := fun w hw =>
      gam_sub_nbhd hz (by rw [Metric.mem_closedBall, dist_eq_norm] at hw; linarith)
    have hdc : DiffContOnCl ℂ (sf L κ (Gfull μ)) (Metric.ball z (ρ / 16)) := by
      refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball z hρ16.ne']
      exact fun w hw => (hsfd w (hcl w hw)).differentiableWithinAt
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ16 hdc
      (fun w hw => hsbd w (hcl w (Metric.sphere_subset_closedBall hw)))
  -- the pointwise identifications on `Γ_N`
  have hqz : ∀ z ∈ Gam (-(cutN L θ N)) (cutN L θ N) h,
      qt z (sNf L (κ / N) (qAct L κ N m) z) (deriv (sNf L (κ / N) (qAct L κ N m)) z) =
        corrf L κ (κ / N) (Gfull μ) (qAct L κ N m) z ∧
      corrf L κ (κ / N) (Gfull μ) (qAct L κ N m) z =
        qch L κ (Gfull μ) z (sNf L (κ / N) (qAct L κ N m) z) (deriv (sNf L (κ / N) (qAct L κ N m)) z) := by
    intro z hz
    have hP := hevN m hm z (hzN z hz)
    have hGc : ∀ᶠ w in 𝓝 z, Df L κ (Gfull μ) w ≠ 0 := by
      filter_upwards [Metric.ball_mem_nhds z hρ8] with w hw
      have := (hevN m hm w (hball z hz hw)).2.2.2.2.2.1
      intro h0; rw [h0, norm_zero] at this; linarith
    have hW : 1 + Wf L κ (κ / N) (Gfull μ) (qAct L κ N m) z ∈ slitPlane := by
      refine Or.inl ?_
      have h1 := Complex.abs_re_le_norm (Wf L κ (κ / N) (Gfull μ) (qAct L κ N m) z)
      have h2 := hP.1.2.1
      simp only [add_re, one_re]
      linarith [neg_abs_le (Wf L κ (κ / N) (Gfull μ) (qAct L κ N m) z).re]
    have hM0' : 0 < 1 / (2 * M) := by positivity
    have ha0 : aNf L κ (κ / N) (Gfull μ) (qAct L κ N m) z ≠ 0 := fun h0 => by
      have := hP.1.2.2.1; rw [h0, norm_zero] at this; linarith
    have hDN0 : DNf L κ (κ / N) (Gfull μ) (qAct L κ N m) z ≠ 0 := fun h0 => by
      have := hP.1.2.2.2.1; rw [h0, norm_zero] at this; linarith
    have hcq := corrf_eq_qch hP.2.2.2.2.1 hGc hP.1.1 hW ha0 hDN0
    refine ⟨?_, hcq⟩
    rw [hqt z _ _ (lt_of_le_of_lt (hdev z hz).1 hsmN.1.1) (lt_of_le_of_lt (hdev z hz).2 hsmN.1.2)]
    exact hcq.symm
  have hcs : ∀ z ∈ Gam (-(cutN L θ N)) (cutN L θ N) h,
      ef L z * deriv (Af κ (Gfull μ)) z / (Af κ (Gfull μ) z * (Af κ (Gfull μ) z ^ 2 - ef L z)) =
        qch L κ (Gfull μ) z (sf L κ (Gfull μ) z) (deriv (sf L κ (Gfull μ)) z) := by
    intro z hz
    have hP := hevN m hm z (hzN z hz)
    have hD0 : Df L κ (Gfull μ) z ≠ 0 := fun h0 => by
      have := hP.2.2.2.2.2.1; rw [h0, norm_zero] at this; linarith
    exact (qch_bg hP.2.2.2.2.1 hD0).symm
  -- continuity of the two integrands on `Γ_N`
  have hPc : Continuous (poly p d) := continuous_poly p d
  have hc1 : ∀ z ∈ Gam (-(cutN L θ N)) (cutN L θ N) h,
      ContinuousAt (fun z => poly p d z * corrf L κ (κ / N) (Gfull μ) (qAct L κ N m) z) z := by
    intro z hz
    have hP := hevN m hm z (hzN z hz)
    have hGnear : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (Gfull μ) w := by
      filter_upwards [Metric.ball_mem_nhds z hρ8] with w hw
      exact (hevN m hm w (hball z hz hw)).2.2.2.2.1
    have hDz : Df L κ (Gfull μ) z ≠ 0 := fun h0 => by
      have := hP.2.2.2.2.2.1; rw [h0, norm_zero] at this; linarith
    have hc := contAt_gen hM0 hη hGnear hP.1.1 hDz hP.1.2.1 hP.1.2.2.1 hP.1.2.2.2.1
      hP.1.2.2.2.2.1 hP.2.2.2.2.2.2.2.1
    exact hPc.continuousAt.mul hc.2.1
  have hc0 : ∀ z ∈ Gam (-(cutN L θ N)) (cutN L θ N) h,
      ContinuousAt (fun z => poly p d z * (ef L z * deriv (Af κ (Gfull μ)) z /
        (Af κ (Gfull μ) z * (Af κ (Gfull μ) z ^ 2 - ef L z)))) z := by
    intro z hz
    have hP := hevN m hm z (hzN z hz)
    have hAd : DifferentiableOn ℂ (Af κ (Gfull μ)) (Metric.ball z (ρ / 8)) := fun w hw =>
      (((hevN m hm w (hball z hz hw)).2.2.2.2.1).const_mul (I * κ)).cexp.differentiableWithinAt
    have hA'c : ContinuousAt (deriv (Af κ (Gfull μ))) z :=
      ((hAd.deriv Metric.isOpen_ball).continuousOn).continuousAt (Metric.ball_mem_nhds z hρ8)
    have hAc : ContinuousAt (Af κ (Gfull μ)) z :=
      (hAd.differentiableAt (Metric.ball_mem_nhds z hρ8)).continuousAt
    have hec : ContinuousAt (ef L) z := (hasDerivAt_ef L z).continuousAt
    have hA0 : Af κ (Gfull μ) z ≠ 0 := exp_ne_zero _
    have hD0 : Df L κ (Gfull μ) z ≠ 0 := fun h0 => by
      have := hP.2.2.2.2.2.1; rw [h0, norm_zero] at this; linarith
    have hA2 : Af κ (Gfull μ) z ^ 2 - ef L z ≠ 0 := by
      intro h0; apply hD0; unfold Df; field_simp; linear_combination h0
    exact hPc.continuousAt.mul ((hec.mul hA'c).div (hAc.mul ((hAc.pow 2).sub hec)) (mul_ne_zero hA0 hA2))
  -- assemble
  have hab : -(cutN L θ N) ≤ cutN L θ N := by linarith
  have hC1 : C1ev L κ qt θ h p d N m = ((I / (2 * Real.pi)) *
      rectIntegral (fun z => poly p d z * corrf L κ (κ / N) (Gfull μ) (qAct L κ N m) z)
        (-(cutN L θ N)) (cutN L θ N) h).re := by
    unfold C1ev
    rw [QuantumNLS.HaarNonlinearAbstract.rect_congr_Gam hab hh.le fun z hz => by rw [(hqz z hz).1]]
  have hdiff : rectIntegral (fun z => poly p d z * corrf L κ (κ / N) (Gfull μ) (qAct L κ N m) z)
        (-(cutN L θ N)) (cutN L θ N) h -
      rectIntegral (fun z => poly p d z * (ef L z * deriv (Af κ (Gfull μ)) z /
        (Af κ (Gfull μ) z * (Af κ (Gfull μ) z ^ 2 - ef L z)))) (-(cutN L θ N)) (cutN L θ N) h =
      rectIntegral (fun z => poly p d z * corrf L κ (κ / N) (Gfull μ) (qAct L κ N m) z +
        (-1 : ℂ) * (poly p d z * (ef L z * deriv (Af κ (Gfull μ)) z /
          (Af κ (Gfull μ) z * (Af κ (Gfull μ) z ^ 2 - ef L z))))) (-(cutN L θ N)) (cutN L θ N) h := by
    rw [rectIntegral_add (f := fun z => poly p d z * corrf L κ (κ / N) (Gfull μ) (qAct L κ N m) z)
      (g := fun z => (-1 : ℂ) * (poly p d z * (ef L z * deriv (Af κ (Gfull μ)) z /
          (Af κ (Gfull μ) z * (Af κ (Gfull μ) z ^ 2 - ef L z))))) hab hh.le hc1
      (fun z hz => continuousAt_const.mul (hc0 z hz)), rectIntegral_const_mul]
    ring
  set S : ℝ := ∑ r ∈ Finset.range (d + 1), |p r| with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun r _ => abs_nonneg _
  set B : ℝ := (1 + cutN L θ N) * (1 + h) with hBdef
  have hB1 : 1 ≤ B := by rw [hBdef]; nlinarith
  have hbound : ‖rectIntegral (fun z => poly p d z * corrf L κ (κ / N) (Gfull μ) (qAct L κ N m) z +
        (-1 : ℂ) * (poly p d z * (ef L z * deriv (Af κ (Gfull μ)) z /
          (Af κ (Gfull μ) z * (Af κ (Gfull μ) z ^ 2 - ef L z))))) (-(cutN L θ N)) (cutN L θ N) h‖ ≤
      (2 * (cutN L θ N - -(cutN L θ N)) + 4 * h) * (S * B ^ d * (Lq * δN)) := by
    refine norm_rectIntegral_le hab hh.le fun z hz => ?_
    have hP := hevN m hm z (hzN z hz)
    have e : poly p d z * corrf L κ (κ / N) (Gfull μ) (qAct L κ N m) z +
        (-1 : ℂ) * (poly p d z * (ef L z * deriv (Af κ (Gfull μ)) z /
          (Af κ (Gfull μ) z * (Af κ (Gfull μ) z ^ 2 - ef L z)))) =
        poly p d z * (qch L κ (Gfull μ) z (sNf L (κ / N) (qAct L κ N m) z)
            (deriv (sNf L (κ / N) (qAct L κ N m)) z) -
          qch L κ (Gfull μ) z (sf L κ (Gfull μ) z) (deriv (sf L κ (Gfull μ)) z)) := by
      rw [(hqz z hz).2, hcs z hz]; ring
    rw [e, norm_mul]
    have hz1 : ‖z‖ ≤ B := (norm_le_of_gam (by linarith) hh.le hz).trans (by rw [hBdef]; nlinarith)
    have hq := qch_diff_le hM1 hη hP.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.2.1
      hP.2.2.2.2.2.1 hP.1.2.2.1 hP.1.2.2.2.1 (hvbd z hz) (hdev z hz).1 (hdev z hz).2 hsmN.2.1.le hsmN.2.2.le
    rw [Lbd_scale] at hq
    exact mul_le_mul (norm_poly_le p d hB1 hz1) hq (norm_nonneg _) (mul_nonneg hS0 (pow_nonneg (by linarith) d))
  have hlen : 2 * (cutN L θ N - -(cutN L θ N)) + 4 * h ≤ 4 * B := by rw [hBdef]; nlinarith
  rw [hC1]
  unfold cscal
  rw [← sub_re, ← mul_sub, hdiff]
  calc |((I / (2 * Real.pi)) * rectIntegral (fun z => poly p d z * corrf L κ (κ / N) (Gfull μ) (qAct L κ N m) z +
        (-1 : ℂ) * (poly p d z * (ef L z * deriv (Af κ (Gfull μ)) z /
          (Af κ (Gfull μ) z * (Af κ (Gfull μ) z ^ 2 - ef L z))))) (-(cutN L θ N)) (cutN L θ N) h).re|
      ≤ ‖(I / (2 * Real.pi)) * rectIntegral (fun z => poly p d z * corrf L κ (κ / N) (Gfull μ) (qAct L κ N m) z +
        (-1 : ℂ) * (poly p d z * (ef L z * deriv (Af κ (Gfull μ)) z /
          (Af κ (Gfull μ) z * (Af κ (Gfull μ) z ^ 2 - ef L z))))) (-(cutN L θ N)) (cutN L θ N) h‖ :=
        Complex.abs_re_le_norm _
    _ ≤ 1 / (2 * Real.pi) * ((4 * B) * (S * B ^ d * (Lq * δN))) := by
        rw [norm_mul, norm_div, Complex.norm_I, norm_mul, Complex.norm_two, Complex.norm_real,
          Real.norm_of_nonneg hpi.le]
        refine mul_le_mul_of_nonneg_left (hbound.trans (mul_le_mul_of_nonneg_right hlen ?_)) (by positivity)
        exact mul_nonneg (mul_nonneg hS0 (pow_nonneg (by linarith) d)) (mul_nonneg hLq0 hδN0)
    _ = 4 * Lq * (1 + h) ^ (d + 1) / (2 * Real.pi) * S * (1 + cutN L θ N) ^ (d + 1) * δN := by
        rw [hBdef, mul_pow, pow_succ (1 + cutN L θ N) d, pow_succ (1 + h) d]
        field_simp

/-! ## 5. PROP-018 -/

/-- **PROP-018** (`Q7A:prop:reconstruct`), both estimates on one event. For the actual model in the diagonal regime
`R_N = N^θ`, `ε_N = N^{−γ}`, `a_N = cutN L θ N` (`RootSpectralInputs` as an explicit hypothesis) there is a packet radius `ρ`
with `P_{N,u}(𝓔_Nᶜ) → 0` and constants `Cp, Cs ≥ 0` such that for every chart radius `r₀ > 0` and all extensions `f`, `q̃`
agreeing with `λ`, `q` on the `r₀`-disks around the background, eventually in `N`, for every real polynomial `p` of degree
`≤ d` and every label `m ∈ 𝓔_N`:
* `eq:phase`: `|Σ_r p_r Q_{N,r}(m) − N C_{0,N,p}(m) − C_{1,N,p}(m)| ≤ Cp Σ_r|p_r| (1+a_N)^{d+1}/N`;
* `eq:scalarerror`: `|C_{1,N,p}(m) − c_{N,p}| ≤ Cs Σ_r|p_r| (1+a_N)^{d+1} (ε_N + R_N^{−b} + N^{−1})`.
Here `Q_{N,r}(m)`, `C_{0,N,p}(m)`, `C_{1,N,p}(m)` are the eigenvalues on the actual Bethe vector `Ψ_{N,m}` of the commuting
diagonal operators; the bound for every `m ∈ 𝓔_N` is the operator-norm bound on `ran P_N`. -/
theorem prop018_reconstruct (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {h δ d0 : ℝ} {l0 : ℕ} (hηh : eta0 L κ < h)
    (hδ : 0 < δ) (hd0 : 0 < d0) (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (b pc : ℕ) (hb : 1 ≤ b) (hbpc : b ≤ 2 * pc)
    (θ γ : ℝ) (hθ : 0 < θ) (hγ : 0 < γ) (hsum : 3 * γ + θ < 1) (pt : ℕ) (hpt : 1 < 2 * (pt : ℝ) * θ)
    (d : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧
      Tendsto (fun N : ℕ => (bornMeasure (physBasis L hκ N) u hu).real
        (EN (μ : Measure ℝ) (qAct L κ N) ((N : ℝ) ^ θ) (cutN L θ N) ρ h (eta0 L κ) ((N : ℝ) ^ (-γ)) b)ᶜ)
        atTop (𝓝 0) ∧
      ∃ Cp Cs : ℝ, 0 ≤ Cp ∧ 0 ≤ Cs ∧ ∀ r0 : ℝ, 0 < r0 → ∀ (f : ℂ → ℂ → ℂ) (qt : ℂ → ℂ → ℂ → ℂ),
        (∀ z w, ‖w - sf L κ (Gfull (μ : Measure ℝ)) z‖ < r0 → f z w = lam L κ (Gfull (μ : Measure ℝ)) z w) →
        (∀ z w v, ‖w - sf L κ (Gfull (μ : Measure ℝ)) z‖ < r0 →
          ‖v - deriv (sf L κ (Gfull (μ : Measure ℝ))) z‖ < r0 → qt z w v = qch L κ (Gfull (μ : Measure ℝ)) z w v) →
        ∀ᶠ N : ℕ in atTop, ∀ p : ℕ → ℝ, ∀ m ∈ EN (μ : Measure ℝ) (qAct L κ N) ((N : ℝ) ^ θ) (cutN L θ N) ρ h
          (eta0 L κ) ((N : ℝ) ^ (-γ)) b,
          |∑ r ∈ Finset.range (d + 1), p r * eigenvalue L N (κ / N) r m
            - (N : ℝ) * C0ev L κ f θ h p d N m - C1ev L κ qt θ h p d N m| ≤
            Cp * (∑ r ∈ Finset.range (d + 1), |p r|) * (1 + cutN L θ N) ^ (d + 1) / N ∧
          |C1ev L κ qt θ h p d N m - cscal L κ (μ : Measure ℝ) θ h p d N| ≤
            Cs * (∑ r ∈ Finset.range (d + 1), |p r|) * (1 + cutN L θ N) ^ (d + 1) *
              ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b + 1 / (N : ℝ)) := by
  obtain ⟨ρ, hρ0, h2ρ, hprob, C, M, η, r, K, Kd, hM1, hη, hr0, hK0, hev⟩ :=
    moving_contour_bundle hκ u hu hμ hηh hδ hd0 hin b pc hb hbpc θ γ hθ hγ hsum pt hpt
  have hh : 0 < h := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hM0 : 0 < M := by linarith
  have hVs0 : 0 ≤ (M + M * M) / (ρ / 16) := by positivity
  have hLq0 := Lbd_nonneg (L := L) hM1 hη hVs0 (le_max_right Kd 0) hρ0
  refine ⟨ρ, hρ0, hprob, κ ^ 2 + 4 * max C 0 * (1 + h) ^ (d + 1) / (2 * Real.pi * κ),
    4 * Lbd M η L ((M + M * M) / (ρ / 16)) (max Kd 0) (max Kd 0 / (ρ / 2)) * (1 + h) ^ (d + 1) / (2 * Real.pi),
    by positivity, by positivity, fun r0 hr0' f qt hf hqt => ?_⟩
  set E : (N : ℕ) → Set (MArr N) := fun N =>
    EN (μ : Measure ℝ) (qAct L κ N) ((N : ℝ) ^ θ) (cutN L θ N) ρ h (eta0 L κ) ((N : ℝ) ^ (-γ)) b with hE
  have h1 := phase_of_bundle hκ (μ : Measure ℝ) hh hρ0 hM1 hη hθ hγ hb E hev d r0 hr0' f qt hf hqt
  have h2 := scalar_of_bundle (μ : Measure ℝ) hh hρ0 hM1 hη hθ hγ hb E hev d r0 hr0' qt hqt
  filter_upwards [h1, h2] with N hN1 hN2
  exact fun p m hm => ⟨hN1 p m hm, hN2 p m hm⟩

end QuantumNLS.Prop018Scalar

#print axioms QuantumNLS.Prop018Scalar.lip_q
#print axioms QuantumNLS.Prop018Scalar.qch_bg
#print axioms QuantumNLS.Prop018Scalar.norm_DN_sub_D
#print axioms QuantumNLS.Prop018Scalar.qch_diff_le
#print axioms QuantumNLS.Prop018Scalar.scalar_of_bundle
#print axioms QuantumNLS.Prop018Scalar.prop018_reconstruct
