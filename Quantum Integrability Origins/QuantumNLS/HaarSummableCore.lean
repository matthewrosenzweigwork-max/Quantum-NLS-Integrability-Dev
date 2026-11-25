import QuantumNLS.PeriodTwoTerm

/-!
# R-9A71E77E `QG:prop:haar-summable-reconstruction` (QUANTUM_GAUGE_COMPONENTS.tex:486-600): core

The moment form of the BO1 remainder estimate (PROP-006, `PeriodReconstructionBigO`), along an
arbitrary filter `l` on an arbitrary index type `ι`, with the constants tracked through a second
small parameter `θ` (in the application `θ = 1/|n|`):

* moment-form pointwise lemmas `ell_lin_m`, `ell_pair_m`, `sumsq_m`, `dell_m`, `Icdell_m`,
  `dell_pair_m` (the per-root bounds of RA1 summed against `Σ_j ‖z − q_j‖^{-s}` instead of
  `N d^{-s}`);
* **`haar_core`**: if the root distance is bounded below, `N⁻¹ Σ_j ‖z − q_j‖^{-s} ≤ K θ²`
  (`s = 2, 3`), `θ → 0`, `N → ∞`, and the background bounds of BO1 hold eventually, then
  `rem = ℓ_N − log a_N + (iκ/N) e^{izL} a_N'/(a_N(a_N² − e^{izL})) = O(N^{-2} θ²)`, the correction
  integrand `e^{izL} a_N'/(a_N(a_N² − e^{izL}))` is `O(θ²)`, and the eventual pointwise bounds
  (root distance, `‖W‖ ≤ 1/2`, `‖a_N‖ ≥ 1/(2M)`, `‖D_N‖ ≥ 3η/4`, `‖a_N − A‖ ≤ 1/(2M)`) hold.

The proof is the BO1 proof with every `O(ν)` rate replaced by `O(ρ)`, `ρ = ν θ²`, and every
`O(ν²)` rate by `O(νρ)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000
noncomputable section

open Complex Filter Topology Asymptotics

namespace QuantumNLS.HaarSummableCore

open QuantumNLS.PeriodReconstructionCore QuantumNLS.PeriodReconstructionAsymp
  QuantumNLS.PeriodReconstructionBigO QuantumNLS.PeriodTwoTerm

/-- The remainder of eq:B3-log-reconstruction along an arbitrary index. -/
def remG {ι : Type*} (κ L : ℝ) (Nf : ι → ℕ) (qf : ∀ i, Fin (Nf i) → ℝ) (zf : ι → ℂ)
    (G : ℂ → ℂ) (p : ι) : ℂ :=
  ellf (κ / Nf p) (qf p) (zf p) - logaNf L κ (κ / Nf p) G (qf p) (zf p) +
    I * κ / (Nf p : ℂ) * (ef L (zf p) * deriv (aNf L κ (κ / Nf p) G (qf p)) (zf p) /
      (aNf L κ (κ / Nf p) G (qf p) (zf p) *
        (aNf L κ (κ / Nf p) G (qf p) (zf p) ^ 2 - ef L (zf p))))

/-! ## 1. Moment-form pointwise bounds -/

section Pointwise

variable {N : ℕ}

lemma norm_u_eq {c q : ℝ} {z : ℂ} : ‖I * c / (z - q)‖ = |c| / ‖z - q‖ := by
  rw [norm_div, norm_Ic]

lemma u_half {c q : ℝ} {z : ℂ} (h : 2 * |c| ≤ ‖z - q‖) : ‖I * c / (z - q)‖ ≤ 1 / 2 := by
  rw [norm_u_eq]
  rcases (norm_nonneg (z - q)).eq_or_lt with h0 | h0
  · rw [← h0, div_zero]; norm_num
  · rw [div_le_iff₀ h0]; linarith

lemma ell_lin_m {c : ℝ} {q : Fin N → ℝ} {z : ℂ} (hz : ∀ j, 2 * |c| ≤ ‖z - q j‖) :
    ‖ellf c q z - ∑ j, I * c / (z - q j)‖ ≤ c ^ 2 * ∑ j, (‖z - q j‖ ^ 2)⁻¹ := by
  unfold ellf
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  refine (log_lin (u_half (hz j))).trans (le_of_eq ?_)
  rw [norm_u_eq, div_pow, ← sq_abs c, div_eq_mul_inv]

lemma ell_pair_m {c : ℝ} {q : Fin N → ℝ} {z : ℂ} (hz : ∀ j, 2 * |c| ≤ ‖z - q j‖) :
    ‖ellf c q z + ellf (-c) q z - ∑ j, ((c : ℂ) ^ 2 / (z - q j) ^ 2)‖ ≤
      2 * |c| ^ 3 * ∑ j, (‖z - q j‖ ^ 3)⁻¹ := by
  unfold ellf
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  set u := I * c / (z - q j)
  have hu' : I * ((-c : ℝ) : ℂ) / (z - q j) = -u := by simp only [u]; push_cast; ring
  have hu2 : (c : ℂ) ^ 2 / (z - q j) ^ 2 = -u ^ 2 := by
    simp only [u]; rw [div_pow, mul_pow, I_sq]; ring
  rw [hu', hu2]
  have hh := u_half (hz j)
  have h1 := log_quad hh
  have h2 := log_quad (u := -u) (by rw [norm_neg]; exact hh)
  rw [norm_neg] at h2
  have e : log (1 + u) + log (1 + -u) - -u ^ 2 =
      (log (1 + u) - (u - u ^ 2 / 2)) + (log (1 + -u) - (-u - (-u) ^ 2 / 2)) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h3 : ‖u‖ ^ 3 = |c| ^ 3 * (‖z - q j‖ ^ 3)⁻¹ := by
    simp only [u]; rw [norm_u_eq, div_pow, div_eq_mul_inv]
  linarith

lemma shift_ge {c q : ℝ} {z : ℂ} (h : 2 * |c| ≤ ‖z - q‖) : ‖z - q‖ / 2 ≤ ‖z - q + I * c‖ := by
  have h4 := norm_sub_norm_le (z - q) (-(I * c))
  rw [sub_neg_eq_add, norm_neg, norm_Ic] at h4
  linarith

lemma shift_ge' {c q : ℝ} {z : ℂ} (h : 2 * |c| ≤ ‖z - q‖) : ‖z - q‖ / 2 ≤ ‖z - q - I * c‖ := by
  have h4 := norm_sub_norm_le (z - q) (I * c)
  rw [norm_Ic] at h4
  linarith

lemma sumsq_m {c : ℝ} {q : Fin N → ℝ} {z : ℂ} :
    ‖∑ j, ((c : ℂ) ^ 2 / (z - q j) ^ 2)‖ ≤ c ^ 2 * ∑ j, (‖z - q j‖ ^ 2)⁻¹ := by
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => le_of_eq ?_)
  rw [norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_eq_mul_inv]

lemma dell_m {c : ℝ} {q : Fin N → ℝ} {z : ℂ} (hz : ∀ j, 2 * |c| ≤ ‖z - q j‖)
    (hpos : ∀ j, 0 < ‖z - q j‖) :
    ‖dellf c q z‖ ≤ 2 * |c| * ∑ j, (‖z - q j‖ ^ 2)⁻¹ := by
  unfold dellf
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have hw := hpos j
  have ha := shift_ge (hz j)
  have ha0 : 0 < ‖z - q j + I * c‖ := lt_of_lt_of_le (by positivity) ha
  simp only [norm_div, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs]
  rw [div_le_iff₀ (mul_pos hw ha0)]
  have : ‖z - q j‖ * (‖z - q j‖ / 2) ≤ ‖z - q j‖ * ‖z - q j + I * c‖ :=
    mul_le_mul_of_nonneg_left ha hw.le
  have e : 2 * |c| * (‖z - q j‖ ^ 2)⁻¹ * (‖z - q j‖ * (‖z - q j‖ / 2)) = |c| := by
    field_simp
  nlinarith [abs_nonneg c, inv_nonneg.2 (sq_nonneg ‖z - q j‖)]

lemma Icdell_m {c : ℝ} {q : Fin N → ℝ} {z : ℂ} (hz : ∀ j, 2 * |c| ≤ ‖z - q j‖)
    (hpos : ∀ j, 0 < ‖z - q j‖) :
    ‖I * c * dellf c q z - ∑ j, ((c : ℂ) ^ 2 / (z - q j) ^ 2)‖ ≤
      2 * |c| ^ 3 * ∑ j, (‖z - q j‖ ^ 3)⁻¹ := by
  unfold dellf
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have hw0' := hpos j
  have ha := shift_ge (hz j)
  have ha0' : 0 < ‖z - q j + I * c‖ := lt_of_lt_of_le (by positivity) ha
  have hw0 : z - q j ≠ 0 := norm_pos_iff.1 hw0'
  have ha0 : z - q j + I * c ≠ 0 := norm_pos_iff.1 ha0'
  have e : I * c * (-(I * c) / ((z - q j) * (z - q j + I * c))) - (c : ℂ) ^ 2 / (z - q j) ^ 2
      = -(I * c) * (c : ℂ) ^ 2 / ((z - q j) ^ 2 * (z - q j + I * c)) := by
    field_simp; ring_nf; rw [I_sq]; ring
  rw [e]
  simp only [norm_div, norm_mul, norm_neg, norm_pow, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs]
  rw [div_le_iff₀ (by positivity)]
  have h1 : ‖z - q j‖ ^ 2 * (‖z - q j‖ / 2) ≤ ‖z - q j‖ ^ 2 * ‖z - q j + I * c‖ :=
    mul_le_mul_of_nonneg_left ha (by positivity)
  have e2 : 2 * |c| ^ 3 * (‖z - q j‖ ^ 3)⁻¹ * (‖z - q j‖ ^ 2 * (‖z - q j‖ / 2)) = |c| ^ 3 := by
    field_simp
  have e3 : |c| * |c| ^ 2 = |c| ^ 3 := by ring
  rw [e3]
  nlinarith [pow_nonneg (abs_nonneg c) 3, inv_nonneg.2 (pow_nonneg hw0'.le 3)]

lemma dell_pair_m {c : ℝ} {q : Fin N → ℝ} {z : ℂ} (hz : ∀ j, 2 * |c| ≤ ‖z - q j‖)
    (hpos : ∀ j, 0 < ‖z - q j‖) :
    ‖dellf c q z + dellf (-c) q z‖ ≤ 8 * |c| ^ 2 * ∑ j, (‖z - q j‖ ^ 3)⁻¹ := by
  unfold dellf
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have hw0' := hpos j
  have ha := shift_ge (hz j)
  have hb := shift_ge' (hz j)
  have ha0' : 0 < ‖z - q j + I * c‖ := lt_of_lt_of_le (by positivity) ha
  have hb0' : 0 < ‖z - q j - I * c‖ := lt_of_lt_of_le (by positivity) hb
  have hw0 := norm_pos_iff.1 hw0'
  have ha0 := norm_pos_iff.1 ha0'
  have hb0 := norm_pos_iff.1 hb0'
  have e : -(I * c) / ((z - q j) * (z - q j + I * c)) +
      -(I * ((-c : ℝ) : ℂ)) / ((z - q j) * (z - q j + I * ((-c : ℝ) : ℂ))) =
      -2 * (c : ℂ) ^ 2 / ((z - q j) * (z - q j + I * c) * (z - q j - I * c)) := by
    have e1 : z - q j + I * ((-c : ℝ) : ℂ) = z - q j - I * c := by push_cast; ring
    have e2 : -(I * ((-c : ℝ) : ℂ)) = I * c := by push_cast; ring
    rw [e1, e2, div_add_div _ _ (mul_ne_zero hw0 ha0) (mul_ne_zero hw0 hb0), div_eq_div_iff
      (mul_ne_zero (mul_ne_zero hw0 ha0) (mul_ne_zero hw0 hb0))
      (mul_ne_zero (mul_ne_zero hw0 ha0) hb0)]
    ring_nf
    simp only [Complex.I_pow_four, I_sq]
    ring
  rw [e]
  simp only [norm_div, norm_mul, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_ofNat]
  rw [div_le_iff₀ (by positivity)]
  have h1 : ‖z - q j‖ * (‖z - q j‖ / 2) * (‖z - q j‖ / 2) ≤
      ‖z - q j‖ * ‖z - q j + I * c‖ * ‖z - q j - I * c‖ :=
    mul_le_mul (mul_le_mul_of_nonneg_left ha hw0'.le) hb (by positivity) (by positivity)
  have e2 : 8 * |c| ^ 2 * (‖z - q j‖ ^ 3)⁻¹ * (‖z - q j‖ * (‖z - q j‖ / 2) * (‖z - q j‖ / 2)) =
      2 * |c| ^ 2 := by field_simp; ring
  have := mul_le_mul_of_nonneg_left h1
    (show 0 ≤ 8 * |c| ^ 2 * (‖z - q j‖ ^ 3)⁻¹ by positivity)
  linarith [e2]

end Pointwise

/-! ## 2. The moment form of the remainder estimate -/

theorem haar_core {ι : Type*} {l : Filter ι} {κ L : ℝ} {Nf : ι → ℕ}
    {qf : ∀ i, Fin (Nf i) → ℝ} {zf : ι → ℂ} {θ : ι → ℝ} {G : ℂ → ℂ}
    (hκ : 0 < κ) (hN : ∀ i, 0 < Nf i) (hνt : Tendsto (fun i => ((Nf i : ℝ))⁻¹) l (𝓝 0))
    (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Tendsto θ l (𝓝 0))
    {d : ℝ} (hd : 0 < d) (hroot : ∀ᶠ i in l, ∀ j, d ≤ ‖zf i - (qf i j : ℂ)‖)
    {K : ℝ} (hK : 0 ≤ K)
    (hm2 : ∀ᶠ i in l, ((Nf i : ℝ))⁻¹ * ∑ j, (‖zf i - (qf i j : ℂ)‖ ^ 2)⁻¹ ≤ K * θ i ^ 2)
    (hm3 : ∀ᶠ i in l, ((Nf i : ℝ))⁻¹ * ∑ j, (‖zf i - (qf i j : ℂ)‖ ^ 3)⁻¹ ≤ K * θ i ^ 2)
    (hU : Tendsto (fun i => (∑ j, I * ((κ / Nf i : ℝ) : ℂ) / (zf i - (qf i j : ℂ))) -
      I * κ * G (zf i)) l (𝓝 0))
    (hGd : ∀ᶠ i in l, DifferentiableAt ℂ G (zf i))
    (hDev : ∀ᶠ i in l, ∀ᶠ w in 𝓝 (zf i), Df L κ G w ≠ 0)
    {M η : ℝ} (hM0 : 1 ≤ M) (hη : 0 < η)
    (hM : ∀ᶠ i in l, ‖Af κ G (zf i)‖ ≤ M ∧ ‖(Af κ G (zf i))⁻¹‖ ≤ M ∧ ‖ef L (zf i)‖ ≤ M ∧
      η ≤ ‖Df L κ G (zf i)‖) :
    remG κ L Nf qf zf G =O[l] (fun i => ((Nf i : ℝ))⁻¹ * (((Nf i : ℝ))⁻¹ * θ i ^ 2)) ∧
    (fun i => corrf L κ (κ / Nf i) G (qf i) (zf i)) =O[l] (fun i => θ i ^ 2) ∧
    (∀ᶠ i in l, (∀ j, 2 * |κ / (Nf i : ℝ)| < ‖zf i - (qf i j : ℂ)‖) ∧
      ‖Wf L κ (κ / Nf i) G (qf i) (zf i)‖ ≤ 1 / 2 ∧
      1 / (2 * M) ≤ ‖aNf L κ (κ / Nf i) G (qf i) (zf i)‖ ∧
      3 * η / 4 ≤ ‖DNf L κ (κ / Nf i) G (qf i) (zf i)‖ ∧
      ‖aNf L κ (κ / Nf i) G (qf i) (zf i) - Af κ G (zf i)‖ ≤ 1 / (2 * M)) := by
  set ν : ι → ℝ := fun p => (Nf p : ℝ)⁻¹ with hνdef
  have hν0 : ∀ p, 0 < ν p := fun p => inv_pos.2 (Nat.cast_pos.2 (hN p))
  have hνsq0 : ∀ p, 0 ≤ ν p ^ 2 := fun p => sq_nonneg _
  have habsc : ∀ p : ι, |κ / (Nf p : ℝ)| = κ * ν p := fun p => by
    rw [abs_of_pos (div_pos hκ (Nat.cast_pos.2 (hN p))), div_eq_mul_inv]
  have hNν : ∀ p : ι, (Nf p : ℝ) * ν p = 1 := fun p =>
    mul_inv_cancel₀ (Nat.cast_pos.2 (hN p)).ne'
  have hν : Tendsto ν l (𝓝 0) := hνt
  set ρ : ι → ℝ := fun p => ν p * θ p ^ 2 with hρdef
  have hρ0 : ∀ p, 0 ≤ ρ p := fun p => mul_nonneg (hν0 p).le (sq_nonneg _)
  have hνρ0 : ∀ p, 0 ≤ ν p * ρ p := fun p => mul_nonneg (hν0 p).le (hρ0 p)
  have hρ : Tendsto ρ l (𝓝 0) := by
    have := hν.mul (hθ.pow 2)
    simpa using this
  have hθle : ∀ᶠ p in l, θ p ≤ 1 := hθ.eventually (ge_mem_nhds one_pos)
  have hroot' := hroot
  have hsmall : ∀ᶠ p in l, 4 * |κ / (Nf p : ℝ)| ≤ d := by
    have := hν.eventually (ge_mem_nhds (show (0 : ℝ) < d / (4 * κ) by positivity))
    filter_upwards [this] with p hp
    rw [habsc]; rw [le_div_iff₀ (by positivity)] at hp; linarith
  have hc2 : ∀ᶠ p in l, 2 * |κ / (Nf p : ℝ)| ≤ d :=
    hsmall.mono fun p hp => by linarith [abs_nonneg (κ / (Nf p : ℝ))]
  have hc2' : ∀ᶠ p in l, 2 * |-(κ / (Nf p : ℝ))| ≤ d :=
    hc2.mono fun p hp => by rwa [abs_neg]
  have hdist : ∀ᶠ p in l, ∀ j, 2 * |κ / (Nf p : ℝ)| < ‖zf p - (qf p j : ℂ)‖ := by
    filter_upwards [hroot', hsmall] with p h1 h2 j
    have := h1 j; linarith [abs_nonneg (κ / (Nf p : ℝ))]
  have hdist' : ∀ᶠ p in l, ∀ j, 2 * |-(κ / (Nf p : ℝ))| < ‖zf p - (qf p j : ℂ)‖ :=
    hdist.mono fun p h j => by rw [abs_neg]; exact h j
  have hνle : ∀ᶠ p in l, ν p ≤ 1 := hν.eventually (ge_mem_nhds one_pos)
  -- background bounds
  have hbg := hM
  -- the main functions
  set AN : ι → ℂ := fun p => ANf (κ / Nf p) (qf p) (zf p) with hAN
  set BN : ι → ℂ := fun p => ANf (-(κ / Nf p)) (qf p) (zf p) with hBN
  set ℓ : ι → ℂ := fun p => ellf (κ / Nf p) (qf p) (zf p) with hℓ
  set ℓB : ι → ℂ := fun p => ellf (-(κ / Nf p)) (qf p) (zf p) with hℓB
  set dl : ι → ℂ := fun p => dellf (κ / Nf p) (qf p) (zf p) with hdl
  set dlB : ι → ℂ := fun p => dellf (-(κ / Nf p)) (qf p) (zf p) with hdlB
  set e : ι → ℂ := fun p => ef L (zf p) with he
  set A : ι → ℂ := fun p => Af κ G (zf p) with hA
  set Dd : ι → ℂ := fun p => Df L κ G (zf p) with hDd
  set s : ι → ℂ := fun p => sf L κ G (zf p) with hs
  set sN : ι → ℂ := fun p => sNf L (κ / Nf p) (qf p) (zf p) with hsN
  set W : ι → ℂ := fun p => Wf L κ (κ / Nf p) G (qf p) (zf p) with hW
  set DN : ι → ℂ := fun p => DNf L κ (κ / Nf p) G (qf p) (zf p) with hDN
  set a : ι → ℂ := fun p => aNf L κ (κ / Nf p) G (qf p) (zf p) with ha
  set a' : ι → ℂ := fun p => deriv (aNf L κ (κ / Nf p) G (qf p)) (zf p) with ha'
  set Sc : ι → ℂ := fun p => ∑ j, I * ((κ / Nf p : ℝ) : ℂ) / (zf p - (qf p j : ℂ)) with hSc
  -- S1: leading log
  have hc2r : ∀ᶠ p in l, ∀ j, 2 * |κ / (Nf p : ℝ)| ≤ ‖zf p - (qf p j : ℂ)‖ :=
    hdist.mono fun p h j => (h j).le
  have hc2r' : ∀ᶠ p in l, ∀ j, 2 * |-(κ / (Nf p : ℝ))| ≤ ‖zf p - (qf p j : ℂ)‖ :=
    hdist'.mono fun p h j => (h j).le
  have hposw : ∀ᶠ p in l, ∀ j, 0 < ‖zf p - (qf p j : ℂ)‖ :=
    hdist.mono fun p h j => lt_of_le_of_lt (by positivity) (h j)
  have hS1 : (fun p => ℓ p - Sc p) =O[l] ρ := by
    refine bigO_of_le (κ ^ 2 * K) hρ0 ?_
    filter_upwards [hc2r, hm2] with p h2 hm
    have := ell_lin_m h2
    calc ‖ℓ p - Sc p‖ ≤ (κ / (Nf p : ℝ)) ^ 2 * ∑ j, (‖zf p - (qf p j : ℂ)‖ ^ 2)⁻¹ := this
      _ = κ ^ 2 * ν p * (((Nf p : ℝ))⁻¹ * ∑ j, (‖zf p - (qf p j : ℂ)‖ ^ 2)⁻¹) := by
          simp only [hνdef]; ring
      _ ≤ κ ^ 2 * ν p * (K * θ p ^ 2) := by gcongr
      _ = κ ^ 2 * K * ρ p := by simp only [hρdef]; ring
  have hS1B : (fun p => ℓB p + Sc p) =O[l] ρ := by
    refine bigO_of_le (κ ^ 2 * K) hρ0 ?_
    filter_upwards [hc2r', hm2] with p h2 hm
    have := ell_lin_m h2
    have e1 : ∑ j, I * (((-(κ / Nf p)) : ℝ) : ℂ) / (zf p - (qf p j : ℂ)) = -Sc p := by
      simp only [hSc]; rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_; push_cast; ring
    rw [e1, sub_neg_eq_add, neg_sq] at this
    calc ‖ℓB p + Sc p‖ ≤ (κ / (Nf p : ℝ)) ^ 2 * ∑ j, (‖zf p - (qf p j : ℂ)‖ ^ 2)⁻¹ := this
      _ = κ ^ 2 * ν p * (((Nf p : ℝ))⁻¹ * ∑ j, (‖zf p - (qf p j : ℂ)‖ ^ 2)⁻¹) := by
          simp only [hνdef]; ring
      _ ≤ κ ^ 2 * ν p * (K * θ p ^ 2) := by gcongr
      _ = κ ^ 2 * K * ρ p := by simp only [hρdef]; ring
  have hT1 : Tendsto (fun p => ℓ p - I * κ * G (zf p)) l (𝓝 0) := by
    have := (hS1.trans_tendsto hρ).add hU
    rw [add_zero] at this
    exact this.congr' (Eventually.of_forall fun p => by
      show ℓ p - Sc p + (Sc p - I * κ * G (zf p)) = ℓ p - I * κ * G (zf p); ring)
  have hT1B : Tendsto (fun p => ℓB p + I * κ * G (zf p)) l (𝓝 0) := by
    have := (hS1B.trans_tendsto hρ).sub hU
    rw [sub_zero] at this
    exact this.congr' (Eventually.of_forall fun p => by
      show ℓB p + Sc p - (Sc p - I * κ * G (zf p)) = ℓB p + I * κ * G (zf p); ring)
  -- generic helpers
  have tz : ∀ {f g : ι → ℂ} (K : ℝ), (∀ᶠ p in l, ‖f p‖ ≤ K * ‖g p‖) →
      Tendsto g l (𝓝 0) → Tendsto f l (𝓝 0) := fun K h hg =>
    squeeze_zero_norm' h (by simpa using hg.norm.const_mul K)
  have evb : ∀ {f : ι → ℂ}, Tendsto f l (𝓝 0) → ∀ {r : ℝ}, 0 < r →
      ∀ᶠ p in l, ‖f p‖ ≤ r := fun h r hr =>
    (h.eventually (Metric.closedBall_mem_nhds 0 hr)).mono fun p hp => mem_closedBall_zero_iff.1 hp
  have hνν : (fun p => ν p * ρ p) =O[l] ρ :=
    IsBigO.of_bound 1 (hνle.mono fun p hp => by
      rw [Real.norm_of_nonneg (hνρ0 p), Real.norm_of_nonneg (hρ0 p), one_mul]
      exact mul_le_of_le_one_left (hρ0 p) hp)
  have hρsq : (fun p => ρ p ^ 2) =O[l] (fun p => ν p * ρ p) :=
    IsBigO.of_bound 1 (hθle.mono fun p hp => by
      rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (hνρ0 p), one_mul]
      have h1 : θ p ^ 2 ≤ 1 := by nlinarith [hθ0 p]
      have h2 : ρ p ^ 2 = ν p * ρ p * θ p ^ 2 := by simp only [hρdef]; ring
      rw [h2]; exact mul_le_of_le_one_right (hνρ0 p) h1)
  have hρθ : ρ =O[l] (fun p => θ p ^ 2) :=
    IsBigO.of_bound 1 (hνle.mono fun p hp => by
      rw [Real.norm_of_nonneg (hρ0 p), Real.norm_of_nonneg (sq_nonneg _), one_mul]
      exact mul_le_of_le_one_left (sq_nonneg _) hp)
  -- S3, S4: A_N → A and B_N → A⁻¹
  have hANexp : ∀ᶠ p in l, AN p = exp (ℓ p) := hdist.mono fun p h => AN_eq_exp h
  have hBNexp : ∀ᶠ p in l, BN p = exp (ℓB p) := hdist'.mono fun p h => AN_eq_exp h
  have hT3 : Tendsto (fun p => AN p - A p) l (𝓝 0) := by
    refine tz M ?_ (tendsto_exp_sub_one hT1)
    filter_upwards [hANexp, hbg] with p h1 h2
    have e1 : AN p - A p = A p * (exp (ℓ p - I * κ * G (zf p)) - 1) := by
      rw [h1]; show exp (ℓ p) - exp (I * κ * G (zf p)) = exp (I * κ * G (zf p)) * _
      rw [mul_sub, ← exp_add, add_sub_cancel, mul_one]
    rw [e1, norm_mul]; exact mul_le_mul_of_nonneg_right h2.1 (norm_nonneg _)
  have hT4 : Tendsto (fun p => BN p - (A p)⁻¹) l (𝓝 0) := by
    refine tz M ?_ (tendsto_exp_sub_one hT1B)
    filter_upwards [hBNexp, hbg] with p h1 h2
    have hAi : (A p)⁻¹ = exp (-(I * κ * G (zf p))) := by
      show (exp (I * κ * G (zf p)))⁻¹ = _; rw [exp_neg]
    have e1 : BN p - (A p)⁻¹ = (A p)⁻¹ * (exp (ℓB p + I * κ * G (zf p)) - 1) := by
      rw [h1, hAi, mul_sub, ← exp_add, mul_one]; congr 2; ring
    rw [e1, norm_mul]; exact mul_le_mul_of_nonneg_right h2.2.1 (norm_nonneg _)
  -- S5: s_N → s
  have hsN_eq : ∀ p, sN p = AN p + e p * BN p := fun p => rfl
  have hs_eq : ∀ p, s p = A p + e p * (A p)⁻¹ := fun p => by
    show Af κ G (zf p) + ef L (zf p) / Af κ G (zf p) = _; rw [div_eq_mul_inv]
  have hD_eq : ∀ p, Dd p = A p - e p * (A p)⁻¹ := fun p => by
    show Af κ G (zf p) - ef L (zf p) / Af κ G (zf p) = _; rw [div_eq_mul_inv]
  have hT5 : Tendsto (fun p => sN p - s p) l (𝓝 0) := by
    have h2 : Tendsto (fun p => e p * (BN p - (A p)⁻¹)) l (𝓝 0) :=
      tz M (by filter_upwards [hbg] with p h; rw [norm_mul]
               exact mul_le_mul_of_nonneg_right h.2.2.1 (norm_nonneg _)) hT4
    refine (by simpa using hT3.add h2 : Tendsto (fun p => (AN p - A p) +
      e p * (BN p - (A p)⁻¹)) l (𝓝 0)).congr' (Eventually.of_forall fun p => ?_)
    show AN p - A p + e p * (BN p - (A p)⁻¹) = sN p - s p
    rw [hsN_eq, hs_eq]; ring
  -- bounds on the background
  have hsb : ∀ᶠ p in l, ‖s p‖ ≤ M + M * M := hbg.mono fun p h => by
    rw [hs_eq]; refine (norm_add_le _ _).trans ?_; rw [norm_mul]
    nlinarith [h.1, h.2.1, h.2.2.1, norm_nonneg (e p), norm_nonneg ((A p)⁻¹)]
  have hDb : ∀ᶠ p in l, ‖Dd p‖ ≤ M + M * M := hbg.mono fun p h => by
    rw [hD_eq]; refine (norm_sub_le _ _).trans ?_; rw [norm_mul]
    nlinarith [h.1, h.2.1, h.2.2.1, norm_nonneg (e p), norm_nonneg ((A p)⁻¹)]
  -- S6: W → 0
  have hT6 : Tendsto W l (𝓝 0) := by
    refine tz ((1 + 2 * (M + M * M)) / η ^ 2) ?_ hT5
    filter_upwards [hbg, hsb, evb hT5 one_pos] with p h hs1 h5
    have hDpos : 0 < ‖Dd p‖ := lt_of_lt_of_le hη h.2.2.2
    have e1 : W p = (sN p - s p) * (sN p + s p) / Dd p ^ 2 := by
      show (sNf L (κ / Nf p) (qf p) (zf p) ^ 2 - sf L κ G (zf p) ^ 2) / Df L κ G (zf p) ^ 2 = _
      ring
    rw [e1, norm_div, norm_mul, norm_pow, div_le_iff₀ (by positivity)]
    have h6 : ‖sN p + s p‖ ≤ 1 + 2 * (M + M * M) := by
      calc ‖sN p + s p‖ = ‖(sN p - s p) + 2 * s p‖ := by ring_nf
        _ ≤ ‖sN p - s p‖ + ‖2 * s p‖ := norm_add_le _ _
        _ ≤ 1 + 2 * (M + M * M) := by rw [norm_mul, Complex.norm_ofNat]; linarith
    have h7 : η ^ 2 ≤ ‖Dd p‖ ^ 2 := pow_le_pow_left₀ hη.le h.2.2.2 2
    have h8 := norm_nonneg (sN p - s p)
    calc ‖sN p - s p‖ * ‖sN p + s p‖ ≤ ‖sN p - s p‖ * (1 + 2 * (M + M * M)) :=
          mul_le_mul_of_nonneg_left h6 h8
      _ = (1 + 2 * (M + M * M)) / η ^ 2 * ‖sN p - s p‖ * η ^ 2 := by field_simp
      _ ≤ (1 + 2 * (M + M * M)) / η ^ 2 * ‖sN p - s p‖ * ‖Dd p‖ ^ 2 := by gcongr
  -- S7, S8: D_N → D, a_N → A, ε → 0
  have hT8 : Tendsto (fun p => DN p - Dd p) l (𝓝 0) := by
    refine tz (M + M * M) ?_ (tendsto_cpow_half hT6)
    filter_upwards [hDb] with p h
    have e1 : DN p - Dd p = Dd p * ((1 + W p) ^ ((2 : ℂ)⁻¹) - 1) := by
      show Df L κ G (zf p) * (1 + Wf L κ (κ / Nf p) G (qf p) (zf p)) ^ ((2 : ℂ)⁻¹) -
        Df L κ G (zf p) = _
      ring
    rw [e1, norm_mul]; exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
  have hT9 : Tendsto (fun p => a p - A p) l (𝓝 0) := by
    refine (by simpa using (hT5.div_const 2).add (hT8.div_const 2) :
      Tendsto (fun p => (sN p - s p) / 2 + (DN p - Dd p) / 2) l (𝓝 0)).congr'
      (Eventually.of_forall fun p => ?_)
    show (sN p - s p) / 2 + (DN p - Dd p) / 2 = a p - A p
    have e1 : a p = (sN p + DN p) / 2 := rfl
    rw [e1, hs_eq, hD_eq]; ring
  have hT10 : Tendsto (fun p => AN p - a p) l (𝓝 0) := by
    simpa using hT3.sub hT9
  -- quantitative eventual bounds
  have hM' : 0 < M := lt_of_lt_of_le one_pos hM0
  have hev := ((((evb hT3 (show (0 : ℝ) < 1 / (2 * M) by positivity)).and
    (evb hT9 (show (0 : ℝ) < 1 / (2 * M) by positivity))).and (evb hT4 one_pos)).and
    ((evb hT8 (show (0 : ℝ) < η / 4 by positivity)).and
    ((evb hT10 (show (0 : ℝ) < η / 8 by positivity)).and
    (evb hT6 (show (0 : ℝ) < 1 / 2 by norm_num)))))
  have hAlow : ∀ᶠ p in l, 1 / M ≤ ‖A p‖ := hbg.mono fun p h => by
    have hA0 : A p ≠ 0 := exp_ne_zero _
    have h1 : ‖A p‖ * ‖(A p)⁻¹‖ = 1 := by rw [← norm_mul, mul_inv_cancel₀ hA0, norm_one]
    rw [div_le_iff₀ hM']; nlinarith [h.2.1, norm_nonneg (A p)]
  have hbd : ∀ᶠ p in l, 1 / (2 * M) ≤ ‖AN p‖ ∧ ‖AN p‖ ≤ M + 1 ∧ 1 / (2 * M) ≤ ‖a p‖ ∧
      ‖a p‖ ≤ M + 1 ∧ ‖BN p‖ ≤ M + 1 ∧ 3 * η / 4 ≤ ‖DN p‖ ∧ ‖AN p - a p‖ ≤ η / 8 ∧
      ‖W p‖ ≤ 1 / 2 := by
    filter_upwards [hev, hbg, hAlow] with p h hb hal
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4, h5, h6⟩ := h
    have hinv : 1 / (2 * M) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have hhalf : 1 / M - 1 / (2 * M) = 1 / (2 * M) := by field_simp; ring
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h5, h6⟩
    · have := norm_sub_norm_le (A p) (A p - AN p)
      rw [sub_sub_cancel, norm_sub_rev] at this; linarith
    · have := norm_le_insert' (AN p) (A p)
      have h7 : ‖AN p‖ ≤ ‖A p‖ + ‖AN p - A p‖ := by
        calc ‖AN p‖ = ‖A p + (AN p - A p)‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      linarith [hb.1]
    · have := norm_sub_norm_le (A p) (A p - a p)
      rw [sub_sub_cancel, norm_sub_rev] at this; linarith
    · have h7 : ‖a p‖ ≤ ‖A p‖ + ‖a p - A p‖ := by
        calc ‖a p‖ = ‖A p + (a p - A p)‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      linarith [hb.1]
    · have h7 : ‖BN p‖ ≤ ‖(A p)⁻¹‖ + ‖BN p - (A p)⁻¹‖ := by
        calc ‖BN p‖ = ‖(A p)⁻¹ + (BN p - (A p)⁻¹)‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      linarith [hb.2.1]
    · have := norm_sub_norm_le (Dd p) (Dd p - DN p)
      rw [sub_sub_cancel, norm_sub_rev] at this; linarith [hb.2.2.2]
  -- S10: the product correction
  set δ : ι → ℂ := fun p => AN p * BN p - 1 with hδdef
  set Y : ι → ℂ := fun p => ℓ p + ℓB p with hYdef
  set Q : ι → ℂ := fun p => ∑ j, ((κ / Nf p : ℝ) : ℂ) ^ 2 / (zf p - (qf p j : ℂ)) ^ 2 with hQdef
  set Ic : ι → ℂ := fun p => I * ((κ / Nf p : ℝ) : ℂ) with hIcdef
  have hYQ : (fun p => Y p - Q p) =O[l] (fun p => ν p * ρ p) := by
    refine bigO_of_le (2 * κ ^ 3 * K) hνρ0 ?_
    filter_upwards [hc2r, hm3] with p h2 hm
    have := ell_pair_m h2
    calc ‖Y p - Q p‖ ≤ 2 * |κ / (Nf p : ℝ)| ^ 3 * ∑ j, (‖zf p - (qf p j : ℂ)‖ ^ 3)⁻¹ := this
      _ = 2 * κ ^ 3 * ν p ^ 2 * (((Nf p : ℝ))⁻¹ * ∑ j, (‖zf p - (qf p j : ℂ)‖ ^ 3)⁻¹) := by
          rw [habsc]; simp only [hνdef]; ring
      _ ≤ 2 * κ ^ 3 * ν p ^ 2 * (K * θ p ^ 2) := by gcongr
      _ = 2 * κ ^ 3 * K * (ν p * ρ p) := by simp only [hρdef]; ring
  have hQ : Q =O[l] ρ := by
    refine bigO_of_le (κ ^ 2 * K) hρ0 ?_
    filter_upwards [hm2] with p hm
    have := sumsq_m (c := κ / Nf p) (q := qf p) (z := zf p)
    calc ‖Q p‖ ≤ (κ / (Nf p : ℝ)) ^ 2 * ∑ j, (‖zf p - (qf p j : ℂ)‖ ^ 2)⁻¹ := this
      _ = κ ^ 2 * ν p * (((Nf p : ℝ))⁻¹ * ∑ j, (‖zf p - (qf p j : ℂ)‖ ^ 2)⁻¹) := by
          simp only [hνdef]; ring
      _ ≤ κ ^ 2 * ν p * (K * θ p ^ 2) := by gcongr
      _ = κ ^ 2 * K * ρ p := by simp only [hρdef]; ring
  have hY : Y =O[l] ρ := ((hYQ.trans hνν).add hQ).congr_left fun p => by ring
  have hδexp : ∀ᶠ p in l, δ p = exp (Y p) - 1 := by
    filter_upwards [hANexp, hBNexp] with p h1 h2
    show AN p * BN p - 1 = exp (ℓ p + ℓB p) - 1
    rw [h1, h2, exp_add]
  have hδY : (fun p => δ p - Y p) =O[l] (fun p => ν p * ρ p) := by
    have h1 : (fun p => δ p - Y p) =O[l] (fun p => Y p ^ 2) := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [hδexp, evb (hY.trans_tendsto hρ) one_pos] with p h1 h2
      rw [h1, one_mul, norm_pow]
      exact Complex.norm_exp_sub_one_sub_id_le h2
    exact (h1.trans (hY.pow 2)).trans hρsq
  have hPQ : (fun p => Ic p * dl p - Q p) =O[l] (fun p => ν p * ρ p) := by
    refine bigO_of_le (2 * κ ^ 3 * K) hνρ0 ?_
    filter_upwards [hc2r, hposw, hm3] with p h2 hp hm
    have := Icdell_m h2 hp
    calc ‖Ic p * dl p - Q p‖ ≤ 2 * |κ / (Nf p : ℝ)| ^ 3 *
          ∑ j, (‖zf p - (qf p j : ℂ)‖ ^ 3)⁻¹ := this
      _ = 2 * κ ^ 3 * ν p ^ 2 * (((Nf p : ℝ))⁻¹ * ∑ j, (‖zf p - (qf p j : ℂ)‖ ^ 3)⁻¹) := by
          rw [habsc]; simp only [hνdef]; ring
      _ ≤ 2 * κ ^ 3 * ν p ^ 2 * (K * θ p ^ 2) := by gcongr
      _ = 2 * κ ^ 3 * K * (ν p * ρ p) := by simp only [hρdef]; ring
  have hδP : (fun p => δ p - Ic p * dl p) =O[l] (fun p => ν p * ρ p) :=
    ((hδY.add hYQ).sub hPQ).congr_left fun p => by ring
  have hδ : δ =O[l] ρ := ((hδY.trans hνν).add hY).congr_left fun p => by ring
  have hIc : Ic =O[l] ν := by
    refine bigO_of_le κ (fun p => (hν0 p).le) (Eventually.of_forall fun p => ?_)
    show ‖I * ((κ / Nf p : ℝ) : ℂ)‖ ≤ κ * ν p
    rw [norm_Ic, habsc]
  -- the residual equation
  have hDne : ∀ᶠ p in l, Dd p ≠ 0 := hbg.mono fun p h => by
    intro h0; have h5 : η ≤ ‖Dd p‖ := h.2.2.2; rw [h0, norm_zero] at h5; linarith
  have hres : ∀ᶠ p in l, (AN p - a p) ^ 2 + DN p * (AN p - a p) + e p * δ p = 0 :=
    hDne.mono fun p h => residual_eq L κ (κ / Nf p) G (qf p) h
  have hε : (fun p => AN p - a p) =O[l] ρ := by
    have h1 : (fun p => AN p - a p) =O[l] δ := by
      refine IsBigO.of_bound (8 * M / (5 * η)) ?_
      filter_upwards [hres, hbd, hbg] with p hr hb hg
      obtain ⟨-, -, -, -, -, hDN, hε8, -⟩ := hb
      have h2 : DN p * (AN p - a p) = -((AN p - a p) ^ 2 + e p * δ p) := by
        linear_combination hr
      have h3 : ‖DN p‖ * ‖AN p - a p‖ ≤ ‖AN p - a p‖ ^ 2 + M * ‖δ p‖ := by
        rw [← norm_mul, h2, norm_neg]
        refine (norm_add_le _ _).trans ?_
        rw [norm_pow, norm_mul]
        nlinarith [hg.2.2.1, norm_nonneg (δ p)]
      have h4 := norm_nonneg (AN p - a p)
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
    exact h1.trans hδ
  have hε2 : (fun p => (AN p - a p) + e p * δ p / DN p) =O[l] (fun p => ν p * ρ p) := by
    have h1 : (fun p => (AN p - a p) + e p * δ p / DN p) =O[l]
        (fun p => (AN p - a p) ^ 2) := by
      refine IsBigO.of_bound (4 / (3 * η)) ?_
      filter_upwards [hres, hbd] with p hr hb
      obtain ⟨-, -, -, -, -, hDN, -, -⟩ := hb
      have hDN0 : DN p ≠ 0 := by
        intro h0; rw [h0, norm_zero] at hDN; linarith
      have e1 : (AN p - a p) + e p * δ p / DN p = -((AN p - a p) ^ 2) / DN p := by
        field_simp; linear_combination hr
      rw [e1, norm_div, norm_neg, div_le_iff₀ (lt_of_lt_of_le (by positivity) hDN)]
      have := norm_nonneg ((AN p - a p) ^ 2)
      calc ‖(AN p - a p) ^ 2‖ = 4 / (3 * η) * ‖(AN p - a p) ^ 2‖ * (3 * η / 4) := by
            field_simp
        _ ≤ 4 / (3 * η) * ‖(AN p - a p) ^ 2‖ * ‖DN p‖ := by gcongr
    exact (h1.trans (hε.pow 2)).trans hρsq
  -- derivatives
  have mul_bdd : ∀ {f g : ι → ℂ} {h : ι → ℝ}, f =O[l] h → ∀ (C : ℝ),
      (∀ᶠ p in l, ‖g p‖ ≤ C) → (fun p => f p * g p) =O[l] h := by
    intro f g h hf C hg
    have hg1 : g =O[l] (fun _ => (1 : ℝ)) := IsBigO.of_bound C (hg.mono fun x hx => by simpa using hx)
    simpa using hf.mul hg1
  have hdlθ : dl =O[l] (fun p => θ p ^ 2) := by
    refine bigO_of_le (2 * κ * K) (fun p => sq_nonneg _) ?_
    filter_upwards [hc2r, hposw, hm2] with p h2 hp hm
    have := dell_m h2 hp
    calc ‖dl p‖ ≤ 2 * |κ / (Nf p : ℝ)| * ∑ j, (‖zf p - (qf p j : ℂ)‖ ^ 2)⁻¹ := this
      _ = 2 * κ * (((Nf p : ℝ))⁻¹ * ∑ j, (‖zf p - (qf p j : ℂ)‖ ^ 2)⁻¹) := by
          rw [habsc]; simp only [hνdef]; ring
      _ ≤ 2 * κ * (K * θ p ^ 2) := by gcongr
      _ = 2 * κ * K * θ p ^ 2 := by ring
  have hdlBθ : dlB =O[l] (fun p => θ p ^ 2) := by
    refine bigO_of_le (2 * κ * K) (fun p => sq_nonneg _) ?_
    filter_upwards [hc2r', hposw, hm2] with p h2 hp hm
    have := dell_m h2 hp
    calc ‖dlB p‖ ≤ 2 * |-(κ / (Nf p : ℝ))| * ∑ j, (‖zf p - (qf p j : ℂ)‖ ^ 2)⁻¹ := this
      _ = 2 * κ * (((Nf p : ℝ))⁻¹ * ∑ j, (‖zf p - (qf p j : ℂ)‖ ^ 2)⁻¹) := by
          rw [abs_neg, habsc]; simp only [hνdef]; ring
      _ ≤ 2 * κ * (K * θ p ^ 2) := by gcongr
      _ = 2 * κ * K * θ p ^ 2 := by ring
  have hdlb : ∀ᶠ p in l, ‖dl p‖ ≤ 2 * κ * K := by
    filter_upwards [hc2r, hposw, hm2, hθle] with p h2 hp hm hθ1
    have := dell_m h2 hp
    have h3 : θ p ^ 2 ≤ 1 := by nlinarith [hθ0 p]
    calc ‖dl p‖ ≤ 2 * |κ / (Nf p : ℝ)| * ∑ j, (‖zf p - (qf p j : ℂ)‖ ^ 2)⁻¹ := this
      _ = 2 * κ * (((Nf p : ℝ))⁻¹ * ∑ j, (‖zf p - (qf p j : ℂ)‖ ^ 2)⁻¹) := by
          rw [habsc]; simp only [hνdef]; ring
      _ ≤ 2 * κ * (K * θ p ^ 2) := by gcongr
      _ ≤ 2 * κ * K := by nlinarith [mul_nonneg hκ.le hK]
  have hdlp : (fun p => dl p + dlB p) =O[l] ρ := by
    refine bigO_of_le (8 * κ ^ 2 * K) hρ0 ?_
    filter_upwards [hc2r, hposw, hm3] with p h2 hp hm
    have := dell_pair_m h2 hp
    calc ‖dl p + dlB p‖ ≤ 8 * |κ / (Nf p : ℝ)| ^ 2 * ∑ j, (‖zf p - (qf p j : ℂ)‖ ^ 3)⁻¹ := this
      _ = 8 * κ ^ 2 * ν p * (((Nf p : ℝ))⁻¹ * ∑ j, (‖zf p - (qf p j : ℂ)‖ ^ 3)⁻¹) := by
          rw [habsc]; simp only [hνdef]; ring
      _ ≤ 8 * κ ^ 2 * ν p * (K * θ p ^ 2) := by
          gcongr
      _ = 8 * κ ^ 2 * K * ρ p := by simp only [hρdef]; ring
  set sN' : ι → ℂ := fun p => AN p * dl p + (I * L * e p * BN p + e p * (BN p * dlB p))
    with hsN'
  have ha'rel : ∀ᶠ p in l, a' p * DN p = sN' p * a p - I * L * e p := by
    filter_upwards [hGd, hDev, hdist, hbd] with p hg hdv hd' hb
    have hW2 := hb.2.2.2.2.2.2.2
    have hslit : 1 + W p ∈ slitPlane := Or.inl (by
      have := Complex.abs_re_le_norm (W p)
      simp only [add_re, one_re]; linarith [neg_abs_le (W p).re])
    exact deriv_aN_mul_DN L κ (κ / Nf p) hg hdv hd' hslit
  -- eq:B3-log-derivative-comparison
  have hdla : (fun p => dl p - a' p / a p) =O[l] ρ := by
    set Num : ι → ℂ := fun p => -2 * (AN p - a p) * dl p * a p * AN p -
      e p * BN p * (dl p + dlB p) * a p * AN p + I * L * e p * ((AN p - a p) - a p * δ p)
      with hNum
    have hN1 : Num =O[l] ρ := by
      have t1 := mul_bdd hε (2 * (2 * κ * K) * (M + 1) * (M + 1))
        (g := fun p => -2 * dl p * a p * AN p) (by
          filter_upwards [hdlb, hbd] with p h1 h2
          simp only [norm_mul, norm_neg, Complex.norm_ofNat]
          have := norm_nonneg (dl p); have := norm_nonneg (a p); have := norm_nonneg (AN p)
          have h3 := h2.2.1; have h4 := h2.2.2.2.1
          have h7 : ‖dl p‖ * ‖a p‖ ≤ 2 * κ * K * (M + 1) :=
            mul_le_mul h1 h4 (by positivity) (by positivity)
          have h5 := mul_le_mul h7 h3 (norm_nonneg _) (by positivity)
          linarith)
      have t2 := mul_bdd hdlp (M * (M + 1) * (M + 1) * (M + 1))
        (g := fun p => -(e p * BN p * a p * AN p)) (by
          filter_upwards [hbd, hbg] with p h2 hg
          simp only [norm_mul, norm_neg]
          have := norm_nonneg (e p); have := norm_nonneg (BN p); have := norm_nonneg (a p)
          have := norm_nonneg (AN p)
          have h5 : ‖e p‖ * ‖BN p‖ ≤ M * (M + 1) := mul_le_mul hg.2.2.1 h2.2.2.2.2.1 (by positivity) (by positivity)
          have h6 : ‖e p‖ * ‖BN p‖ * ‖a p‖ ≤ M * (M + 1) * (M + 1) := mul_le_mul h5 h2.2.2.2.1 (by positivity) (by positivity)
          exact mul_le_mul h6 h2.2.1 (by positivity) (by positivity))
      have t3a : (fun p => (AN p - a p) - a p * δ p) =O[l] ρ :=
        hε.sub ((mul_bdd hδ (M + 1) (g := a) (hbd.mono fun p h => h.2.2.2.1)).congr_left
          fun p => mul_comm _ _)
      have t3 := mul_bdd t3a (|L| * M) (g := fun p => I * L * e p) (by
        filter_upwards [hbg] with p hg
        simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left hg.2.2.1 (abs_nonneg L))
      refine ((t1.add t2).add t3).congr_left fun p => ?_
      simp only [hNum]; ring
    have hN2 : (fun p => dl p - a' p / a p) =O[l] Num := by
      refine IsBigO.of_bound ((4 / (3 * η)) * (2 * M) * (2 * M)) ?_
      filter_upwards [ha'rel, hbd] with p hr hb
      obtain ⟨hAN1, -, ha1, -, -, hDN, -, -⟩ := hb
      have hDN0 : DN p ≠ 0 := by intro h0; rw [h0, norm_zero] at hDN; linarith
      have ha0 : a p ≠ 0 := by intro h0; rw [h0, norm_zero] at ha1; linarith [show 0 < 1 / (2 * M) by positivity]
      have hAN0 : AN p ≠ 0 := by intro h0; rw [h0, norm_zero] at hAN1; linarith [show 0 < 1 / (2 * M) by positivity]
      have hDNe : DN p = 2 * a p - sN p := DN_eq L κ (κ / Nf p) G (qf p) (zf p)
      have key : (dl p - a' p / a p) * (DN p * a p * AN p) = Num p := by
        have e1 : (dl p - a' p / a p) * (DN p * a p * AN p) =
            dl p * DN p * a p * AN p - (a' p * DN p) * AN p := by field_simp
        rw [e1, hr]
        simp only [hNum, hsN', hδdef]
        rw [hDNe, hsN_eq]; ring
      have e2 : dl p - a' p / a p = Num p / (DN p * a p * AN p) := by
        rw [← key]; field_simp
      rw [e2, norm_div, norm_mul, norm_mul, div_le_iff₀ (by positivity)]
      have hlow : 3 * η / 4 * (1 / (2 * M)) * (1 / (2 * M)) ≤ ‖DN p‖ * ‖a p‖ * ‖AN p‖ :=
        mul_le_mul (mul_le_mul hDN ha1 (by positivity) (by positivity)) hAN1 (by positivity)
          (by positivity)
      have hK : (4 / (3 * η)) * (2 * M) * (2 * M) * (3 * η / 4 * (1 / (2 * M)) * (1 / (2 * M))) = 1 := by
        field_simp
      have := norm_nonneg (Num p)
      calc ‖Num p‖ = (4 / (3 * η)) * (2 * M) * (2 * M) * ‖Num p‖ *
            (3 * η / 4 * (1 / (2 * M)) * (1 / (2 * M))) := by rw [mul_right_comm, hK, one_mul]
        _ ≤ (4 / (3 * η)) * (2 * M) * (2 * M) * ‖Num p‖ * (‖DN p‖ * ‖a p‖ * ‖AN p‖) := by gcongr
    exact hN2.trans hN1
  -- eq:B3-multiplier-first-correction
  have heDb : ∀ᶠ p in l, ‖e p / DN p‖ ≤ M * (4 / (3 * η)) := by
    filter_upwards [hbd, hbg] with p hb hg
    have hDN := hb.2.2.2.2.2.1
    rw [norm_div, div_le_iff₀ (lt_of_lt_of_le (by positivity) hDN)]
    calc ‖e p‖ ≤ M := hg.2.2.1
      _ = M * (4 / (3 * η)) * (3 * η / 4) := by field_simp
      _ ≤ M * (4 / (3 * η)) * ‖DN p‖ := by gcongr
  have hε3 : (fun p => (AN p - a p) + Ic p * e p * (a' p / a p) / DN p) =O[l]
      (fun p => ν p * ρ p) := by
    have t2 := mul_bdd hδP (M * (4 / (3 * η))) heDb
    have t3a : (fun p => Ic p * (dl p - a' p / a p)) =O[l] (fun p => ν p * ρ p) :=
      (hIc.mul hdla).congr_right fun p => by ring
    have t3 := mul_bdd t3a (M * (4 / (3 * η))) heDb
    refine ((hε2.sub t2).sub t3).congr_left fun p => ?_
    simp only [hδdef]; ring
  -- the logarithms
  have hlogt : Tendsto (fun p => log (a p / A p)) l (𝓝 0) := by
    refine tendsto_log_near_one ?_
    have h1 : Tendsto (fun p => (a p - A p) * (A p)⁻¹) l (𝓝 0) := by
      refine tz M ?_ hT9
      filter_upwards [hbg] with p h
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right h.2.1 (norm_nonneg _)
    have h2 := h1.const_add 1
    rw [add_zero] at h2
    refine h2.congr' (Eventually.of_forall fun p => ?_)
    have hA0 : A p ≠ 0 := exp_ne_zero _
    show 1 + (a p - A p) * (A p)⁻¹ = a p / A p
    field_simp; ring
  set X : ι → ℂ := fun p => ℓ p - (I * κ * G (zf p) + log (a p / A p)) with hX
  have hXt : Tendsto X l (𝓝 0) := by
    have := hT1.sub hlogt
    rw [sub_zero] at this
    exact this.congr' (Eventually.of_forall fun p => by
      show ℓ p - I * κ * G (zf p) - log (a p / A p) = X p; simp only [hX]; ring)
  set v : ι → ℂ := fun p => (AN p - a p) / a p with hv
  have hvO : v =O[l] ρ := (mul_bdd hε (2 * M) (g := fun p => (a p)⁻¹) (by
    filter_upwards [hbd] with p hb
    have ha1 := hb.2.2.1
    rw [norm_inv, inv_le_comm₀ (lt_of_lt_of_le (by positivity) ha1) (by positivity)]
    calc (2 * M)⁻¹ = 1 / (2 * M) := by rw [one_div]
      _ ≤ ‖a p‖ := ha1)).congr_left fun p => by simp only [hv, div_eq_mul_inv]
  have hXv : (fun p => X p - v p) =O[l] (fun p => ν p * ρ p) := by
    have h1 : (fun p => X p - v p) =O[l] (fun p => v p ^ 2) := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [hbd, evb hXt one_pos, evb (hvO.trans_tendsto hρ)
        (show (0 : ℝ) < 1 / 2 by norm_num), hANexp] with p hb hX1 hv1 hAe
      obtain ⟨hAN1, -, ha1, -, -, -, -, -⟩ := hb
      have ha0 : a p ≠ 0 := by intro h0; rw [h0, norm_zero] at ha1; linarith [show 0 < 1 / (2 * M) by positivity]
      have hA0 : A p ≠ 0 := exp_ne_zero _
      have hexp : exp (X p) = 1 + v p := by
        show exp (ℓ p - (I * κ * G (zf p) + log (a p / A p))) = 1 + (AN p - a p) / a p
        rw [exp_sub, exp_add, exp_log (div_ne_zero ha0 hA0), ← hAe]
        show AN p / (A p * (a p / A p)) = _
        field_simp; ring
      have hIm : |(X p).im| < Real.pi :=
        lt_of_le_of_lt (Complex.abs_im_le_norm _) (lt_of_le_of_lt hX1 (by linarith [Real.pi_gt_three]))
      have hXlog : X p = log (1 + v p) := by
        rw [← hexp, log_exp (by linarith [abs_lt.1 hIm]) (by linarith [abs_lt.1 hIm])]
      rw [hXlog, one_mul, norm_pow]
      exact log_lin hv1
    exact (h1.trans (hvO.pow 2)).trans hρsq
  -- conclusion
  have hfin : ∀ᶠ p in l, remG κ L Nf qf zf G p =
      (X p - v p) + ((AN p - a p) + Ic p * e p * (a' p / a p) / DN p) * (a p)⁻¹ := by
    filter_upwards [hbd, hDne] with p hb hD0
    obtain ⟨-, -, ha1, -, -, hDN, -, -⟩ := hb
    have ha0 : a p ≠ 0 := by intro h0; rw [h0, norm_zero] at ha1; linarith [show 0 < 1 / (2 * M) by positivity]
    have hDN0 : DN p ≠ 0 := by intro h0; rw [h0, norm_zero] at hDN; linarith
    have haD : a p * DN p = a p ^ 2 - e p := aD L κ (κ / Nf p) G (qf p) hD0
    show ℓ p - (I * κ * G (zf p) + log (a p / A p)) +
        I * κ / (Nf p : ℂ) * (e p * a' p / (a p * (a p ^ 2 - e p))) = _
    rw [← haD]
    simp only [hX, hv, hIcdef]
    have hNc : (Nf p : ℂ) ≠ 0 := by exact_mod_cast (hN p).ne'
    push_cast
    field_simp
    ring
  have hrem : remG κ L Nf qf zf G =O[l] (fun p => ν p * ρ p) :=
    ((hXv.add (mul_bdd hε3 (2 * M) (g := fun p => (a p)⁻¹) (by
    filter_upwards [hbd] with p hb
    have ha1 := hb.2.2.1
    rw [norm_inv, inv_le_comm₀ (lt_of_lt_of_le (by positivity) ha1) (by positivity)]
    calc (2 * M)⁻¹ = 1 / (2 * M) := by rw [one_div]
      _ ≤ ‖a p‖ := ha1))).congr' (hfin.mono fun p hp => hp.symm) EventuallyEq.rfl)
  -- the derivative of a_N and the first correction integrand
  have ha'O : a' =O[l] (fun p => θ p ^ 2) := by
    set T : ι → ℂ := fun p => AN p * a p * dl p + e p * BN p * a p * dlB p +
      I * L * e p * (δ p - BN p * (AN p - a p)) with hT
    have hTO : T =O[l] (fun p => θ p ^ 2) := by
      have t1 := mul_bdd hdlθ ((M + 1) * (M + 1)) (g := fun p => AN p * a p) (by
        filter_upwards [hbd] with p hb
        rw [norm_mul]
        exact mul_le_mul hb.2.1 hb.2.2.2.1 (norm_nonneg _) (by positivity))
      have t2 := mul_bdd hdlBθ (M * (M + 1) * (M + 1)) (g := fun p => e p * BN p * a p) (by
        filter_upwards [hbd, hbg] with p hb hg
        rw [norm_mul, norm_mul]
        exact mul_le_mul (mul_le_mul hg.2.2.1 hb.2.2.2.2.1 (norm_nonneg _) (by positivity))
          hb.2.2.2.1 (norm_nonneg _) (by positivity))
      have t3a : (fun p => δ p - BN p * (AN p - a p)) =O[l] (fun p => θ p ^ 2) :=
        (hδ.trans hρθ).sub ((mul_bdd (hε.trans hρθ) (M + 1) (g := BN)
          (hbd.mono fun p h => h.2.2.2.2.1)).congr_left fun p => mul_comm _ _)
      have t3 := mul_bdd t3a (|L| * M) (g := fun p => I * L * e p) (by
        filter_upwards [hbg] with p hg
        simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left hg.2.2.1 (abs_nonneg L))
      refine ((t1.add t2).add t3).congr_left fun p => ?_
      simp only [hT]; ring
    refine (IsBigO.of_bound (4 / (3 * η)) ?_).trans hTO
    filter_upwards [ha'rel, hbd] with p hr hb
    obtain ⟨-, -, -, -, -, hDN, -, -⟩ := hb
    have hDN0 : DN p ≠ 0 := by intro h0; rw [h0, norm_zero] at hDN; linarith
    have key : a' p * DN p = T p := by
      rw [hr]; simp only [hsN', hT, hδdef]; ring
    have e2 : a' p = T p / DN p := by rw [← key]; field_simp
    rw [e2, norm_div, div_le_iff₀ (lt_of_lt_of_le (by positivity) hDN)]
    have := norm_nonneg (T p)
    calc ‖T p‖ = 4 / (3 * η) * ‖T p‖ * (3 * η / 4) := by field_simp
      _ ≤ 4 / (3 * η) * ‖T p‖ * ‖DN p‖ := by gcongr
  have hcorr : (fun p => corrf L κ (κ / Nf p) G (qf p) (zf p)) =O[l] (fun p => θ p ^ 2) := by
    refine (IsBigO.of_bound (M * (2 * M) ^ 2 * (4 / (3 * η))) ?_).trans ha'O
    filter_upwards [hbd, hbg, hDne] with p hb hg hD0
    obtain ⟨-, -, ha1, -, -, hDN, -, -⟩ := hb
    have ha0 : a p ≠ 0 := by
      intro h0; rw [h0, norm_zero] at ha1; linarith [show 0 < 1 / (2 * M) by positivity]
    have hDN0 : DN p ≠ 0 := by intro h0; rw [h0, norm_zero] at hDN; linarith
    have haD : a p * DN p = a p ^ 2 - e p := aD L κ (κ / Nf p) G (qf p) hD0
    show ‖e p * a' p / (a p * (a p ^ 2 - e p))‖ ≤ _
    rw [← haD, norm_div, norm_mul, norm_mul, norm_mul, div_le_iff₀ (by
      have := norm_pos_iff.2 ha0; have := norm_pos_iff.2 hDN0; positivity)]
    have hapos : 0 < ‖a p‖ := lt_of_lt_of_le (by positivity) ha1
    have hlow : 1 / (2 * M) * (1 / (2 * M) * (3 * η / 4)) ≤ ‖a p‖ * (‖a p‖ * ‖DN p‖) :=
      mul_le_mul ha1 (mul_le_mul ha1 hDN (by positivity) hapos.le) (by positivity) hapos.le
    have hK1 : M * (2 * M) ^ 2 * (4 / (3 * η)) * (1 / (2 * M) * (1 / (2 * M) * (3 * η / 4))) = M := by
      field_simp
    have h1 := mul_le_mul_of_nonneg_right hg.2.2.1 (norm_nonneg (a' p))
    have h2 := mul_le_mul_of_nonneg_left hlow
      (mul_nonneg (show (0 : ℝ) ≤ M * (2 * M) ^ 2 * (4 / (3 * η)) by positivity) (norm_nonneg (a' p)))
    have h3 : M * (2 * M) ^ 2 * (4 / (3 * η)) * ‖a' p‖ *
        (1 / (2 * M) * (1 / (2 * M) * (3 * η / 4))) = M * ‖a' p‖ := by
      rw [mul_right_comm, hK1]
    linarith
  refine ⟨hrem, hcorr, ?_⟩
  filter_upwards [hdist, hbd, hev] with p h1 h2 h3
  exact ⟨h1, h2.2.2.2.2.2.2.2, h2.2.2.1, h2.2.2.2.2.2.1, h3.1.1.2⟩

end QuantumNLS.HaarSummableCore

#print axioms QuantumNLS.HaarSummableCore.ell_lin_m
#print axioms QuantumNLS.HaarSummableCore.ell_pair_m
#print axioms QuantumNLS.HaarSummableCore.dell_pair_m
#print axioms QuantumNLS.HaarSummableCore.Icdell_m
#print axioms QuantumNLS.HaarSummableCore.haar_core
