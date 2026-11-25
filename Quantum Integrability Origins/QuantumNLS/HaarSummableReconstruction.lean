import QuantumNLS.HaarSummableCore
import QuantumNLS.HighContours

/-!
# R-9A71E77E `QG:prop:haar-summable-reconstruction` (QUANTUM_GAUGE_COMPONENTS.tex:489-527)

Proof: QUANTUM_GAUGE_COMPONENTS.tex:528-600. Built on HighContours (R-93DEB242, `adafba82…`),
the moment form of the BO1 estimate (`HaarSummableCore`), the PROP-005/006 contour machinery
(`LabelExactPeriod`, `PeriodReconstruction`, `PeriodTwoTerm`) and the RC1 algebra
(`PeriodReconstructionCore`) with the free background `G ≡ 0` (`A = 1`, `s = 1 + e^{izL}`,
`D = 1 − e^{izL}`).

Realization:
* the contour `Γ_n` is `HighContours.Γ L n` (the frontier of the square of half-width `ω/4`
  about `ωn`); it coincides with the four edges `Gam (ωn − ω/4) (ωn + ω/4) (ω/4)`
  (`Gam_subset_Γ`, `Γ_subset_Gam`), and `∮_{Γ_n}` is the positively oriented boundary integral
  (`rect_eq_boundary`: EP1's `rectIntegral` equals HighContours' `boundaryIntegral`);
* `ℓ_N` is the Taylor-series logarithm of EP1 (`LabelExactPeriod.ellN`), `a_N = aNf … G0`,
  the remainder `rN = ℓ_N − log a_N + (iκ/N) e^{izL}a_N'/(a_N(a_N² − e^{izL}))`, and
  `C0`, `C1` are the printed `C_{0,N,n}`, `C_{1,N,n}`;
* **`haar_summable_reconstruction`**: there are `N_E`, `R_E ≥ 2`, `C_E ≥ 0` such that for all
  `N ≥ N_E` and every on-shell configuration (`IsActualConfig L (κ/N) n q`) with
  `N^{-1} Σ q_j² ≤ E`:
  (i) for every `|n| > R_E` and `z ∈ Γ_n`: the roots are at distance `> 2κ/N` from `z`,
  `a_N² − s_N a_N + e^{izL} = 0`, `|a_N − 1| ≤ 1/2`, `a_N` is holomorphic at `z`,
  `log a_N` is the Taylor branch at one, `|r_{N,n}(z)| ≤ C_E/(N²n²)` and the correction
  integrand is at most `C_E/n²`;
  (ii) `|m_n − N C_0 − C_1| ≤ C_E/(N n²)` for every `|n| > R_E`;
  (iii) `|Σ_{n∈I} t_n (m_n − N C_0 − C_1)| ≤ C_E/(NR)` for `R ≥ R_E`, finite `I ⊂ {|n| > R}`,
  `|t_n| ≤ 1`;
  (iv) `Σ_{|n|>R} |C_1| ≤ C_E/R` (summable) for `R ≥ R_E`.

Recorded deviations (none weakens the statement): the uniformity in `(N, n, configuration, z)`
is obtained by running the moment form of the BO1 argument along the filter
`comap (N, |n|) atTop ⊓ 𝓟 {admissible (N, n, q, z)}` and unpacking the eventual bounds; the
derivative bound `|a_N'/a_N| ≤ C_E/n²` is obtained from the implicit-differentiation identity
(RC1 `deriv_aN_mul_DN`) instead of a Cauchy estimate on a nested neighbourhood; the moments are
used for `p = 1, 2, 3` (`p = 4` is not needed).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000
noncomputable section

open Complex Filter Topology Asymptotics Set

namespace QuantumNLS.HaarSummableReconstruction

open QuantumNLS.PeriodReconstructionCore QuantumNLS.PeriodReconstructionAsymp
  QuantumNLS.PeriodReconstructionBigO QuantumNLS.PeriodReconstruction QuantumNLS.PeriodTwoTerm
  QuantumNLS.HaarSummableCore

/-! ## 1. The free background -/

/-- The free background `G ≡ 0`. -/
def G0 : ℂ → ℂ := fun _ => 0

lemma Af_G0 (κ : ℝ) (z : ℂ) : Af κ G0 z = 1 := by simp [Af, G0]

lemma Df_G0 (L κ : ℝ) (z : ℂ) : Df L κ G0 z = 1 - ef L z := by simp [Df, Af, G0]

lemma logaNf_G0 (L κ c : ℝ) {N : ℕ} (q : Fin N → ℝ) :
    logaNf L κ c G0 q = fun z => log (aNf L κ c G0 q z) := by
  funext z; simp [logaNf, Af, G0]

/-! ## 2. The contours -/

/-- Left edge `ωn − ω/4`. -/
def lo (L : ℝ) (m : ℤ) : ℝ := HighContours.om L * m - HighContours.om L / 4

/-- Right edge `ωn + ω/4`. -/
def hi (L : ℝ) (m : ℤ) : ℝ := HighContours.om L * m + HighContours.om L / 4

/-- Half-height `ω/4`. -/
def ht (L : ℝ) : ℝ := HighContours.om L / 4

lemma Gam_subset_Γ {L : ℝ} (hL : 0 < L) (m : ℤ) :
    Gam (lo L m) (hi L m) (ht L) ⊆ HighContours.Γ L m := by
  intro z hz
  have hω := HighContours.om_pos hL
  have hh0 : 0 < ht L := by simp only [ht]; linarith
  have hlohi : lo L m < hi L m := by simp only [lo, hi]; linarith
  have hht : -(ht L) < ht L := by linarith
  have hrect : HighContours.rect L m = (Ioo (lo L m) (hi L m)) ×ℂ (Ioo (-(ht L)) (ht L)) := by
    ext w
    simp only [HighContours.rect, mem_ofPred_eq, Complex.mem_reProdIm, mem_Ioo, abs_lt, lo, hi, ht]
    constructor <;> rintro ⟨⟨h1, h2⟩, h3, h4⟩ <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  show z ∈ closure (HighContours.rect L m) \ interior (HighContours.rect L m)
  rw [(HighContours.rect_isOpen L m).interior_eq, hrect, Complex.closure_reProdIm,
    closure_Ioo hlohi.ne, closure_Ioo hht.ne]
  refine ⟨?_, ?_⟩
  · rw [Complex.mem_reProdIm]
    rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨h1, ?_⟩
      rw [mem_Icc]
      rcases h2 with h2 | h2 <;> constructor <;> linarith
    · refine ⟨?_, h1⟩
      rw [mem_Icc]
      rcases h2 with h2 | h2 <;> constructor <;> linarith
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    rcases hz with ⟨-, h5 | h5⟩ | ⟨-, h5 | h5⟩ <;> linarith

lemma Γ_subset_Gam {L : ℝ} (m : ℤ) : HighContours.Γ L m ⊆ Gam (lo L m) (hi L m) (ht L) := by
  intro z hz
  obtain ⟨h1, h2, h3⟩ := HighContours.mem_Γ hz
  rw [abs_le] at h1 h2
  by_cases h : |z.re - HighContours.om L * m| < HighContours.om L / 4
  · have h4 : ¬ |z.im| < HighContours.om L / 4 := fun h' => h3 ⟨h, h'⟩
    rw [abs_lt] at h4
    refine Or.inl ⟨⟨by simp only [lo]; linarith, by simp only [hi]; linarith⟩, ?_⟩
    simp only [ht]
    rcases lt_or_eq_of_le h2.1 with h5 | h5
    · rcases lt_or_eq_of_le h2.2 with h6 | h6
      · exact absurd ⟨h5, h6⟩ h4
      · exact Or.inr h6
    · exact Or.inl h5.symm
  · rw [abs_lt] at h
    refine Or.inr ⟨⟨by simp only [ht]; linarith, by simp only [ht]; linarith⟩, ?_⟩
    simp only [lo, hi]
    rcases lt_or_eq_of_le h1.1 with h5 | h5
    · rcases lt_or_eq_of_le h1.2 with h6 | h6
      · exact absurd ⟨h5, h6⟩ h
      · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)

lemma Γ_subset_nbhd {L : ℝ} (hL : 0 < L) (m : ℤ) : HighContours.Γ L m ⊆ HighContours.nbhd L m :=
  fun z hz => ⟨z, hz, by rw [dist_self]; have := HighContours.om_pos hL; positivity⟩

lemma Gam_subset_nbhd {L : ℝ} (hL : 0 < L) (m : ℤ) :
    Gam (lo L m) (hi L m) (ht L) ⊆ HighContours.nbhd L m :=
  (Gam_subset_Γ hL m).trans (Γ_subset_nbhd hL m)

/-- EP1's rectangle integral over `Γ_n` is HighContours' positively oriented boundary integral. -/
lemma rect_eq_boundary (L : ℝ) (m : ℤ) (f : ℂ → ℂ) :
    LabelExactPeriod.rectIntegral f (lo L m) (hi L m) (ht L) =
      HighContours.boundaryIntegral L m f := by
  simp only [LabelExactPeriod.rectIntegral, HighContours.boundaryIntegral, lo, hi, ht, smul_eq_mul]

lemma Gam_im {a b h : ℝ} (hh : 0 ≤ h) {z : ℂ} (hz : z ∈ Gam a b h) : |z.im| ≤ h := by
  rw [abs_le]
  rcases hz with ⟨-, h2 | h2⟩ | ⟨h1, -⟩
  · constructor <;> linarith
  · constructor <;> linarith
  · exact ⟨h1.1, h1.2⟩

lemma L_om {L : ℝ} (hL : 0 < L) : L * HighContours.om L = 2 * Real.pi := by
  unfold HighContours.om; field_simp

lemma norm_ef_eq (L : ℝ) (z : ℂ) : ‖ef L z‖ = Real.exp (-(L * z.im)) := by
  rw [ef, Complex.norm_exp]; congr 1; simp

lemma norm_ef_le {L : ℝ} (hL : 0 < L) (m : ℤ) {z : ℂ} (hz : z ∈ Gam (lo L m) (hi L m) (ht L)) :
    ‖ef L z‖ ≤ Real.exp (Real.pi / 2) := by
  have hω := HighContours.om_pos hL
  have h1 := Gam_im (by simp only [ht]; linarith) hz
  rw [norm_ef_eq]
  refine Real.exp_le_exp.2 ?_
  have h2 : L * ht L = Real.pi / 2 := by simp only [ht]; linear_combination L_om hL / 4
  have h3 : -(L * z.im) ≤ L * |z.im| := by
    have := neg_abs_le z.im
    nlinarith
  have h4 : L * |z.im| ≤ L * ht L := mul_le_mul_of_nonneg_left h1 hL.le
  linarith

/-- The free discriminant `1 − e^{izL}` is bounded below on every `Γ_n` (periodicity). -/
lemma Df_lower {L : ℝ} (hL : 0 < L) (m : ℤ) {z : ℂ} (hz : z ∈ Gam (lo L m) (hi L m) (ht L)) :
    1 - Real.exp (-(Real.pi / 2)) ≤ ‖1 - ef L z‖ := by
  have hLω := L_om hL
  have hLh : L * ht L = Real.pi / 2 := by simp only [ht]; linear_combination hLω / 4
  have hpos := Real.exp_pos (-(Real.pi / 2))
  rcases hz with ⟨-, h2⟩ | ⟨-, h2⟩
  · rcases h2 with h2 | h2
    · have hn := norm_sub_norm_le (ef L z) 1
      rw [norm_sub_rev, norm_one, norm_ef_eq, h2, mul_neg, neg_neg, hLh] at hn
      have := Real.add_one_le_exp (Real.pi / 2)
      linarith [Real.pi_gt_three]
    · have hn := norm_sub_norm_le (1 : ℂ) (ef L z)
      rw [norm_one, norm_ef_eq, h2, hLh] at hn
      linarith
  · have hre : (1 - ef L z).re = 1 := by
      rw [sub_re, one_re, ef, Complex.exp_re]
      have e1 : (I * L * z).im = L * z.re := by simp
      rw [e1]
      have hc : Real.cos (L * z.re) = 0 := by
        rcases h2 with h2 | h2 <;> rw [h2] <;> simp only [lo, hi]
        · rw [show L * (HighContours.om L * m - HighContours.om L / 4) =
              -(Real.pi / 2) + m * (2 * Real.pi) by linear_combination ((m : ℝ) - 1 / 4) * hLω,
            Real.cos_add_int_mul_two_pi, Real.cos_neg, Real.cos_pi_div_two]
        · rw [show L * (HighContours.om L * m + HighContours.om L / 4) =
              Real.pi / 2 + m * (2 * Real.pi) by linear_combination ((m : ℝ) + 1 / 4) * hLω,
            Real.cos_add_int_mul_two_pi, Real.cos_pi_div_two]
      rw [hc, mul_zero, sub_zero]
    have := Complex.abs_re_le_norm (1 - ef L z)
    rw [hre, abs_one] at this
    linarith

/-! ## 3. Moment bounds, tails -/

lemma mom_le {L E : ℝ} (hL : 0 < L) (hE : 0 ≤ E) {s r : ℕ} (hr : r ≤ s) (hr2 : r ≤ 2) {m : ℤ}
    (hm : 1 ≤ |(m : ℝ)|) :
    (4 / |HighContours.om L * m|) ^ s +
        4 * E / ((HighContours.om L / 8) ^ s * |HighContours.om L * m| ^ 2) ≤
      ((4 / HighContours.om L) ^ s +
        4 * E / ((HighContours.om L / 8) ^ s * HighContours.om L ^ 2)) * (|(m : ℝ)|⁻¹) ^ r := by
  have hω := HighContours.om_pos hL
  set ω := HighContours.om L
  set t := |(m : ℝ)|
  have ht0 : 0 < t := by linarith
  have hu0 : 0 ≤ t⁻¹ := inv_nonneg.2 ht0.le
  have hu1 : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hm
  rw [abs_mul, abs_of_pos hω]
  have e1 : (4 / (ω * t)) ^ s = (4 / ω) ^ s * t⁻¹ ^ s := by
    rw [← mul_pow]; congr 1; field_simp
  have e2 : 4 * E / ((ω / 8) ^ s * (ω * t) ^ 2) = 4 * E / ((ω / 8) ^ s * ω ^ 2) * t⁻¹ ^ 2 := by
    field_simp
  rw [e1, e2, add_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hu0 hu1 hr) (by positivity))
    (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hu0 hu1 hr2) (by positivity))

lemma tsum_tail {R : ℝ} (hR : 2 ≤ R) :
    Summable (fun m : ℤ => if R < |(m : ℝ)| then 1 / (m : ℝ) ^ 2 else 0) ∧
      ∑' m : ℤ, (if R < |(m : ℝ)| then 1 / (m : ℝ) ^ 2 else 0) ≤ 4 / R := by
  set M : ℕ := ⌊R⌋₊
  have hR0 : 0 ≤ R := by linarith
  have hMR : (M : ℝ) ≤ R := Nat.floor_le hR0
  have hRM : R < M + 1 := Nat.lt_floor_add_one R
  have hM1 : 1 ≤ M := (Nat.one_le_cast (α := ℝ)).1 (by linarith)
  obtain ⟨hs, ht⟩ := HighContours.int_tail M hM1
  have hle : ∀ m : ℤ, (if R < |(m : ℝ)| then 1 / (m : ℝ) ^ 2 else 0) ≤
      (if (M : ℝ) < |(m : ℝ)| then 1 / (m : ℝ) ^ 2 else 0) := fun m => by
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (lt_of_le_of_lt hMR h1) h2
    · positivity
    · exact le_rfl
  have hnn : ∀ m : ℤ, 0 ≤ (if R < |(m : ℝ)| then 1 / (m : ℝ) ^ 2 else 0) := fun m => by
    split_ifs <;> positivity
  have hs' := Summable.of_nonneg_of_le hnn hle hs
  refine ⟨hs', (hs'.tsum_le_tsum hle hs).trans (ht.trans ?_)⟩
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
  rw [div_le_div_iff₀ hM0 (by linarith)]
  linarith

lemma finite_tail {R : ℝ} (hR : 2 ≤ R) (I : Finset ℤ) (hI : ∀ m ∈ I, R < |(m : ℝ)|) :
    ∑ m ∈ I, 1 / (m : ℝ) ^ 2 ≤ 4 / R := by
  obtain ⟨hs, ht⟩ := tsum_tail hR
  have e : ∑ m ∈ I, 1 / (m : ℝ) ^ 2 =
      ∑ m ∈ I, (if R < |(m : ℝ)| then 1 / (m : ℝ) ^ 2 else 0) :=
    Finset.sum_congr rfl fun m hm => by simp only [hI m hm, ↓reduceIte]
  rw [e]
  refine (hs.sum_le_tsum I fun m _ => ?_).trans ht
  split_ifs <;> positivity

/-! ## 4. The period formula for a counted block -/

lemma period_count {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (q : Fin N → ℝ) (n : Fin N → ℤ)
    (m : ℤ) {a b h : ℝ} (hab : a < b) (hsmallh : 2 * (κ / N) < h)
    (hqa : ∀ j, 2 * (κ / N) < |q j - a|) (hqb : ∀ j, 2 * (κ / N) < |q j - b|)
    (hin : ∀ j, (a < q j ∧ q j < b) ↔ n j = m) :
    (((Finset.univ.filter fun j => n j = m).card : ℝ) / N : ℂ) =
      -(1 / (2 * Real.pi * κ)) * LabelExactPeriod.rectIntegral (ellf (κ / N) q) a b h := by
  set c : ℝ := κ / N with hc
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hc0 : 0 < c := div_pos hκ hNr
  have hd := fun j =>
    LabelExactPeriod.bdry_dist (q := q j) (a := a) (b := b) hc0 hsmallh (hqa j) (hqb j)
  have hcont : ∀ j, ∀ z : ℂ, 2 * c < ‖z - q j‖ →
      ContinuousAt (fun z => log (1 + I * c / (z - q j))) z := fun j z hz =>
    (LabelExactPeriod.deriv_facts hc0 hz).1.continuousAt
  have e : ellf c q = fun z => ∑ j, log (1 + I * c / (z - q j)) := rfl
  rw [e, LabelExactPeriod.rectIntegral_sum Finset.univ (fun j _ x _ => hcont j _ ((hd j).1 x))
    (fun j _ x _ => hcont j _ ((hd j).2.1 x)) (fun j _ y _ => hcont j _ ((hd j).2.2.1 y))
    (fun j _ y _ => hcont j _ ((hd j).2.2.2 y))]
  rw [Finset.sum_congr rfl fun j _ => LabelExactPeriod.root_period hc0 hsmallh (hqa j) (hqb j) hab]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hfilt : (Finset.univ.filter fun j => a < q j ∧ q j < b) =
      Finset.univ.filter fun j => n j = m := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hin j
  rw [hfilt]
  have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  rw [hc]
  push_cast
  field_simp
  rw [I_sq]
  ring

/-! ## 5. Continuity of the reconstruction functions -/

lemma contAt_gen {L κ c : ℝ} {G : ℂ → ℂ} {N : ℕ} {q : Fin N → ℝ} {z : ℂ} {M η : ℝ}
    (hM : 0 < M) (hη : 0 < η) (hGnear : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ G w)
    (hR : ∀ j, 2 * |c| < ‖z - q j‖) (hDz : Df L κ G z ≠ 0)
    (hW : ‖Wf L κ c G q z‖ ≤ 1 / 2) (ha : 1 / (2 * M) ≤ ‖aNf L κ c G q z‖)
    (hDN : 3 * η / 4 ≤ ‖DNf L κ c G q z‖)
    (haA : ‖aNf L κ c G q z - Af κ G z‖ ≤ 1 / (2 * M)) (hAi : ‖(Af κ G z)⁻¹‖ ≤ M) :
    ContinuousAt (logaNf L κ c G q) z ∧ ContinuousAt (corrf L κ c G q) z ∧
      ContinuousAt (ellf c q) z ∧ DifferentiableAt ℂ (aNf L κ c G q) z := by
  have hGc : ContinuousAt G z := hGnear.self_of_nhds.continuousAt
  have hAc : ContinuousAt (Af κ G) z := (hGc.const_mul (I * κ)).cexp
  have hec : ContinuousAt (ef L) z := (hasDerivAt_ef L z).continuousAt
  have hA0 : Af κ G z ≠ 0 := exp_ne_zero _
  have hsc : ContinuousAt (sf L κ G) z := hAc.add (hec.div hAc hA0)
  have hDc : ContinuousAt (Df L κ G) z := hAc.sub (hec.div hAc hA0)
  have hsNc : ContinuousAt (sNf L c q) z := (hasDerivAt_sN L hR).continuousAt
  have hWc : ContinuousAt (Wf L κ c G q) z :=
    ((hsNc.pow 2).sub (hsc.pow 2)).div (hDc.pow 2) (pow_ne_zero 2 hDz)
  have hWnear : ∀ᶠ w in 𝓝 z, 1 + Wf L κ c G q w ∈ slitPlane := by
    filter_upwards [hWc.norm.eventually (gt_mem_nhds (show ‖Wf L κ c G q z‖ < 1 by linarith))]
      with w hw
    refine Or.inl ?_
    have := Complex.abs_re_le_norm (Wf L κ c G q w)
    simp only [add_re, one_re]
    linarith [neg_abs_le (Wf L κ c G q w).re]
  have hdiff : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (aNf L κ c G q) w := by
    filter_upwards [hGnear, hDc.eventually_ne hDz, ev_dist hR, hWnear] with w h1 h2 h3 h4
    exact differentiableAt_aN L κ c h1 h2 h3 h4
  obtain ⟨s, hs, hsd⟩ := hdiff.exists_mem
  have han : AnalyticAt ℂ (aNf L κ c G q) z :=
    DifferentiableOn.analyticAt (fun w hw => (hsd w hw).differentiableWithinAt) hs
  have hac : ContinuousAt (aNf L κ c G q) z := han.continuousAt
  have hdc : ContinuousAt (deriv (aNf L κ c G q)) z := han.deriv.continuousAt
  have ha0 : aNf L κ c G q z ≠ 0 := by
    intro h0; rw [h0, norm_zero] at ha; linarith [show 0 < 1 / (2 * M) by positivity]
  have hDN0 : DNf L κ c G q z ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hDN; linarith
  have haD : aNf L κ c G q z * DNf L κ c G q z = aNf L κ c G q z ^ 2 - ef L z := aD L κ c G q hDz
  have hden : aNf L κ c G q z ^ 2 - ef L z ≠ 0 := by rw [← haD]; exact mul_ne_zero ha0 hDN0
  have hslit : aNf L κ c G q z / Af κ G z ∈ slitPlane := by
    refine Or.inl ?_
    have e : aNf L κ c G q z / Af κ G z - 1 = (aNf L κ c G q z - Af κ G z) * (Af κ G z)⁻¹ := by
      field_simp
    have hb : ‖aNf L κ c G q z / Af κ G z - 1‖ ≤ 1 / 2 := by
      rw [e, norm_mul]
      calc _ ≤ 1 / (2 * M) * M := mul_le_mul haA hAi (norm_nonneg _) (by positivity)
        _ = 1 / 2 := by field_simp
    have := Complex.abs_re_le_norm (aNf L κ c G q z / Af κ G z - 1)
    have e2 : (aNf L κ c G q z / Af κ G z).re = 1 + (aNf L κ c G q z / Af κ G z - 1).re := by
      simp
    rw [e2]
    linarith [neg_abs_le (aNf L κ c G q z / Af κ G z - 1).re]
  refine ⟨?_, ?_, (hasDerivAt_ell hR).continuousAt, hdiff.self_of_nhds⟩
  · exact (hGc.const_mul (I * κ)).add ((hac.div hAc hA0).clog hslit)
  · exact (hec.mul hdc).div (hac.mul ((hac.pow 2).sub hec)) (mul_ne_zero ha0 hden)

/-! ## 6. Filters on configurations -/

lemma ev_extract {ι : Type*} {g : ι → ℕ × ℕ} {S : Set ι} {P : ι → Prop}
    (h : ∀ᶠ i in comap g atTop ⊓ 𝓟 S, P i) :
    ∃ N0 R0 : ℕ, ∀ i ∈ S, N0 ≤ (g i).1 → R0 ≤ (g i).2 → P i := by
  rw [eventually_inf_principal, eventually_comap, eventually_atTop] at h
  obtain ⟨⟨N0, R0⟩, h⟩ := h
  exact ⟨N0, R0, fun i hi h1 h2 => h (g i) (Prod.le_def.2 ⟨h1, h2⟩) i rfl hi⟩

lemma tendsto_comps {ι : Type*} (g : ι → ℕ × ℕ) (S : Set ι) :
    Tendsto (fun i => (g i).1) (comap g atTop ⊓ 𝓟 S) atTop ∧
      Tendsto (fun i => (g i).2) (comap g atTop ⊓ 𝓟 S) atTop := by
  have hg : Tendsto g (comap g atTop ⊓ 𝓟 S) (atTop ×ˢ atTop) := by
    rw [prod_atTop_atTop_eq]; exact tendsto_comap.mono_left inf_le_left
  exact ⟨tendsto_fst.comp hg, tendsto_snd.comp hg⟩

/-- Index: a configuration with `N = k + 1` roots (labels, roots), a contour label and a point. -/
abbrev Idx := Σ k : ℕ, (Fin (k + 1) → ℤ) × (Fin (k + 1) → ℝ) × ℤ × ℂ

/-! ## 7. The statement -/

/-- `r_{N,n} = ℓ_N − log a_N + (iκ/N) e^{izL}a_N'/(a_N(a_N² − e^{izL}))`, `ℓ_N` by Taylor series. -/
def rN (L κ : ℝ) {N : ℕ} (q : Fin N → ℝ) (z : ℂ) : ℂ :=
  LabelExactPeriod.ellN κ q z - log (aNf L κ (κ / N) G0 q z) +
    I * κ / (N : ℂ) * corrf L κ (κ / N) G0 q z

/-- `C_{0,N,n} = −(1/(2πκ)) Re ∮_{Γ_n} log a_N`. -/
def C0 (L κ : ℝ) {N : ℕ} (q : Fin N → ℝ) (m : ℤ) : ℝ :=
  -(1 / (2 * Real.pi * κ)) *
    (HighContours.boundaryIntegral L m (fun z => log (aNf L κ (κ / N) G0 q z))).re

/-- `C_{1,N,n} = Re (i/(2π)) ∮_{Γ_n} e^{izL}a_N'/(a_N(a_N² − e^{izL}))`. -/
def C1 (L κ : ℝ) {N : ℕ} (q : Fin N → ℝ) (m : ℤ) : ℝ :=
  (I / (2 * Real.pi) * HighContours.boundaryIntegral L m (corrf L κ (κ / N) G0 q)).re

/-- **R-9A71E77E `QG:prop:haar-summable-reconstruction`.** -/
theorem haar_summable_reconstruction {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) {E : ℝ} (hE : 0 < E) :
    ∃ (NE : ℕ) (RE CE : ℝ), 0 < NE ∧ 2 ≤ RE ∧ 0 ≤ CE ∧
      ∀ (N : ℕ) (n : Fin N → ℤ) (q : Fin N → ℝ), NE ≤ N →
        RootContraction.IsActualConfig L (κ / N) n q → (N : ℝ)⁻¹ * ∑ j, q j ^ 2 ≤ E →
        (∀ m : ℤ, RE < |(m : ℝ)| → ∀ z ∈ HighContours.Γ L m,
          (∀ j, 2 * |κ / (N : ℝ)| < ‖z - q j‖) ∧
          aNf L κ (κ / N) G0 q z ^ 2 - sNf L (κ / N) q z * aNf L κ (κ / N) G0 q z + ef L z = 0 ∧
          ‖aNf L κ (κ / N) G0 q z - 1‖ ≤ 1 / 2 ∧
          DifferentiableAt ℂ (aNf L κ (κ / N) G0 q) z ∧
          log (aNf L κ (κ / N) G0 q z) =
            LabelExactPeriod.logT (aNf L κ (κ / N) G0 q z - 1) ∧
          ‖rN L κ q z‖ ≤ CE / ((N : ℝ) ^ 2 * (m : ℝ) ^ 2) ∧
          ‖corrf L κ (κ / N) G0 q z‖ ≤ CE / (m : ℝ) ^ 2) ∧
        (∀ m : ℤ, RE < |(m : ℝ)| →
          |((Finset.univ.filter fun j => n j = m).card : ℝ) - N * C0 L κ q m - C1 L κ q m| ≤
            CE / (N * (m : ℝ) ^ 2)) ∧
        (∀ R : ℝ, RE ≤ R → ∀ I : Finset ℤ, (∀ m ∈ I, R < |(m : ℝ)|) → ∀ t : ℤ → ℝ,
          (∀ m, |t m| ≤ 1) →
          |∑ m ∈ I, t m * (((Finset.univ.filter fun j => n j = m).card : ℝ) -
              N * C0 L κ q m - C1 L κ q m)| ≤ CE / (N * R)) ∧
        (∀ R : ℝ, RE ≤ R →
          Summable (fun m : ℤ => if R < |(m : ℝ)| then |C1 L κ q m| else 0) ∧
          ∑' m : ℤ, (if R < |(m : ℝ)| then |C1 L κ q m| else 0) ≤ CE / R) := by
  have hω := HighContours.om_pos hL
  set ω := HighContours.om L with hωdef
  have hω' : 0 < HighContours.om L := HighContours.om_pos hL
  obtain ⟨R, -, hHC⟩ := HighContours.high_contours hL hκ E hE
  -- the admissible indices
  set S : Set Idx := {i | RootContraction.IsActualConfig L (κ / ((i.1 + 1 : ℕ) : ℝ)) i.2.1 i.2.2.1 ∧
    (((i.1 + 1 : ℕ) : ℝ))⁻¹ * ∑ j, i.2.2.1 j ^ 2 ≤ E ∧ R < |((i.2.2.2.1 : ℤ) : ℝ)| ∧
    i.2.2.2.2 ∈ Gam (lo L i.2.2.2.1) (hi L i.2.2.2.1) (ht L)} with hSdef
  set g : Idx → ℕ × ℕ := fun i => (i.1, i.2.2.2.1.natAbs) with hgdef
  set l : Filter Idx := comap g atTop ⊓ 𝓟 S with hldef
  obtain ⟨hg1, hg2⟩ := tendsto_comps g S
  have hcast : ∀ m : ℤ, ((m.natAbs : ℕ) : ℝ) = |(m : ℝ)| := fun m => by simp
  have hSev : ∀ᶠ i in l, i ∈ S := mem_inf_of_right (mem_principal_self S)
  have hnat1 : ∀ᶠ i in l, 1 ≤ |((i.2.2.2.1 : ℤ) : ℝ)| := by
    filter_upwards [hg2.eventually_ge_atTop 1] with i hi
    have hi' : 1 ≤ i.2.2.2.1.natAbs := hi
    rw [← hcast]; exact_mod_cast hi'
  -- the two small parameters
  have hνt : Tendsto (fun i : Idx => (((i.1 + 1 : ℕ) : ℝ))⁻¹) l (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_natCast_atTop_atTop : Tendsto (Nat.cast : ℕ → ℝ) atTop atTop).comp
      ((tendsto_add_atTop_nat 1).comp hg1))
  set θ : Idx → ℝ := fun i => |((i.2.2.2.1 : ℤ) : ℝ)|⁻¹ with hθdef
  have hθ0 : ∀ i, 0 ≤ θ i := fun i => inv_nonneg.2 (abs_nonneg _)
  have hθ : Tendsto θ l (𝓝 0) := by
    have := tendsto_inv_atTop_zero.comp
      ((tendsto_natCast_atTop_atTop : Tendsto (Nat.cast : ℕ → ℝ) atTop atTop).comp hg2)
    refine this.congr fun i => ?_
    simp only [Function.comp_apply, hθdef, hgdef]; rw [hcast]
  -- constants
  set K1 : ℝ := 4 / ω + 4 * E / (ω / 8 * ω ^ 2) with hK1
  set K2 : ℝ := (4 / ω) ^ 2 + 4 * E / ((ω / 8) ^ 2 * ω ^ 2) with hK2
  set K3 : ℝ := (4 / ω) ^ 3 + 4 * E / ((ω / 8) ^ 3 * ω ^ 2) with hK3
  have hK1p : 0 ≤ K1 := by positivity
  have hK2p : 0 ≤ K2 := by positivity
  have hK3p : 0 ≤ K3 := by positivity
  set M : ℝ := Real.exp (Real.pi / 2) with hMdef
  have hM0 : 1 ≤ M := Real.one_le_exp (by positivity)
  set η : ℝ := 1 - Real.exp (-(Real.pi / 2)) with hηdef
  have hη : 0 < η := by
    have := Real.exp_lt_exp.2 (show -(Real.pi / 2) < 0 by linarith [Real.pi_pos])
    rw [Real.exp_zero] at this
    linarith
  -- hypotheses of the core estimate
  have hroot : ∀ᶠ i in l, ∀ j, ω / 8 ≤ ‖i.2.2.2.2 - (i.2.2.1 j : ℂ)‖ := by
    filter_upwards [hSev] with i hi
    exact (hHC (i.1 + 1) i.2.1 i.2.2.1 hi.1 hi.2.1 i.2.2.2.1 hi.2.2.1).1 _
      (Gam_subset_nbhd hL _ hi.2.2.2)
  have hmom : ∀ s : ℕ, ∀ r : ℕ, 1 ≤ s → r ≤ s → r ≤ 2 → ∀ᶠ i in l,
      (((i.1 + 1 : ℕ) : ℝ))⁻¹ * ∑ j, (‖i.2.2.2.2 - (i.2.2.1 j : ℂ)‖ ^ s)⁻¹ ≤
        ((4 / ω) ^ s + 4 * E / ((ω / 8) ^ s * ω ^ 2)) * θ i ^ r := by
    intro s r hs hr hr2
    filter_upwards [hSev, hnat1] with i hi h1
    exact ((hHC (i.1 + 1) i.2.1 i.2.2.1 hi.1 hi.2.1 i.2.2.2.1 hi.2.2.1).2.2 s hs _
      (Gam_subset_nbhd hL _ hi.2.2.2)).trans (mom_le hL hE.le hr hr2 h1)
  have hm2 : ∀ᶠ i in l, (((i.1 + 1 : ℕ) : ℝ))⁻¹ * ∑ j, (‖i.2.2.2.2 - (i.2.2.1 j : ℂ)‖ ^ 2)⁻¹ ≤
      (K2 + K3) * θ i ^ 2 := by
    filter_upwards [hmom 2 2 (by norm_num) le_rfl le_rfl] with i hi
    exact hi.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hK3p) (sq_nonneg _))
  have hm3 : ∀ᶠ i in l, (((i.1 + 1 : ℕ) : ℝ))⁻¹ * ∑ j, (‖i.2.2.2.2 - (i.2.2.1 j : ℂ)‖ ^ 3)⁻¹ ≤
      (K2 + K3) * θ i ^ 2 := by
    filter_upwards [hmom 3 2 (by norm_num) (by norm_num) le_rfl] with i hi
    exact hi.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK2p) (sq_nonneg _))
  have hU : Tendsto (fun i : Idx => (∑ j, I * ((κ / ((i.1 + 1 : ℕ) : ℝ) : ℝ) : ℂ) /
      (i.2.2.2.2 - (i.2.2.1 j : ℂ))) - I * κ * G0 i.2.2.2.2) l (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun i => κ * K1 * θ i) ?_ (by simpa using hθ.const_mul (κ * K1))
    filter_upwards [hmom 1 1 le_rfl le_rfl (by norm_num)] with i hb
    simp only [G0, mul_zero, sub_zero, pow_one] at hb ⊢
    have hN0 : (0 : ℝ) < ((i.1 + 1 : ℕ) : ℝ) := by positivity
    calc ‖∑ j, I * ((κ / ((i.1 + 1 : ℕ) : ℝ) : ℝ) : ℂ) / (i.2.2.2.2 - (i.2.2.1 j : ℂ))‖
        ≤ ∑ j, ‖I * ((κ / ((i.1 + 1 : ℕ) : ℝ) : ℝ) : ℂ) / (i.2.2.2.2 - (i.2.2.1 j : ℂ))‖ :=
          norm_sum_le _ _
      _ = κ * ((((i.1 + 1 : ℕ) : ℝ))⁻¹ * ∑ j, ‖i.2.2.2.2 - (i.2.2.1 j : ℂ)‖⁻¹) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [norm_u_eq, abs_of_pos (div_pos hκ hN0)]; ring
      _ ≤ κ * (K1 * θ i) := mul_le_mul_of_nonneg_left hb hκ.le
      _ = κ * K1 * θ i := by ring
  have hGd : ∀ᶠ i in l, DifferentiableAt ℂ G0 (i.2.2.2.2 : ℂ) :=
    Eventually.of_forall fun i => differentiableAt_const _
  have hDlow : ∀ᶠ i in l, η ≤ ‖Df L κ G0 i.2.2.2.2‖ := by
    filter_upwards [hSev] with i hi
    rw [Df_G0]; exact Df_lower hL _ hi.2.2.2
  have hDev : ∀ᶠ i in l, ∀ᶠ w in 𝓝 (i.2.2.2.2 : ℂ), Df L κ G0 w ≠ 0 := by
    filter_upwards [hDlow] with i hi
    have hc : ContinuousAt (Df L κ G0) i.2.2.2.2 := by
      have : Df L κ G0 = fun w => 1 - ef L w := funext (Df_G0 L κ)
      rw [this]; exact continuousAt_const.sub (hasDerivAt_ef L _).continuousAt
    refine hc.eventually_ne fun h0 => ?_
    rw [h0, norm_zero] at hi; linarith
  have hMb : ∀ᶠ i in l, ‖Af κ G0 i.2.2.2.2‖ ≤ M ∧ ‖(Af κ G0 i.2.2.2.2)⁻¹‖ ≤ M ∧
      ‖ef L i.2.2.2.2‖ ≤ M ∧ η ≤ ‖Df L κ G0 i.2.2.2.2‖ := by
    filter_upwards [hSev, hDlow] with i hi hD
    rw [Af_G0, inv_one, norm_one]
    exact ⟨hM0, hM0, norm_ef_le hL _ hi.2.2.2, hD⟩
  have hcore := haar_core (ι := Idx) (l := l) (κ := κ) (L := L) (Nf := fun i => i.1 + 1)
    (qf := fun i => i.2.2.1) (zf := fun i => i.2.2.2.2) (θ := θ) (G := G0) hκ
    (fun i => Nat.succ_pos _) hνt hθ0 hθ (by positivity : (0 : ℝ) < ω / 8) hroot
    (by positivity : (0 : ℝ) ≤ K2 + K3) hm2 hm3 hU hGd hDev hM0 hη hMb
  obtain ⟨hremO, hcorrO, hprops⟩ := hcore
  obtain ⟨Cr, hCr⟩ := hremO.bound
  obtain ⟨Cc, hCc⟩ := hcorrO.bound
  have hsmall : ∀ᶠ i in l, 2 * (κ / ((i.1 + 1 : ℕ) : ℝ)) < ω / 8 := by
    filter_upwards [hνt.eventually (gt_mem_nhds (show (0 : ℝ) < ω / (16 * κ) by positivity))]
      with i hi
    rw [lt_div_iff₀ (by positivity)] at hi
    rw [div_eq_mul_inv]; linarith
  obtain ⟨N0, R0, hext⟩ := ev_extract (hSev.and (hCr.and (hCc.and (hprops.and hsmall))))
  -- constants
  set Crem : ℝ := max Cr 0 with hCrem
  set Ccor : ℝ := max Cc 0 with hCcor
  set A1 : ℝ := ω / (Real.pi * κ) * Crem with hA1
  set A2 : ℝ := ω / Real.pi * Ccor with hA2
  have hCrem0 : 0 ≤ Crem := le_max_right _ _
  have hCcor0 : 0 ≤ Ccor := le_max_right _ _
  have hA10 : 0 ≤ A1 := by positivity
  have hA20 : 0 ≤ A2 := by positivity
  set CE : ℝ := Crem + Ccor + 4 * A1 + 4 * A2 with hCE
  set RE : ℝ := max (max R (R0 : ℝ)) 2 with hREdef
  refine ⟨N0 + 1, RE, CE, Nat.succ_pos _, le_max_right _ _, by positivity, ?_⟩
  intro N n q hNE hcfg hEn
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  have hk : N0 ≤ k := by omega
  have hNr : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hNne : ((k + 1 : ℕ) : ℝ) ≠ 0 := hNr.ne'
  have hκne : κ ≠ 0 := hκ.ne'
  have hpine : Real.pi ≠ 0 := Real.pi_pos.ne'
  -- pointwise data at every admissible contour point
  have hpt : ∀ m : ℤ, RE < |(m : ℝ)| → ∀ z ∈ Gam (lo L m) (hi L m) (ht L),
      (∀ j, 2 * |κ / ((k + 1 : ℕ) : ℝ)| < ‖z - q j‖) ∧
      ‖Wf L κ (κ / ((k + 1 : ℕ) : ℝ)) G0 q z‖ ≤ 1 / 2 ∧
      1 / (2 * M) ≤ ‖aNf L κ (κ / ((k + 1 : ℕ) : ℝ)) G0 q z‖ ∧
      3 * η / 4 ≤ ‖DNf L κ (κ / ((k + 1 : ℕ) : ℝ)) G0 q z‖ ∧
      ‖aNf L κ (κ / ((k + 1 : ℕ) : ℝ)) G0 q z - Af κ G0 z‖ ≤ 1 / (2 * M) ∧
      ‖remG κ L (fun i : Idx => i.1 + 1) (fun i => i.2.2.1) (fun i => i.2.2.2.2) G0
        ⟨k, (n, q, m, z)⟩‖ ≤ Crem / (((k + 1 : ℕ) : ℝ) ^ 2 * (m : ℝ) ^ 2) ∧
      ‖corrf L κ (κ / ((k + 1 : ℕ) : ℝ)) G0 q z‖ ≤ Ccor / (m : ℝ) ^ 2 ∧
      2 * (κ / ((k + 1 : ℕ) : ℝ)) < ω / 8 ∧
      (∀ w ∈ HighContours.nbhd L m, ∀ j, ω / 8 ≤ ‖w - q j‖) ∧
      (∀ j, ((q j : ℂ) ∈ HighContours.rect L m ↔ n j = m)) := by
    intro m hm z hz
    have hRm : R < |(m : ℝ)| := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hm
    have hR0m : (R0 : ℝ) < |(m : ℝ)| :=
      lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hm
    have hmem : (⟨k, (n, q, m, z)⟩ : Idx) ∈ S := ⟨hcfg, hEn, hRm, hz⟩
    have hR0' : R0 ≤ m.natAbs := by
      have : (R0 : ℝ) ≤ (m.natAbs : ℝ) := by rw [hcast]; exact hR0m.le
      exact_mod_cast this
    obtain ⟨-, h1, h2, ⟨h3, h4, h5, h6, h7⟩, h8⟩ := hext _ hmem hk hR0'
    have hm0 : 0 < |(m : ℝ)| := lt_of_lt_of_le (by norm_num) ((le_max_right _ _).trans hm.le)
    have hsq : (m : ℝ) ^ 2 = |(m : ℝ)| ^ 2 := (sq_abs _).symm
    refine ⟨h3, h4, h5, h6, h7, ?_, ?_, h8, (hHC (k + 1) n q hcfg hEn m hRm).1,
      (hHC (k + 1) n q hcfg hEn m hRm).2.1⟩
    · refine h1.trans ((mul_le_mul_of_nonneg_right (le_max_left Cr 0) (norm_nonneg _)).trans
        (le_of_eq ?_))
      show Crem * ‖(((k + 1 : ℕ) : ℝ))⁻¹ * ((((k + 1 : ℕ) : ℝ))⁻¹ * (|(m : ℝ)|⁻¹) ^ 2)‖ = _
      rw [Real.norm_of_nonneg (by positivity), hsq]
      field_simp
    · refine h2.trans ((mul_le_mul_of_nonneg_right (le_max_left Cc 0) (norm_nonneg _)).trans
        (le_of_eq ?_))
      show Ccor * ‖(|(m : ℝ)|⁻¹) ^ 2‖ = _
      rw [Real.norm_of_nonneg (by positivity), hsq]
      field_simp
  -- the free background facts
  have hG0d : ∀ z : ℂ, ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ G0 w :=
    fun z => Eventually.of_forall fun w => differentiableAt_const _
  have hM' : 0 < M := by linarith
  have hDne : ∀ m : ℤ, ∀ z ∈ Gam (lo L m) (hi L m) (ht L), Df L κ G0 z ≠ 0 := by
    intro m z hz h0
    have := Df_lower hL m hz
    rw [← Df_G0 L κ, h0, norm_zero] at this; linarith
  have hcont : ∀ m : ℤ, RE < |(m : ℝ)| → ∀ z ∈ Gam (lo L m) (hi L m) (ht L),
      ContinuousAt (logaNf L κ (κ / ((k + 1 : ℕ) : ℝ)) G0 q) z ∧ ContinuousAt (corrf L κ (κ / ((k + 1 : ℕ) : ℝ)) G0 q) z ∧
        ContinuousAt (ellf (κ / ((k + 1 : ℕ) : ℝ)) q) z ∧ DifferentiableAt ℂ (aNf L κ (κ / ((k + 1 : ℕ) : ℝ)) G0 q) z := by
    intro m hm z hz
    obtain ⟨h3, h4, h5, h6, h7, -⟩ := hpt m hm z hz
    exact contAt_gen hM' hη (hG0d z) h3 (hDne m z hz) h4 h5 h6 h7
      (by rw [Af_G0, inv_one, norm_one]; exact hM0)
  -- the remainder in ellf form
  set r' : ℂ → ℂ := fun z => ellf (κ / ((k + 1 : ℕ) : ℝ)) q z - log (aNf L κ (κ / ((k + 1 : ℕ) : ℝ)) G0 q z) +
    I * κ / ((k + 1 : ℕ) : ℂ) * corrf L κ (κ / ((k + 1 : ℕ) : ℝ)) G0 q z with hr'
  have hrr : ∀ m : ℤ, RE < |(m : ℝ)| → ∀ z ∈ Gam (lo L m) (hi L m) (ht L),
      rN L κ q z = r' z ∧ ‖r' z‖ ≤ Crem / (((k + 1 : ℕ) : ℝ) ^ 2 * (m : ℝ) ^ 2) := by
    intro m hm z hz
    obtain ⟨h3, -, -, -, -, h9, -⟩ := hpt m hm z hz
    have e1 : rN L κ q z = r' z := by
      simp only [rN, hr']
      rw [ellN_eq_ellf κ q h3]
    refine ⟨e1, ?_⟩
    have e2 : r' z = remG κ L (fun i : Idx => i.1 + 1) (fun i => i.2.2.1) (fun i => i.2.2.2.2) G0
        ⟨k, (n, q, m, z)⟩ := by
      simp only [hr', remG, corrf, logaNf_G0]
    rw [e2]; exact h9
  -- the pointwise period error
  have hperiod : ∀ m : ℤ, RE < |(m : ℝ)| →
      |((Finset.univ.filter fun j => n j = m).card : ℝ) - ((k + 1 : ℕ) : ℝ) * C0 L κ q m -
        C1 L κ q m| ≤ A1 / (((k + 1 : ℕ) : ℝ) * (m : ℝ) ^ 2) := by
    intro m hm
    have hlohi : lo L m < hi L m := by simp only [lo, hi]; linarith
    have hh0 : 0 < ht L := by simp only [ht]; linarith
    obtain ⟨-, -, -, -, -, -, -, hsm, hroot', hlab⟩ := hpt m hm _
      (show ((lo L m : ℝ) : ℂ) ∈ Gam (lo L m) (hi L m) (ht L) from
        Or.inr ⟨by simp only [ofReal_im, mem_Icc]; constructor <;> linarith, Or.inl (by simp)⟩)
    have hlo : ((lo L m : ℝ) : ℂ) ∈ HighContours.nbhd L m :=
      Gam_subset_nbhd hL m (Or.inr ⟨by simp only [ofReal_im, mem_Icc]; constructor <;> linarith,
        Or.inl (by simp)⟩)
    have hhi : ((hi L m : ℝ) : ℂ) ∈ HighContours.nbhd L m :=
      Gam_subset_nbhd hL m (Or.inr ⟨by simp only [ofReal_im, mem_Icc]; constructor <;> linarith,
        Or.inr (by simp)⟩)
    have hqa : ∀ j, 2 * (κ / ((k + 1 : ℕ) : ℝ)) < |q j - lo L m| := fun j => by
      have := hroot' _ hlo j
      rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm] at this
      linarith
    have hqb : ∀ j, 2 * (κ / ((k + 1 : ℕ) : ℝ)) < |q j - hi L m| := fun j => by
      have := hroot' _ hhi j
      rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm] at this
      linarith
    have hin : ∀ j, (lo L m < q j ∧ q j < hi L m) ↔ n j = m := fun j => by
      rw [← hlab j]
      simp only [HighContours.rect, mem_ofPred_eq, ofReal_re, ofReal_im, abs_zero, lo, hi]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨abs_lt.2 ⟨by linarith, by linarith⟩, by linarith⟩
      · rintro ⟨h1, -⟩; obtain ⟨h1, h2⟩ := abs_lt.1 h1; exact ⟨by linarith, by linarith⟩
    have hP := period_count hκ (Nat.succ_pos k) q n m (h := ht L) hlohi
      (by simp only [ht, ← hωdef]; linarith) hqa hqb hin
    -- ellf → log a_N, corr, remainder
    have hcm := hcont m hm
    have hlogc : ∀ z ∈ Gam (lo L m) (hi L m) (ht L),
        ContinuousAt (fun z => log (aNf L κ (κ / ((k + 1 : ℕ) : ℝ)) G0 q z)) z := fun z hz => by
      have := (hcm z hz).1; rwa [logaNf_G0] at this
    have hrc : ∀ z ∈ Gam (lo L m) (hi L m) (ht L), ContinuousAt r' z := fun z hz =>
      (((hcm z hz).2.2.1.sub (hlogc z hz)).add (continuousAt_const.mul (hcm z hz).2.1))
    set J0 := LabelExactPeriod.rectIntegral (fun z => log (aNf L κ (κ / ((k + 1 : ℕ) : ℝ)) G0 q z)) (lo L m) (hi L m)
      (ht L) with hJ0
    set J1 := LabelExactPeriod.rectIntegral (corrf L κ (κ / ((k + 1 : ℕ) : ℝ)) G0 q) (lo L m) (hi L m) (ht L) with hJ1
    set Jr := LabelExactPeriod.rectIntegral r' (lo L m) (hi L m) (ht L) with hJr
    have hsplit : LabelExactPeriod.rectIntegral (ellf (κ / ((k + 1 : ℕ) : ℝ)) q) (lo L m) (hi L m) (ht L) =
        J0 + (-(I * κ / ((k + 1 : ℕ) : ℂ))) * J1 + Jr := by
      have e : ellf (κ / ((k + 1 : ℕ) : ℝ)) q = fun z => (log (aNf L κ (κ / ((k + 1 : ℕ) : ℝ)) G0 q z) +
          (-(I * κ / ((k + 1 : ℕ) : ℂ))) * corrf L κ (κ / ((k + 1 : ℕ) : ℝ)) G0 q z) + r' z := by
        funext z; simp only [hr']; ring
      rw [e, rectIntegral_add (f := fun z => log (aNf L κ (κ / ((k + 1 : ℕ) : ℝ)) G0 q z) +
          (-(I * κ / ((k + 1 : ℕ) : ℂ))) * corrf L κ (κ / ((k + 1 : ℕ) : ℝ)) G0 q z) (g := r') hlohi.le hh0.le
          (fun z hz => (hlogc z hz).add (continuousAt_const.mul (hcm z hz).2.1)) hrc,
        rectIntegral_add (f := fun z => log (aNf L κ (κ / ((k + 1 : ℕ) : ℝ)) G0 q z))
          (g := fun z => (-(I * κ / ((k + 1 : ℕ) : ℂ))) * corrf L κ (κ / ((k + 1 : ℕ) : ℝ)) G0 q z) hlohi.le hh0.le
          hlogc (fun z hz => continuousAt_const.mul (hcm z hz).2.1),
        rectIntegral_const_mul]
    have hJrb : ‖Jr‖ ≤ (2 * (hi L m - lo L m) + 4 * ht L) *
        (Crem / (((k + 1 : ℕ) : ℝ) ^ 2 * (m : ℝ) ^ 2)) :=
      norm_rectIntegral_le hlohi.le hh0.le fun z hz => (hrr m hm z hz).2
    have hper : 2 * (hi L m - lo L m) + 4 * ht L = 2 * ω := by simp only [lo, hi, ht, hωdef]; ring
    rw [hper] at hJrb
    -- the complex identity
    set cnt : ℝ := ((Finset.univ.filter fun j => n j = m).card : ℝ) with hcnt
    have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    have hN0 : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_pos k).ne'
    have hW : (cnt : ℂ) - ((((k + 1 : ℕ) : ℝ) * (-(1 / (2 * Real.pi * κ))) : ℝ) : ℂ) * J0 -
        I / (2 * Real.pi) * J1 = -(((k + 1 : ℕ) : ℂ) / (2 * Real.pi * κ)) * Jr := by
      have hc' : (cnt : ℂ) = ((k + 1 : ℕ) : ℂ) * (-(1 / (2 * Real.pi * κ)) *
          (J0 + (-(I * κ / ((k + 1 : ℕ) : ℂ))) * J1 + Jr)) := by
        rw [← hsplit, ← hP]; field_simp
      rw [hc']
      simp only [ofReal_mul, ofReal_neg, ofReal_div, ofReal_one, ofReal_ofNat, ofReal_natCast]
      field_simp
      ring
    have hre : ((cnt : ℂ) - ((((k + 1 : ℕ) : ℝ) * (-(1 / (2 * Real.pi * κ))) : ℝ) : ℂ) * J0 -
        I / (2 * Real.pi) * J1).re = cnt - ((k + 1 : ℕ) : ℝ) * C0 L κ q m - C1 L κ q m := by
      simp only [sub_re, ofReal_re, re_ofReal_mul, C0, C1, ← rect_eq_boundary, hJ0, hJ1]
      ring
    rw [← hre]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [hW, norm_mul, norm_neg, norm_div]
    have hn1 : ‖(((k + 1 : ℕ) : ℂ))‖ = ((k + 1 : ℕ) : ℝ) := by
      rw [Complex.norm_natCast]
    have hn2 : ‖(2 * Real.pi * κ : ℂ)‖ = 2 * Real.pi * κ := by
      rw [show (2 * Real.pi * κ : ℂ) = ((2 * Real.pi * κ : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [hn1, hn2]
    have hm0 : 0 < (m : ℝ) ^ 2 := by
      have : 0 < |(m : ℝ)| := lt_of_lt_of_le (by norm_num) ((le_max_right _ _).trans hm.le)
      rw [← sq_abs]; positivity
    calc ((k + 1 : ℕ) : ℝ) / (2 * Real.pi * κ) * ‖Jr‖
        ≤ ((k + 1 : ℕ) : ℝ) / (2 * Real.pi * κ) *
            (2 * ω * (Crem / (((k + 1 : ℕ) : ℝ) ^ 2 * (m : ℝ) ^ 2))) := by gcongr
      _ = A1 / (((k + 1 : ℕ) : ℝ) * (m : ℝ) ^ 2) := by
          simp only [hA1]; field_simp
  -- the bound on C₁
  have hC1 : ∀ m : ℤ, RE < |(m : ℝ)| → |C1 L κ q m| ≤ A2 / (m : ℝ) ^ 2 := by
    intro m hm
    have hlohi : lo L m < hi L m := by simp only [lo, hi]; linarith
    have hh0 : 0 < ht L := by simp only [ht]; linarith
    have hb := norm_rectIntegral_le hlohi.le hh0.le fun z hz => (hpt m hm z hz).2.2.2.2.2.2.1
    have hper : 2 * (hi L m - lo L m) + 4 * ht L = 2 * ω := by simp only [lo, hi, ht, hωdef]; ring
    rw [hper, rect_eq_boundary] at hb
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_div, Complex.norm_I]
    have hn2 : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
      rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [hn2]
    have hm0 : 0 < (m : ℝ) ^ 2 := by
      have : 0 < |(m : ℝ)| := lt_of_lt_of_le (by norm_num) ((le_max_right _ _).trans hm.le)
      rw [← sq_abs]; positivity
    calc 1 / (2 * Real.pi) * ‖HighContours.boundaryIntegral L m (corrf L κ (κ / ((k + 1 : ℕ) : ℝ)) G0 q)‖
        ≤ 1 / (2 * Real.pi) * (2 * ω * (Ccor / (m : ℝ) ^ 2)) := by gcongr
      _ = A2 / (m : ℝ) ^ 2 := by simp only [hA2]; field_simp
  refine ⟨?_, ?_, ?_, ?_⟩
  -- (i) pointwise
  · intro m hm z hz
    have hz' := Γ_subset_Gam m hz
    obtain ⟨h3, -, -, -, h7, -, h10, -⟩ := hpt m hm z hz'
    obtain ⟨-, -, -, hdiff⟩ := hcont m hm z hz'
    have ha1 : ‖aNf L κ (κ / ((k + 1 : ℕ) : ℝ)) G0 q z - 1‖ ≤ 1 / 2 := by
      rw [Af_G0] at h7
      refine h7.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    refine ⟨h3, quad L κ (κ / ((k + 1 : ℕ) : ℝ)) G0 q (hDne m z hz'), ha1, hdiff, ?_, ?_, ?_⟩
    · rw [LabelExactPeriod.logT_eq (by linarith), add_sub_cancel]
    · rw [(hrr m hm z hz').1]
      exact ((hrr m hm z hz').2).trans (div_le_div_of_nonneg_right (by linarith) (by positivity))
    · exact h10.trans (div_le_div_of_nonneg_right (by linarith) (by positivity))
  -- (ii) pointwise period
  · intro m hm
    refine (hperiod m hm).trans (div_le_div_of_nonneg_right (by linarith) ?_)
    positivity
  -- (iii) summed period
  · intro Rr hRr I hI t ht1
    have hR2 : 2 ≤ Rr := (le_max_right _ _).trans hRr
    have hmI : ∀ m ∈ I, RE < |(m : ℝ)| := fun m hm => lt_of_le_of_lt hRr (hI m hm)
    calc |∑ m ∈ I, t m * (((Finset.univ.filter fun j => n j = m).card : ℝ) -
            ((k + 1 : ℕ) : ℝ) * C0 L κ q m - C1 L κ q m)|
        ≤ ∑ m ∈ I, |t m * (((Finset.univ.filter fun j => n j = m).card : ℝ) -
            ((k + 1 : ℕ) : ℝ) * C0 L κ q m - C1 L κ q m)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ I, A1 / ((k + 1 : ℕ) : ℝ) * (1 / (m : ℝ) ^ 2) := by
          refine Finset.sum_le_sum fun m hm => ?_
          rw [abs_mul]
          have h1 := hperiod m (hmI m hm)
          have h2 : A1 / (((k + 1 : ℕ) : ℝ) * (m : ℝ) ^ 2) =
              A1 / ((k + 1 : ℕ) : ℝ) * (1 / (m : ℝ) ^ 2) := by
            rw [div_mul_div_comm, mul_one]
          rw [← h2]
          exact (mul_le_mul_of_nonneg_right (ht1 m) (abs_nonneg _)).trans (by rw [one_mul]; exact h1)
      _ = A1 / ((k + 1 : ℕ) : ℝ) * ∑ m ∈ I, 1 / (m : ℝ) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ A1 / ((k + 1 : ℕ) : ℝ) * (4 / Rr) :=
          mul_le_mul_of_nonneg_left (finite_tail hR2 I hI) (by positivity)
      _ ≤ CE / (((k + 1 : ℕ) : ℝ) * Rr) := by
          rw [div_mul_div_comm, mul_comm (A1 : ℝ) 4]
          exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  -- (iv) tail of C₁
  · intro Rr hRr
    have hR2 : 2 ≤ Rr := (le_max_right _ _).trans hRr
    obtain ⟨hs, ht⟩ := tsum_tail hR2
    have hle : ∀ m : ℤ, (if Rr < |(m : ℝ)| then |C1 L κ q m| else 0) ≤
        A2 * (if Rr < |(m : ℝ)| then 1 / (m : ℝ) ^ 2 else 0) := fun m => by
      split_ifs with h
      · rw [mul_one_div]; exact hC1 m (lt_of_le_of_lt hRr h)
      · rw [mul_zero]
    have hnn : ∀ m : ℤ, 0 ≤ (if Rr < |(m : ℝ)| then |C1 L κ q m| else 0) := fun m => by
      split_ifs <;> positivity
    have hs2 := hs.mul_left A2
    have hs' := Summable.of_nonneg_of_le hnn hle hs2
    refine ⟨hs', (hs'.tsum_le_tsum hle hs2).trans ?_⟩
    rw [tsum_mul_left]
    calc A2 * ∑' m : ℤ, (if Rr < |(m : ℝ)| then 1 / (m : ℝ) ^ 2 else 0) ≤ A2 * (4 / Rr) :=
          mul_le_mul_of_nonneg_left ht hA20
      _ ≤ CE / Rr := by
          rw [mul_div_assoc', mul_comm A2 4]
          exact div_le_div_of_nonneg_right (by linarith) (by linarith)

end QuantumNLS.HaarSummableReconstruction

#print axioms QuantumNLS.HaarSummableReconstruction.Df_lower
#print axioms QuantumNLS.HaarSummableReconstruction.period_count
#print axioms QuantumNLS.HaarSummableReconstruction.haar_summable_reconstruction
