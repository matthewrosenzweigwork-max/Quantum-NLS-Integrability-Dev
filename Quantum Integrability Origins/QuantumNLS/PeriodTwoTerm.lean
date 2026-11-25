import QuantumNLS.PeriodReconstruction

/-!
# PROP-006 `thm:B3-period-reconstruction` (label_periods.tex:338-442): the complete statement

On PR1 (`PeriodReconstruction` `3ff1c246…`, own, read-only) and EP1 (`LabelExactPeriod`
`5eebcfca…`):
* `ellN_eq_ellf` — the ℓ_N bridge: on `Γ` the Taylor-series `ℓ_N` of EP1 (`ellN`, the definition
  prescribed in label_periods.tex:258-266) equals the principal-log `ellf` used in PR1;
* `eventual_props`, `setup` — the eventual uniform bounds on `Γ` (as in BO1/PR1);
* `contAt_props` — `log a_N`, `a_N'` and `ℓ_N` are continuous at the points of `Γ` (`a_N` is
  holomorphic near `Γ`);
* `rectIntegral_add`, `rectIntegral_const_mul`, `norm_rectIntegral_le` (`|∮ f| ≤ perimeter · sup`);
* **`two_term_period`** (eq:B3-two-term-period): `m_n/N = −(1/(2πκ)) ∮ log a_N +
  (i/(2πN)) ∮ e^{izL}a_N'/(a_N(a_N² − e^{izL})) + O(N^{-2})`;
* **`log_reconstruction_uniform`**, **`two_term_period_uniform`** — the uniformity clause: one
  constant, a weak neighbourhood `U` of `μ` and `N₀` serve every on-shell configuration with
  `N ≥ N₀` and `L_N ∈ U` (PROP-003-style contradiction argument);
* **`period_reconstruction`** — PROP-006 as one theorem.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000
noncomputable section

open MeasureTheory Complex Filter Topology Asymptotics Set

namespace QuantumNLS.PeriodTwoTerm

open QuantumNLS.PeriodReconstructionCore QuantumNLS.PeriodReconstructionAsymp
  QuantumNLS.PeriodReconstructionBigO QuantumNLS.PeriodReconstruction
  QuantumNLS.LabelJointLimit QuantumNLS.LabelJointWeak QuantumNLS.LabelBlock
  QuantumNLS.IndexedScalarMeasure QuantumNLS.IndexedScalarMeasureCuts QuantumNLS.EmpiricalRapidity

/-! ## 1. Eventual bounds (as in BO1) -/

section Generic

variable {κ L : ℝ} {N : ℕ → ℕ} {q : ∀ k, Fin (N k) → ℝ} {G : ℂ → ℂ} {Γ : Set ℂ}

theorem eventual_props (hκ : 0 < κ) (hN : ∀ k, 0 < N k) (hNtop : Tendsto N atTop atTop)
    {d : ℝ} (hd : 0 < d) (hroot : ∀ᶠ k in atTop, ∀ z ∈ Γ, ∀ j, d ≤ ‖z - q k j‖)
    (hU : Tendsto (fun p : ℕ × ℂ => (∑ j, I * ((κ / N p.1 : ℝ) : ℂ) / (p.2 - (q p.1 j : ℂ))) -
      I * κ * G p.2) (atTop ×ˢ 𝓟 Γ) (𝓝 0))
    (_hGd : ∀ z ∈ Γ, DifferentiableAt ℂ G z) (_hDev : ∀ z ∈ Γ, ∀ᶠ w in 𝓝 z, Df L κ G w ≠ 0)
    {M η : ℝ} (hM0 : 1 ≤ M) (hη : 0 < η)
    (hM : ∀ z ∈ Γ, ‖Af κ G z‖ ≤ M ∧ ‖(Af κ G z)⁻¹‖ ≤ M ∧ ‖ef L z‖ ≤ M ∧ η ≤ ‖Df L κ G z‖) :
    ∀ᶠ p in atTop ×ˢ 𝓟 Γ, (∀ j, 2 * |κ / (N p.1 : ℝ)| < ‖p.2 - (q p.1 j : ℂ)‖) ∧
      ‖Wf L κ (κ / N p.1) G (q p.1) p.2‖ ≤ 1 / 2 ∧
      1 / (2 * M) ≤ ‖aNf L κ (κ / N p.1) G (q p.1) p.2‖ ∧
      3 * η / 4 ≤ ‖DNf L κ (κ / N p.1) G (q p.1) p.2‖ ∧
      ‖aNf L κ (κ / N p.1) G (q p.1) p.2 - Af κ G p.2‖ ≤ 1 / (2 * M) := by
  set l : Filter (ℕ × ℂ) := atTop ×ˢ 𝓟 Γ with hl
  set ν : ℕ × ℂ → ℝ := fun p => (N p.1 : ℝ)⁻¹ with hνdef
  have hν0 : ∀ p, 0 < ν p := fun p => inv_pos.2 (Nat.cast_pos.2 (hN p.1))
  have hνsq0 : ∀ p, 0 ≤ ν p ^ 2 := fun p => sq_nonneg _
  have habsc : ∀ p : ℕ × ℂ, |κ / (N p.1 : ℝ)| = κ * ν p := fun p => by
    rw [abs_of_pos (div_pos hκ (Nat.cast_pos.2 (hN p.1))), div_eq_mul_inv]
  have hNν : ∀ p : ℕ × ℂ, (N p.1 : ℝ) * ν p = 1 := fun p =>
    mul_inv_cancel₀ (Nat.cast_pos.2 (hN p.1)).ne'
  have hν : Tendsto ν l (𝓝 0) :=
    (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hNtop)).comp tendsto_fst
  have hmem : ∀ᶠ p in l, p.2 ∈ Γ :=
    Filter.eventually_prod_principal_iff.2 (Eventually.of_forall fun _ _ h => h)
  have hroot' : ∀ᶠ p in l, ∀ j, d ≤ ‖p.2 - (q p.1 j : ℂ)‖ :=
    Filter.eventually_prod_principal_iff.2 hroot
  have hsmall : ∀ᶠ p in l, 4 * |κ / (N p.1 : ℝ)| ≤ d := by
    have := hν.eventually (ge_mem_nhds (show (0 : ℝ) < d / (4 * κ) by positivity))
    filter_upwards [this] with p hp
    rw [habsc]; rw [le_div_iff₀ (by positivity)] at hp; linarith
  have hc2 : ∀ᶠ p in l, 2 * |κ / (N p.1 : ℝ)| ≤ d :=
    hsmall.mono fun p hp => by linarith [abs_nonneg (κ / (N p.1 : ℝ))]
  have hc2' : ∀ᶠ p in l, 2 * |-(κ / (N p.1 : ℝ))| ≤ d :=
    hc2.mono fun p hp => by rwa [abs_neg]
  have hdist : ∀ᶠ p in l, ∀ j, 2 * |κ / (N p.1 : ℝ)| < ‖p.2 - (q p.1 j : ℂ)‖ := by
    filter_upwards [hroot', hsmall] with p h1 h2 j
    have := h1 j; linarith [abs_nonneg (κ / (N p.1 : ℝ))]
  have hdist' : ∀ᶠ p in l, ∀ j, 2 * |-(κ / (N p.1 : ℝ))| < ‖p.2 - (q p.1 j : ℂ)‖ :=
    hdist.mono fun p h j => by rw [abs_neg]; exact h j
  have hνle : ∀ᶠ p in l, ν p ≤ 1 := hν.eventually (ge_mem_nhds one_pos)
  -- background bounds
  have hbg : ∀ᶠ p in l, ‖Af κ G p.2‖ ≤ M ∧ ‖(Af κ G p.2)⁻¹‖ ≤ M ∧ ‖ef L p.2‖ ≤ M ∧
      η ≤ ‖Df L κ G p.2‖ := hmem.mono fun p hp => hM p.2 hp
  -- the main functions
  set AN : ℕ × ℂ → ℂ := fun p => ANf (κ / N p.1) (q p.1) p.2 with hAN
  set BN : ℕ × ℂ → ℂ := fun p => ANf (-(κ / N p.1)) (q p.1) p.2 with hBN
  set ℓ : ℕ × ℂ → ℂ := fun p => ellf (κ / N p.1) (q p.1) p.2 with hℓ
  set ℓB : ℕ × ℂ → ℂ := fun p => ellf (-(κ / N p.1)) (q p.1) p.2 with hℓB
  set dl : ℕ × ℂ → ℂ := fun p => dellf (κ / N p.1) (q p.1) p.2 with hdl
  set dlB : ℕ × ℂ → ℂ := fun p => dellf (-(κ / N p.1)) (q p.1) p.2 with hdlB
  set e : ℕ × ℂ → ℂ := fun p => ef L p.2 with he
  set A : ℕ × ℂ → ℂ := fun p => Af κ G p.2 with hA
  set Dd : ℕ × ℂ → ℂ := fun p => Df L κ G p.2 with hDd
  set s : ℕ × ℂ → ℂ := fun p => sf L κ G p.2 with hs
  set sN : ℕ × ℂ → ℂ := fun p => sNf L (κ / N p.1) (q p.1) p.2 with hsN
  set W : ℕ × ℂ → ℂ := fun p => Wf L κ (κ / N p.1) G (q p.1) p.2 with hW
  set DN : ℕ × ℂ → ℂ := fun p => DNf L κ (κ / N p.1) G (q p.1) p.2 with hDN
  set a : ℕ × ℂ → ℂ := fun p => aNf L κ (κ / N p.1) G (q p.1) p.2 with ha
  set a' : ℕ × ℂ → ℂ := fun p => deriv (aNf L κ (κ / N p.1) G (q p.1)) p.2 with ha'
  set Sc : ℕ × ℂ → ℂ := fun p => ∑ j, I * ((κ / N p.1 : ℝ) : ℂ) / (p.2 - (q p.1 j : ℂ)) with hSc
  -- S1: leading log
  have hS1 : (fun p => ℓ p - Sc p) =O[l] ν := by
    refine bigO_of_le ((κ / d) ^ 2) (fun p => (hν0 p).le) ?_
    filter_upwards [hroot', hc2] with p h1 h2
    have := ell_lin hd h2 h1
    calc ‖ℓ p - Sc p‖ ≤ N p.1 * (|κ / (N p.1 : ℝ)| / d) ^ 2 := this
      _ = (κ / d) ^ 2 * ν p * ((N p.1 : ℝ) * ν p) := by rw [habsc]; ring
      _ = (κ / d) ^ 2 * ν p := by rw [hNν, mul_one]
  have hS1B : (fun p => ℓB p + Sc p) =O[l] ν := by
    refine bigO_of_le ((κ / d) ^ 2) (fun p => (hν0 p).le) ?_
    filter_upwards [hroot', hc2'] with p h1 h2
    have := ell_lin hd h2 h1
    have e1 : ∑ j, I * (((-(κ / N p.1)) : ℝ) : ℂ) / (p.2 - (q p.1 j : ℂ)) = -Sc p := by
      simp only [hSc]; rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_; push_cast; ring
    rw [e1, sub_neg_eq_add] at this
    calc ‖ℓB p + Sc p‖ ≤ N p.1 * (|-(κ / (N p.1 : ℝ))| / d) ^ 2 := this
      _ = (κ / d) ^ 2 * ν p * ((N p.1 : ℝ) * ν p) := by rw [abs_neg, habsc]; ring
      _ = (κ / d) ^ 2 * ν p := by rw [hNν, mul_one]
  have hT1 : Tendsto (fun p => ℓ p - I * κ * G p.2) l (𝓝 0) := by
    have := (hS1.trans_tendsto hν).add hU
    rw [add_zero] at this
    exact this.congr' (Eventually.of_forall fun p => by
      show ℓ p - Sc p + (Sc p - I * κ * G p.2) = ℓ p - I * κ * G p.2; ring)
  have hT1B : Tendsto (fun p => ℓB p + I * κ * G p.2) l (𝓝 0) := by
    have := (hS1B.trans_tendsto hν).sub hU
    rw [sub_zero] at this
    exact this.congr' (Eventually.of_forall fun p => by
      show ℓB p + Sc p - (Sc p - I * κ * G p.2) = ℓB p + I * κ * G p.2; ring)
  -- generic helpers
  have tz : ∀ {f g : ℕ × ℂ → ℂ} (K : ℝ), (∀ᶠ p in l, ‖f p‖ ≤ K * ‖g p‖) →
      Tendsto g l (𝓝 0) → Tendsto f l (𝓝 0) := fun K h hg =>
    squeeze_zero_norm' h (by simpa using hg.norm.const_mul K)
  have evb : ∀ {f : ℕ × ℂ → ℂ}, Tendsto f l (𝓝 0) → ∀ {r : ℝ}, 0 < r →
      ∀ᶠ p in l, ‖f p‖ ≤ r := fun h r hr =>
    (h.eventually (Metric.closedBall_mem_nhds 0 hr)).mono fun p hp => mem_closedBall_zero_iff.1 hp
  have hνν : (fun p => ν p ^ 2) =O[l] ν :=
    IsBigO.of_bound 1 (hνle.mono fun p hp => by
      rw [Real.norm_of_nonneg (hνsq0 p), Real.norm_of_nonneg (hν0 p).le, one_mul, sq]
      exact mul_le_of_le_one_left (hν0 p).le hp)
  -- S3, S4: A_N → A and B_N → A⁻¹
  have hANexp : ∀ᶠ p in l, AN p = exp (ℓ p) := hdist.mono fun p h => AN_eq_exp h
  have hBNexp : ∀ᶠ p in l, BN p = exp (ℓB p) := hdist'.mono fun p h => AN_eq_exp h
  have hT3 : Tendsto (fun p => AN p - A p) l (𝓝 0) := by
    refine tz M ?_ (tendsto_exp_sub_one hT1)
    filter_upwards [hANexp, hbg] with p h1 h2
    have e1 : AN p - A p = A p * (exp (ℓ p - I * κ * G p.2) - 1) := by
      rw [h1]; show exp (ℓ p) - exp (I * κ * G p.2) = exp (I * κ * G p.2) * _
      rw [mul_sub, ← exp_add, add_sub_cancel, mul_one]
    rw [e1, norm_mul]; exact mul_le_mul_of_nonneg_right h2.1 (norm_nonneg _)
  have hT4 : Tendsto (fun p => BN p - (A p)⁻¹) l (𝓝 0) := by
    refine tz M ?_ (tendsto_exp_sub_one hT1B)
    filter_upwards [hBNexp, hbg] with p h1 h2
    have hAi : (A p)⁻¹ = exp (-(I * κ * G p.2)) := by
      show (exp (I * κ * G p.2))⁻¹ = _; rw [exp_neg]
    have e1 : BN p - (A p)⁻¹ = (A p)⁻¹ * (exp (ℓB p + I * κ * G p.2) - 1) := by
      rw [h1, hAi, mul_sub, ← exp_add, mul_one]; congr 2; ring
    rw [e1, norm_mul]; exact mul_le_mul_of_nonneg_right h2.2.1 (norm_nonneg _)
  -- S5: s_N → s
  have hsN_eq : ∀ p, sN p = AN p + e p * BN p := fun p => rfl
  have hs_eq : ∀ p, s p = A p + e p * (A p)⁻¹ := fun p => by
    show Af κ G p.2 + ef L p.2 / Af κ G p.2 = _; rw [div_eq_mul_inv]
  have hD_eq : ∀ p, Dd p = A p - e p * (A p)⁻¹ := fun p => by
    show Af κ G p.2 - ef L p.2 / Af κ G p.2 = _; rw [div_eq_mul_inv]
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
      show (sNf L (κ / N p.1) (q p.1) p.2 ^ 2 - sf L κ G p.2 ^ 2) / Df L κ G p.2 ^ 2 = _
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
      show Df L κ G p.2 * (1 + Wf L κ (κ / N p.1) G (q p.1) p.2) ^ ((2 : ℂ)⁻¹) -
        Df L κ G p.2 = _
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
  filter_upwards [hdist, hbd, hev] with p h1 h2 h3
  exact ⟨h1, h2.2.2.2.2.2.2.2, h2.2.2.1, h2.2.2.2.2.2.1, h3.1.1.2⟩

end Generic

/-! ## 2. Setup (as in PR1) -/

theorem setup {L κ : ℝ} (S : IndexedScalarMeasureCuts L κ)
    {μ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ) = S.μ) {N : ℕ → ℕ} {hN : ∀ k, 0 < N k}
    {B : ∀ k, OnShellBethe L κ (N k)}
    (hconv : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ)) (hNtop : Tendsto N atTop atTop)
    {n : ℤ} {xm xp h : ℝ} (hxm : xm ∈ S.cuts) (hxp : xp ∈ S.cuts) (hlt : xm < xp) (hh : 0 < h)
    (h1 : 2 * Real.pi * (n - 1) < exteriorForce L κ S.μ xm)
    (h2 : exteriorForce L κ S.μ xm < 2 * Real.pi * n)
    (h3 : 2 * Real.pi * n < exteriorForce L κ S.μ xp)
    (h4 : exteriorForce L κ S.μ xp < 2 * Real.pi * (n + 1)) :
    ∃ d > 0, ∃ d0 > 0, ∃ M η : ℝ, 1 ≤ M ∧ 0 < η ∧
      (∀ᶠ k in atTop, ∀ z ∈ Gam xm xp h, ∀ j, d ≤ ‖z - (B k).q j‖) ∧
      (∀ z ∈ Gam xm xp h, ∀ t ∈ S.μ.support, d0 ≤ ‖z - t‖) ∧
      Tendsto (fun p : ℕ × ℂ => (∑ j, I * ((κ / N p.1 : ℝ) : ℂ) / (p.2 - ((B p.1).q j : ℂ))) -
        I * κ * cauchyTransform S.μ p.2) (atTop ×ˢ 𝓟 (Gam xm xp h)) (𝓝 0) ∧
      (∀ z ∈ Gam xm xp h, DifferentiableAt ℂ (cauchyTransform S.μ) z) ∧
      (∀ z ∈ Gam xm xp h, ∀ᶠ w in 𝓝 z, Df L κ (cauchyTransform S.μ) w ≠ 0) ∧
      (∀ z ∈ Gam xm xp h, ‖Af κ (cauchyTransform S.μ) z‖ ≤ M ∧
        ‖(Af κ (cauchyTransform S.μ) z)⁻¹‖ ≤ M ∧ ‖ef L z‖ ≤ M ∧
        η ≤ ‖Df L κ (cauchyTransform S.μ) z‖) := by
  have : IsProbabilityMeasure S.μ := S.isProb
  have hL := S.hL
  have hκ := S.hκ
  set G := cauchyTransform S.μ with hG
  set Γ := Gam xm xp h with hΓ
  have hΓc : IsCompact Γ := isCompact_Gam xm xp h
  -- distance of Γ from the support
  obtain ⟨rm, hrm, hbm⟩ := Metric.isOpen_iff.1 Measure.isClosed_support.isOpen_compl xm
    (S.cuts_sub hxm)
  obtain ⟨rp, hrp, hbp⟩ := Metric.isOpen_iff.1 Measure.isClosed_support.isOpen_compl xp
    (S.cuts_sub hxp)
  have hsm : ∀ t ∈ S.μ.support, min rm rp ≤ |t - xm| := fun t ht => by
    by_contra hc; push Not at hc
    exact hbm (by rw [Metric.mem_ball, Real.dist_eq]; exact lt_of_lt_of_le hc (min_le_left _ _)) ht
  have hsp : ∀ t ∈ S.μ.support, min rm rp ≤ |t - xp| := fun t ht => by
    by_contra hc; push Not at hc
    exact hbp (by rw [Metric.mem_ball, Real.dist_eq]; exact lt_of_lt_of_le hc (min_le_right _ _)) ht
  set d0 := min (min rm rp) h with hd0def
  have hd0 : 0 < d0 := by positivity
  have hsupp : ∀ z ∈ Γ, ∀ t ∈ S.μ.support, d0 ≤ ‖z - t‖ := fun z hz t ht =>
    Gam_dist hh (hsm t ht) (hsp t ht) hz
  -- roots
  obtain ⟨δ, hδ, hblock⟩ := label_block_seq S hμ hconv hNtop hxm hxp hlt h1 h2 h3 h4
  set d := min δ h with hddef
  have hd : 0 < d := by positivity
  have hroot : ∀ᶠ k in atTop, ∀ z ∈ Γ, ∀ j, d ≤ ‖z - (B k).q j‖ :=
    hblock.mono fun k hk z hz j => Gam_dist hh (hk j).2.1 (hk j).2.2 hz
  -- uniform convergence
  set d1 := min d d0
  have hd1 : 0 < d1 := by positivity
  have hU0 := unif_conv hconv hΓc hd1 (fun z hz t ht => by
      rw [hμ] at ht; exact (min_le_right _ _).trans (hsupp z hz t ht))
    (hroot.mono fun k hk z hz j => (min_le_left _ _).trans (hk z hz j))
  rw [hμ] at hU0
  have hU : Tendsto (fun p : ℕ × ℂ => (∑ j, I * ((κ / N p.1 : ℝ) : ℂ) / (p.2 - ((B p.1).q j : ℂ))) -
      I * κ * G p.2) (atTop ×ˢ 𝓟 Γ) (𝓝 0) := by
    have := hU0.const_mul (I * κ)
    rw [mul_zero] at this
    refine this.congr' (Eventually.of_forall fun p => ?_)
    show I * κ * (((N p.1 : ℝ)⁻¹ : ℂ) * ∑ j, (p.2 - ((B p.1).q j : ℂ))⁻¹ - G p.2) =
      (∑ j, I * ((κ / N p.1 : ℝ) : ℂ) / (p.2 - ((B p.1).q j : ℂ))) - I * κ * G p.2
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast; ring
  -- background
  have hGd : ∀ z ∈ Γ, DifferentiableAt ℂ G z := fun z hz =>
    differentiableAt_cauchy S.μ hd0 (hsupp z hz)
  have hDz : ∀ z ∈ Γ, Df L κ G z ≠ 0 := by
    intro z hz
    rcases Gam_im_ne_zero_or hh hz with him | hreal
    · exact D_ne_zero_of_im hL hκ (im_sign_cauchy S.μ him)
    · rcases hreal with rfl | rfl
      · exact D_ne_zero_real S.μ (F_not_mem h1 h2)
      · exact D_ne_zero_real S.μ (F_not_mem (n := n + 1) (by push_cast; linarith)
          (by push_cast; linarith))
  have hDc : ∀ z ∈ Γ, ContinuousAt (Df L κ G) z := fun z hz => by
    have hA : ContinuousAt (Af κ G) z := ((hGd z hz).continuousAt.const_mul (I * κ)).cexp
    have he : ContinuousAt (ef L) z := (hasDerivAt_ef L z).continuousAt
    exact hA.sub (he.div hA (exp_ne_zero _))
  have hDev : ∀ z ∈ Γ, ∀ᶠ w in 𝓝 z, Df L κ G w ≠ 0 := fun z hz =>
    (hDc z hz).eventually_ne (hDz z hz)
  obtain ⟨z0, hz0, hmin⟩ := hΓc.exists_isMinOn (Gam_nonempty hlt.le)
    (f := fun z => ‖Df L κ G z‖) (fun z hz => (hDc z hz).norm.continuousWithinAt)
  set η := ‖Df L κ G z0‖
  have hη : 0 < η := norm_pos_iff.2 (hDz z0 hz0)
  set M := max 1 (max (Real.exp (κ / d0)) (Real.exp (L * h)))
  have hM0 : 1 ≤ M := le_max_left _ _
  have hM : ∀ z ∈ Γ, ‖Af κ G z‖ ≤ M ∧ ‖(Af κ G z)⁻¹‖ ≤ M ∧ ‖ef L z‖ ≤ M ∧
      η ≤ ‖Df L κ G z‖ := by
    intro z hz
    have hGb := norm_cauchy_le S.μ hd0 (hsupp z hz)
    have himG : |(G z).im| ≤ 1 / d0 := (Complex.abs_im_le_norm _).trans hGb
    have hk : κ * |(G z).im| ≤ κ / d0 := by
      rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left himG hκ.le
    have hzim := Gam_abs_im hh hz
    have hexp1 : Real.exp (κ / d0) ≤ M := (le_max_left _ _).trans (le_max_right _ _)
    have hexp2 : Real.exp (L * h) ≤ M := (le_max_right _ _).trans (le_max_right _ _)
    refine ⟨?_, ?_, ?_, hmin hz⟩
    · rw [norm_Af]
      refine (Real.exp_le_exp.2 ?_).trans hexp1
      nlinarith [neg_abs_le (G z).im, le_abs_self (G z).im]
    · rw [norm_inv_Af]
      refine (Real.exp_le_exp.2 ?_).trans hexp1
      nlinarith [neg_abs_le (G z).im, le_abs_self (G z).im]
    · rw [norm_ef]
      refine (Real.exp_le_exp.2 ?_).trans hexp2
      nlinarith [neg_abs_le z.im, le_abs_self z.im]
  exact ⟨d, hd, d0, hd0, M, η, hM0, hη, hroot, hsupp, hU, hGd, hDev, hM⟩

/-! ## 3. The ℓ_N bridge -/

/-- On points `2|c|` away from all roots, EP1's Taylor-series `ℓ_N` equals `ellf`. -/
lemma ellN_eq_ellf (κ : ℝ) {N : ℕ} (q : Fin N → ℝ) {z : ℂ}
    (hz : ∀ j, 2 * |κ / (N : ℝ)| < ‖z - q j‖) :
    LabelExactPeriod.ellN κ q z = ellf (κ / N) q z := by
  unfold LabelExactPeriod.ellN ellf
  refine Finset.sum_congr rfl fun j _ => LabelExactPeriod.logT_eq ?_
  have h1 := hz j
  have hpos : 0 < ‖z - q j‖ := lt_of_le_of_lt (by positivity) h1
  rw [norm_div, norm_Ic, div_lt_one hpos]
  linarith [abs_nonneg (κ / (N : ℝ))]

/-! ## 4. Rectangle integrals over `Γ` -/

lemma bot_mem {a b h x : ℝ} (hab : a ≤ b) (hx : x ∈ uIcc a b) :
    (x : ℂ) + ((-h : ℝ) : ℂ) * I ∈ Gam a b h := by
  rw [uIcc_of_le hab] at hx
  exact Or.inl ⟨by simpa using hx, Or.inl (by simp)⟩

lemma top_mem {a b h x : ℝ} (hab : a ≤ b) (hx : x ∈ uIcc a b) :
    (x : ℂ) + h * I ∈ Gam a b h := by
  rw [uIcc_of_le hab] at hx
  exact Or.inl ⟨by simpa using hx, Or.inr (by simp)⟩

lemma right_mem {a b h y : ℝ} (hh : 0 ≤ h) (hy : y ∈ uIcc (-h) h) :
    (b : ℂ) + y * I ∈ Gam a b h := by
  rw [uIcc_of_le (by linarith)] at hy
  exact Or.inr ⟨by simpa using hy, Or.inr (by simp)⟩

lemma left_mem {a b h y : ℝ} (hh : 0 ≤ h) (hy : y ∈ uIcc (-h) h) :
    (a : ℂ) + y * I ∈ Gam a b h := by
  rw [uIcc_of_le (by linarith)] at hy
  exact Or.inr ⟨by simpa using hy, Or.inl (by simp)⟩

lemma rectIntegral_add {f g : ℂ → ℂ} {a b h : ℝ} (hab : a ≤ b) (hh : 0 ≤ h)
    (hf : ∀ z ∈ Gam a b h, ContinuousAt f z) (hg : ∀ z ∈ Gam a b h, ContinuousAt g z) :
    LabelExactPeriod.rectIntegral (fun z => f z + g z) a b h =
      LabelExactPeriod.rectIntegral f a b h + LabelExactPeriod.rectIntegral g a b h := by
  unfold LabelExactPeriod.rectIntegral
  rw [intervalIntegral.integral_add
      (LabelExactPeriod.ii_h fun x hx => hf _ (bot_mem hab hx))
      (LabelExactPeriod.ii_h fun x hx => hg _ (bot_mem hab hx)),
    intervalIntegral.integral_add
      (LabelExactPeriod.ii_h fun x hx => hf _ (top_mem hab hx))
      (LabelExactPeriod.ii_h fun x hx => hg _ (top_mem hab hx)),
    intervalIntegral.integral_add
      (LabelExactPeriod.ii_v fun y hy => hf _ (right_mem hh hy))
      (LabelExactPeriod.ii_v fun y hy => hg _ (right_mem hh hy)),
    intervalIntegral.integral_add
      (LabelExactPeriod.ii_v fun y hy => hf _ (left_mem hh hy))
      (LabelExactPeriod.ii_v fun y hy => hg _ (left_mem hh hy))]
  simp only [smul_add]
  ring

lemma rectIntegral_const_mul (c : ℂ) (f : ℂ → ℂ) (a b h : ℝ) :
    LabelExactPeriod.rectIntegral (fun z => c * f z) a b h =
      c * LabelExactPeriod.rectIntegral f a b h := by
  unfold LabelExactPeriod.rectIntegral
  simp only [intervalIntegral.integral_const_mul, smul_eq_mul]
  ring

lemma norm_rectIntegral_le {f : ℂ → ℂ} {a b h K : ℝ} (hab : a ≤ b) (hh : 0 ≤ h)
    (hK : ∀ z ∈ Gam a b h, ‖f z‖ ≤ K) :
    ‖LabelExactPeriod.rectIntegral f a b h‖ ≤ (2 * (b - a) + 4 * h) * K := by
  unfold LabelExactPeriod.rectIntegral
  have h1 : ‖∫ x in a..b, f (x + ((-h : ℝ) : ℂ) * I)‖ ≤ K * |b - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun x hx =>
      hK _ (bot_mem hab (uIoc_subset_uIcc hx))
  have h2 : ‖∫ x in a..b, f (x + h * I)‖ ≤ K * |b - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun x hx =>
      hK _ (top_mem hab (uIoc_subset_uIcc hx))
  have h3 : ‖∫ y in (-h)..h, f (b + y * I)‖ ≤ K * |h - -h| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun y hy =>
      hK _ (right_mem hh (uIoc_subset_uIcc hy))
  have h4 : ‖∫ y in (-h)..h, f (a + y * I)‖ ≤ K * |h - -h| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun y hy =>
      hK _ (left_mem hh (uIoc_subset_uIcc hy))
  rw [abs_of_nonneg (by linarith)] at h1 h2
  rw [abs_of_nonneg (by linarith)] at h3 h4
  have e1 : ‖I • ∫ y in (-h)..h, f (b + y * I)‖ = ‖∫ y in (-h)..h, f (b + y * I)‖ := by
    rw [norm_smul, Complex.norm_I, one_mul]
  have e2 : ‖I • ∫ y in (-h)..h, f (a + y * I)‖ = ‖∫ y in (-h)..h, f (a + y * I)‖ := by
    rw [norm_smul, Complex.norm_I, one_mul]
  calc _ ≤ ‖(∫ x in a..b, f (x + ((-h : ℝ) : ℂ) * I)) - (∫ x in a..b, f (x + h * I)) +
          I • (∫ y in (-h)..h, f (b + y * I))‖ + ‖I • ∫ y in (-h)..h, f (a + y * I)‖ :=
        norm_sub_le _ _
    _ ≤ ‖∫ x in a..b, f (x + ((-h : ℝ) : ℂ) * I)‖ + ‖∫ x in a..b, f (x + h * I)‖ +
          ‖I • ∫ y in (-h)..h, f (b + y * I)‖ + ‖I • ∫ y in (-h)..h, f (a + y * I)‖ := by
        gcongr
        exact (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
    _ ≤ _ := by rw [e1, e2]; linarith

/-! ## 5. Continuity at the points of `Γ` -/

/-- The correction integrand `e^{izL} a_N'/(a_N(a_N² − e^{izL}))`. -/
def corrf (L κ c : ℝ) (G : ℂ → ℂ) {N : ℕ} (q : Fin N → ℝ) (z : ℂ) : ℂ :=
  ef L z * deriv (aNf L κ c G q) z / (aNf L κ c G q z * (aNf L κ c G q z ^ 2 - ef L z))

lemma contAt_props {L κ c : ℝ} (μ : Measure ℝ) [IsProbabilityMeasure μ] {N : ℕ}
    {q : Fin N → ℝ} {z : ℂ} {d0 M η : ℝ} (hd0 : 0 < d0) (hM : 0 < M) (hη : 0 < η)
    (hS : ∀ t ∈ μ.support, d0 ≤ ‖z - t‖) (hR : ∀ j, 2 * |c| < ‖z - q j‖)
    (hDz : Df L κ (cauchyTransform μ) z ≠ 0)
    (hW : ‖Wf L κ c (cauchyTransform μ) q z‖ ≤ 1 / 2)
    (ha : 1 / (2 * M) ≤ ‖aNf L κ c (cauchyTransform μ) q z‖)
    (hDN : 3 * η / 4 ≤ ‖DNf L κ c (cauchyTransform μ) q z‖)
    (haA : ‖aNf L κ c (cauchyTransform μ) q z - Af κ (cauchyTransform μ) z‖ ≤ 1 / (2 * M))
    (hAi : ‖(Af κ (cauchyTransform μ) z)⁻¹‖ ≤ M) :
    ContinuousAt (logaNf L κ c (cauchyTransform μ) q) z ∧
      ContinuousAt (corrf L κ c (cauchyTransform μ) q) z ∧ ContinuousAt (ellf c q) z := by
  set G := cauchyTransform μ
  have hGnear : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ G w := by
    filter_upwards [Metric.ball_mem_nhds z (show 0 < d0 / 2 by positivity)] with w hw
    refine differentiableAt_cauchy μ (show 0 < d0 / 2 by positivity) fun t ht => ?_
    have h1 := hS t ht
    have h2 : ‖w - z‖ < d0 / 2 := by rwa [Metric.mem_ball, dist_eq_norm] at hw
    have := norm_sub_norm_le (z - t) (z - w)
    rw [sub_sub_sub_cancel_left, norm_sub_rev z w] at this
    linarith
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
  refine ⟨?_, ?_, (hasDerivAt_ell hR).continuousAt⟩
  · exact (hGc.const_mul (I * κ)).add ((hac.div hAc hA0).clog hslit)
  · exact (hec.mul hdc).div (hac.mul ((hac.pow 2).sub hec)) (mul_ne_zero ha0 hden)

/-! ## 6. eq:B3-two-term-period -/

/-- **eq:B3-two-term-period.** -/
theorem two_term_period {L κ : ℝ} (S : IndexedScalarMeasureCuts L κ)
    {μ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ) = S.μ) {N : ℕ → ℕ} {hN : ∀ k, 0 < N k}
    {B : ∀ k, OnShellBethe L κ (N k)}
    (hconv : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ)) (hNtop : Tendsto N atTop atTop)
    {n : ℤ} {xm xp h : ℝ} (hxm : xm ∈ S.cuts) (hxp : xp ∈ S.cuts) (hlt : xm < xp) (hh : 0 < h)
    (h1 : 2 * Real.pi * (n - 1) < exteriorForce L κ S.μ xm)
    (h2 : exteriorForce L κ S.μ xm < 2 * Real.pi * n)
    (h3 : 2 * Real.pi * n < exteriorForce L κ S.μ xp)
    (h4 : exteriorForce L κ S.μ xp < 2 * Real.pi * (n + 1)) :
    ∃ C : ℝ, ∀ᶠ k in atTop,
      ‖(((Finset.univ.filter fun j => (B k).n j = n).card : ℝ) / N k : ℂ) -
        (-(1 / (2 * Real.pi * κ)) * LabelExactPeriod.rectIntegral
            (logaNf L κ (κ / N k) (cauchyTransform S.μ) (B k).q) xm xp h +
          I / (2 * Real.pi * N k) * LabelExactPeriod.rectIntegral
            (corrf L κ (κ / N k) (cauchyTransform S.μ) (B k).q) xm xp h)‖ ≤
        C * ((N k : ℝ)⁻¹) ^ 2 := by
  have : IsProbabilityMeasure S.μ := S.isProb
  have hκ := S.hκ
  obtain ⟨d, hd, d0, hd0, M, η, hM0, hη, hroot, hsupp, hU, hGd, hDev, hM⟩ :=
    setup S hμ hconv hNtop hxm hxp hlt hh h1 h2 h3 h4
  have hM' : 0 < M := lt_of_lt_of_le one_pos hM0
  have hev := eventual_props (q := fun k => (B k).q) hκ hN hNtop hd hroot hU hGd hDev hM0 hη hM
  obtain ⟨C, hC⟩ := (rem_isBigO (q := fun k => (B k).q) hκ hN hNtop hd hroot hU hGd hDev hM0
    hη hM).bound
  have hEP := LabelExactPeriod.exact_period_seq S hμ hconv hNtop hxm hxp hlt hh h1 h2 h3 h4
  refine ⟨(1 / (2 * Real.pi * κ)) * ((2 * (xp - xm) + 4 * h) * C), ?_⟩
  filter_upwards [Filter.eventually_prod_principal_iff.1 hev,
    Filter.eventually_prod_principal_iff.1 hC, hEP] with k hk hCk hEPk
  set G := cauchyTransform S.μ
  set c : ℝ := κ / N k
  set q := (B k).q
  have hNk : (0 : ℝ) < N k := Nat.cast_pos.2 (hN k)
  have hcont : ∀ z ∈ Gam xm xp h, ContinuousAt (logaNf L κ c G q) z ∧
      ContinuousAt (corrf L κ c G q) z ∧ ContinuousAt (ellf c q) z := fun z hz => by
    obtain ⟨hR, hW, ha, hDN, haA⟩ := hk z hz
    exact contAt_props S.μ hd0 hM' hη (hsupp z hz) hR
      (fun h0 => by have := (hM z hz).2.2.2; rw [h0, norm_zero] at this; linarith)
      hW ha hDN haA (hM z hz).2.1
  -- the remainder
  set r : ℂ → ℂ := fun z => ellf c q z - logaNf L κ c G q z + I * κ / (N k : ℂ) * corrf L κ c G q z
  have hr_eq : ∀ z, r z = remf κ L N (fun k => (B k).q) G (k, z) := fun z => rfl
  have hrc : ∀ z ∈ Gam xm xp h, ContinuousAt r z := fun z hz =>
    (((hcont z hz).2.2.sub (hcont z hz).1).add (continuousAt_const.mul (hcont z hz).2.1))
  have hrb : ∀ z ∈ Gam xm xp h, ‖r z‖ ≤ C * ((N k : ℝ)⁻¹) ^ 2 := fun z hz => by
    have := hCk z hz
    rw [Real.norm_of_nonneg (sq_nonneg _)] at this
    rw [hr_eq]; exact this
  -- ℓ_N on Γ
  have hbridge : LabelExactPeriod.rectIntegral (LabelExactPeriod.ellN κ q) xm xp h =
      LabelExactPeriod.rectIntegral (ellf c q) xm xp h := by
    refine LabelExactPeriod.rectIntegral_congr (fun x hx => ?_) (fun x hx => ?_)
      (fun y hy => ?_) (fun y hy => ?_)
    · exact ellN_eq_ellf κ q ((hk _ (bot_mem hlt.le hx)).1)
    · exact ellN_eq_ellf κ q ((hk _ (top_mem hlt.le hx)).1)
    · exact ellN_eq_ellf κ q ((hk _ (right_mem hh.le hy)).1)
    · exact ellN_eq_ellf κ q ((hk _ (left_mem hh.le hy)).1)
  have hsplit : LabelExactPeriod.rectIntegral (ellf c q) xm xp h =
      LabelExactPeriod.rectIntegral (logaNf L κ c G q) xm xp h +
        (-(I * κ / (N k : ℂ))) * LabelExactPeriod.rectIntegral (corrf L κ c G q) xm xp h +
        LabelExactPeriod.rectIntegral r xm xp h := by
    have e : ellf c q = fun z => (logaNf L κ c G q z + (-(I * κ / (N k : ℂ))) * corrf L κ c G q z) +
        r z := by
      funext z; simp only [r]; ring
    rw [e, rectIntegral_add (f := fun z => logaNf L κ c G q z +
        (-(I * κ / (N k : ℂ))) * corrf L κ c G q z) (g := r) hlt.le hh.le
        (fun z hz => (hcont z hz).1.add (continuousAt_const.mul (hcont z hz).2.1)) hrc,
      rectIntegral_add (f := logaNf L κ c G q)
        (g := fun z => (-(I * κ / (N k : ℂ))) * corrf L κ c G q z) hlt.le hh.le
        (fun z hz => (hcont z hz).1) (fun z hz => continuousAt_const.mul (hcont z hz).2.1),
      rectIntegral_const_mul]
  rw [hEPk, hbridge, hsplit]
  have hbound := norm_rectIntegral_le hlt.le hh.le hrb
  have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hN0 : (N k : ℂ) ≠ 0 := by exact_mod_cast (hN k).ne'
  have e2 : -(1 / (2 * Real.pi * κ)) * (LabelExactPeriod.rectIntegral (logaNf L κ c G q) xm xp h +
        (-(I * κ / (N k : ℂ))) * LabelExactPeriod.rectIntegral (corrf L κ c G q) xm xp h +
        LabelExactPeriod.rectIntegral r xm xp h) -
      (-(1 / (2 * Real.pi * κ)) * LabelExactPeriod.rectIntegral (logaNf L κ c G q) xm xp h +
        I / (2 * Real.pi * N k) * LabelExactPeriod.rectIntegral (corrf L κ c G q) xm xp h) =
      -(1 / (2 * Real.pi * κ)) * LabelExactPeriod.rectIntegral r xm xp h := by
    field_simp; ring
  rw [e2, norm_mul, norm_neg, norm_div, norm_one]
  have hnorm : ‖(2 * Real.pi * κ : ℂ)‖ = 2 * Real.pi * κ := by
    rw [show (2 * Real.pi * κ : ℂ) = ((2 * Real.pi * κ : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hnorm]
  calc 1 / (2 * Real.pi * κ) * ‖LabelExactPeriod.rectIntegral r xm xp h‖
      ≤ 1 / (2 * Real.pi * κ) * ((2 * (xp - xm) + 4 * h) * (C * ((N k : ℝ)⁻¹) ^ 2)) := by
        gcongr
    _ = _ := by ring

/-! ## 7. Uniformity over configuration families -/

/-- The remainder of eq:B3-log-reconstruction for one configuration. -/
def remOne (κ L : ℝ) (G : ℂ → ℂ) {N : ℕ} (q : Fin N → ℝ) (z : ℂ) : ℂ :=
  remf κ L (fun _ => N) (fun _ => q) G (0, z)

/-- **The uniformity clause** for eq:B3-log-reconstruction. -/
theorem log_reconstruction_uniform {L κ : ℝ} (S : IndexedScalarMeasureCuts L κ)
    {μ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ) = S.μ)
    {n : ℤ} {xm xp h : ℝ} (hxm : xm ∈ S.cuts) (hxp : xp ∈ S.cuts) (hlt : xm < xp) (hh : 0 < h)
    (h1 : 2 * Real.pi * (n - 1) < exteriorForce L κ S.μ xm)
    (h2 : exteriorForce L κ S.μ xm < 2 * Real.pi * n)
    (h3 : 2 * Real.pi * n < exteriorForce L κ S.μ xp)
    (h4 : exteriorForce L κ S.μ xp < 2 * Real.pi * (n + 1)) :
    ∃ C : ℝ, ∃ U ∈ 𝓝 μ, ∃ N₀ : ℕ, ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N →
      ∀ B : OnShellBethe L κ N, rootP B hN ∈ U → ∀ z ∈ Gam xm xp h,
        ‖remOne κ L (cauchyTransform S.μ) B.q z‖ ≤ C * ((N : ℝ)⁻¹) ^ 2 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨u, hu⟩ := (𝓝 μ).exists_antitone_basis
  have hpick : ∀ k : ℕ, ∃ N : ℕ, ∃ hN : 0 < N, k + 1 ≤ N ∧ ∃ B : OnShellBethe L κ N,
      rootP B hN ∈ u k ∧ ∃ z ∈ Gam xm xp h,
        (k : ℝ) * ((N : ℝ)⁻¹) ^ 2 < ‖remOne κ L (cauchyTransform S.μ) B.q z‖ := fun k =>
    hcon k (u k) (hu.1.mem_of_mem trivial) (k + 1)
  choose Nk hNk hkN Bk hBk zk hzk hviol using hpick
  have hconv : Tendsto (fun k => rootP (Bk k) (hNk k)) atTop (𝓝 μ) := hu.tendsto hBk
  have hNtop : Tendsto Nk atTop atTop :=
    tendsto_atTop_mono (fun k => (Nat.le_succ k).trans (hkN k)) tendsto_id
  obtain ⟨C0, hC0⟩ := log_reconstruction S hμ hconv hNtop hxm hxp hlt hh h1 h2 h3 h4
  obtain ⟨K, hK⟩ := eventually_atTop.1 hC0
  obtain ⟨m, hm⟩ := exists_nat_ge (max (K : ℝ) C0)
  have hmK : K ≤ m := by exact_mod_cast (le_max_left _ _).trans hm
  have hb := hK m hmK (zk m) (hzk m)
  have hv := hviol m
  have hpos : 0 ≤ ((Nk m : ℝ)⁻¹) ^ 2 := sq_nonneg _
  have : C0 * ((Nk m : ℝ)⁻¹) ^ 2 ≤ (m : ℝ) * ((Nk m : ℝ)⁻¹) ^ 2 :=
    mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hm) hpos
  have e : ‖remOne κ L (cauchyTransform S.μ) (Bk m).q (zk m)‖ =
      ‖remf κ L Nk (fun k => (Bk k).q) (cauchyTransform S.μ) (m, zk m)‖ := rfl
  linarith

/-- The two-term period for one configuration (the left side minus the two contour terms). -/
def twoTermErr (L κ : ℝ) (G : ℂ → ℂ) {N : ℕ} (B : OnShellBethe L κ N) (n : ℤ) (xm xp h : ℝ) : ℂ :=
  (((Finset.univ.filter fun j => B.n j = n).card : ℝ) / N : ℂ) -
    (-(1 / (2 * Real.pi * κ)) * LabelExactPeriod.rectIntegral (logaNf L κ (κ / N) G B.q) xm xp h +
      I / (2 * Real.pi * N) * LabelExactPeriod.rectIntegral (corrf L κ (κ / N) G B.q) xm xp h)

/-- **The uniformity clause** for eq:B3-two-term-period. -/
theorem two_term_period_uniform {L κ : ℝ} (S : IndexedScalarMeasureCuts L κ)
    {μ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ) = S.μ)
    {n : ℤ} {xm xp h : ℝ} (hxm : xm ∈ S.cuts) (hxp : xp ∈ S.cuts) (hlt : xm < xp) (hh : 0 < h)
    (h1 : 2 * Real.pi * (n - 1) < exteriorForce L κ S.μ xm)
    (h2 : exteriorForce L κ S.μ xm < 2 * Real.pi * n)
    (h3 : 2 * Real.pi * n < exteriorForce L κ S.μ xp)
    (h4 : exteriorForce L κ S.μ xp < 2 * Real.pi * (n + 1)) :
    ∃ C : ℝ, ∃ U ∈ 𝓝 μ, ∃ N₀ : ℕ, ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N →
      ∀ B : OnShellBethe L κ N, rootP B hN ∈ U →
        ‖twoTermErr L κ (cauchyTransform S.μ) B n xm xp h‖ ≤ C * ((N : ℝ)⁻¹) ^ 2 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨u, hu⟩ := (𝓝 μ).exists_antitone_basis
  have hpick : ∀ k : ℕ, ∃ N : ℕ, ∃ hN : 0 < N, k + 1 ≤ N ∧ ∃ B : OnShellBethe L κ N,
      rootP B hN ∈ u k ∧
        (k : ℝ) * ((N : ℝ)⁻¹) ^ 2 < ‖twoTermErr L κ (cauchyTransform S.μ) B n xm xp h‖ :=
    fun k => hcon k (u k) (hu.1.mem_of_mem trivial) (k + 1)
  choose Nk hNk hkN Bk hBk hviol using hpick
  have hconv : Tendsto (fun k => rootP (Bk k) (hNk k)) atTop (𝓝 μ) := hu.tendsto hBk
  have hNtop : Tendsto Nk atTop atTop :=
    tendsto_atTop_mono (fun k => (Nat.le_succ k).trans (hkN k)) tendsto_id
  obtain ⟨C0, hC0⟩ := two_term_period S hμ hconv hNtop hxm hxp hlt hh h1 h2 h3 h4
  obtain ⟨K, hK⟩ := eventually_atTop.1 hC0
  obtain ⟨m, hm⟩ := exists_nat_ge (max (K : ℝ) C0)
  have hmK : K ≤ m := by exact_mod_cast (le_max_left _ _).trans hm
  have hb := hK m hmK
  have hv := hviol m
  have hpos : 0 ≤ ((Nk m : ℝ)⁻¹) ^ 2 := sq_nonneg _
  have : C0 * ((Nk m : ℝ)⁻¹) ^ 2 ≤ (m : ℝ) * ((Nk m : ℝ)⁻¹) ^ 2 :=
    mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hm) hpos
  have e : ‖twoTermErr L κ (cauchyTransform S.μ) (Bk m) n xm xp h‖ =
      ‖(((Finset.univ.filter fun j => (Bk m).n j = n).card : ℝ) / Nk m : ℂ) -
        (-(1 / (2 * Real.pi * κ)) * LabelExactPeriod.rectIntegral
            (logaNf L κ (κ / Nk m) (cauchyTransform S.μ) (Bk m).q) xm xp h +
          I / (2 * Real.pi * Nk m) * LabelExactPeriod.rectIntegral
            (corrf L κ (κ / Nk m) (cauchyTransform S.μ) (Bk m).q) xm xp h)‖ := rfl
  linarith

/-! ## 8. PROP-006 -/

/-- **PROP-006 `thm:B3-period-reconstruction`**: for any sequence of PROP-003 and the fixed
contour, (i) eq:B3-log-reconstruction holds uniformly on `Γ` with an `O(N^{-2})` remainder,
(ii) eq:B3-two-term-period holds with an `O(N^{-2})` error, and (iii) both error constants are
uniform over configuration families converging weakly to `μ` uniformly. -/
theorem period_reconstruction {L κ : ℝ} (S : IndexedScalarMeasureCuts L κ)
    {μ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ) = S.μ) {N : ℕ → ℕ} {hN : ∀ k, 0 < N k}
    {B : ∀ k, OnShellBethe L κ (N k)}
    (hconv : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ)) (hNtop : Tendsto N atTop atTop)
    {n : ℤ} {xm xp h : ℝ} (hxm : xm ∈ S.cuts) (hxp : xp ∈ S.cuts) (hlt : xm < xp) (hh : 0 < h)
    (h1 : 2 * Real.pi * (n - 1) < exteriorForce L κ S.μ xm)
    (h2 : exteriorForce L κ S.μ xm < 2 * Real.pi * n)
    (h3 : 2 * Real.pi * n < exteriorForce L κ S.μ xp)
    (h4 : exteriorForce L κ S.μ xp < 2 * Real.pi * (n + 1)) :
    (∃ C : ℝ, ∀ᶠ k in atTop, ∀ z ∈ Gam xm xp h,
      ‖remf κ L N (fun k => (B k).q) (cauchyTransform S.μ) (k, z)‖ ≤ C * ((N k : ℝ)⁻¹) ^ 2) ∧
    (∃ C : ℝ, ∀ᶠ k in atTop,
      ‖twoTermErr L κ (cauchyTransform S.μ) (B k) n xm xp h‖ ≤ C * ((N k : ℝ)⁻¹) ^ 2) ∧
    (∃ C : ℝ, ∃ U ∈ 𝓝 μ, ∃ N₀ : ℕ, ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N →
      ∀ B : OnShellBethe L κ N, rootP B hN ∈ U → ∀ z ∈ Gam xm xp h,
        ‖remOne κ L (cauchyTransform S.μ) B.q z‖ ≤ C * ((N : ℝ)⁻¹) ^ 2) ∧
    (∃ C : ℝ, ∃ U ∈ 𝓝 μ, ∃ N₀ : ℕ, ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N →
      ∀ B : OnShellBethe L κ N, rootP B hN ∈ U →
        ‖twoTermErr L κ (cauchyTransform S.μ) B n xm xp h‖ ≤ C * ((N : ℝ)⁻¹) ^ 2) :=
  ⟨log_reconstruction S hμ hconv hNtop hxm hxp hlt hh h1 h2 h3 h4,
    two_term_period S hμ hconv hNtop hxm hxp hlt hh h1 h2 h3 h4,
    log_reconstruction_uniform S hμ hxm hxp hlt hh h1 h2 h3 h4,
    two_term_period_uniform S hμ hxm hxp hlt hh h1 h2 h3 h4⟩

end QuantumNLS.PeriodTwoTerm

#print axioms QuantumNLS.PeriodTwoTerm.ellN_eq_ellf
#print axioms QuantumNLS.PeriodTwoTerm.two_term_period
#print axioms QuantumNLS.PeriodTwoTerm.log_reconstruction_uniform
#print axioms QuantumNLS.PeriodTwoTerm.two_term_period_uniform
#print axioms QuantumNLS.PeriodTwoTerm.period_reconstruction
