import QuantumNLS.PeriodReconstructionAsymp

/-!
# PROP-006 `thm:B3-period-reconstruction`: the uniform `O(N^{-2})` remainder (abstract form)

Along `l = atTop ×ˢ 𝓟 Γ` (uniformly for `z ∈ Γ` as `k → ∞`):
`rem = ℓ_N − log a_N + (iκ/N) e^{izL} a_N'/(a_N(a_N² − e^{izL})) = O(N^{-2})` (**`rem_isBigO`**),
under the hypotheses listed in `PeriodReconstructionAsymp` (root distance, uniform convergence of
`iκG_N` to `iκG`, differentiable background, `D` bounded below, `A^{±1}`, `e^{izL}` bounded).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000
noncomputable section

open Complex Filter Topology Asymptotics

namespace QuantumNLS.PeriodReconstructionBigO

open QuantumNLS.PeriodReconstructionCore QuantumNLS.PeriodReconstructionAsymp

/-- The remainder of eq:B3-log-reconstruction. -/
def remf (κ L : ℝ) (N : ℕ → ℕ) (q : ∀ k, Fin (N k) → ℝ) (G : ℂ → ℂ) (p : ℕ × ℂ) : ℂ :=
  ellf (κ / N p.1) (q p.1) p.2 - logaNf L κ (κ / N p.1) G (q p.1) p.2 +
    I * κ / (N p.1 : ℂ) * (ef L p.2 * deriv (aNf L κ (κ / N p.1) G (q p.1)) p.2 /
      (aNf L κ (κ / N p.1) G (q p.1) p.2 *
        (aNf L κ (κ / N p.1) G (q p.1) p.2 ^ 2 - ef L p.2)))

lemma bigO_of_le {α : Type*} {l : Filter α} {f : α → ℂ} {g : α → ℝ} (C : ℝ)
    (hg : ∀ x, 0 ≤ g x) (h : ∀ᶠ x in l, ‖f x‖ ≤ C * g x) : f =O[l] g :=
  IsBigO.of_bound C (h.mono fun x hx => by rwa [Real.norm_of_nonneg (hg x)])

lemma tendsto_exp_sub_one {α : Type*} {l : Filter α} {x : α → ℂ} (hx : Tendsto x l (𝓝 0)) :
    Tendsto (fun p => exp (x p) - 1) l (𝓝 0) := by
  have := ((continuous_exp.tendsto 0).comp hx).sub_const 1
  simpa using this

lemma tendsto_cpow_half {α : Type*} {l : Filter α} {x : α → ℂ} (hx : Tendsto x l (𝓝 0)) :
    Tendsto (fun p => (1 + x p) ^ ((2 : ℂ)⁻¹) - 1) l (𝓝 0) := by
  have hc : ContinuousAt (fun w : ℂ => (1 + w) ^ ((2 : ℂ)⁻¹)) 0 :=
    (continuousAt_const.add continuousAt_id).cpow continuousAt_const (by simp)
  have := (hc.tendsto.comp hx).sub_const 1
  simpa using this

lemma tendsto_log_near_one {α : Type*} {l : Filter α} {x : α → ℂ} (hx : Tendsto x l (𝓝 1)) :
    Tendsto (fun p => log (x p)) l (𝓝 0) := by
  have hc : ContinuousAt log 1 := continuousAt_clog (by simp)
  have := hc.tendsto.comp hx
  rw [log_one] at this
  exact this

section Asymp

variable {κ L : ℝ} {N : ℕ → ℕ} {q : ∀ k, Fin (N k) → ℝ} {G : ℂ → ℂ} {Γ : Set ℂ}

/-- **eq:B3-log-reconstruction, abstract form.** -/
theorem rem_isBigO (hκ : 0 < κ) (hN : ∀ k, 0 < N k) (hNtop : Tendsto N atTop atTop)
    {d : ℝ} (hd : 0 < d) (hroot : ∀ᶠ k in atTop, ∀ z ∈ Γ, ∀ j, d ≤ ‖z - q k j‖)
    (hU : Tendsto (fun p : ℕ × ℂ => (∑ j, I * ((κ / N p.1 : ℝ) : ℂ) / (p.2 - (q p.1 j : ℂ))) -
      I * κ * G p.2) (atTop ×ˢ 𝓟 Γ) (𝓝 0))
    (hGd : ∀ z ∈ Γ, DifferentiableAt ℂ G z) (hDev : ∀ z ∈ Γ, ∀ᶠ w in 𝓝 z, Df L κ G w ≠ 0)
    {M η : ℝ} (hM0 : 1 ≤ M) (hη : 0 < η)
    (hM : ∀ z ∈ Γ, ‖Af κ G z‖ ≤ M ∧ ‖(Af κ G z)⁻¹‖ ≤ M ∧ ‖ef L z‖ ≤ M ∧ η ≤ ‖Df L κ G z‖) :
    remf κ L N q G =O[atTop ×ˢ 𝓟 Γ] (fun p : ℕ × ℂ => ((N p.1 : ℝ)⁻¹) ^ 2) := by
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
  -- S10: the product correction
  set δ : ℕ × ℂ → ℂ := fun p => AN p * BN p - 1 with hδdef
  set Y : ℕ × ℂ → ℂ := fun p => ℓ p + ℓB p with hYdef
  set Q : ℕ × ℂ → ℂ := fun p => ∑ j, ((κ / N p.1 : ℝ) : ℂ) ^ 2 / (p.2 - (q p.1 j : ℂ)) ^ 2 with hQdef
  set Ic : ℕ × ℂ → ℂ := fun p => I * ((κ / N p.1 : ℝ) : ℂ) with hIcdef
  have hYQ : (fun p => Y p - Q p) =O[l] (fun p => ν p ^ 2) := by
    refine bigO_of_le (2 * (κ / d) ^ 3) hνsq0 ?_
    filter_upwards [hroot', hc2] with p h1 h2
    have := ell_pair hd h2 h1
    calc ‖Y p - Q p‖ ≤ 2 * N p.1 * (|κ / (N p.1 : ℝ)| / d) ^ 3 := this
      _ = 2 * (κ / d) ^ 3 * ν p ^ 2 * ((N p.1 : ℝ) * ν p) := by rw [habsc]; ring
      _ = 2 * (κ / d) ^ 3 * ν p ^ 2 := by rw [hNν, mul_one]
  have hQ : Q =O[l] ν := by
    refine bigO_of_le ((κ / d) ^ 2) (fun p => (hν0 p).le) ?_
    filter_upwards [hroot'] with p h1
    have := sumsq_bound (c := κ / N p.1) hd h1
    calc ‖Q p‖ ≤ N p.1 * (|κ / (N p.1 : ℝ)| / d) ^ 2 := this
      _ = (κ / d) ^ 2 * ν p * ((N p.1 : ℝ) * ν p) := by rw [habsc]; ring
      _ = (κ / d) ^ 2 * ν p := by rw [hNν, mul_one]
  have hY : Y =O[l] ν := ((hYQ.trans hνν).add hQ).congr_left fun p => by ring
  have hδexp : ∀ᶠ p in l, δ p = exp (Y p) - 1 := by
    filter_upwards [hANexp, hBNexp] with p h1 h2
    show AN p * BN p - 1 = exp (ℓ p + ℓB p) - 1
    rw [h1, h2, exp_add]
  have hδY : (fun p => δ p - Y p) =O[l] (fun p => ν p ^ 2) := by
    have h1 : (fun p => δ p - Y p) =O[l] (fun p => Y p ^ 2) := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [hδexp, evb (hY.trans_tendsto hν) one_pos] with p h1 h2
      rw [h1, one_mul, norm_pow]
      exact Complex.norm_exp_sub_one_sub_id_le h2
    exact h1.trans (hY.pow 2)
  have hPQ : (fun p => Ic p * dl p - Q p) =O[l] (fun p => ν p ^ 2) := by
    refine bigO_of_le (2 * (κ / d) ^ 3) hνsq0 ?_
    filter_upwards [hroot', hc2] with p h1 h2
    have := Icdell_sub hd h2 h1
    calc ‖Ic p * dl p - Q p‖ ≤ N p.1 * (2 * |κ / (N p.1 : ℝ)| ^ 3 / d ^ 3) := this
      _ = 2 * (κ / d) ^ 3 * ν p ^ 2 * ((N p.1 : ℝ) * ν p) := by rw [habsc]; ring
      _ = 2 * (κ / d) ^ 3 * ν p ^ 2 := by rw [hNν, mul_one]
  have hδP : (fun p => δ p - Ic p * dl p) =O[l] (fun p => ν p ^ 2) :=
    ((hδY.add hYQ).sub hPQ).congr_left fun p => by ring
  have hδ : δ =O[l] ν := ((hδY.trans hνν).add hY).congr_left fun p => by ring
  have hIc : Ic =O[l] ν := by
    refine bigO_of_le κ (fun p => (hν0 p).le) (Eventually.of_forall fun p => ?_)
    show ‖I * ((κ / N p.1 : ℝ) : ℂ)‖ ≤ κ * ν p
    rw [norm_Ic, habsc]
  -- the residual equation
  have hDne : ∀ᶠ p in l, Dd p ≠ 0 := hbg.mono fun p h => by
    intro h0; have h5 : η ≤ ‖Dd p‖ := h.2.2.2; rw [h0, norm_zero] at h5; linarith
  have hres : ∀ᶠ p in l, (AN p - a p) ^ 2 + DN p * (AN p - a p) + e p * δ p = 0 :=
    hDne.mono fun p h => residual_eq L κ (κ / N p.1) G (q p.1) h
  have hε : (fun p => AN p - a p) =O[l] ν := by
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
  have hε2 : (fun p => (AN p - a p) + e p * δ p / DN p) =O[l] (fun p => ν p ^ 2) := by
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
    exact h1.trans (hε.pow 2)
  -- derivatives
  have mul_bdd : ∀ {f g : ℕ × ℂ → ℂ} {h : ℕ × ℂ → ℝ}, f =O[l] h → ∀ (C : ℝ),
      (∀ᶠ p in l, ‖g p‖ ≤ C) → (fun p => f p * g p) =O[l] h := by
    intro f g h hf C hg
    have hg1 : g =O[l] (fun _ => (1 : ℝ)) := IsBigO.of_bound C (hg.mono fun x hx => by simpa using hx)
    simpa using hf.mul hg1
  have hdlb : ∀ᶠ p in l, ‖dl p‖ ≤ 2 * κ / d ^ 2 := by
    filter_upwards [hroot', hc2] with p h1 h2
    have := dell_bound hd h2 h1
    calc ‖dl p‖ ≤ N p.1 * (2 * |κ / (N p.1 : ℝ)| / d ^ 2) := this
      _ = 2 * κ / d ^ 2 * ((N p.1 : ℝ) * ν p) := by rw [habsc]; ring
      _ = 2 * κ / d ^ 2 := by rw [hNν, mul_one]
  have hdlBb : ∀ᶠ p in l, ‖dlB p‖ ≤ 2 * κ / d ^ 2 := by
    filter_upwards [hroot', hc2'] with p h1 h2
    have := dell_bound hd h2 h1
    calc ‖dlB p‖ ≤ N p.1 * (2 * |-(κ / (N p.1 : ℝ))| / d ^ 2) := this
      _ = 2 * κ / d ^ 2 * ((N p.1 : ℝ) * ν p) := by rw [abs_neg, habsc]; ring
      _ = 2 * κ / d ^ 2 := by rw [hNν, mul_one]
  have hdlp : (fun p => dl p + dlB p) =O[l] ν := by
    refine bigO_of_le (8 * κ ^ 2 / d ^ 3) (fun p => (hν0 p).le) ?_
    filter_upwards [hroot', hc2] with p h1 h2
    have := dell_pair hd h2 h1
    calc ‖dl p + dlB p‖ ≤ N p.1 * (8 * |κ / (N p.1 : ℝ)| ^ 2 / d ^ 3) := this
      _ = 8 * κ ^ 2 / d ^ 3 * ν p * ((N p.1 : ℝ) * ν p) := by rw [habsc]; ring
      _ = 8 * κ ^ 2 / d ^ 3 * ν p := by rw [hNν, mul_one]
  set sN' : ℕ × ℂ → ℂ := fun p => AN p * dl p + (I * L * e p * BN p + e p * (BN p * dlB p))
    with hsN'
  have ha'rel : ∀ᶠ p in l, a' p * DN p = sN' p * a p - I * L * e p := by
    filter_upwards [hmem, hdist, hbd] with p hm hd' hb
    have hW2 := hb.2.2.2.2.2.2.2
    have hslit : 1 + W p ∈ slitPlane := Or.inl (by
      have := Complex.abs_re_le_norm (W p)
      simp only [add_re, one_re]; linarith [neg_abs_le (W p).re])
    exact deriv_aN_mul_DN L κ (κ / N p.1) (hGd p.2 hm) (hDev p.2 hm) hd' hslit
  -- eq:B3-log-derivative-comparison
  have hdla : (fun p => dl p - a' p / a p) =O[l] ν := by
    set Num : ℕ × ℂ → ℂ := fun p => -2 * (AN p - a p) * dl p * a p * AN p -
      e p * BN p * (dl p + dlB p) * a p * AN p + I * L * e p * ((AN p - a p) - a p * δ p)
      with hNum
    have hN1 : Num =O[l] ν := by
      have t1 := mul_bdd hε (2 * (2 * κ / d ^ 2) * (M + 1) * (M + 1))
        (g := fun p => -2 * dl p * a p * AN p) (by
          filter_upwards [hdlb, hbd] with p h1 h2
          simp only [norm_mul, norm_neg, Complex.norm_ofNat]
          have := norm_nonneg (dl p); have := norm_nonneg (a p); have := norm_nonneg (AN p)
          have h3 := h2.2.1; have h4 := h2.2.2.2.1
          have h7 : ‖dl p‖ * ‖a p‖ ≤ 2 * κ / d ^ 2 * (M + 1) :=
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
      have t3a : (fun p => (AN p - a p) - a p * δ p) =O[l] ν :=
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
      have hDNe : DN p = 2 * a p - sN p := DN_eq L κ (κ / N p.1) G (q p.1) p.2
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
      (fun p => ν p ^ 2) := by
    have t2 := mul_bdd hδP (M * (4 / (3 * η))) heDb
    have t3a : (fun p => Ic p * (dl p - a' p / a p)) =O[l] (fun p => ν p ^ 2) :=
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
  set X : ℕ × ℂ → ℂ := fun p => ℓ p - (I * κ * G p.2 + log (a p / A p)) with hX
  have hXt : Tendsto X l (𝓝 0) := by
    have := hT1.sub hlogt
    rw [sub_zero] at this
    exact this.congr' (Eventually.of_forall fun p => by
      show ℓ p - I * κ * G p.2 - log (a p / A p) = X p; simp only [hX]; ring)
  set v : ℕ × ℂ → ℂ := fun p => (AN p - a p) / a p with hv
  have hvO : v =O[l] ν := (mul_bdd hε (2 * M) (g := fun p => (a p)⁻¹) (by
    filter_upwards [hbd] with p hb
    have ha1 := hb.2.2.1
    rw [norm_inv, inv_le_comm₀ (lt_of_lt_of_le (by positivity) ha1) (by positivity)]
    calc (2 * M)⁻¹ = 1 / (2 * M) := by rw [one_div]
      _ ≤ ‖a p‖ := ha1)).congr_left fun p => by simp only [hv, div_eq_mul_inv]
  have hXv : (fun p => X p - v p) =O[l] (fun p => ν p ^ 2) := by
    have h1 : (fun p => X p - v p) =O[l] (fun p => v p ^ 2) := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [hbd, evb hXt one_pos, evb (hvO.trans_tendsto hν)
        (show (0 : ℝ) < 1 / 2 by norm_num), hANexp] with p hb hX1 hv1 hAe
      obtain ⟨hAN1, -, ha1, -, -, -, -, -⟩ := hb
      have ha0 : a p ≠ 0 := by intro h0; rw [h0, norm_zero] at ha1; linarith [show 0 < 1 / (2 * M) by positivity]
      have hA0 : A p ≠ 0 := exp_ne_zero _
      have hexp : exp (X p) = 1 + v p := by
        show exp (ℓ p - (I * κ * G p.2 + log (a p / A p))) = 1 + (AN p - a p) / a p
        rw [exp_sub, exp_add, exp_log (div_ne_zero ha0 hA0), ← hAe]
        show AN p / (A p * (a p / A p)) = _
        field_simp; ring
      have hIm : |(X p).im| < Real.pi :=
        lt_of_le_of_lt (Complex.abs_im_le_norm _) (lt_of_le_of_lt hX1 (by linarith [Real.pi_gt_three]))
      have hXlog : X p = log (1 + v p) := by
        rw [← hexp, log_exp (by linarith [abs_lt.1 hIm]) (by linarith [abs_lt.1 hIm])]
      rw [hXlog, one_mul, norm_pow]
      exact log_lin hv1
    exact h1.trans (hvO.pow 2)
  -- conclusion
  have hfin : ∀ᶠ p in l, remf κ L N q G p =
      (X p - v p) + ((AN p - a p) + Ic p * e p * (a' p / a p) / DN p) * (a p)⁻¹ := by
    filter_upwards [hbd, hDne] with p hb hD0
    obtain ⟨-, -, ha1, -, -, hDN, -, -⟩ := hb
    have ha0 : a p ≠ 0 := by intro h0; rw [h0, norm_zero] at ha1; linarith [show 0 < 1 / (2 * M) by positivity]
    have hDN0 : DN p ≠ 0 := by intro h0; rw [h0, norm_zero] at hDN; linarith
    have haD : a p * DN p = a p ^ 2 - e p := aD L κ (κ / N p.1) G (q p.1) hD0
    show ℓ p - (I * κ * G p.2 + log (a p / A p)) +
        I * κ / (N p.1 : ℂ) * (e p * a' p / (a p * (a p ^ 2 - e p))) = _
    rw [← haD]
    simp only [hX, hv, hIcdef]
    have hNc : (N p.1 : ℂ) ≠ 0 := by exact_mod_cast (hN p.1).ne'
    push_cast
    field_simp
    ring
  refine ((hXv.add (mul_bdd hε3 (2 * M) (g := fun p => (a p)⁻¹) (by
    filter_upwards [hbd] with p hb
    have ha1 := hb.2.2.1
    rw [norm_inv, inv_le_comm₀ (lt_of_lt_of_le (by positivity) ha1) (by positivity)]
    calc (2 * M)⁻¹ = 1 / (2 * M) := by rw [one_div]
      _ ≤ ‖a p‖ := ha1))).congr' (hfin.mono fun p hp => hp.symm) EventuallyEq.rfl)

end Asymp

end QuantumNLS.PeriodReconstructionBigO

#print axioms QuantumNLS.PeriodReconstructionBigO.rem_isBigO
