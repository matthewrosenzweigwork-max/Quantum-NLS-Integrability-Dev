import NlsGge.GK38.MolnarLocalizationB3

/-!
# Mo2 (part B4): the localization estimate in sequence form

`core_one`: the first row of the `2 × 2` Lyapunov-Schmidt reduction, with the Molnár constants
(`⟨n⟩ ≥ 8 R2` and Lemma 10: `R2/⟨n⟩ + √2 √R2/⟨2n⟩`); `molnar_ls_core`: a nonzero solution of the
system exists only for `|λ - nπ| ≤ R2/⟨n⟩ + √2 √R2/⟨2n⟩`.  Proof route: absorption
`‖h‖ ≤ ‖r‖/(1 - κ)` with `κ = 7/25` (so `1/(1 - κ) = 25/18 < √2`), then
`|d||p_i| ≤ A|p_i| + B|p_{ī}|` and the maximum of `|p₁|, |p₂|` (instead of the determinant of
`S_n`, Lemma 10; neither the symmetry `a⁺ = a⁻` (Lemma 8) nor Rouché's theorem is needed).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ENNReal NNReal

namespace NlsGge.GK38.Mo2

noncomputable section

open NlsGge.GK38.Mo2

theorem final_real (D P₁ P₂ N W2 R2 a₁ a₂ : ℝ) (hN : 1 ≤ N) (hW : N ≤ W2) (_hD : 0 ≤ D)
    (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hsum : a₁ ^ 2 + a₂ ^ 2 ≤ R2)
    (hE : W2 * (D * P₁) ≤ 25 / 18 * a₁ * P₂ + W2 * P₁ * (2 / 3 * (1 / N) * (a₁ * a₂)) +
      7 / 18 * P₁ * (a₁ * (4 / 3 * (Real.sqrt 3 * a₂)))) :
    D * P₁ ≤ R2 / N * P₁ + Real.sqrt 2 * Real.sqrt R2 / W2 * P₂ := by
  have hN0 : 0 < N := by linarith
  have hW0 : 0 < W2 := by linarith
  have hR2 : 0 ≤ R2 := by nlinarith [sq_nonneg a₁, sq_nonneg a₂]
  have h1 : a₁ ≤ Real.sqrt R2 := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg a₂])
  have h2 : (25 / 18 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have h3 : a₁ * a₂ ≤ R2 / 2 := by nlinarith [sq_nonneg (a₁ - a₂)]
  have h4 : Real.sqrt 3 ≤ 7 / 4 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h5 : 0 ≤ a₁ * a₂ := mul_nonneg ha₁ ha₂
  have hsq3 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hA : 25 / 18 * a₁ * P₂ ≤ Real.sqrt 2 * Real.sqrt R2 * P₂ := by
    have : 25 / 18 * a₁ ≤ Real.sqrt 2 * Real.sqrt R2 :=
      mul_le_mul h2 h1 ha₁ (Real.sqrt_nonneg _)
    exact mul_le_mul_of_nonneg_right this hP₂
  have hB : W2 * P₁ * (2 / 3 * (1 / N) * (a₁ * a₂)) ≤ W2 * R2 / N * P₁ * (1 / 3) := by
    have : 2 / 3 * (1 / N) * (a₁ * a₂) ≤ 2 / 3 * (1 / N) * (R2 / 2) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    calc W2 * P₁ * (2 / 3 * (1 / N) * (a₁ * a₂)) ≤ W2 * P₁ * (2 / 3 * (1 / N) * (R2 / 2)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = W2 * R2 / N * P₁ * (1 / 3) := by field_simp
  have hC : 7 / 18 * P₁ * (a₁ * (4 / 3 * (Real.sqrt 3 * a₂))) ≤ W2 * R2 / N * P₁ * (49 / 108) := by
    have e1 : a₁ * (4 / 3 * (Real.sqrt 3 * a₂)) = 4 / 3 * Real.sqrt 3 * (a₁ * a₂) := by ring
    have e2 : 4 / 3 * Real.sqrt 3 * (a₁ * a₂) ≤ 4 / 3 * (7 / 4) * (R2 / 2) := by
      have := mul_le_mul h4 h3 h5 (by norm_num)
      nlinarith
    have e3 : R2 ≤ W2 * R2 / N := by
      rw [le_div_iff₀ hN0]; nlinarith
    calc 7 / 18 * P₁ * (a₁ * (4 / 3 * (Real.sqrt 3 * a₂)))
        = 7 / 18 * P₁ * (4 / 3 * Real.sqrt 3 * (a₁ * a₂)) := by rw [e1]
      _ ≤ 7 / 18 * P₁ * (4 / 3 * (7 / 4) * (R2 / 2)) := by gcongr
      _ = P₁ * R2 * (49 / 108) := by ring
      _ ≤ P₁ * (W2 * R2 / N) * (49 / 108) := by gcongr
      _ = _ := by ring
  have hF : W2 * (D * P₁) ≤ W2 * (R2 / N * P₁ + Real.sqrt 2 * Real.sqrt R2 / W2 * P₂) := by
    calc W2 * (D * P₁) ≤ _ := hE
      _ ≤ Real.sqrt 2 * Real.sqrt R2 * P₂ + W2 * R2 / N * P₁ * (1 / 3) + W2 * R2 / N * P₁ * (49 / 108) := by
          linarith
      _ ≤ W2 * (R2 / N * P₁ + Real.sqrt 2 * Real.sqrt R2 / W2 * P₂) := by
          have : 0 ≤ W2 * R2 / N * P₁ := by positivity
          have e : W2 * (R2 / N * P₁ + Real.sqrt 2 * Real.sqrt R2 / W2 * P₂) =
              W2 * R2 / N * P₁ + Real.sqrt 2 * Real.sqrt R2 * P₂ := by field_simp
          rw [e]; nlinarith
  exact le_of_mul_le_mul_left hF hW0


theorem enorm_hF_n (n : ℤ) (lam : ℝ) (f : ℤ → ℂ) :
    ‖hF lam f n‖ = |lam - n * Real.pi| * ‖f n‖ := by
  unfold hF
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]

/-- One component of the Lyapunov-Schmidt reduction (Molnár, Lemmas 6, 9, 10). -/
theorem core_one {n : ℤ} {lam : ℝ} {c₁ c₂ f₁ f₂ : ℤ → ℂ} {R2 : ℝ}
    (S : Setup n lam c₁ c₂ f₁ f₂ R2) :
    (f₁ n = 0 → f₂ n = 0 → ∀ m, hF lam f₁ m = 0) ∧
    |lam - n * Real.pi| * ‖f₁ n‖ ≤ R2 / (1 + |(n : ℝ)|) * ‖f₁ n‖ +
      Real.sqrt 2 * Real.sqrt R2 / (1 + |((2 * n : ℤ) : ℝ)|) * ‖f₂ n‖ := by
  obtain ⟨hc₁, hc₂⟩ := SW_ne_top S
  set σ₁ := (SW c₁).toReal with hσ₁
  set σ₂ := (SW c₂).toReal with hσ₂
  have e₁ : SW c₁ = ENNReal.ofReal σ₁ := SW_eq_ofReal c₁ hc₁
  have e₂ : SW c₂ = ENNReal.ofReal σ₂ := SW_eq_ofReal c₂ hc₂
  have h₁ : 0 ≤ σ₁ := ENNReal.toReal_nonneg
  have h₂ : 0 ≤ σ₂ := ENNReal.toReal_nonneg
  have hsum : σ₁ + σ₂ ≤ R2 := by
    have := S.hS
    rw [e₁, e₂, ← ENNReal.ofReal_add h₁ h₂] at this
    exact (ENNReal.ofReal_le_ofReal_iff S.hR).1 this
  -- notation
  set H : ℤ → ℂ := hF lam f₁ with hH
  set U : ℤ → ℂ := fun m => c₁ (m + n) with hU
  set q : ℤ → ℂ := hk c₁ (Gs n lam (fun k => c₂ (k + n))) with hq
  set r : ℤ → ℂ := fun m => c₁ (m + n) * f₂ n + f₁ n * q m with hr
  set OmH : ℤ → ℂ := hk c₁ (Gs n lam (hk c₂ (Gs n lam H))) with hOmH
  have hHr : H = r + OmH := by
    funext m
    simp only [Pi.add_apply, hr, hOmH, hq, hH]
    exact key_identity S m
  have hrUq : r = f₂ n • U + f₁ n • q := by
    funext m; simp [hr, hU]; ring
  have hfin : nu n H ≠ ⊤ := by
    have hH2 : H = hk c₁ f₂ := funext fun m => ((S.e₁ m).tsum_eq).symm
    have : Q n H ≠ ⊤ := by rw [hH2]; exact Q_hk_ne_top n c₁ f₂ hc₁ S.hf₂
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) this
  have hnuH : nu n H ≤ ENNReal.ofReal (25 / 18) * nu n r := by
    apply absorb _ _ hfin
    calc nu n H = nu n (r + OmH) := by rw [← hHr]
      _ ≤ nu n r + nu n OmH := nu_add n r OmH
      _ ≤ nu n r + ENNReal.ofReal (7 / 25) * nu n H := by
          gcongr; exact nu_Om_le S H
  have hnur : nu n r ≤ ‖f₂ n‖ₑ * nu n U + ‖f₁ n‖ₑ * nu n q := by
    rw [hrUq]
    refine (nu_add n _ _).trans ?_
    rw [nu_smul, nu_smul]
  constructor
  · intro hp₁ hp₂ m
    have h0 : nu n r = 0 := by
      refine le_antisymm ?_ zero_le
      refine hnur.trans ?_
      simp [hp₁, hp₂]
    have h1 : nu n H = 0 := by
      refine le_antisymm ?_ zero_le
      refine hnuH.trans ?_
      simp [h0]
    have h2 := nu_point n H m
    rw [h1] at h2
    have h3 : eW (m + n) * ‖H m‖ₑ = 0 := le_antisymm h2 zero_le
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd h4 (eW_ne_zero _)
    · exact enorm_eq_zero.mp h4
  · -- the quantitative bound at the index `n`
    have hat := key_identity S n
    have hNU := nu_U_eq n c₁ σ₁ h₁ e₁
    have hq1 := nu_q_le S σ₁ σ₂ h₁ h₂ e₁ e₂
    have hq2 := q_n_le S σ₁ σ₂ h₁ h₂ e₁ e₂
    set a₁ := Real.sqrt σ₁ with ha₁
    set a₂ := Real.sqrt σ₂ with ha₂
    set P₁ := ‖f₁ n‖ with hP₁
    set P₂ := ‖f₂ n‖ with hP₂
    set N : ℝ := 1 + |(n : ℝ)| with hNdef
    set W2 : ℝ := 1 + |((2 * n : ℤ) : ℝ)| with hW2def
    have hN1 : 1 ≤ N := by simp only [hNdef]; linarith [abs_nonneg (n : ℝ)]
    have hNW : N ≤ W2 := by
      simp only [hNdef, hW2def]; push_cast; rw [abs_mul]; norm_num
      linarith [abs_nonneg (n : ℝ)]
    have hWe : eW (n + n) = ENNReal.ofReal W2 := by
      unfold eW; rw [show (n + n : ℤ) = 2 * n by ring]
    -- the chain in `ℝ≥0∞`
    have hmain : ENNReal.ofReal W2 * ENNReal.ofReal (|lam - n * Real.pi| * P₁) ≤
        ENNReal.ofReal (25 / 18 * a₁ * P₂ + W2 * P₁ * (2 / 3 * (1 / N) * (a₁ * a₂)) +
          7 / 18 * P₁ * (a₁ * (4 / 3 * (Real.sqrt 3 * a₂)))) := by
      have hHn : ‖H n‖ₑ = ENNReal.ofReal (|lam - n * Real.pi| * P₁) := by
        rw [← ofReal_norm, hH, enorm_hF_n]
      rw [← hHn, ← hWe]
      have hsplit : ‖H n‖ₑ ≤ ‖c₁ (n + n)‖ₑ * ‖f₂ n‖ₑ + ‖f₁ n‖ₑ * ‖q n‖ₑ + ‖OmH n‖ₑ := by
        have : H n = c₁ (n + n) * f₂ n + f₁ n * q n + OmH n := hat
        rw [this]
        refine (enorm_add_le _ _).trans ?_
        gcongr
        refine (enorm_add_le _ _).trans ?_
        simp only [enorm_mul]; exact le_rfl
      -- the three terms
      have t1 : eW (n + n) * (‖c₁ (n + n)‖ₑ * ‖f₂ n‖ₑ) ≤
          ENNReal.ofReal a₁ * ENNReal.ofReal P₂ := by
        have := nu_point n U n
        rw [hNU] at this
        calc eW (n + n) * (‖c₁ (n + n)‖ₑ * ‖f₂ n‖ₑ)
            = (eW (n + n) * ‖c₁ (n + n)‖ₑ) * ‖f₂ n‖ₑ := by ring
          _ ≤ ENNReal.ofReal a₁ * ‖f₂ n‖ₑ := by gcongr
          _ = _ := by rw [← ofReal_norm]
      have t3 : eW (n + n) * ‖OmH n‖ₑ ≤ ENNReal.ofReal (7 / 18) *
          (‖f₂ n‖ₑ * ENNReal.ofReal a₁ + ‖f₁ n‖ₑ * ENNReal.ofReal (a₁ * (4 / 3 * (Real.sqrt 3 * a₂)))) := by
        calc eW (n + n) * ‖OmH n‖ₑ ≤ nu n OmH := nu_point n OmH n
          _ ≤ ENNReal.ofReal (7 / 25) * nu n H := nu_Om_le S H
          _ ≤ ENNReal.ofReal (7 / 25) * (ENNReal.ofReal (25 / 18) * nu n r) := by gcongr
          _ = ENNReal.ofReal (7 / 18) * nu n r := by
              rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]; norm_num
          _ ≤ ENNReal.ofReal (7 / 18) * (‖f₂ n‖ₑ * nu n U + ‖f₁ n‖ₑ * nu n q) := by gcongr
          _ ≤ _ := by
              rw [hNU]
              gcongr
      have t2 : eW (n + n) * (‖f₁ n‖ₑ * ‖q n‖ₑ) ≤
          ENNReal.ofReal W2 * ENNReal.ofReal P₁ *
            ENNReal.ofReal (2 / 3 * (1 / N) * (a₁ * a₂)) := by
        rw [hWe, ← ofReal_norm]
        calc ENNReal.ofReal W2 * (ENNReal.ofReal ‖f₁ n‖ * ‖q n‖ₑ)
            ≤ ENNReal.ofReal W2 * (ENNReal.ofReal ‖f₁ n‖ *
              ENNReal.ofReal (2 / 3 * (1 / N) * (a₁ * a₂))) := by gcongr
          _ = _ := by ring
      calc eW (n + n) * ‖H n‖ₑ ≤ eW (n + n) * (‖c₁ (n + n)‖ₑ * ‖f₂ n‖ₑ + ‖f₁ n‖ₑ * ‖q n‖ₑ + ‖OmH n‖ₑ) := by
            gcongr
        _ = eW (n + n) * (‖c₁ (n + n)‖ₑ * ‖f₂ n‖ₑ) + eW (n + n) * (‖f₁ n‖ₑ * ‖q n‖ₑ) +
            eW (n + n) * ‖OmH n‖ₑ := by ring
        _ ≤ ENNReal.ofReal a₁ * ENNReal.ofReal P₂ + ENNReal.ofReal W2 * ENNReal.ofReal P₁ *
            ENNReal.ofReal (2 / 3 * (1 / N) * (a₁ * a₂)) +
            ENNReal.ofReal (7 / 18) * (‖f₂ n‖ₑ * ENNReal.ofReal a₁ +
              ‖f₁ n‖ₑ * ENNReal.ofReal (a₁ * (4 / 3 * (Real.sqrt 3 * a₂)))) := by
            gcongr
        _ = ENNReal.ofReal (25 / 18 * a₁ * P₂ + W2 * P₁ * (2 / 3 * (1 / N) * (a₁ * a₂)) +
          7 / 18 * P₁ * (a₁ * (4 / 3 * (Real.sqrt 3 * a₂)))) := by
            have ha₁0 : 0 ≤ a₁ := Real.sqrt_nonneg _
            have ha₂0 : 0 ≤ a₂ := Real.sqrt_nonneg _
            have hP₁0 : 0 ≤ P₁ := norm_nonneg _
            have hP₂0 : 0 ≤ P₂ := norm_nonneg _
            have hW0 : 0 ≤ W2 := by linarith
            have hN0 : 0 ≤ N := by linarith
            have hs3 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
            have hX : 0 ≤ a₁ * (4 / 3 * (Real.sqrt 3 * a₂)) := by positivity
            rw [← ofReal_norm (f₂ n), ← ofReal_norm (f₁ n)]
            rw [← ENNReal.ofReal_mul ha₁0, ← ENNReal.ofReal_mul (by positivity : 0 ≤ W2),
              ← ENNReal.ofReal_mul (by positivity : 0 ≤ W2 * P₁),
              ← ENNReal.ofReal_mul hP₂0, ← ENNReal.ofReal_mul hP₁0,
              ← ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 7 / 18),
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1
            ring
    have hmain' : W2 * (|lam - n * Real.pi| * P₁) ≤ 25 / 18 * a₁ * P₂ +
        W2 * P₁ * (2 / 3 * (1 / N) * (a₁ * a₂)) + 7 / 18 * P₁ * (a₁ * (4 / 3 * (Real.sqrt 3 * a₂))) := by
      have ha₁0 : 0 ≤ a₁ := Real.sqrt_nonneg _
      have ha₂0 : 0 ≤ a₂ := Real.sqrt_nonneg _
      have hP₁0 : 0 ≤ P₁ := norm_nonneg _
      have hP₂0 : 0 ≤ P₂ := norm_nonneg _
      have hW0 : 0 ≤ W2 := by linarith
      have hN0 : 0 ≤ N := by linarith
      have hs3 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
      have := hmain
      rw [← ENNReal.ofReal_mul hW0] at this
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 this
    exact final_real _ _ _ N W2 R2 a₁ a₂ hN1 hNW (abs_nonneg _) (norm_nonneg _) (norm_nonneg _)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      (by rw [ha₁, ha₂, Real.sq_sqrt h₁, Real.sq_sqrt h₂]; exact hsum) hmain'


/-- **Molnár, arXiv:1403.1369, Lemmas 5-10 in sequence form.**  A nonzero `H¹` solution
of the Fourier-side eigenvalue system forces `|λ - nπ| ≤ R2/⟨n⟩ + √2 √R2/⟨2n⟩`, where
`R2 ≥ Σ_k ⟨k⟩² (|c₁_k|² + |c₂_k|²)` and `⟨x⟩ = 1 + |x|`, whenever `⟨n⟩ ≥ 8 R2` and
`|λ - nπ| ≤ π/2`. -/
theorem molnar_ls_core {n : ℤ} {lam : ℝ} {c₁ c₂ f₁ f₂ : ℤ → ℂ} {R2 : ℝ}
    (S : Setup n lam c₁ c₂ f₁ f₂ R2) (hne : (∃ m, f₁ m ≠ 0) ∨ (∃ m, f₂ m ≠ 0)) :
    |lam - n * Real.pi| ≤ R2 / (1 + |(n : ℝ)|) +
      Real.sqrt 2 * Real.sqrt R2 / (1 + |((2 * n : ℤ) : ℝ)|) := by
  obtain ⟨hz₁, i₁⟩ := core_one S
  obtain ⟨hz₂, i₂⟩ := core_one S.swap
  have hp : ¬ (f₁ n = 0 ∧ f₂ n = 0) := by
    rintro ⟨h1, h2⟩
    have g1 := hz₁ h1 h2
    have g2 := hz₂ h2 h1
    have hf : ∀ (f : ℤ → ℂ), f n = 0 → (∀ m, hF lam f m = 0) → ∀ m, f m = 0 := by
      intro f hf0 hg m
      by_cases hm : m = n
      · rw [hm]; exact hf0
      · rw [← sF_hF n lam S.hlam f m hm, hg m, mul_zero]
    rcases hne with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact hm (hf f₁ h1 g1 m)
    · exact hm (hf f₂ h2 g2 m)
  set A := R2 / (1 + |(n : ℝ)|)
  set B := Real.sqrt 2 * Real.sqrt R2 / (1 + |((2 * n : ℤ) : ℝ)|)
  have hA : 0 ≤ A := div_nonneg S.hR (by positivity)
  have hB : 0 ≤ B := by positivity
  set D := |lam - n * Real.pi|
  rcases le_total ‖f₂ n‖ ‖f₁ n‖ with h | h
  · have hpos : 0 < ‖f₁ n‖ := by
      rcases (norm_nonneg (f₁ n)).lt_or_eq with h0 | h0
      · exact h0
      · exfalso; apply hp
        have h1 : f₁ n = 0 := norm_eq_zero.mp h0.symm
        refine ⟨h1, norm_eq_zero.mp (le_antisymm (h0 ▸ h) (norm_nonneg _))⟩
    have : D * ‖f₁ n‖ ≤ (A + B) * ‖f₁ n‖ := by
      calc D * ‖f₁ n‖ ≤ A * ‖f₁ n‖ + B * ‖f₂ n‖ := i₁
        _ ≤ A * ‖f₁ n‖ + B * ‖f₁ n‖ := by gcongr
        _ = _ := by ring
    exact le_of_mul_le_mul_right this hpos
  · have hpos : 0 < ‖f₂ n‖ := by
      rcases (norm_nonneg (f₂ n)).lt_or_eq with h0 | h0
      · exact h0
      · exfalso; apply hp
        have h2 : f₂ n = 0 := norm_eq_zero.mp h0.symm
        refine ⟨norm_eq_zero.mp (le_antisymm (h0 ▸ h) (norm_nonneg _)), h2⟩
    have : D * ‖f₂ n‖ ≤ (A + B) * ‖f₂ n‖ := by
      calc D * ‖f₂ n‖ ≤ A * ‖f₂ n‖ + B * ‖f₁ n‖ := i₂
        _ ≤ A * ‖f₂ n‖ + B * ‖f₂ n‖ := by gcongr
        _ = _ := by ring
    exact le_of_mul_le_mul_right this hpos

end

end NlsGge.GK38.Mo2
