import NlsGge.GK38.MolnarLocalizationB2

/-!
# Mo2 (part B3): the reduction to `h = u + p₁ q + Ω h`

Fourier-side system (Molnár §3, `A_λ f = Φ f`): `(λ - mπ) f₁_m = Σ_l c₁_{m+l} f₂_l`,
`(λ - mπ) f₂_m = Σ_l c₂_{m+l} f₁_l` (`Setup`).  With `h_i = (λ - ·π) f_i` and `s = (λ - ·π)⁻¹`
off `n`: `h₁ = c₁(·+n) p₂ + C₁ G h₂`, hence (`key_identity`) `h₁ = c₁(·+n) p₂ + p₁ q + Ω h₁`
with `q = C₁ G c₂(·+n)` and `Ω = C₁ G C₂ G`.  `K_bound`/`nu_Om_le`: under `⟨n⟩ ≥ 8 R2` the
operator `Ω` has norm `≤ 7/25` in the shifted norm (Molnár's Lemma 6: `‖T_n²‖ ≤ 1/2`).
Then the size bounds for `q` (`nu_q_le`, `q_n_le`, Molnár Lemma 9).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ENNReal NNReal

namespace NlsGge.GK38.Mo2

noncomputable section

open NlsGge.GK38.Mo2

/-! ### The reduction -/

/-- `h_m = (λ - mπ) f_m`. -/
def hF (lam : ℝ) (f : ℤ → ℂ) (m : ℤ) : ℂ := ((lam - m * Real.pi : ℝ) : ℂ) * f m

/-- Hypotheses of the Lyapunov-Schmidt estimate (Molnár, Lemmas 5-10). -/
structure Setup (n : ℤ) (lam : ℝ) (c₁ c₂ f₁ f₂ : ℤ → ℂ) (R2 : ℝ) : Prop where
  hlam : |lam - n * Real.pi| ≤ Real.pi / 2
  hR : 0 ≤ R2
  hS : SW c₁ + SW c₂ ≤ ENNReal.ofReal R2
  h8 : 8 * R2 ≤ 1 + |(n : ℝ)|
  hf₁ : SW f₁ ≠ ⊤
  hf₂ : SW f₂ ≠ ⊤
  e₁ : ∀ m, HasSum (fun l => c₁ (m + l) * f₂ l) (hF lam f₁ m)
  e₂ : ∀ m, HasSum (fun l => c₂ (m + l) * f₁ l) (hF lam f₂ m)

theorem Setup.swap {n : ℤ} {lam : ℝ} {c₁ c₂ f₁ f₂ : ℤ → ℂ} {R2 : ℝ}
    (S : Setup n lam c₁ c₂ f₁ f₂ R2) : Setup n lam c₂ c₁ f₂ f₁ R2 :=
  ⟨S.hlam, S.hR, by rw [add_comm]; exact S.hS, S.h8, S.hf₂, S.hf₁, S.e₂, S.e₁⟩

theorem sF_hF (n : ℤ) (lam : ℝ) (hlam : |lam - n * Real.pi| ≤ Real.pi / 2) (f : ℤ → ℂ) (l : ℤ)
    (h : l ≠ n) : sF n lam l * hF lam f l = f l := by
  have h2 := lam_sub_abs_ge n l lam hlam h
  have h1 := int_sub_abs_ge n l h
  have hne : lam - l * Real.pi ≠ 0 := by
    intro h0; rw [h0] at h2; simp at h2; linarith
  have hne' : ((lam - l * Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hne
  simp only [sF, hF, h, ite_false]
  rw [← mul_assoc, inv_mul_cancel₀ hne', one_mul]

theorem Gs_hF (n : ℤ) (lam : ℝ) (hlam : |lam - n * Real.pi| ≤ Real.pi / 2) (f : ℤ → ℂ) (l : ℤ) :
    Gs n lam (hF lam f) l = if l = n then 0 else f l := by
  by_cases h : l = n
  · subst h; simp [Gs, sF_self]
  · simp only [Gs, h, ite_false]; exact sF_hF n lam hlam f l h

theorem split_hk {n : ℤ} {lam : ℝ} {c₁ c₂ f₁ f₂ : ℤ → ℂ} {R2 : ℝ}
    (S : Setup n lam c₁ c₂ f₁ f₂ R2) (m : ℤ) :
    HasSum (fun l => c₁ (m + l) * Gs n lam (hF lam f₂) l) (hF lam f₁ m - c₁ (m + n) * f₂ n) := by
  have hg := (S.e₁ m).update n 0
  have hfun : (fun l => c₁ (m + l) * Gs n lam (hF lam f₂) l) =
      Function.update (fun l => c₁ (m + l) * f₂ l) n 0 := by
    funext l
    rw [Gs_hF n lam S.hlam]
    by_cases h : l = n
    · subst h; simp
    · simp [h]
  rw [hfun]
  convert hg using 1
  ring

theorem hk_split_eq {n : ℤ} {lam : ℝ} {c₁ c₂ f₁ f₂ : ℤ → ℂ} {R2 : ℝ}
    (S : Setup n lam c₁ c₂ f₁ f₂ R2) (m : ℤ) :
    hk c₁ (Gs n lam (hF lam f₂)) m = hF lam f₁ m - c₁ (m + n) * f₂ n :=
  (split_hk S m).tsum_eq


theorem sF_enorm_le (n : ℤ) (lam : ℝ) (hlam : |lam - n * Real.pi| ≤ Real.pi / 2) (l : ℤ) :
    ‖sF n lam l‖ₑ ≤ ENNReal.ofReal (2 / 3) := by
  by_cases h : l = n
  · subst h; simp [sF_self]
  have h1 := int_sub_abs_ge n l h
  have h2 := sF_norm_le n lam hlam l h
  rw [← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  refine h2.trans ?_
  rw [div_le_iff₀ (by linarith)]
  nlinarith

theorem eW_ge_one (k : ℤ) : 1 ≤ eW k := by
  unfold eW
  calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith [abs_nonneg (k : ℝ)])

theorem enorm_sq_shift_le (m : ℤ) (c : ℤ → ℂ) : ∑' l, ‖c (m + l)‖ₑ ^ 2 ≤ SW c := by
  have : ∑' l : ℤ, (eW (m + l) * ‖c (m + l)‖ₑ) ^ 2 = SW c :=
    (Equiv.addLeft m).tsum_eq (fun k : ℤ => (eW k * ‖c k‖ₑ) ^ 2)
  rw [← this]
  refine ENNReal.tsum_le_tsum fun l => ?_
  gcongr
  calc ‖c (m + l)‖ₑ = 1 * ‖c (m + l)‖ₑ := (one_mul _).symm
    _ ≤ _ := by gcongr; exact eW_ge_one _

theorem enorm_sq_shift_le' (n : ℤ) (c : ℤ → ℂ) : ∑' l, ‖c (l + n)‖ₑ ^ 2 ≤ SW c := by
  have := enorm_sq_shift_le n c
  simpa [add_comm] using this

theorem summable_A {n : ℤ} {lam : ℝ} {c₁ c₂ f₁ f₂ : ℤ → ℂ} {R2 : ℝ}
    (S : Setup n lam c₁ c₂ f₁ f₂ R2) (m : ℤ) :
    Summable (fun l => c₁ (m + l) * (sF n lam l * c₂ (l + n))) := by
  apply Summable.of_enorm
  have hc₁ : SW c₁ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans le_self_add S.hS)
  have hc₂ : SW c₂ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans le_add_self S.hS)
  have h1 : ∑' l, ‖c₁ (m + l) * (sF n lam l * c₂ (l + n))‖ₑ ≤
      ENNReal.ofReal (2 / 3) * ∑' l, ‖c₁ (m + l)‖ₑ * ‖c₂ (l + n)‖ₑ := by
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun l => ?_
    simp only [enorm_mul]
    calc ‖c₁ (m + l)‖ₑ * (‖sF n lam l‖ₑ * ‖c₂ (l + n)‖ₑ)
        ≤ ‖c₁ (m + l)‖ₑ * (ENNReal.ofReal (2 / 3) * ‖c₂ (l + n)‖ₑ) := by
          gcongr; exact sF_enorm_le n lam S.hlam l
      _ = _ := by ring
  have h2 : (∑' l, ‖c₁ (m + l)‖ₑ * ‖c₂ (l + n)‖ₑ) ^ 2 ≤ SW c₁ * SW c₂ :=
    (cs _ _).trans (mul_le_mul' (enorm_sq_shift_le m c₁) (enorm_sq_shift_le' n c₂))
  have h3 : ∑' l, ‖c₁ (m + l)‖ₑ * ‖c₂ (l + n)‖ₑ ≠ ⊤ := by
    intro htop
    rw [htop] at h2
    simp at h2
    exact (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hc₁) (lt_top_iff_ne_top.2 hc₂)).ne h2
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h3) h1

/-- The identity `h = u + p₁ q + Ω h` (Molnár, proof of Lemma 6/9, with `h = Φ(u+v)`). -/
theorem key_identity {n : ℤ} {lam : ℝ} {c₁ c₂ f₁ f₂ : ℤ → ℂ} {R2 : ℝ}
    (S : Setup n lam c₁ c₂ f₁ f₂ R2) (m : ℤ) :
    hF lam f₁ m = c₁ (m + n) * f₂ n + f₁ n * hk c₁ (Gs n lam (fun k => c₂ (k + n))) m +
      hk c₁ (Gs n lam (hk c₂ (Gs n lam (hF lam f₁)))) m := by
  set z := hk c₂ (Gs n lam (hF lam f₁)) with hz
  have e2 : ∀ l, hF lam f₂ l = c₂ (l + n) * f₁ n + z l := by
    intro l
    have := hk_split_eq S.swap l
    rw [← hz] at this
    rw [this]; ring
  have hGs : ∀ l, Gs n lam (hF lam f₂) l =
      f₁ n * Gs n lam (fun k => c₂ (k + n)) l + Gs n lam z l := by
    intro l; simp only [Gs, e2]; ring
  set A : ℤ → ℂ := fun l => c₁ (m + l) * (f₁ n * Gs n lam (fun k => c₂ (k + n)) l) with hA
  set B : ℤ → ℂ := fun l => c₁ (m + l) * Gs n lam z l with hB
  have hAB := split_hk S m
  have hAB' : HasSum (fun l => A l + B l) (hF lam f₁ m - c₁ (m + n) * f₂ n) := by
    convert hAB using 1
    funext l
    rw [hGs]; simp only [hA, hB]; ring
  have hAs : Summable A := by
    have := (summable_A S m).mul_left (f₁ n)
    refine this.congr fun l => ?_
    simp only [hA, Gs]; ring
  have hBs : Summable B := by
    have := hAB'.summable.sub hAs
    refine this.congr fun l => ?_
    simp
  have hsum := hAB'.tsum_eq
  rw [hAs.tsum_add hBs] at hsum
  have h1 : ∑' l, A l = f₁ n * hk c₁ (Gs n lam (fun k => c₂ (k + n))) m := by
    unfold hk
    rw [← tsum_mul_left]
    refine tsum_congr fun l => ?_
    simp only [hA]; ring
  have h2 : ∑' l, B l = hk c₁ (Gs n lam z) m := rfl
  rw [h1, h2] at hsum
  linear_combination -hsum


theorem le_of_sq_le_sq (x y : ℝ≥0∞) (h : x ^ 2 ≤ y ^ 2) : x ≤ y := by
  have := ENNReal.rpow_le_rpow h (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  rwa [sq_rpow_half, sq_rpow_half] at this

theorem SW_ne_top {n : ℤ} {lam : ℝ} {c₁ c₂ f₁ f₂ : ℤ → ℂ} {R2 : ℝ}
    (S : Setup n lam c₁ c₂ f₁ f₂ R2) : SW c₁ ≠ ⊤ ∧ SW c₂ ≠ ⊤ :=
  ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans le_self_add S.hS),
   ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans le_add_self S.hS)⟩

/-- `‖Ω‖² ≤ 49/625` in the range `⟨n⟩ ≥ 8 ‖φ‖₁²` (Molnár, Lemma 6: `Tₙ²` is a contraction). -/
theorem K_bound {n : ℤ} {lam : ℝ} {c₁ c₂ f₁ f₂ : ℤ → ℂ} {R2 : ℝ}
    (S : Setup n lam c₁ c₂ f₁ f₂ R2) :
    SW c₁ * SW c₂ * (ENNReal.ofReal (512 / 27) * iW n ^ 2) ≤ ENNReal.ofReal (49 / 625) := by
  set S₁ := SW c₁
  set S₂ := SW c₂
  have h4 : 4 * (S₁ * S₂) ≤ ENNReal.ofReal R2 ^ 2 := by
    have := two_mul_le_sq S₁ S₂
    calc 4 * (S₁ * S₂) = 2 * (S₁ * S₂) + 2 * (S₁ * S₂) := by ring
      _ ≤ (S₁ ^ 2 + S₂ ^ 2) + 2 * (S₁ * S₂) := by gcongr
      _ = (S₁ + S₂) ^ 2 := by ring
      _ ≤ _ := by gcongr; exact S.hS
  have hN : 0 < 1 + |(n : ℝ)| := by positivity
  have hiW : iW n ^ 2 = ENNReal.ofReal (1 / (1 + |(n : ℝ)|) ^ 2) := iW_sq n
  have h5 : 4 * (S₁ * S₂ * iW n ^ 2) ≤ ENNReal.ofReal (1 / 64) := by
    calc 4 * (S₁ * S₂ * iW n ^ 2) = (4 * (S₁ * S₂)) * iW n ^ 2 := by ring
      _ ≤ ENNReal.ofReal R2 ^ 2 * iW n ^ 2 := by gcongr
      _ = ENNReal.ofReal (R2 ^ 2 * (1 / (1 + |(n : ℝ)|) ^ 2)) := by
          rw [hiW, ← ENNReal.ofReal_pow S.hR, ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (1 / 64) := by
          apply ENNReal.ofReal_le_ofReal
          have h8 := S.h8
          have hR := S.hR
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  have h6 : 4 * (S₁ * S₂ * (ENNReal.ofReal (512 / 27) * iW n ^ 2)) ≤ ENNReal.ofReal (8 / 27) := by
    calc 4 * (S₁ * S₂ * (ENNReal.ofReal (512 / 27) * iW n ^ 2))
        = ENNReal.ofReal (512 / 27) * (4 * (S₁ * S₂ * iW n ^ 2)) := by ring
      _ ≤ ENNReal.ofReal (512 / 27) * ENNReal.ofReal (1 / 64) := by gcongr
      _ = ENNReal.ofReal (8 / 27) := by
          rw [← ENNReal.ofReal_mul (by norm_num)]; norm_num
  have h7 : 4 * (S₁ * S₂ * (ENNReal.ofReal (512 / 27) * iW n ^ 2)) ≤
      4 * ENNReal.ofReal (49 / 625) := by
    refine h6.trans ?_
    rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).1 h7

theorem nu_Om_le {n : ℤ} {lam : ℝ} {c₁ c₂ f₁ f₂ : ℤ → ℂ} {R2 : ℝ}
    (S : Setup n lam c₁ c₂ f₁ f₂ R2) (x : ℤ → ℂ) :
    nu n (hk c₁ (Gs n lam (hk c₂ (Gs n lam x)))) ≤ ENNReal.ofReal (7 / 25) * nu n x := by
  have h1 := Q_Om n lam S.hlam c₁ c₂ x
  have h2 : Q n (hk c₁ (Gs n lam (hk c₂ (Gs n lam x)))) ≤ ENNReal.ofReal (49 / 625) * Q n x :=
    h1.trans (mul_le_mul' (K_bound S) le_rfl)
  unfold nu
  calc (Q n (hk c₁ (Gs n lam (hk c₂ (Gs n lam x))))) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal (49 / 625) * Q n x) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow h2 (by norm_num)
    _ = ENNReal.ofReal (7 / 25) * (Q n x) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by norm_num)]
        congr 2
        rw [← Real.sqrt_eq_rpow, show (49 / 625 : ℝ) = (7 / 25) ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]


theorem le_ofReal_sqrt (x : ℝ≥0∞) (σ : ℝ) (hσ : 0 ≤ σ) (h : x ^ 2 ≤ ENNReal.ofReal σ) :
    x ≤ ENNReal.ofReal (Real.sqrt σ) := by
  have := ENNReal.rpow_le_rpow h (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  rwa [sq_rpow_half, ENNReal.ofReal_rpow_of_nonneg hσ (by norm_num), ← Real.sqrt_eq_rpow] at this

theorem nu_U (n : ℤ) (c : ℤ → ℂ) : nu n (fun m => c (m + n)) = (SW c) ^ (1 / 2 : ℝ) := by
  unfold nu; rw [Q_shift]

theorem SW_eq_ofReal (c : ℤ → ℂ) (h : SW c ≠ ⊤) : SW c = ENNReal.ofReal (SW c).toReal :=
  (ENNReal.ofReal_toReal h).symm

theorem nu_U_eq (n : ℤ) (c : ℤ → ℂ) (σ : ℝ) (hσ : 0 ≤ σ) (h : SW c = ENNReal.ofReal σ) :
    nu n (fun m => c (m + n)) = ENNReal.ofReal (Real.sqrt σ) := by
  rw [nu_U, h, ENNReal.ofReal_rpow_of_nonneg hσ (by norm_num), ← Real.sqrt_eq_rpow]

/-- Weighted `ℓ¹` bound of `Σ_k ‖c_k‖ₑ` in terms of `σ = Σ ⟨k⟩²|c_k|²`. -/
theorem l1_le_sqrt (c : ℤ → ℂ) (σ : ℝ) (hσ : 0 ≤ σ) (h : SW c = ENNReal.ofReal σ) :
    ∑' k, ‖c k‖ₑ ≤ ENNReal.ofReal (Real.sqrt 3 * Real.sqrt σ) := by
  rw [← Real.sqrt_mul (by norm_num)]
  apply le_ofReal_sqrt _ _ (by positivity)
  refine (l1_sq_le c).trans ?_
  rw [h, show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by simp, ← ENNReal.ofReal_mul (by norm_num)]

theorem nu_q_le {n : ℤ} {lam : ℝ} {c₁ c₂ f₁ f₂ : ℤ → ℂ} {R2 : ℝ}
    (S : Setup n lam c₁ c₂ f₁ f₂ R2) (σ₁ σ₂ : ℝ) (h₁ : 0 ≤ σ₁) (h₂ : 0 ≤ σ₂)
    (e₁ : SW c₁ = ENNReal.ofReal σ₁) (e₂ : SW c₂ = ENNReal.ofReal σ₂) :
    nu n (hk c₁ (Gs n lam (fun k => c₂ (k + n)))) ≤
      ENNReal.ofReal (Real.sqrt σ₁ * (4 / 3 * (Real.sqrt 3 * Real.sqrt σ₂))) := by
  refine (nu_hk n c₁ _).trans ?_
  have h1 : ∑' l, eW (l - n) * ‖Gs n lam (fun k => c₂ (k + n)) l‖ₑ ≤
      ENNReal.ofReal (4 / 3) * ∑' k, ‖c₂ k‖ₑ := by
    calc ∑' l, eW (l - n) * ‖Gs n lam (fun k => c₂ (k + n)) l‖ₑ
        ≤ ∑' l, ENNReal.ofReal (4 / 3) * ‖c₂ (l + n)‖ₑ := by
          refine ENNReal.tsum_le_tsum fun l => ?_
          simp only [Gs, enorm_mul]
          calc eW (l - n) * (‖sF n lam l‖ₑ * ‖c₂ (l + n)‖ₑ)
              = (eW (l - n) * ‖sF n lam l‖ₑ) * ‖c₂ (l + n)‖ₑ := by ring
            _ ≤ _ := by gcongr; exact S1_bound n lam S.hlam l
      _ = ENNReal.ofReal (4 / 3) * ∑' k, ‖c₂ k‖ₑ := by
          rw [ENNReal.tsum_mul_left]
          congr 1
          exact (Equiv.addRight n).tsum_eq (fun k : ℤ => ‖c₂ k‖ₑ)
  have h2 := l1_le_sqrt c₂ σ₂ h₂ e₂
  calc (SW c₁) ^ (1 / 2 : ℝ) * ∑' l, eW (l - n) * ‖Gs n lam (fun k => c₂ (k + n)) l‖ₑ
      ≤ (SW c₁) ^ (1 / 2 : ℝ) * (ENNReal.ofReal (4 / 3) * ENNReal.ofReal (Real.sqrt 3 * Real.sqrt σ₂)) := by
        gcongr; exact h1.trans (by gcongr)
    _ = _ := by
        rw [e₁, ENNReal.ofReal_rpow_of_nonneg h₁ (by norm_num), ← Real.sqrt_eq_rpow,
          ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]

theorem q_n_le {n : ℤ} {lam : ℝ} {c₁ c₂ f₁ f₂ : ℤ → ℂ} {R2 : ℝ}
    (S : Setup n lam c₁ c₂ f₁ f₂ R2) (σ₁ σ₂ : ℝ) (h₁ : 0 ≤ σ₁) (h₂ : 0 ≤ σ₂)
    (e₁ : SW c₁ = ENNReal.ofReal σ₁) (e₂ : SW c₂ = ENNReal.ofReal σ₂) :
    ‖hk c₁ (Gs n lam (fun k => c₂ (k + n))) n‖ₑ ≤
      ENNReal.ofReal (2 / 3 * (1 / (1 + |(n : ℝ)|)) * (Real.sqrt σ₁ * Real.sqrt σ₂)) := by
  set u : ℤ → ℝ≥0∞ := fun l => ‖c₁ (n + l)‖ₑ with hu
  set v : ℤ → ℝ≥0∞ := fun l => eW (l + n) * ‖c₂ (l + n)‖ₑ with hv
  have hpt : ‖hk c₁ (Gs n lam (fun k => c₂ (k + n))) n‖ₑ ≤
      ENNReal.ofReal (2 / 3) * iW n * ∑' l, u l * v l := by
    calc _ ≤ ∑' l, ‖c₁ (n + l)‖ₑ * ‖Gs n lam (fun k => c₂ (k + n)) l‖ₑ := enorm_hk_le _ _ n
      _ ≤ ∑' l, ENNReal.ofReal (2 / 3) * iW n * (u l * v l) := by
          refine ENNReal.tsum_le_tsum fun l => ?_
          simp only [Gs, enorm_mul, hu, hv]
          have h3 := S3_bound n lam S.hlam l
          calc ‖c₁ (n + l)‖ₑ * (‖sF n lam l‖ₑ * ‖c₂ (l + n)‖ₑ)
              = ‖c₁ (n + l)‖ₑ * ((‖sF n lam l‖ₑ * iW (l + n)) * (eW (l + n) * ‖c₂ (l + n)‖ₑ)) := by
                have := iW_mul_eW (l + n)
                calc ‖c₁ (n + l)‖ₑ * (‖sF n lam l‖ₑ * ‖c₂ (l + n)‖ₑ)
                    = ‖c₁ (n + l)‖ₑ * (‖sF n lam l‖ₑ * ‖c₂ (l + n)‖ₑ) * (iW (l + n) * eW (l + n)) := by
                      rw [this, mul_one]
                  _ = _ := by ring
            _ ≤ ‖c₁ (n + l)‖ₑ * ((ENNReal.ofReal (2 / 3) * iW n) * (eW (l + n) * ‖c₂ (l + n)‖ₑ)) := by
                gcongr
            _ = _ := by ring
      _ = _ := by rw [ENNReal.tsum_mul_left]
  have hcs : (∑' l, u l * v l) ^ 2 ≤ ENNReal.ofReal (σ₁ * σ₂) := by
    refine (cs u v).trans ?_
    have hu2 : ∑' l, u l ^ 2 ≤ SW c₁ := enorm_sq_shift_le n c₁
    have hv2 : ∑' l, v l ^ 2 = SW c₂ :=
      (Equiv.addRight n).tsum_eq (fun k : ℤ => (eW k * ‖c₂ k‖ₑ) ^ 2)
    rw [hv2, e₂, ENNReal.ofReal_mul h₁]
    rw [e₁] at hu2
    exact mul_le_mul' hu2 le_rfl
  have h4 := le_ofReal_sqrt _ _ (mul_nonneg h₁ h₂) hcs
  rw [Real.sqrt_mul h₁] at h4
  refine hpt.trans ?_
  calc ENNReal.ofReal (2 / 3) * iW n * ∑' l, u l * v l
      ≤ ENNReal.ofReal (2 / 3) * iW n * ENNReal.ofReal (Real.sqrt σ₁ * Real.sqrt σ₂) := by gcongr
    _ = _ := by
        unfold iW
        rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]

end

end NlsGge.GK38.Mo2
