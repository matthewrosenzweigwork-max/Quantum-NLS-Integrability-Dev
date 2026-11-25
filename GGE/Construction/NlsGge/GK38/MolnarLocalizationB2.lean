import NlsGge.GK38.MolnarLocalizationB1

/-!
# Mo2 (part B2): the resolvent weights and the contraction estimate

`sF n λ l = (λ - lπ)⁻¹` (`l ≠ n`), `|λ - nπ| ≤ π/2`, hence `|λ - lπ| ≥ (3/2)|l - n|`.
Contents: `S1_bound`, `S3_bound`, `Lb_sum` (the lattice sum behind Molnár's constants `32/5`, `5/2`
of Lemma 6, here `Σ_k |s_k|² ⟨k+n⟩⁻² ≤ (32/9)⟨n⟩⁻²`), `LB` (weighted `ℓ¹` bound of `G C₂ G x`,
Lemma 6) and `Q_Om` (squared contraction bound for `Ω = C₁ G C₂ G`, i.e. `T_n²`), then the
finiteness `Q_hk_ne_top` of `c ⋆ y` for two `H¹` sequences and the absorption lemma `absorb`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ENNReal NNReal

namespace NlsGge.GK38.Mo2

noncomputable section

open NlsGge.GK38.Mo2

/-! ### The resolvent weights `s_l = 1/(λ - lπ)` -/

/-- `s_l = (λ - lπ)⁻¹` for `l ≠ n`, and `s_n = 0`. -/
def sF (n : ℤ) (lam : ℝ) (l : ℤ) : ℂ := if l = n then 0 else (((lam - l * Real.pi : ℝ)) : ℂ)⁻¹

theorem sF_self (n : ℤ) (lam : ℝ) : sF n lam n = 0 := by simp [sF]

theorem int_sub_abs_ge (n l : ℤ) (h : l ≠ n) : (1 : ℝ) ≤ |((l : ℝ) - n)| := by
  have : (1 : ℤ) ≤ |l - n| := Int.one_le_abs (sub_ne_zero.mpr h)
  have h2 : (1 : ℝ) ≤ ((|l - n| : ℤ) : ℝ) := by exact_mod_cast this
  simpa using h2

theorem lam_sub_abs_ge (n l : ℤ) (lam : ℝ) (hlam : |lam - n * Real.pi| ≤ Real.pi / 2) (h : l ≠ n) :
    (3 / 2 : ℝ) * |((l : ℝ) - n)| ≤ |lam - l * Real.pi| := by
  have hpi := Real.pi_gt_three
  have h1 := int_sub_abs_ge n l h
  have h2 : |((l : ℝ) - n) * Real.pi| ≤ |lam - l * Real.pi| + |lam - n * Real.pi| := by
    have : ((l : ℝ) - n) * Real.pi = (lam - n * Real.pi) - (lam - l * Real.pi) := by ring
    rw [this]
    calc |(lam - n * Real.pi) - (lam - l * Real.pi)|
        ≤ |lam - n * Real.pi| + |lam - l * Real.pi| := abs_sub _ _
      _ = _ := add_comm _ _
  rw [abs_mul, abs_of_pos Real.pi_pos] at h2
  nlinarith

theorem sF_norm_le (n : ℤ) (lam : ℝ) (hlam : |lam - n * Real.pi| ≤ Real.pi / 2) (l : ℤ)
    (h : l ≠ n) : ‖sF n lam l‖ ≤ (2 / 3) / |((l : ℝ) - n)| := by
  have h1 := int_sub_abs_ge n l h
  have h2 := lam_sub_abs_ge n l lam hlam h
  have hpos : 0 < |((l : ℝ) - n)| := by linarith
  have hne : lam - l * Real.pi ≠ 0 := by
    intro h0; rw [h0] at h2; simp at h2; linarith
  simp only [sF, h, ite_false, norm_inv, Complex.norm_real, Real.norm_eq_abs]
  rw [le_div_iff₀ hpos, inv_mul_le_iff₀ (abs_pos.mpr hne)]
  linarith

/-- `|l - n| (1 + |l + n|) ≥ 1 + |n|` for `l ≠ n`. -/
theorem key_prod_ge (n l : ℤ) (h : l ≠ n) :
    1 + |(n : ℝ)| ≤ |((l : ℝ) - n)| * (1 + |((l : ℝ) + n)|) := by
  have h1 := int_sub_abs_ge n l h
  have hlin : (|n| : ℤ) + 1 ≤ |l - n| ∨ (|n| : ℤ) ≤ |l + n| := by
    rcases abs_cases n with ⟨hn, _⟩ | ⟨hn, _⟩ <;> rcases abs_cases (l - n) with ⟨ha, _⟩ | ⟨ha, _⟩ <;>
      rcases abs_cases (l + n) with ⟨hb, _⟩ | ⟨hb, _⟩ <;> omega
  have hb0 : (0 : ℝ) ≤ |((l : ℝ) + n)| := abs_nonneg _
  rcases hlin with hc | hc
  · have : (|n| : ℝ) + 1 ≤ |(l : ℝ) - n| := by exact_mod_cast hc
    nlinarith
  · have : (|n| : ℝ) ≤ |(l : ℝ) + n| := by exact_mod_cast hc
    nlinarith

theorem key_sq (n l : ℤ) (h : l ≠ n) :
    (1 + |(n : ℝ)|) ^ 2 ≤ 2 * |((l : ℝ) - n)| ^ 2 + (1 + |((l : ℝ) + n)|) ^ 2 / 2 := by
  have h1 := int_sub_abs_ge n l h
  have hn : 2 * |(n : ℝ)| ≤ |((l : ℝ) - n)| + |((l : ℝ) + n)| := by
    have : (2 : ℝ) * n = ((l : ℝ) + n) - ((l : ℝ) - n) := by ring
    calc 2 * |(n : ℝ)| = |2 * (n : ℝ)| := by rw [abs_mul]; norm_num
      _ = |((l : ℝ) + n) - ((l : ℝ) - n)| := by rw [this]
      _ ≤ |((l : ℝ) + n)| + |((l : ℝ) - n)| := abs_sub _ _
      _ = _ := add_comm _ _
  set X := |((l : ℝ) - n)|
  set Y := 1 + |((l : ℝ) + n)|
  have hY : 1 ≤ Y := by simp only [Y]; linarith [abs_nonneg ((l : ℝ) + n)]
  have hN : 1 + |(n : ℝ)| ≤ (1 + X + Y) / 2 := by simp only [Y]; linarith
  have hN0 : 0 ≤ 1 + |(n : ℝ)| := by positivity
  have h2 : (1 + |(n : ℝ)|) ^ 2 ≤ ((1 + X + Y) / 2) ^ 2 := by gcongr
  nlinarith [sq_nonneg (2 * X - Y)]

theorem S1_bound (n : ℤ) (lam : ℝ) (hlam : |lam - n * Real.pi| ≤ Real.pi / 2) (l : ℤ) :
    eW (l - n) * ‖sF n lam l‖ₑ ≤ ENNReal.ofReal (4 / 3) := by
  by_cases h : l = n
  · subst h; simp [sF_self]
  have h1 := int_sub_abs_ge n l h
  have h2 := sF_norm_le n lam hlam l h
  have hpos : 0 < |((l : ℝ) - n)| := by linarith
  rw [← ofReal_norm]
  unfold eW
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  push_cast
  calc (1 + |((l : ℝ) - n)|) * ‖sF n lam l‖ ≤ (1 + |((l : ℝ) - n)|) * ((2 / 3) / |((l : ℝ) - n)|) := by
        gcongr
    _ ≤ 4 / 3 := by
        rw [mul_div_assoc', div_le_iff₀ hpos]
        nlinarith

theorem S3_bound (n : ℤ) (lam : ℝ) (hlam : |lam - n * Real.pi| ≤ Real.pi / 2) (l : ℤ) :
    ‖sF n lam l‖ₑ * iW (l + n) ≤ ENNReal.ofReal (2 / 3) * iW n := by
  by_cases h : l = n
  · subst h; simp [sF_self]
  have h1 := int_sub_abs_ge n l h
  have h2 := sF_norm_le n lam hlam l h
  have hpos : 0 < |((l : ℝ) - n)| := by linarith
  have hk := key_prod_ge n l h
  rw [← ofReal_norm]
  unfold iW
  rw [← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  push_cast
  have hY : 0 < 1 + |((l : ℝ) + n)| := by positivity
  have hN : 0 < 1 + |(n : ℝ)| := by positivity
  calc ‖sF n lam l‖ * (1 / (1 + |((l : ℝ) + n)|))
      ≤ ((2 / 3) / |((l : ℝ) - n)|) * (1 / (1 + |((l : ℝ) + n)|)) := by gcongr
    _ = (2 / 3) / (|((l : ℝ) - n)| * (1 + |((l : ℝ) + n)|)) := by
        field_simp
    _ ≤ (2 / 3) * (1 / (1 + |(n : ℝ)|)) := by
        rw [mul_one_div]
        apply div_le_div_of_nonneg_left (by norm_num) hN hk


theorem Lb_term (n : ℤ) (lam : ℝ) (hlam : |lam - n * Real.pi| ≤ Real.pi / 2) (k : ℤ) :
    eW n ^ 2 * (‖sF n lam k‖ₑ ^ 2 * iW (k + n) ^ 2) ≤
      ENNReal.ofReal (8 / 9) * iW (k + n) ^ 2 +
      ENNReal.ofReal (2 / 9) * ENNReal.ofReal (1 / (((k - n : ℤ) : ℝ)) ^ 2) := by
  by_cases h : k = n
  · subst h; simp [sF_self]
  have h1 := int_sub_abs_ge n k h
  have h2 := sF_norm_le n lam hlam k h
  have hk := key_sq n k h
  set X := |((k : ℝ) - n)| with hX
  set Y := 1 + |((k : ℝ) + n)| with hY
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by simp only [hY]; positivity
  have hu : ‖sF n lam k‖ ^ 2 * X ^ 2 ≤ 4 / 9 := by
    have h3 : ‖sF n lam k‖ * X ≤ 2 / 3 := by
      calc ‖sF n lam k‖ * X ≤ ((2 / 3) / X) * X := by gcongr
        _ = 2 / 3 := by field_simp
    calc ‖sF n lam k‖ ^ 2 * X ^ 2 = (‖sF n lam k‖ * X) ^ 2 := by ring
      _ ≤ (2 / 3) ^ 2 := pow_le_pow_left₀ (by positivity) h3 2
      _ = 4 / 9 := by norm_num
  have hreal : (1 + |(n : ℝ)|) ^ 2 * (‖sF n lam k‖ ^ 2 * (1 / Y) ^ 2) ≤
      (8 / 9) * (1 / Y) ^ 2 + (2 / 9) * (1 / X ^ 2) := by
    have hmain : (1 + |(n : ℝ)|) ^ 2 * (‖sF n lam k‖ ^ 2 * X ^ 2) ≤ (8 / 9) * X ^ 2 + (2 / 9) * Y ^ 2 := by
      have hN2 : 0 ≤ (1 + |(n : ℝ)|) ^ 2 := by positivity
      calc (1 + |(n : ℝ)|) ^ 2 * (‖sF n lam k‖ ^ 2 * X ^ 2) ≤ (1 + |(n : ℝ)|) ^ 2 * (4 / 9) := by gcongr
        _ ≤ (2 * X ^ 2 + Y ^ 2 / 2) * (4 / 9) := by gcongr
        _ = _ := by ring
    calc (1 + |(n : ℝ)|) ^ 2 * (‖sF n lam k‖ ^ 2 * (1 / Y) ^ 2)
        = ((1 + |(n : ℝ)|) ^ 2 * (‖sF n lam k‖ ^ 2 * X ^ 2)) / (X ^ 2 * Y ^ 2) := by
          field_simp
      _ ≤ ((8 / 9) * X ^ 2 + (2 / 9) * Y ^ 2) / (X ^ 2 * Y ^ 2) := by gcongr
      _ = _ := by field_simp
  have hXsq : X ^ 2 = (((k - n : ℤ) : ℝ)) ^ 2 := by
    simp only [hX]; push_cast; exact sq_abs _
  rw [← hXsq]
  have e1 : eW n ^ 2 = ENNReal.ofReal ((1 + |(n : ℝ)|) ^ 2) := by
    unfold eW; rw [ENNReal.ofReal_pow (by positivity)]
  have e2 : ‖sF n lam k‖ₑ ^ 2 = ENNReal.ofReal (‖sF n lam k‖ ^ 2) := by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  have e3 : iW (k + n) ^ 2 = ENNReal.ofReal ((1 / Y) ^ 2) := by
    unfold iW
    rw [← ENNReal.ofReal_pow (by positivity)]
    simp only [hY]; push_cast; rfl
  rw [e1, e2, e3, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal hreal


theorem Lb_sum (n : ℤ) (lam : ℝ) (hlam : |lam - n * Real.pi| ≤ Real.pi / 2) :
    ∑' k, ‖sF n lam k‖ₑ ^ 2 * iW (k + n) ^ 2 ≤ ENNReal.ofReal (32 / 9) * iW n ^ 2 := by
  have hsum1 : ∑' k : ℤ, iW (k + n) ^ 2 = ∑' k : ℤ, iW k ^ 2 :=
    (Equiv.addRight n).tsum_eq (fun j : ℤ => iW j ^ 2)
  have hsum2 : ∑' k : ℤ, ENNReal.ofReal (1 / (((k - n : ℤ) : ℝ)) ^ 2) =
      ∑' a : ℤ, ENNReal.ofReal (1 / (a : ℝ) ^ 2) :=
    (Equiv.subRight n).tsum_eq (fun a : ℤ => ENNReal.ofReal (1 / (a : ℝ) ^ 2))
  have h1 : eW n ^ 2 * ∑' k, ‖sF n lam k‖ₑ ^ 2 * iW (k + n) ^ 2 ≤ ENNReal.ofReal (32 / 9) := by
    rw [← ENNReal.tsum_mul_left]
    calc ∑' k, eW n ^ 2 * (‖sF n lam k‖ₑ ^ 2 * iW (k + n) ^ 2)
        ≤ ∑' k : ℤ, (ENNReal.ofReal (8 / 9) * iW (k + n) ^ 2 +
          ENNReal.ofReal (2 / 9) * ENNReal.ofReal (1 / (((k - n : ℤ) : ℝ)) ^ 2)) :=
          ENNReal.tsum_le_tsum (Lb_term n lam hlam)
      _ = ENNReal.ofReal (8 / 9) * ∑' k : ℤ, iW (k + n) ^ 2 +
          ENNReal.ofReal (2 / 9) * ∑' k : ℤ, ENNReal.ofReal (1 / (((k - n : ℤ) : ℝ)) ^ 2) := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
      _ ≤ ENNReal.ofReal (8 / 9) * 3 + ENNReal.ofReal (2 / 9) * 4 := by
          rw [hsum1, hsum2]
          gcongr
          · exact La_sum
          · exact Lc_sum
      _ = ENNReal.ofReal (32 / 9) := by
          rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by simp, show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp,
            ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
          norm_num
  have h2 : iW n ^ 2 * eW n ^ 2 = 1 := by rw [← mul_pow, iW_mul_eW]; simp
  calc ∑' k, ‖sF n lam k‖ₑ ^ 2 * iW (k + n) ^ 2
      = iW n ^ 2 * (eW n ^ 2 * ∑' k, ‖sF n lam k‖ₑ ^ 2 * iW (k + n) ^ 2) := by
        rw [← mul_assoc, h2, one_mul]
    _ ≤ iW n ^ 2 * ENNReal.ofReal (32 / 9) := by gcongr
    _ = _ := mul_comm _ _


/-! ### The second-order operator `Ω = C₁ G C₂ G` -/

/-- `(G y)_l = s_l y_l`. -/
def Gs (n : ℤ) (lam : ℝ) (y : ℤ → ℂ) : ℤ → ℂ := fun l => sF n lam l * y l

theorem enorm_hk_le (c y : ℤ → ℂ) (m : ℤ) : ‖hk c y m‖ₑ ≤ ∑' l, ‖c (m + l)‖ₑ * ‖y l‖ₑ := by
  refine (enorm_tsum_le_tsum_enorm).trans ?_
  exact le_of_eq (tsum_congr fun l => enorm_mul _ _)

/-- Weighted `ℓ¹` bound of the intermediate vector `G C₂ G x` (Molnár, Lemma 6). -/
theorem LB (n : ℤ) (lam : ℝ) (hlam : |lam - n * Real.pi| ≤ Real.pi / 2) (c : ℤ → ℂ)
    (x : ℤ → ℂ) :
    (∑' l, eW (l - n) * ‖sF n lam l‖ₑ * ‖hk c (Gs n lam x) l‖ₑ) ^ 2 ≤
      SW c * (ENNReal.ofReal (512 / 27) * iW n ^ 2) * Q n x := by
  set a : ℤ → ℤ → ℝ≥0∞ := fun l k =>
    eW (l - n) * ‖sF n lam l‖ₑ * (‖sF n lam k‖ₑ * iW (k + n)) * iW (l + k) with ha
  set α : ℤ → ℝ≥0∞ := fun j => eW j * ‖c j‖ₑ with hα
  set β : ℤ → ℝ≥0∞ := fun k => eW (k + n) * ‖x k‖ₑ with hβ
  -- Step 1 and 2: rewrite as a double sum with the splitting
  have hstep : ∑' l, eW (l - n) * ‖sF n lam l‖ₑ * ‖hk c (Gs n lam x) l‖ₑ ≤
      ∑' k, β k * ∑' l, a l k * α (l + k) := by
    calc ∑' l, eW (l - n) * ‖sF n lam l‖ₑ * ‖hk c (Gs n lam x) l‖ₑ
        ≤ ∑' l, eW (l - n) * ‖sF n lam l‖ₑ * ∑' k, ‖c (l + k)‖ₑ * (‖sF n lam k‖ₑ * ‖x k‖ₑ) := by
          refine ENNReal.tsum_le_tsum fun l => ?_
          gcongr
          refine (enorm_hk_le c (Gs n lam x) l).trans ?_
          exact le_of_eq (tsum_congr fun k => by simp [Gs, enorm_mul])
      _ = ∑' l, ∑' k, eW (l - n) * ‖sF n lam l‖ₑ * (‖c (l + k)‖ₑ * (‖sF n lam k‖ₑ * ‖x k‖ₑ)) := by
          refine tsum_congr fun l => ?_
          rw [ENNReal.tsum_mul_left]
      _ = ∑' k, ∑' l, eW (l - n) * ‖sF n lam l‖ₑ * (‖c (l + k)‖ₑ * (‖sF n lam k‖ₑ * ‖x k‖ₑ)) :=
          ENNReal.tsum_comm
      _ = ∑' k, β k * ∑' l, a l k * α (l + k) := by
          refine tsum_congr fun k => ?_
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun l => ?_
          have e1 := iW_mul_eW (l + k)
          have e2 := iW_mul_eW (k + n)
          simp only [ha, hα, hβ]
          calc eW (l - n) * ‖sF n lam l‖ₑ * (‖c (l + k)‖ₑ * (‖sF n lam k‖ₑ * ‖x k‖ₑ))
              = (eW (l - n) * ‖sF n lam l‖ₑ * (‖c (l + k)‖ₑ * (‖sF n lam k‖ₑ * ‖x k‖ₑ))) *
                (iW (l + k) * eW (l + k)) * (iW (k + n) * eW (k + n)) := by
                rw [e1, e2]; simp
            _ = _ := by ring
  -- Step 3: Cauchy-Schwarz in `l`
  have hu : ∀ k, (∑' l, a l k * α (l + k)) ^ 2 ≤ (∑' l, a l k ^ 2) * SW c := by
    intro k
    have := cs (fun l => a l k) (fun l => α (l + k))
    have hre : ∑' l, α (l + k) ^ 2 = SW c :=
      (Equiv.addRight k).tsum_eq (fun j : ℤ => (eW j * ‖c j‖ₑ) ^ 2)
    rwa [hre] at this
  -- Step 4: Cauchy-Schwarz in `k`
  have h4 : (∑' k, β k * ∑' l, a l k * α (l + k)) ^ 2 ≤
      Q n x * ∑' k, (∑' l, a l k * α (l + k)) ^ 2 := cs β _
  -- Step 5: the size of `Σ_k Σ_l a²`
  have hA : ∀ k, ∑' l, a l k ^ 2 ≤ ENNReal.ofReal (16 / 3) * (‖sF n lam k‖ₑ ^ 2 * iW (k + n) ^ 2) := by
    intro k
    have hl : ∀ l, a l k ^ 2 ≤ ENNReal.ofReal (16 / 9) * ((‖sF n lam k‖ₑ * iW (k + n)) ^ 2 * iW (l + k) ^ 2) := by
      intro l
      have h1 := S1_bound n lam hlam l
      have h2 : (eW (l - n) * ‖sF n lam l‖ₑ) ^ 2 ≤ ENNReal.ofReal (16 / 9) := by
        calc (eW (l - n) * ‖sF n lam l‖ₑ) ^ 2 ≤ (ENNReal.ofReal (4 / 3)) ^ 2 := by gcongr
          _ = ENNReal.ofReal (16 / 9) := by
            rw [← ENNReal.ofReal_pow (by norm_num)]; norm_num
      calc a l k ^ 2 = (eW (l - n) * ‖sF n lam l‖ₑ) ^ 2 * ((‖sF n lam k‖ₑ * iW (k + n)) ^ 2 * iW (l + k) ^ 2) := by
            simp only [ha]; ring
        _ ≤ _ := by gcongr
    calc ∑' l, a l k ^ 2 ≤ ∑' l, ENNReal.ofReal (16 / 9) * ((‖sF n lam k‖ₑ * iW (k + n)) ^ 2 * iW (l + k) ^ 2) :=
          ENNReal.tsum_le_tsum hl
      _ = ENNReal.ofReal (16 / 9) * ((‖sF n lam k‖ₑ * iW (k + n)) ^ 2 * ∑' l, iW (l + k) ^ 2) := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
      _ ≤ ENNReal.ofReal (16 / 9) * ((‖sF n lam k‖ₑ * iW (k + n)) ^ 2 * 3) := by
          gcongr
          have : ∑' l : ℤ, iW (l + k) ^ 2 = ∑' l : ℤ, iW l ^ 2 :=
            (Equiv.addRight k).tsum_eq (fun j : ℤ => iW j ^ 2)
          rw [this]; exact La_sum
      _ = ENNReal.ofReal (16 / 3) * (‖sF n lam k‖ₑ ^ 2 * iW (k + n) ^ 2) := by
          rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by simp, mul_pow]
          rw [show ENNReal.ofReal (16 / 3) = ENNReal.ofReal (16 / 9) * ENNReal.ofReal 3 by
            rw [← ENNReal.ofReal_mul (by norm_num)]; norm_num]
          ring
  have hD : ∑' k, ∑' l, a l k ^ 2 ≤ ENNReal.ofReal (512 / 27) * iW n ^ 2 := by
    calc ∑' k, ∑' l, a l k ^ 2
        ≤ ∑' k, ENNReal.ofReal (16 / 3) * (‖sF n lam k‖ₑ ^ 2 * iW (k + n) ^ 2) :=
          ENNReal.tsum_le_tsum hA
      _ = ENNReal.ofReal (16 / 3) * ∑' k, ‖sF n lam k‖ₑ ^ 2 * iW (k + n) ^ 2 := ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal (16 / 3) * (ENNReal.ofReal (32 / 9) * iW n ^ 2) := by
          gcongr; exact Lb_sum n lam hlam
      _ = ENNReal.ofReal (512 / 27) * iW n ^ 2 := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]; norm_num
  -- assemble
  calc (∑' l, eW (l - n) * ‖sF n lam l‖ₑ * ‖hk c (Gs n lam x) l‖ₑ) ^ 2
      ≤ (∑' k, β k * ∑' l, a l k * α (l + k)) ^ 2 := by gcongr
    _ ≤ Q n x * ∑' k, (∑' l, a l k * α (l + k)) ^ 2 := h4
    _ ≤ Q n x * ∑' k, ((∑' l, a l k ^ 2) * SW c) := by
        gcongr with k; exact hu k
    _ = Q n x * ((∑' k, ∑' l, a l k ^ 2) * SW c) := by rw [ENNReal.tsum_mul_right]
    _ ≤ Q n x * ((ENNReal.ofReal (512 / 27) * iW n ^ 2) * SW c) := by gcongr
    _ = _ := by ring


/-- Squared form of the contraction estimate for `Ω = C₁ G C₂ G`. -/
theorem Q_Om (n : ℤ) (lam : ℝ) (hlam : |lam - n * Real.pi| ≤ Real.pi / 2) (c₁ c₂ x : ℤ → ℂ) :
    Q n (hk c₁ (Gs n lam (hk c₂ (Gs n lam x)))) ≤
      SW c₁ * SW c₂ * (ENNReal.ofReal (512 / 27) * iW n ^ 2) * Q n x := by
  have h1 := Q_hk n c₁ (Gs n lam (hk c₂ (Gs n lam x)))
  have h2 := LB n lam hlam c₂ x
  have e : ∑' l, eW (l - n) * ‖Gs n lam (hk c₂ (Gs n lam x)) l‖ₑ =
      ∑' l, eW (l - n) * ‖sF n lam l‖ₑ * ‖hk c₂ (Gs n lam x) l‖ₑ := by
    refine tsum_congr fun l => ?_
    simp only [Gs, enorm_mul]; ring
  rw [e] at h1
  calc _ ≤ SW c₁ * (∑' l, eW (l - n) * ‖sF n lam l‖ₑ * ‖hk c₂ (Gs n lam x) l‖ₑ) ^ 2 := h1
    _ ≤ SW c₁ * (SW c₂ * (ENNReal.ofReal (512 / 27) * iW n ^ 2) * Q n x) := by gcongr
    _ = _ := by ring


/-! ### Finiteness and absorption -/

theorem eW_add_le_add (a b : ℤ) : eW (a + b) ≤ eW a + eW b := by
  unfold eW
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  push_cast
  have := abs_add_le (a : ℝ) (b : ℝ)
  linarith

theorem Q_shift (n : ℤ) (c : ℤ → ℂ) : Q n (fun m => c (m + n)) = SW c :=
  (Equiv.addRight n).tsum_eq (fun k : ℤ => (eW k * ‖c k‖ₑ) ^ 2)

theorem l1_sq_le (c : ℤ → ℂ) : (∑' k, ‖c k‖ₑ) ^ 2 ≤ 3 * SW c := by
  have h1 : ∑' k, ‖c k‖ₑ = ∑' k, iW k * (eW k * ‖c k‖ₑ) := by
    refine tsum_congr fun k => ?_
    rw [← mul_assoc, iW_mul_eW, one_mul]
  rw [h1]
  calc _ ≤ (∑' k, iW k ^ 2) * ∑' k, (eW k * ‖c k‖ₑ) ^ 2 := cs _ _
    _ ≤ 3 * SW c := mul_le_mul' La_sum (le_of_eq rfl)

theorem l1_ne_top (c : ℤ → ℂ) (h : SW c ≠ ⊤) : ∑' k, ‖c k‖ₑ ≠ ⊤ := by
  intro htop
  have := l1_sq_le c
  rw [htop] at this
  have h3 : (3 : ℝ≥0∞) * SW c = ⊤ := by simpa using this
  rcases ENNReal.mul_eq_top.mp h3 with ⟨_, h2⟩ | ⟨h3', _⟩
  · exact h h2
  · exact absurd h3' (by simp)

theorem Q_hk_ne_top (n : ℤ) (c y : ℤ → ℂ) (hc : SW c ≠ ⊤) (hy : SW y ≠ ⊤) :
    Q n (hk c y) ≠ ⊤ := by
  set a : ℤ → ℝ≥0∞ := fun k => eW k * ‖c k‖ₑ with ha
  have hpt : ∀ m, eW (m + n) * ‖hk c y m‖ₑ ≤
      ∑' l, a (m + l) * ‖y l‖ₑ + ∑' l, ‖c (m + l)‖ₑ * (eW (l - n) * ‖y l‖ₑ) := by
    intro m
    rw [← ENNReal.tsum_add]
    calc eW (m + n) * ‖hk c y m‖ₑ
        ≤ eW (m + n) * ∑' l, ‖c (m + l)‖ₑ * ‖y l‖ₑ := by gcongr; exact enorm_hk_le c y m
      _ = ∑' l, eW (m + n) * (‖c (m + l)‖ₑ * ‖y l‖ₑ) := ENNReal.tsum_mul_left.symm
      _ ≤ _ := by
          refine ENNReal.tsum_le_tsum fun l => ?_
          have h1 : eW (m + n) ≤ eW (m + l) + eW (l - n) := by
            have := eW_add_le_add (m + l) (n - l)
            rw [show m + l + (n - l) = m + n by ring] at this
            rwa [show n - l = -(l - n) by ring, eW_neg] at this
          calc eW (m + n) * (‖c (m + l)‖ₑ * ‖y l‖ₑ)
              ≤ (eW (m + l) + eW (l - n)) * (‖c (m + l)‖ₑ * ‖y l‖ₑ) := by gcongr
            _ = _ := by simp only [ha]; ring
  have hQ : Q n (hk c y) ≤ 2 * (∑' m, (∑' l, a (m + l) * ‖y l‖ₑ) ^ 2) +
      2 * ∑' m, (∑' l, ‖c (m + l)‖ₑ * (eW (l - n) * ‖y l‖ₑ)) ^ 2 := by
    calc Q n (hk c y) ≤ ∑' m, (∑' l, a (m + l) * ‖y l‖ₑ + ∑' l, ‖c (m + l)‖ₑ * (eW (l - n) * ‖y l‖ₑ)) ^ 2 :=
          ENNReal.tsum_le_tsum fun m => by gcongr; exact hpt m
      _ ≤ ∑' m, (2 * (∑' l, a (m + l) * ‖y l‖ₑ) ^ 2 +
            2 * (∑' l, ‖c (m + l)‖ₑ * (eW (l - n) * ‖y l‖ₑ)) ^ 2) := by
          refine ENNReal.tsum_le_tsum fun m => ?_
          set u := ∑' l, a (m + l) * ‖y l‖ₑ
          set v := ∑' l, ‖c (m + l)‖ₑ * (eW (l - n) * ‖y l‖ₑ)
          have := two_mul_le_sq u v
          calc (u + v) ^ 2 = u ^ 2 + 2 * (u * v) + v ^ 2 := by ring
            _ ≤ u ^ 2 + (u ^ 2 + v ^ 2) + v ^ 2 := by gcongr
            _ = _ := by ring
      _ = _ := by rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
  have h1 : ∑' m, (∑' l, a (m + l) * ‖y l‖ₑ) ^ 2 ≤ (∑' l, ‖y l‖ₑ) ^ 2 * SW c :=
    young a (fun l => ‖y l‖ₑ)
  have h2 : ∑' m, (∑' l, ‖c (m + l)‖ₑ * (eW (l - n) * ‖y l‖ₑ)) ^ 2 ≤
      (∑' k, ‖c k‖ₑ) ^ 2 * ∑' l, (eW (l - n) * ‖y l‖ₑ) ^ 2 :=
    young' (fun k => ‖c k‖ₑ) (fun l => eW (l - n) * ‖y l‖ₑ)
  have h3 : ∑' l, (eW (l - n) * ‖y l‖ₑ) ^ 2 ≤ eW n ^ 2 * SW y := by
    calc ∑' l, (eW (l - n) * ‖y l‖ₑ) ^ 2 ≤ ∑' l, eW n ^ 2 * (eW l * ‖y l‖ₑ) ^ 2 := by
          refine ENNReal.tsum_le_tsum fun l => ?_
          have : eW (l - n) ≤ eW l * eW n := by
            have := eW_add_le l (-n)
            rwa [← sub_eq_add_neg, eW_neg] at this
          calc (eW (l - n) * ‖y l‖ₑ) ^ 2 ≤ ((eW l * eW n) * ‖y l‖ₑ) ^ 2 := by gcongr
            _ = _ := by ring
      _ = _ := by rw [ENNReal.tsum_mul_left]; rfl
  have hfin1 := l1_ne_top y hy
  have hfin2 := l1_ne_top c hc
  have h4 : Q n (hk c y) < ⊤ := by
    refine lt_of_le_of_lt hQ ?_
    refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
    · refine ENNReal.mul_lt_top (by simp) (lt_of_le_of_lt h1 ?_)
      exact ENNReal.mul_lt_top (ENNReal.pow_lt_top (lt_top_iff_ne_top.2 hfin1)) (lt_top_iff_ne_top.2 hc)
    · refine ENNReal.mul_lt_top (by simp) (lt_of_le_of_lt h2 ?_)
      refine ENNReal.mul_lt_top (ENNReal.pow_lt_top (lt_top_iff_ne_top.2 hfin2)) ?_
      refine lt_of_le_of_lt h3 (ENNReal.mul_lt_top ?_ (lt_top_iff_ne_top.2 hy))
      exact ENNReal.pow_lt_top (lt_top_iff_ne_top.2 (eW_ne_top n))
  exact h4.ne

theorem absorb (a r : ℝ≥0∞) (ha : a ≠ ⊤) (h : a ≤ r + ENNReal.ofReal (7 / 25) * a) :
    a ≤ ENNReal.ofReal (25 / 18) * r := by
  by_cases hr : r = ⊤
  · rw [hr]; simp
  lift a to ℝ≥0 using ha
  lift r to ℝ≥0 using hr
  have h' : (a : ℝ) ≤ r + 7 / 25 * a := by
    have := h
    rw [show ENNReal.ofReal (7 / 25) = ((7 / 25 : ℝ≥0) : ℝ≥0∞) by
      rw [ENNReal.ofReal_eq_coe_nnreal (by norm_num)]; rfl] at this
    rw [← ENNReal.coe_mul, ← ENNReal.coe_add, ENNReal.coe_le_coe] at this
    exact_mod_cast this
  rw [show ENNReal.ofReal (25 / 18) = ((25 / 18 : ℝ≥0) : ℝ≥0∞) by
    rw [ENNReal.ofReal_eq_coe_nnreal (by norm_num)]; rfl, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
  have : (a : ℝ) ≤ 25 / 18 * r := by linarith
  exact_mod_cast this

end

end NlsGge.GK38.Mo2
