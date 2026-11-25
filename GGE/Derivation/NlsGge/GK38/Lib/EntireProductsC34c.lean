import NlsGge.GK38.Lib.EntireProductsC34b

/-!
# L4c part 2b, module c: Lemma C.3, the pointwise bound for the ratio product

`ratio_pointwise`: for `λ` with the separation hypothesis (C.2) and a finite set `E` outside which
`c ‖σ_m - ρ_m‖ ≤ 1/2`, the ratio product `∏_{m≠n} (σ_m - λ)/(ρ_m - λ)` is multipliable and
`‖∏ - 1‖ ≤ Λ² e_n + Λ ‖Σ_m u^G_m‖ + Λ B_n`.  The three quantities `e_n`, `Σ u^G`, `B_n` are treated in
the following modules (the middle one is the Hilbert-transform term, book Lemma F.6).
-/

set_option autoImplicit false

open Filter Topology SummationFilter

namespace NlsGge.GK38.Lib

noncomputable section

/-- `Λ = exp(S₀ + S₀²)`. -/
def c3Lam (c K : ℝ) : ℝ := Real.exp (c3S c K + c3S c K ^ 2)

/-- `e_n = Σ_{m∈E} c ‖a_m‖ w_{n,m}`. -/
def c3eX (c : ℝ) (σ ρ : ℤ → ℂ) (E : Finset ℤ) (n : ℤ) : ℝ :=
  ∑ m ∈ E, c * (‖σ m - ρ m‖ * c3w n m)

/-- `B_n = c² Σ_m ‖a_m‖² w_{n,m}²`. -/
def c3B (c : ℝ) (σ ρ : ℤ → ℂ) (n : ℤ) : ℝ :=
  c ^ 2 * ∑' m, ‖σ m - ρ m‖ ^ 2 * c3w n m ^ 2

/-- `Σ_m u^G_m`, the Hilbert-transform term. -/
def c3A (σ ρ : ℤ → ℂ) (E : Finset ℤ) (n : ℤ) (lam : ℂ) : ℂ :=
  ∑' m, uG E (ratioU σ ρ n lam) m

theorem c3Lam_pos (c K : ℝ) : 0 < c3Lam c K := Real.exp_pos _

theorem exp_le_c3Lam {c : ℝ} (K x : ℝ) (hxS : x ≤ c3S c K) :
    Real.exp x ≤ c3Lam c K := by
  unfold c3Lam
  exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (c3S c K)])

theorem exp_add_sq_le_c3Lam {c : ℝ} (K x : ℝ) (hx : 0 ≤ x) (hxS : x ≤ c3S c K) :
    Real.exp (x + x ^ 2) ≤ c3Lam c K := by
  unfold c3Lam
  refine Real.exp_le_exp.mpr ?_
  have : x ^ 2 ≤ c3S c K ^ 2 := by nlinarith
  linarith

theorem ratioFam_eq_of_sep {σ ρ : ℤ → ℂ} {n : ℤ} {lam : ℂ} {c : ℝ} (hc : 0 < c)
    (hsep : ∀ m : ℤ, m ≠ n → c⁻¹ * |(m : ℝ) - n| ≤ ‖ρ m - lam‖) :
    ratioFam σ ρ n lam = fun m => 1 + ratioU σ ρ n lam m := by
  refine funext (ratioFam_eq_one_add fun m hm h => ?_)
  have h1 := hsep m hm
  rw [h, sub_self, norm_zero] at h1
  have hpos : 0 < |(m : ℝ) - n| := by
    rw [abs_pos, sub_ne_zero]; exact_mod_cast hm
  have : 0 < c⁻¹ * |(m : ℝ) - n| := by positivity
  linarith

/-- **Book Lemma C.3, pointwise form.** -/
theorem ratio_pointwise {σ ρ : ℤ → ℂ} {n : ℤ} {lam : ℂ} {c K : ℝ} {E : Finset ℤ} (hc : 0 < c)
    (ha : Summable fun m => ‖σ m - ρ m‖ ^ 2) (haK : ∑' m, ‖σ m - ρ m‖ ^ 2 ≤ K)
    (hsep : ∀ m : ℤ, m ≠ n → c⁻¹ * |(m : ℝ) - n| ≤ ‖ρ m - lam‖)
    (hE : ∀ m, m ∉ E → c * ‖σ m - ρ m‖ ≤ 1 / 2) :
    Multipliable (ratioFam σ ρ n lam) (symmetricIcc ℤ) ∧
      ‖ratioProd σ ρ n lam - 1‖ ≤
        c3Lam c K ^ 2 * c3eX c σ ρ E n + c3Lam c K * ‖c3A σ ρ E n lam‖ + c3Lam c K * c3B c σ ρ n := by
  obtain ⟨hu, huS⟩ := summable_ratioU (n := n) (lam := lam) hc ha haK hsep
  set u := ratioU σ ρ n lam with hudef
  have hfam := ratioFam_eq_of_sep (σ := σ) (ρ := ρ) (n := n) (lam := lam) hc hsep
  have hL0 := c3Lam_pos c K
  have hS0 := c3S_nonneg hc K
  -- summability of the pieces
  have hE' : Summable fun m => ‖uE E u m‖ := hu.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_uE_le E u)
  have hG' : Summable fun m => ‖uG E u m‖ := hu.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_uG_le E u)
  have mE := multipliable_one_add_of_summable hE'
  have mG := multipliable_one_add_of_summable hG'
  have mu := multipliable_one_add_of_summable hu
  refine ⟨?_, ?_⟩
  · rw [hfam]
    exact HasProd.multipliable (mu.hasProd.mono_left (symmetricIcc ℤ).le_atTop)
  have hsymm : ratioProd σ ρ n lam = ∏' m, (1 + u m) := by
    unfold ratioProd
    rw [hfam]
    exact tprod_symm_eq_tprod_of_summable hu
  have hsplit : ∏' m, (1 + u m) = (∏' m, (1 + uE E u m)) * ∏' m, (1 + uG E u m) := by
    rw [← mE.tprod_mul mG]
    exact tprod_congr (one_add_eq_mul E u)
  rw [hsymm, hsplit]
  set PX := ∏' m, (1 + uE E u m) with hPX
  set PY := ∏' m, (1 + uG E u m) with hPY
  -- bound for the X part
  have hX := norm_prod_uE_sub_one hu E huS
  have heX : ∑ m ∈ E, ‖u m‖ ≤ c3eX c σ ρ E n :=
    Finset.sum_le_sum fun m _ => norm_ratioU_le hc hsep m
  have hX' : ‖PX - 1‖ ≤ c3eX c σ ρ E n * Real.exp (c3S c K) :=
    hX.trans (mul_le_mul_of_nonneg_right heX (Real.exp_pos _).le)
  -- bound for the G part
  have hSG : ∑' m, ‖uG E u m‖ ≤ c3S c K :=
    (hG'.tsum_le_tsum (norm_uG_le E u) hu).trans huS
  have hSG0 : 0 ≤ ∑' m, ‖uG E u m‖ := tsum_nonneg fun _ => norm_nonneg _
  have hhalf : ∀ m, ‖uG E u m‖ ≤ 1 / 2 := by
    intro m
    unfold uG
    by_cases hm : m ∈ E
    · simp [hm]
    · simp only [hm, ite_false]
      refine (norm_ratioU_le hc hsep m).trans ?_
      have h1 := c3w_le_one n m
      calc c * (‖σ m - ρ m‖ * c3w n m) ≤ c * ‖σ m - ρ m‖ := by
            rw [← mul_assoc]
            exact mul_le_of_le_one_right (by positivity) h1
        _ ≤ 1 / 2 := hE m hm
  have hPYn : ‖PY‖ ≤ c3Lam c K := by
    refine (norm_tprod_one_add_le hG').trans ?_
    exact exp_le_c3Lam K _ hSG
  have hsharp := norm_tprod_one_add_sub_one_le_sharp hG' hhalf
  -- B bound
  have hB : ∑' m, ‖uG E u m‖ ^ 2 ≤ c3B c σ ρ n := by
    have hb : Summable fun m => ‖σ m - ρ m‖ ^ 2 * c3w n m ^ 2 :=
      ha.of_nonneg_of_le (fun m => by have := c3w_nonneg n m; positivity) (fun m => by
        have := c3w_le_one n m
        have h0 := c3w_nonneg n m
        calc ‖σ m - ρ m‖ ^ 2 * c3w n m ^ 2 ≤ ‖σ m - ρ m‖ ^ 2 * 1 :=
              mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg _)
          _ = _ := mul_one _)
    have hpt : ∀ m, ‖uG E u m‖ ^ 2 ≤ c ^ 2 * (‖σ m - ρ m‖ ^ 2 * c3w n m ^ 2) := by
      intro m
      have h1 := (norm_uG_le E u m).trans (norm_ratioU_le hc hsep m)
      have h0 := norm_nonneg (uG E u m)
      calc ‖uG E u m‖ ^ 2 ≤ (c * (‖σ m - ρ m‖ * c3w n m)) ^ 2 := by gcongr
        _ = c ^ 2 * (‖σ m - ρ m‖ ^ 2 * c3w n m ^ 2) := by ring
    have hb2 : Summable fun m => c ^ 2 * (‖σ m - ρ m‖ ^ 2 * c3w n m ^ 2) := hb.mul_left _
    have hs2 : Summable fun m => ‖uG E u m‖ ^ 2 :=
      hb2.of_nonneg_of_le (fun _ => sq_nonneg _) hpt
    calc ∑' m, ‖uG E u m‖ ^ 2 ≤ ∑' m, c ^ 2 * (‖σ m - ρ m‖ ^ 2 * c3w n m ^ 2) :=
          hs2.tsum_le_tsum hpt hb2
      _ = c3B c σ ρ n := by unfold c3B; rw [tsum_mul_left]
  have hBnn : 0 ≤ ∑' m, ‖uG E u m‖ ^ 2 := tsum_nonneg fun _ => sq_nonneg _
  have e1 := exp_le_c3Lam K _ hSG
  have e2 := exp_add_sq_le_c3Lam (c := c) K _ hSG0 hSG
  have hPY1 : ‖PY - 1‖ ≤ c3Lam c K * ‖c3A σ ρ E n lam‖ + c3Lam c K * c3B c σ ρ n := by
    refine hsharp.trans ?_
    have hA : ‖∑' m, uG E u m‖ = ‖c3A σ ρ E n lam‖ := rfl
    rw [hA]
    have t1 : ‖c3A σ ρ E n lam‖ * Real.exp (∑' m, ‖uG E u m‖) ≤ c3Lam c K * ‖c3A σ ρ E n lam‖ := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right e1 (norm_nonneg _)
    have t2 : (∑' m, ‖uG E u m‖ ^ 2) * Real.exp ((∑' m, ‖uG E u m‖) + (∑' m, ‖uG E u m‖) ^ 2)
        ≤ c3Lam c K * c3B c σ ρ n := by
      calc _ ≤ c3B c σ ρ n * c3Lam c K := mul_le_mul hB e2 (Real.exp_pos _).le (hBnn.trans hB)
        _ = _ := mul_comm _ _
    linarith
  -- assemble
  have hdecomp : PX * PY - 1 = (PX - 1) * PY + (PY - 1) := by ring
  rw [hdecomp]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  have heXn : 0 ≤ c3eX c σ ρ E n :=
    Finset.sum_nonneg fun m _ => by have := c3w_nonneg n m; positivity
  calc ‖PX - 1‖ * ‖PY‖ + ‖PY - 1‖
      ≤ (c3eX c σ ρ E n * Real.exp (c3S c K)) * c3Lam c K + ‖PY - 1‖ :=
        add_le_add (mul_le_mul hX' hPYn (norm_nonneg _) (by positivity)) le_rfl
    _ ≤ (c3eX c σ ρ E n * c3Lam c K) * c3Lam c K + ‖PY - 1‖ :=
        add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (exp_le_c3Lam K _ le_rfl) heXn) hL0.le) le_rfl
    _ ≤ _ := by nlinarith [hPY1]

end

end NlsGge.GK38.Lib
