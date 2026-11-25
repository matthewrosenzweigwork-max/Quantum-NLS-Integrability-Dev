import NlsGge.GK38.Lib.EntireProductsSine

/-!
# L4c, part 1e: book Lemma C.2, sharp form

For an `ℓ¹` sequence `a` with `‖a_m‖ ≤ 1/2`, with `A = Σ a_m`, `B = Σ ‖a_m‖²`, `S = Σ ‖a_m‖`:
`‖∏(1 + a_m) - 1‖ ≤ ‖A‖ e^S + B e^{S + S²}`.

The book writes `|A|` as `A`, which is complex; here `‖A‖`.  The proof is the book's: with
`K = Σ a_m`, `L = Σ (log(1 + a_m) - a_m)` one has `∏ = e^K e^L`, `‖L‖ ≤ B ≤ S²`, and
`∏ - 1 = (e^K - 1) + e^K (e^L - 1)`.  The L4a file has only the crude bound `exp S - 1`
(`norm_tprod_one_add_sub_one_le`); the sharp bound gives the `ℓ²` estimates of book Lemma C.3
(through the Hilbert transform bound `Σ a_m` of L4b).
-/

set_option autoImplicit false

open Filter Topology SummationFilter

namespace NlsGge.GK38.Lib

noncomputable section

/-- `‖e^x - 1‖ ≤ ‖x‖ e^{‖x‖}`. -/
theorem norm_cexp_sub_one_le (x : ℂ) : ‖Complex.exp x - 1‖ ≤ ‖x‖ * Real.exp ‖x‖ := by
  have := Complex.norm_exp_sub_sum_le_norm_mul_exp x 1
  simpa using this

/-- `‖log(1 + x) - x‖ ≤ ‖x‖²` for `‖x‖ ≤ 1/2`. -/
theorem norm_log_one_add_sub_le {x : ℂ} (hx : ‖x‖ ≤ 1 / 2) :
    ‖Complex.log (1 + x) - x‖ ≤ ‖x‖ ^ 2 := by
  have h := Complex.norm_log_one_add_sub_self_le (z := x) (by linarith)
  refine h.trans ?_
  have h1 : (1 - ‖x‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have h2 : 0 ≤ ‖x‖ ^ 2 := sq_nonneg _
  calc ‖x‖ ^ 2 * (1 - ‖x‖)⁻¹ / 2 ≤ ‖x‖ ^ 2 * 2 / 2 := by gcongr
    _ = ‖x‖ ^ 2 := by ring

/-- **Book Lemma C.2, sharp form** (unconditional product of an `ℓ¹` family). -/
theorem norm_tprod_one_add_sub_one_le_sharp {a : ℤ → ℂ} (ha : Summable fun m => ‖a m‖)
    (h : ∀ m, ‖a m‖ ≤ 1 / 2) :
    ‖(∏' m : ℤ, (1 + a m)) - 1‖
      ≤ ‖∑' m, a m‖ * Real.exp (∑' m, ‖a m‖)
        + (∑' m, ‖a m‖ ^ 2) * Real.exp ((∑' m, ‖a m‖) + (∑' m, ‖a m‖) ^ 2) := by
  set S : ℝ := ∑' m, ‖a m‖ with hS
  set B : ℝ := ∑' m, ‖a m‖ ^ 2 with hB
  set K : ℂ := ∑' m, a m with hK
  have haS : Summable a := ha.of_norm
  have hsq : Summable fun m => ‖a m‖ ^ 2 :=
    ha.of_nonneg_of_le (fun _ => sq_nonneg _) fun m => by
      have := h m
      nlinarith [norm_nonneg (a m)]
  have hdiff : ∀ m, ‖Complex.log (1 + a m) - a m‖ ≤ ‖a m‖ ^ 2 := fun m => norm_log_one_add_sub_le (h m)
  have hLs : Summable fun m => Complex.log (1 + a m) - a m :=
    Summable.of_norm (hsq.of_nonneg_of_le (fun _ => norm_nonneg _) hdiff)
  have hlog : Summable fun m => Complex.log (1 + a m) := by
    have := hLs.add haS
    simpa using this
  have hne : ∀ m, 1 + a m ≠ 0 := by
    intro m h0
    have : a m = -1 := by linear_combination h0
    have := h m
    rw [‹a m = -1›] at this
    simp at this
    linarith
  set L : ℂ := ∑' m, (Complex.log (1 + a m) - a m) with hL
  have hprod : ∏' m : ℤ, (1 + a m) = Complex.exp K * Complex.exp L := by
    rw [← Complex.cexp_tsum_eq_tprod hne hlog, ← Complex.exp_add]
    congr 1
    have := hLs.tsum_add haS
    simp only [sub_add_cancel] at this
    rw [this, hK, hL, add_comm]
  have hLB : ‖L‖ ≤ B := by
    refine (norm_tsum_le_tsum_norm hLs.norm).trans ?_
    exact Summable.tsum_le_tsum hdiff hLs.norm hsq
  have hBS : B ≤ S ^ 2 := by
    have hle : ∀ m, ‖a m‖ ^ 2 ≤ ‖a m‖ * S := by
      intro m
      have : ‖a m‖ ≤ S := ha.le_tsum m (fun _ _ => norm_nonneg _)
      nlinarith [norm_nonneg (a m)]
    calc B ≤ ∑' m, ‖a m‖ * S := Summable.tsum_le_tsum hle hsq (ha.mul_right S)
      _ = S ^ 2 := by rw [tsum_mul_right]; ring
  have hKS : ‖K‖ ≤ S := norm_tsum_le_tsum_norm ha
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => norm_nonneg _
  have hB0 : 0 ≤ B := tsum_nonneg fun _ => by positivity
  have eq1 : Complex.exp K * Complex.exp L - 1
      = (Complex.exp K - 1) + Complex.exp K * (Complex.exp L - 1) := by ring
  rw [hprod, eq1]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_cexp_sub_one_le K).trans ?_
    gcongr
  · rw [norm_mul]
    have h1 : ‖Complex.exp K‖ ≤ Real.exp S := (Complex.norm_exp_le_exp_norm K).trans
      (Real.exp_le_exp.mpr hKS)
    have h2 : ‖Complex.exp L - 1‖ ≤ B * Real.exp B :=
      (norm_cexp_sub_one_le L).trans (by
        have := Real.exp_le_exp.mpr hLB
        exact mul_le_mul hLB this (Real.exp_pos _).le hB0)
    calc ‖Complex.exp K‖ * ‖Complex.exp L - 1‖ ≤ Real.exp S * (B * Real.exp B) :=
          mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_pos _).le
      _ ≤ B * Real.exp (S + S ^ 2) := by
          have : Real.exp B ≤ Real.exp (S ^ 2) := Real.exp_le_exp.mpr hBS
          rw [Real.exp_add]
          have hh : 0 ≤ B * Real.exp S := by positivity
          calc Real.exp S * (B * Real.exp B) = (B * Real.exp S) * Real.exp B := by ring
            _ ≤ (B * Real.exp S) * Real.exp (S ^ 2) := mul_le_mul_of_nonneg_left this hh
            _ = B * (Real.exp S * Real.exp (S ^ 2)) := by ring

/-- The same bound for the symmetric product (which equals the unconditional one on `ℓ¹`). -/
theorem tprod_symm_eq_tprod_of_summable {a : ℤ → ℂ} (ha : Summable fun m => ‖a m‖) :
    ∏'[symmetricIcc ℤ] m : ℤ, (1 + a m) = ∏' m : ℤ, (1 + a m) := by
  have hP : HasProd (fun m : ℤ => 1 + a m) (∏' m : ℤ, (1 + a m)) (symmetricIcc ℤ) :=
    (multipliable_one_add_of_summable ha).hasProd.mono_left (symmetricIcc ℤ).le_atTop
  exact hP.tprod_eq

theorem norm_tprod_symm_one_add_sub_one_le_sharp {a : ℤ → ℂ} (ha : Summable fun m => ‖a m‖)
    (h : ∀ m, ‖a m‖ ≤ 1 / 2) :
    ‖(∏'[symmetricIcc ℤ] m : ℤ, (1 + a m)) - 1‖
      ≤ ‖∑' m, a m‖ * Real.exp (∑' m, ‖a m‖)
        + (∑' m, ‖a m‖ ^ 2) * Real.exp ((∑' m, ‖a m‖) + (∑' m, ‖a m‖) ^ 2) := by
  rw [tprod_symm_eq_tprod_of_summable ha]
  exact norm_tprod_one_add_sub_one_le_sharp ha h

end

end NlsGge.GK38.Lib
