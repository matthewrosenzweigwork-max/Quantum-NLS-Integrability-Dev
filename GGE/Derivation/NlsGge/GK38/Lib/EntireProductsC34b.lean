import NlsGge.GK38.Lib.EntireProductsC34a

/-!
# L4c part 2b, module b: Lemma C.3, pointwise estimates

Book Lemma C.3 (Appendix C).  Fix `n` and `λ` with the separation hypothesis (C.2)
`‖ρ_m - λ‖ ≥ c⁻¹ |m - n|` (`m ≠ n`).  With `a = σ - ρ`, `u_m = a_m/(ρ_m - λ)` (`u_n = 0`) we have
`∏_{m≠n} (σ_m - λ)/(ρ_m - λ) = ∏ (1 + u_m)`, `‖u_m‖ ≤ c ‖a_m‖ w_{n,m}`, `w_{n,m} = 1/|m - n|`.

*Splitting* (the book's `M`, replaced by a finite exceptional set `E ⊇ {m : c‖a_m‖ ≥ 1/2}`, which
depends only on `a` and `c`, uniformly in `‖a‖_{ℓ²}`; the book's "`M` can be chosen locally uniformly
in `α`" is thereby made precise): `1 + u = (1 + u^E)(1 + u^G)` where `u^E` is supported on `E`,
`u^G` is `u` off `E`.  Then
`‖∏(1 + u) - 1‖ ≤ Λ² e_n + Λ |Σ u^G| + Λ B_n`
with `e_n = Σ_{m∈E} c ‖a_m‖ w_{n,m}`, `B_n = c² Σ_m ‖a_m‖² w_{n,m}²`, `Λ = exp(S₀ + S₀²)`,
`S₀ = c √K' √K₀`, and the sharp C.2 (L4c part 1) applied to `u^G` (`‖u^G_m‖ ≤ 1/2`).
-/

set_option autoImplicit false

open Filter Topology SummationFilter

namespace NlsGge.GK38.Lib

noncomputable section

/-- The weight `w_{n,m} = 1/|m - n|` (`0` at `m = n`). -/
def c3w (n m : ℤ) : ℝ := 1 / |(m : ℝ) - n|

theorem c3w_nonneg (n m : ℤ) : 0 ≤ c3w n m := by unfold c3w; positivity

theorem c3w_le_one (n m : ℤ) : c3w n m ≤ 1 := by
  unfold c3w
  by_cases h : m = n
  · simp [h]
  · have h1 : (1 : ℤ) ≤ |m - n| := Int.one_le_abs (sub_ne_zero.mpr h)
    have h2 : (1 : ℝ) ≤ |(m : ℝ) - n| := by
      have : (1 : ℝ) ≤ ((|m - n| : ℤ) : ℝ) := by exact_mod_cast h1
      simpa [Int.cast_abs] using this
    exact (div_le_one (by linarith)).mpr h2

theorem c3w_sq (n m : ℤ) : c3w n m ^ 2 = 1 / ((m : ℝ) - n) ^ 2 := by
  unfold c3w; rw [div_pow, one_pow, sq_abs]

theorem summable_c3w_sq (n : ℤ) : Summable fun m => c3w n m ^ 2 := by
  refine (summable_sq_inv_int_sub n).congr fun m => ?_
  rw [c3w_sq, div_pow, one_pow]

theorem tsum_c3w_sq (n : ℤ) : ∑' m, c3w n m ^ 2 = invSqSum := by
  have : ∀ m : ℤ, c3w n m ^ 2 = 1 / ((m - n : ℤ) : ℝ) ^ 2 := fun m => by
    rw [c3w_sq]; push_cast; rfl
  simp_rw [this]
  exact (Equiv.subRight n).tsum_eq (fun j : ℤ => 1 / (j : ℝ) ^ 2)

theorem sum_c3w_sq_le (m : ℤ) (T : Finset ℤ) : ∑ n ∈ T, c3w n m ^ 2 ≤ invSqSum := by
  have : ∀ n : ℤ, c3w n m ^ 2 = 1 / (((Equiv.subLeft m) n : ℤ) : ℝ) ^ 2 := fun n => by
    rw [c3w_sq]; simp only [Equiv.subLeft_apply]; push_cast; rw [← neg_sub, neg_sq]
  simp_rw [this]
  have h := summable_invSq.sum_le_tsum (T.map (Equiv.subLeft m).toEmbedding)
    (fun _ _ => by positivity)
  rw [Finset.sum_map] at h
  exact h

/-- `√(Σ_m (w_{n,m})²) = √K₀`. -/
theorem c3_cs {a : ℤ → ℂ} (ha : Summable fun m => ‖a m‖ ^ 2) (n : ℤ) :
    Summable (fun m => ‖a m‖ * c3w n m) ∧
      ∑' m, ‖a m‖ * c3w n m ≤ Real.sqrt (∑' m, ‖a m‖ ^ 2) * Real.sqrt invSqSum := by
  obtain ⟨h1, h2⟩ := cs_tsum (f := fun m => ‖a m‖) (g := c3w n) (fun _ => norm_nonneg _)
    (c3w_nonneg n) ha (summable_c3w_sq n)
  exact ⟨h1, by rwa [tsum_c3w_sq] at h2⟩

/-! ### The perturbation `u` -/

theorem norm_ratioU_le {σ ρ : ℤ → ℂ} {n : ℤ} {lam : ℂ} {c : ℝ} (hc : 0 < c)
    (hsep : ∀ m : ℤ, m ≠ n → c⁻¹ * |(m : ℝ) - n| ≤ ‖ρ m - lam‖) (m : ℤ) :
    ‖ratioU σ ρ n lam m‖ ≤ c * (‖σ m - ρ m‖ * c3w n m) := by
  unfold ratioU
  by_cases h : m = n
  · simp only [h, ite_true, norm_zero]
    have := c3w_nonneg n n
    positivity
  · simp only [h, ite_false]
    have hpos : 0 < |(m : ℝ) - n| := by
      rw [abs_pos, sub_ne_zero]; exact_mod_cast h
    have h1 := hsep m h
    have h2 : 0 < c⁻¹ * |(m : ℝ) - n| := by positivity
    rw [norm_div]
    calc ‖σ m - ρ m‖ / ‖ρ m - lam‖ ≤ ‖σ m - ρ m‖ / (c⁻¹ * |(m : ℝ) - n|) :=
          div_le_div_of_nonneg_left (norm_nonneg _) h2 h1
      _ = c * (‖σ m - ρ m‖ * c3w n m) := by
          unfold c3w; field_simp

/-- The constant `S₀ = c √K' √K₀`. -/
def c3S (c K : ℝ) : ℝ := c * Real.sqrt K * Real.sqrt invSqSum

theorem c3S_nonneg {c : ℝ} (hc : 0 < c) (K : ℝ) : 0 ≤ c3S c K := by
  unfold c3S; have := invSqSum_nonneg; positivity

/-- The `ℓ¹` bound `Σ_m ‖u_m‖ ≤ S₀`. -/
theorem summable_ratioU {σ ρ : ℤ → ℂ} {n : ℤ} {lam : ℂ} {c K : ℝ} (hc : 0 < c)
    (ha : Summable fun m => ‖σ m - ρ m‖ ^ 2) (haK : ∑' m, ‖σ m - ρ m‖ ^ 2 ≤ K)
    (hsep : ∀ m : ℤ, m ≠ n → c⁻¹ * |(m : ℝ) - n| ≤ ‖ρ m - lam‖) :
    Summable (fun m => ‖ratioU σ ρ n lam m‖) ∧ ∑' m, ‖ratioU σ ρ n lam m‖ ≤ c3S c K := by
  obtain ⟨h1, h2⟩ := c3_cs (a := fun m => σ m - ρ m) ha n
  have hb : Summable fun m => c * (‖σ m - ρ m‖ * c3w n m) := h1.mul_left c
  have hs := hb.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_ratioU_le (σ := σ) (lam := lam) hc hsep)
  refine ⟨hs, ?_⟩
  calc ∑' m, ‖ratioU σ ρ n lam m‖ ≤ ∑' m, c * (‖σ m - ρ m‖ * c3w n m) :=
        hs.tsum_le_tsum (norm_ratioU_le hc hsep) hb
    _ = c * ∑' m, ‖σ m - ρ m‖ * c3w n m := tsum_mul_left
    _ ≤ c * (Real.sqrt (∑' m, ‖σ m - ρ m‖ ^ 2) * Real.sqrt invSqSum) :=
        mul_le_mul_of_nonneg_left h2 hc.le
    _ ≤ c3S c K := by
        unfold c3S
        have : Real.sqrt (∑' m, ‖σ m - ρ m‖ ^ 2) ≤ Real.sqrt K := Real.sqrt_le_sqrt haK
        have h3 := Real.sqrt_nonneg invSqSum
        calc c * (Real.sqrt (∑' m, ‖σ m - ρ m‖ ^ 2) * Real.sqrt invSqSum)
            ≤ c * (Real.sqrt K * Real.sqrt invSqSum) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this h3) hc.le
          _ = c * Real.sqrt K * Real.sqrt invSqSum := by ring

/-! ### The splitting `1 + u = (1 + u^E)(1 + u^G)` -/

/-- The part of `u` supported on the exceptional set `E`. -/
def uE (E : Finset ℤ) (u : ℤ → ℂ) (m : ℤ) : ℂ := if m ∈ E then u m else 0

/-- The part of `u` off the exceptional set. -/
def uG (E : Finset ℤ) (u : ℤ → ℂ) (m : ℤ) : ℂ := if m ∈ E then 0 else u m

theorem one_add_eq_mul (E : Finset ℤ) (u : ℤ → ℂ) (m : ℤ) :
    1 + u m = (1 + uE E u m) * (1 + uG E u m) := by
  unfold uE uG
  by_cases h : m ∈ E <;> simp [h]

theorem norm_uE_le (E : Finset ℤ) (u : ℤ → ℂ) (m : ℤ) : ‖uE E u m‖ ≤ ‖u m‖ := by
  unfold uE; split_ifs <;> simp

theorem norm_uG_le (E : Finset ℤ) (u : ℤ → ℂ) (m : ℤ) : ‖uG E u m‖ ≤ ‖u m‖ := by
  unfold uG; split_ifs <;> simp

/-- Exponential bound `e^x - 1 ≤ x e^x`. -/
theorem exp_sub_one_le_mul_exp (x : ℝ) : Real.exp x - 1 ≤ x * Real.exp x := by
  have h := Real.add_one_le_exp (-x)
  have h2 : (-x + 1) * Real.exp x ≤ Real.exp (-x) * Real.exp x :=
    mul_le_mul_of_nonneg_right h (Real.exp_pos x).le
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h2
  nlinarith

/-- The exceptional part: `‖∏(1 + u^E) - 1‖ ≤ e_n e^{S}`, `e_n = Σ_{m∈E} ‖u_m‖`. -/
theorem norm_prod_uE_sub_one {u : ℤ → ℂ} (hu : Summable fun m => ‖u m‖) (E : Finset ℤ) {S : ℝ}
    (hS : ∑' m, ‖u m‖ ≤ S) :
    ‖(∏' m, (1 + uE E u m)) - 1‖ ≤ (∑ m ∈ E, ‖u m‖) * Real.exp S := by
  have hE : Summable fun m => ‖uE E u m‖ :=
    hu.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_uE_le E u)
  have hfin : ∑' m, ‖uE E u m‖ = ∑ m ∈ E, ‖u m‖ := by
    rw [tsum_eq_sum (s := E)]
    · exact Finset.sum_congr rfl fun m hm => by simp [uE, hm]
    · intro m hm; simp [uE, hm]
  have h1 := norm_tprod_one_add_sub_one_le hE
  have hle : ∑' m, ‖uE E u m‖ ≤ S := by
    refine (hE.tsum_le_tsum (norm_uE_le E u) hu).trans hS
  rw [hfin] at h1 hle
  refine h1.trans ?_
  refine (exp_sub_one_le_mul_exp _).trans ?_
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) (Finset.sum_nonneg fun _ _ => norm_nonneg _)

end

end NlsGge.GK38.Lib
