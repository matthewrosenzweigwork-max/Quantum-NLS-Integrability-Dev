import NlsGge.GK38.Lib.InterpolationHilbertOp

/-!
# L4b, part 3: the generalized Hilbert transform (book Lemma F.6)

Source: Grébert–Kappeler book, Appendix F, Lemma F.6 (GKP Lemma 22.5, the form applied in
Lemma C.3): for `σ = nπ + σ̃`, `ρ = nπ + ρ̂` with `σ̃`, `ρ̂` bounded and
`|ρ_m - σ_n| ≥ c |m - n|` (`m ≠ n`), `(Ax)_n = π Σ_{m≠n} x_m/(ρ_m - σ_n)` is a bounded operator on
`ℓ²` whose bound depends only on `‖σ̃‖_∞`, `‖ρ̂‖_∞`, `c`.

Proof (book): `π/(ρ_m-σ_n) = 1/(m-n) + r_{nm}` with `|r_{nm}| ≤ (‖σ̃‖_∞ + ‖ρ̂‖_∞)/(c (m-n)²)`, i.e.
`A = H + (remainder)`; the remainder is bounded by the Schur test for the kernel `1/(m-n)²`
(`schur_finite`).  The constant is `π + (M_σ + M_ρ) K₀ / c` with `K₀ = Σ_{j≠0} 1/j² = π²/3`.
-/

set_option autoImplicit false

open Filter Topology

namespace NlsGge.GK38.Lib

noncomputable section

/-- `K₀ = Σ_{j ∈ ℤ, j ≠ 0} 1/j²` (in Lean `1/0^2 = 0`, so the sum over `ℤ` is the same). -/
def invSqSum : ℝ := ∑' j : ℤ, 1 / (j : ℝ) ^ 2

theorem summable_invSq : Summable fun j : ℤ => 1 / (j : ℝ) ^ 2 :=
  Real.summable_one_div_int_pow.mpr (by norm_num)

theorem invSqSum_nonneg : 0 ≤ invSqSum := tsum_nonneg fun _ => by positivity

/-- Optimization of a one-parameter AM-GM bound. -/
theorem le_mul_sqrt_of_forall {v K P Q : ℝ} (hK : 0 ≤ K) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (h : ∀ s : ℝ, 0 < s → v ≤ K / 2 * (s * P + Q / s)) : v ≤ K * Real.sqrt P * Real.sqrt Q := by
  rcases hP.eq_or_lt with hP0 | hPp
  · -- `P = 0`: `v s ≤ K Q / 2` for all `s > 0`
    subst hP0
    rw [Real.sqrt_zero]
    simp only [mul_zero, zero_mul]
    by_contra hv
    push Not at hv
    have key : ∀ s : ℝ, 0 < s → v * s ≤ K / 2 * Q := by
      intro s hs
      have := h s hs
      calc v * s ≤ K / 2 * (0 + Q / s) * s := by
            simpa using mul_le_mul_of_nonneg_right this hs.le
        _ = K / 2 * Q := by field_simp; ring
    have := key (K * Q / v + 1) (by positivity)
    have h3 : v * (K * Q / v + 1) = K * Q + v := by field_simp
    nlinarith [mul_nonneg hK hQ]
  rcases hQ.eq_or_lt with hQ0 | hQp
  · subst hQ0
    rw [Real.sqrt_zero]
    simp only [mul_zero]
    by_contra hv
    push Not at hv
    set w := K * P with hw
    have hw0 : 0 ≤ w := mul_nonneg hK hPp.le
    have hs : 0 < v / (w + 1) := by positivity
    have := h (v / (w + 1)) hs
    simp only [zero_div, add_zero] at this
    have e : v / (w + 1) * (w + 1) = v := by field_simp
    nlinarith [mul_nonneg hw0 hs.le]
  have := h (Real.sqrt Q / Real.sqrt P) (div_pos (Real.sqrt_pos.mpr hQp) (Real.sqrt_pos.mpr hPp))
  refine this.trans (le_of_eq ?_)
  have eP : Real.sqrt P ^ 2 = P := Real.sq_sqrt hPp.le
  have eQ : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt hQp.le
  have h1 := Real.sqrt_pos.mpr hPp
  have h2 := Real.sqrt_pos.mpr hQp
  generalize Real.sqrt P = a at *
  generalize Real.sqrt Q = b at *
  rw [← eP, ← eQ]
  field_simp
  ring

/-- **Schur test** (finite windows) for a nonnegative kernel `k(m-n)` with `Σ k ≤ K`. -/
theorem schur_finite (k : ℤ → ℝ) (hk0 : ∀ j, 0 ≤ k j) (hks : Summable k) (S T : Finset ℤ)
    (p q : ℤ → ℝ) :
    ∑ n ∈ T, ∑ m ∈ S, k (m - n) * p m * q n
      ≤ (∑' j, k j) * Real.sqrt (∑ m ∈ S, p m ^ 2) * Real.sqrt (∑ n ∈ T, q n ^ 2) := by
  have hK : 0 ≤ ∑' j, k j := tsum_nonneg hk0
  refine le_mul_sqrt_of_forall hK (Finset.sum_nonneg fun _ _ => by positivity)
    (Finset.sum_nonneg fun _ _ => by positivity) fun s hs => ?_
  have hrow : ∀ m : ℤ, ∑ n ∈ T, k (m - n) ≤ ∑' j, k j := by
    intro m
    have hinj : Function.Injective (fun n : ℤ => m - n) := fun a b h => by simpa using h
    calc ∑ n ∈ T, k (m - n) = ∑ j ∈ T.map ⟨fun n => m - n, hinj⟩, k j := by
          rw [Finset.sum_map]; rfl
      _ ≤ ∑' j, k j := hks.sum_le_tsum _ fun j _ => hk0 j
  have hcol : ∀ n : ℤ, ∑ m ∈ S, k (m - n) ≤ ∑' j, k j := by
    intro n
    have hinj : Function.Injective (fun m : ℤ => m - n) := fun a b h => by simpa using h
    calc ∑ m ∈ S, k (m - n) = ∑ j ∈ S.map ⟨fun m => m - n, hinj⟩, k j := by
          rw [Finset.sum_map]; rfl
      _ ≤ ∑' j, k j := hks.sum_le_tsum _ fun j _ => hk0 j
  have step : ∀ n m, k (m - n) * p m * q n ≤ k (m - n) * (s * p m ^ 2 + q n ^ 2 / s) / 2 := by
    intro n m
    have h2 : p m * q n ≤ (s * p m ^ 2 + q n ^ 2 / s) / 2 := by
      have hsp : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
      have hs' : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
      have e : (Real.sqrt s * p m - q n / Real.sqrt s) ^ 2
          = s * p m ^ 2 - 2 * (p m * q n) + q n ^ 2 / s := by
        rw [sub_sq, mul_pow, div_pow, hs']
        field_simp
      nlinarith [sq_nonneg (Real.sqrt s * p m - q n / Real.sqrt s)]
    calc k (m - n) * p m * q n = k (m - n) * (p m * q n) := by ring
      _ ≤ k (m - n) * ((s * p m ^ 2 + q n ^ 2 / s) / 2) := mul_le_mul_of_nonneg_left h2 (hk0 _)
      _ = k (m - n) * (s * p m ^ 2 + q n ^ 2 / s) / 2 := by ring
  calc ∑ n ∈ T, ∑ m ∈ S, k (m - n) * p m * q n
      ≤ ∑ n ∈ T, ∑ m ∈ S, k (m - n) * (s * p m ^ 2 + q n ^ 2 / s) / 2 :=
        Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun m _ => step n m
    _ = (s / 2) * ∑ m ∈ S, p m ^ 2 * ∑ n ∈ T, k (m - n)
          + (1 / (2 * s)) * ∑ n ∈ T, q n ^ 2 * ∑ m ∈ S, k (m - n) := by
        have e : ∀ n m, k (m - n) * (s * p m ^ 2 + q n ^ 2 / s) / 2
            = s / 2 * (p m ^ 2 * k (m - n)) + 1 / (2 * s) * (q n ^ 2 * k (m - n)) := by
          intro n m; field_simp
        simp_rw [e, Finset.sum_add_distrib, ← Finset.mul_sum]
        congr 1
        · congr 1
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.mul_sum]
    _ ≤ (s / 2) * ∑ m ∈ S, p m ^ 2 * (∑' j, k j)
          + (1 / (2 * s)) * ∑ n ∈ T, q n ^ 2 * (∑' j, k j) := by
        gcongr
        · exact hrow _
        · exact hcol _
    _ = (∑' j, k j) / 2 * (s * ∑ m ∈ S, p m ^ 2 + (∑ n ∈ T, q n ^ 2) / s) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        field_simp

/-! ### The generalized kernel -/

/-- The kernel `π/(ρ_m - σ_n)` (`m ≠ n`), `0` on the diagonal. -/
def genKernel (σ ρ : ℤ → ℂ) (n m : ℤ) : ℂ := if m = n then 0 else (Real.pi : ℂ) / (ρ m - σ n)

theorem norm_int_sub_cast (m n : ℤ) : ‖(m : ℂ) - n‖ = |(m : ℝ) - n| := by
  rw [← Complex.ofReal_intCast, ← Complex.ofReal_intCast, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs]

section Gen

variable {σ ρ : ℤ → ℂ} {Ms Mr c : ℝ}

theorem genKernel_diff_bound (hc : 0 < c)
    (hσ : ∀ n, ‖σ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ Ms) (hρ : ∀ n, ‖ρ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ Mr)
    (hsep : ∀ m n : ℤ, m ≠ n → c * |(m : ℝ) - n| ≤ ‖ρ m - σ n‖) (n m : ℤ) :
    ‖genKernel σ ρ n m - hilbKernel n m‖ ≤ (Ms + Mr) / c * (1 / ((m - n : ℤ) : ℝ) ^ 2) := by
  by_cases h : m = n
  · simp [genKernel, hilbKernel, h]
  have hmn : (m : ℝ) - n ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)
  have habs : 0 < |(m : ℝ) - n| := abs_pos.mpr hmn
  have hD : 0 < ‖ρ m - σ n‖ := lt_of_lt_of_le (mul_pos hc habs) (hsep m n h)
  have hD0 : ρ m - σ n ≠ 0 := norm_pos_iff.mp hD
  have hd0 : (m : ℂ) - n ≠ 0 := by
    intro h0
    apply h
    exact_mod_cast sub_eq_zero.mp h0
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [genKernel, hilbKernel, h, ite_false]
  have e : (Real.pi : ℂ) / (ρ m - σ n) - 1 / ((m : ℂ) - n)
      = (-(ρ m - (m : ℂ) * (Real.pi : ℂ)) + (σ n - (n : ℂ) * (Real.pi : ℂ)))
        / (((m : ℂ) - n) * (ρ m - σ n)) := by
    field_simp
    ring
  rw [e, norm_div, norm_mul, norm_int_sub_cast]
  have hnum : ‖-(ρ m - (m : ℂ) * (Real.pi : ℂ)) + (σ n - (n : ℂ) * (Real.pi : ℂ))‖ ≤ Ms + Mr := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg]
    linarith [hρ m, hσ n]
  have hM : 0 ≤ Ms + Mr := (norm_nonneg _).trans hnum
  have hcast : (((m - n : ℤ) : ℝ)) = (m : ℝ) - n := by push_cast; ring
  rw [hcast, ← sq_abs ((m : ℝ) - n)]
  calc ‖-(ρ m - (m : ℂ) * (Real.pi : ℂ)) + (σ n - (n : ℂ) * (Real.pi : ℂ))‖ /
        (|(m : ℝ) - n| * ‖ρ m - σ n‖)
      ≤ (Ms + Mr) / (|(m : ℝ) - n| * (c * |(m : ℝ) - n|)) := by
        apply div_le_div₀ hM hnum (by positivity)
        exact mul_le_mul_of_nonneg_left (hsep m n h) habs.le
    _ = (Ms + Mr) / c * (1 / |(m : ℝ) - n| ^ 2) := by
        field_simp

theorem genKernel_norm_le (hc : 0 < c)
    (hsep : ∀ m n : ℤ, m ≠ n → c * |(m : ℝ) - n| ≤ ‖ρ m - σ n‖) (n m : ℤ) :
    ‖genKernel σ ρ n m‖ ≤ Real.pi / c * |1 / ((m : ℝ) - n)| := by
  by_cases h : m = n
  · simp [genKernel, h]
  have hmn : (m : ℝ) - n ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)
  have habs : 0 < |(m : ℝ) - n| := abs_pos.mpr hmn
  have hD : 0 < ‖ρ m - σ n‖ := lt_of_lt_of_le (mul_pos hc habs) (hsep m n h)
  simp only [genKernel, h, ite_false, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, abs_div, abs_one]
  rw [div_mul_div_comm, mul_one, div_le_div_iff₀ hD (mul_pos hc habs)]
  nlinarith [Real.pi_pos, hsep m n h]

theorem summable_sq_genKernel (hc : 0 < c)
    (hsep : ∀ m n : ℤ, m ≠ n → c * |(m : ℝ) - n| ≤ ‖ρ m - σ n‖) (n : ℤ) :
    Summable fun m : ℤ => ‖genKernel σ ρ n m‖ ^ 2 := by
  refine ((summable_sq_inv_int_sub n).mul_left ((Real.pi / c) ^ 2)).of_nonneg_of_le
    (fun _ => by positivity) fun m => ?_
  have := genKernel_norm_le hc hsep n m
  calc ‖genKernel σ ρ n m‖ ^ 2 ≤ (Real.pi / c * |1 / ((m : ℝ) - n)|) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) this 2
    _ = (Real.pi / c) ^ 2 * (1 / ((m : ℝ) - n)) ^ 2 := by rw [mul_pow, sq_abs]

end Gen

/-- **Book Lemma F.6 (generalized Hilbert transform).**  The bound `C` depends only on the bounds
`Ms ≥ ‖σ̃‖_∞`, `Mr ≥ ‖ρ̂‖_∞` and on `c` (explicitly `π + (|Ms| + |Mr|) K₀ / c`).  The rows are
absolutely summable, so the unconditional sum is the symmetric one. -/
theorem hilbertGen_bdd (Ms Mr c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, ∀ σ ρ : ℤ → ℂ,
      (∀ n : ℤ, ‖σ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ Ms) →
      (∀ n : ℤ, ‖ρ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ Mr) →
      (∀ m n : ℤ, m ≠ n → c * |(m : ℝ) - n| ≤ ‖ρ m - σ n‖) →
      ∃ A : L2Z →L[ℂ] L2Z, ‖A‖ ≤ C ∧ ∀ (x : L2Z) (n : ℤ),
        (Summable fun m : ℤ => ‖if m = n then 0 else (x : ℤ → ℂ) m / (ρ m - σ n)‖) ∧
          (A x : ℤ → ℂ) n = Real.pi * ∑' m : ℤ, if m = n then 0 else (x : ℤ → ℂ) m / (ρ m - σ n) := by
  refine ⟨Real.pi + (|Ms| + |Mr|) / c * invSqSum, fun σ ρ hσ hρ hsep => ?_⟩
  have hC : 0 ≤ Real.pi + (|Ms| + |Mr|) / c * invSqSum :=
    add_nonneg Real.pi_pos.le (mul_nonneg (div_nonneg (by positivity) hc.le) invSqSum_nonneg)
  have hσ' : ∀ n : ℤ, ‖σ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ |Ms| := fun n => (hσ n).trans (le_abs_self _)
  have hρ' : ∀ n : ℤ, ‖ρ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ |Mr| := fun n => (hρ n).trans (le_abs_self _)
  set B : ℝ := (|Ms| + |Mr|) / c with hB
  have hB0 : 0 ≤ B := div_nonneg (by positivity) hc.le
  have hform : ∀ (S T : Finset ℤ) (x y : ℤ → ℂ),
      ‖∑ n ∈ T, ∑ m ∈ S, genKernel σ ρ n m * x m * (starRingEnd ℂ) (y n)‖
        ≤ (Real.pi + B * invSqSum) * Real.sqrt (∑ m ∈ S, ‖x m‖ ^ 2) * Real.sqrt (∑ n ∈ T, ‖y n‖ ^ 2) := by
    intro S T x y
    have hsplit : ∑ n ∈ T, ∑ m ∈ S, genKernel σ ρ n m * x m * (starRingEnd ℂ) (y n)
        = ∑ n ∈ T, ∑ m ∈ S, hilbKernel n m * x m * (starRingEnd ℂ) (y n)
          + ∑ n ∈ T, ∑ m ∈ S, (genKernel σ ρ n m - hilbKernel n m) * x m * (starRingEnd ℂ) (y n) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have h1 := hilbKernel_form_bound S T x y
    have h2 : ‖∑ n ∈ T, ∑ m ∈ S, (genKernel σ ρ n m - hilbKernel n m) * x m * (starRingEnd ℂ) (y n)‖
        ≤ B * invSqSum * Real.sqrt (∑ m ∈ S, ‖x m‖ ^ 2) * Real.sqrt (∑ n ∈ T, ‖y n‖ ^ 2) := by
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun n _ => norm_sum_le _ _).trans ?_
      have h3 : ∑ n ∈ T, ∑ m ∈ S, ‖(genKernel σ ρ n m - hilbKernel n m) * x m * (starRingEnd ℂ) (y n)‖
          ≤ ∑ n ∈ T, ∑ m ∈ S, B * ((1 / ((m - n : ℤ) : ℝ) ^ 2) * ‖x m‖ * ‖y n‖) := by
        refine Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun m _ => ?_
        rw [norm_mul, norm_mul, Complex.norm_conj]
        have := genKernel_diff_bound hc hσ' hρ' hsep n m
        calc ‖genKernel σ ρ n m - hilbKernel n m‖ * ‖x m‖ * ‖y n‖
            ≤ (B * (1 / ((m - n : ℤ) : ℝ) ^ 2)) * ‖x m‖ * ‖y n‖ := by gcongr
          _ = B * ((1 / ((m - n : ℤ) : ℝ) ^ 2) * ‖x m‖ * ‖y n‖) := by ring
      refine h3.trans ?_
      have h4 := schur_finite (fun j : ℤ => 1 / (j : ℝ) ^ 2) (fun j => by positivity) summable_invSq S T
        (fun m => ‖x m‖) (fun n => ‖y n‖)
      simp only [← Finset.mul_sum]
      calc B * ∑ n ∈ T, ∑ m ∈ S, (1 / ((m - n : ℤ) : ℝ) ^ 2) * ‖x m‖ * ‖y n‖
          ≤ B * ((∑' j : ℤ, 1 / (j : ℝ) ^ 2) * Real.sqrt (∑ m ∈ S, ‖x m‖ ^ 2)
              * Real.sqrt (∑ n ∈ T, ‖y n‖ ^ 2)) := mul_le_mul_of_nonneg_left h4 hB0
        _ = B * invSqSum * Real.sqrt (∑ m ∈ S, ‖x m‖ ^ 2) * Real.sqrt (∑ n ∈ T, ‖y n‖ ^ 2) := by
            unfold invSqSum; ring
    calc _ ≤ Real.pi * Real.sqrt (∑ m ∈ S, ‖x m‖ ^ 2) * Real.sqrt (∑ n ∈ T, ‖y n‖ ^ 2)
          + B * invSqSum * Real.sqrt (∑ m ∈ S, ‖x m‖ ^ 2) * Real.sqrt (∑ n ∈ T, ‖y n‖ ^ 2) :=
          add_le_add h1 h2
      _ = _ := by ring
  obtain ⟨A, hA, hA2⟩ := exists_clm_of_form_bound (genKernel σ ρ) (summable_sq_genKernel hc hsep) hC
    hform
  refine ⟨A, hA, fun x n => ?_⟩
  obtain ⟨h1, h2⟩ := hA2 x n
  have e : ∀ m : ℤ, genKernel σ ρ n m * (x : ℤ → ℂ) m
      = (Real.pi : ℂ) * (if m = n then 0 else (x : ℤ → ℂ) m / (ρ m - σ n)) := by
    intro m
    by_cases h : m = n
    · simp [genKernel, h]
    · simp only [genKernel, h, ite_false]; ring
  simp_rw [e] at h1 h2
  refine ⟨?_, ?_⟩
  · have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    refine (h1.mul_left (1 / Real.pi)).congr fun m => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    field_simp
  · rw [h2, tsum_mul_left]

end

end NlsGge.GK38.Lib
