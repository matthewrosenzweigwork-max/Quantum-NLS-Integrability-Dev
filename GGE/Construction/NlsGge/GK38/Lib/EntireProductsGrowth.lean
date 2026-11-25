import NlsGge.GK38.Lib.EntireProductsCircle

/-!
# L4a, part 5: growth on the circles `|z| = nπ + π/2` (GKP Lemma 20.2; book Lemma C.5)

For `σ = σ° + σ̃`, `σ̃ ∈ ℓ²`:
`∏'[symmetricIcc ℤ] (σ_m - z)/π_m = -sin z · (1 + o(1))` uniformly on `‖z‖ = nπ + π/2`, `n → ∞`.
Proof as in the book: `f / sin = ∏_m (σ_m - z)/(mπ - z) = ∏ (1 + c_m)` with
`Σ_m ‖c_m‖ ≤ π⁻¹ Σ_m |σ̃_m| / circDist(n,m) → 0` and `‖∏(1 + c_m) - 1‖ ≤ exp(Σ‖c_m‖) - 1`.
-/

set_option autoImplicit false

open Filter Topology SummationFilter

namespace NlsGge.GK38.Lib

noncomputable section

theorem amgm_mul_le_aux (x y t : ℝ) (ht : 0 < t) : x * y ≤ t * x ^ 2 / 2 + y ^ 2 / (2 * t) := by
  have h := sq_nonneg (t * x - y)
  have : 0 ≤ (t * x - y) ^ 2 / (2 * t) := by positivity
  have e : (t * x - y) ^ 2 / (2 * t) = t * x ^ 2 / 2 - x * y + y ^ 2 / (2 * t) := by
    field_simp; ring
  linarith

/-- Uniform smallness of the finite partial sums `Σ_{m∈s} ‖σ̃_m‖/circDist(n,m)` for large `n`. -/
theorem circle_sum_bound {σ : ℤ → ℂ} (hσ : Summable fun n : ℤ => ‖prodDev σ n‖ ^ 2) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ s : Finset ℤ, ∑ m ∈ s, ‖prodDev σ m‖ / circDist n m ≤ ε := by
  classical
  set K : ℝ := 2 * halfInvSqSum with hK
  have hK0 : 0 ≤ K := by have := halfInvSqSum_nonneg; positivity
  set η : ℝ := ε ^ 2 / (4 * (K + 1)) with hη
  have hηpos : 0 < η := by positivity
  set t : ℝ := 2 * (K + 1) / ε with ht
  have htpos : 0 < t := by positivity
  obtain ⟨s0, hs0⟩ := hσ.vanishing (Iio_mem_nhds hηpos)
  set M : ℕ := s0.sup Int.natAbs with hM
  set A0 : ℝ := ∑ m ∈ s0, ‖prodDev σ m‖ with hA0
  have hA0n : 0 ≤ A0 := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨M + ⌈2 * A0 / ε⌉₊ + 1, fun n hn s => ?_⟩
  have hnM : (M : ℝ) + 2 * A0 / ε + 1 ≤ n := by
    have h1 : 2 * A0 / ε ≤ (⌈2 * A0 / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((M + ⌈2 * A0 / ε⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h2
    linarith
  rw [← Finset.sum_inter_add_sum_sdiff s s0]
  -- small part
  have hsmall : ∑ m ∈ s ∩ s0, ‖prodDev σ m‖ / circDist n m ≤ ε / 2 := by
    have hdd : ∀ m ∈ s0, 2 * A0 / ε ≤ circDist n m := by
      intro m hm
      have hle : (m.natAbs : ℝ) ≤ M := by exact_mod_cast Finset.le_sup (f := Int.natAbs) hm
      unfold circDist
      have h0 : 0 ≤ 2 * A0 / ε := by positivity
      rw [abs_cast_eq, abs_of_nonneg (by have := Nat.cast_nonneg (α := ℝ) M; linarith)]
      linarith
    calc ∑ m ∈ s ∩ s0, ‖prodDev σ m‖ / circDist n m
        ≤ ∑ m ∈ s0, ‖prodDev σ m‖ / circDist n m :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
            (fun m _ _ => div_nonneg (norm_nonneg _) (circDist_pos n m).le)
      _ ≤ ∑ m ∈ s0, ‖prodDev σ m‖ / (2 * A0 / ε) := by
          refine Finset.sum_le_sum fun m hm => ?_
          rcases eq_or_lt_of_le hA0n with h0 | h0
          · rw [← h0] at hdd
            have : ‖prodDev σ m‖ ≤ A0 := by
              rw [hA0]
              exact Finset.single_le_sum (f := fun m => ‖prodDev σ m‖) (fun _ _ => norm_nonneg _) hm
            have hz : ‖prodDev σ m‖ = 0 := by linarith [norm_nonneg (prodDev σ m)]
            simp [hz]
          · exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) (hdd m hm)
      _ = A0 / (2 * A0 / ε) := by rw [← Finset.sum_div]
      _ ≤ ε / 2 := by
          rcases eq_or_lt_of_le hA0n with h0 | h0
          · rw [← h0]; simp; positivity
          · rw [div_div_eq_mul_div]; field_simp; exact le_rfl
  -- tail part
  have hbig : ∑ m ∈ s \ s0, ‖prodDev σ m‖ / circDist n m ≤ ε / 2 := by
    have h1 : ∑ m ∈ s \ s0, ‖prodDev σ m‖ ^ 2 < η := hs0 _ Finset.sdiff_disjoint
    have h2 : ∑ m ∈ s \ s0, 1 / circDist n m ^ 2 ≤ K := sum_inv_circDist_sq_le n _
    calc ∑ m ∈ s \ s0, ‖prodDev σ m‖ / circDist n m
        ≤ ∑ m ∈ s \ s0, (t * ‖prodDev σ m‖ ^ 2 / 2 + (1 / circDist n m ^ 2) / (2 * t)) := by
          refine Finset.sum_le_sum fun m _ => ?_
          have := amgm_mul_le_aux ‖prodDev σ m‖ (1 / circDist n m) t htpos
          rw [div_eq_mul_one_div ‖prodDev σ m‖ (circDist n m)]
          convert this using 2
          rw [div_pow, one_pow]
      _ = t / 2 * ∑ m ∈ s \ s0, ‖prodDev σ m‖ ^ 2 + (1 / (2 * t)) * ∑ m ∈ s \ s0, 1 / circDist n m ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
          congr 1
          · refine Finset.sum_congr rfl fun m _ => by ring
          · refine Finset.sum_congr rfl fun m _ => by ring
      _ ≤ t / 2 * η + (1 / (2 * t)) * K := by
          gcongr
      _ ≤ ε / 2 := by
          have e1 : t / 2 * η = ε / 4 := by
            rw [ht, hη]; field_simp
          have e2 : (1 / (2 * t)) * K = K * ε / (4 * (K + 1)) := by
            rw [ht]; field_simp; ring
          rw [e1, e2]
          have : K * ε / (4 * (K + 1)) ≤ ε / 4 := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith
          linarith
  linarith

/-- **Lemma 20.2 / C.5** (growth on the circles).  `∏'[sym] (σ_m - z)/π_m = -sin z (1 + o(1))` on
`‖z‖ = nπ + π/2`, uniformly in `z` on the circle, as `n → ∞`. -/
theorem product_growth (σ : ℤ → ℂ)
    (hσ : Summable fun n : ℤ => ‖σ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : ℂ, ‖z‖ = n * Real.pi + Real.pi / 2 →
      ‖(∏'[symmetricIcc ℤ] m : ℤ, (σ m - z) / (piN m : ℂ)) + Complex.sin z‖
        ≤ ε * ‖Complex.sin z‖ := by
  intro ε hε
  have hpi := Real.pi_pos
  have hlog : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
  obtain ⟨N, hN⟩ := circle_sum_bound hσ (mul_pos hpi hlog)
  refine ⟨N, fun n hn z hz => ?_⟩
  have hg0 : ∀ m : ℤ, 0 ≤ ‖prodDev σ m‖ / circDist n m := fun m =>
    div_nonneg (norm_nonneg _) (circDist_pos n m).le
  have hg : Summable fun m : ℤ => ‖prodDev σ m‖ / circDist n m := summable_of_sum_le hg0 (hN n hn)
  have hgt : ∑' m : ℤ, ‖prodDev σ m‖ / circDist n m ≤ Real.pi * Real.log (1 + ε) :=
    Real.tsum_le_of_sum_le hg0 (hN n hn)
  have hz0 : ∀ m : ℤ, (m : ℂ) * (Real.pi : ℂ) ≠ z := by
    intro m h
    have h1 := pi_mul_dd_le hz m
    rw [h, sub_self, norm_zero] at h1
    have := mul_pos hpi (circDist_pos n m)
    linarith
  have hcb : ∀ m : ℤ, ‖prodDev σ m / ((m : ℂ) * (Real.pi : ℂ) - z)‖
      ≤ (1 / Real.pi) * (‖prodDev σ m‖ / circDist n m) := by
    intro m
    rw [norm_div]
    calc ‖prodDev σ m‖ / ‖(m : ℂ) * (Real.pi : ℂ) - z‖ ≤ ‖prodDev σ m‖ / (Real.pi * circDist n m) :=
          div_le_div_of_nonneg_left (norm_nonneg _) (mul_pos hpi (circDist_pos n m)) (pi_mul_dd_le hz m)
      _ = (1 / Real.pi) * (‖prodDev σ m‖ / circDist n m) := by
          have := (circDist_pos n m).ne'
          field_simp
  have hc : Summable fun m : ℤ => ‖prodDev σ m / ((m : ℂ) * (Real.pi : ℂ) - z)‖ :=
    (hg.mul_left (1 / Real.pi)).of_nonneg_of_le (fun _ => norm_nonneg _) hcb
  have hS : ∑' m : ℤ, ‖prodDev σ m / ((m : ℂ) * (Real.pi : ℂ) - z)‖ ≤ Real.log (1 + ε) := by
    calc _ ≤ ∑' m : ℤ, (1 / Real.pi) * (‖prodDev σ m‖ / circDist n m) :=
          hc.tsum_le_tsum hcb (hg.mul_left _)
      _ = (1 / Real.pi) * ∑' m : ℤ, ‖prodDev σ m‖ / circDist n m := tsum_mul_left
      _ ≤ (1 / Real.pi) * (Real.pi * Real.log (1 + ε)) :=
          mul_le_mul_of_nonneg_left hgt (by positivity)
      _ = Real.log (1 + ε) := by field_simp
  have key := tprod_prodFactor_add_sin (σ := σ) hz0 hc
  have hQ := norm_tprod_one_add_sub_one_le hc
  have hexp : Real.exp (∑' m : ℤ, ‖prodDev σ m / ((m : ℂ) * (Real.pi : ℂ) - z)‖) - 1 ≤ ε := by
    have := Real.exp_le_exp.mpr hS
    rw [Real.exp_log (by linarith)] at this
    linarith
  show ‖∏'[symmetricIcc ℤ] m, prodFactor σ z m + Complex.sin z‖ ≤ _
  rw [key, norm_mul, norm_sub_rev]
  rw [mul_comm ε]
  exact mul_le_mul_of_nonneg_left (hQ.trans hexp) (norm_nonneg _)

end

end NlsGge.GK38.Lib
