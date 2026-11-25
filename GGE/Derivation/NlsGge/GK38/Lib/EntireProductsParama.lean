import NlsGge.GK38.Lib.EntireProducts

/-!
# L4c, part 1a: `ℓ²` parametrisation of the sequences, finite roots, zero criterion

Plan section 6.1, piece L4c, item (a).  Grébert–Kappeler book, Appendix C.

* `sigmaOf s n = nπ + s n` (`σ = σ° + σ̃`), `dev_sigmaOf`, `summable_dev_sigmaOf`.
* `finite_roots`: for `Σ ‖σ_n - nπ‖² < ∞` and every `w`, `{n | σ n = w}` is finite
  (so `Set.encard` equals `Set.ncard`, and `analyticOrderAt` of the product is finite).
* `entProd_eq_zero_iff`: the symmetric product `∏'[symmetricIcc ℤ] (σ_m - z)/π_m` vanishes iff `z`
  is one of the `σ_n`.

The helper `dev σ n = σ n - nπ` of the plan is the landed `prodDev` of L4a (`EntireProductsCore`).
-/

set_option autoImplicit false

open Filter Topology SummationFilter

namespace NlsGge.GK38.Lib

noncomputable section

/-- The Hilbert space `ℓ²(ℤ, ℂ)` of perturbations `σ̃ = σ - σ°`. -/
abbrev L2Seq : Type := lp (fun _ : ℤ => ℂ) 2

/-- `σ = σ° + σ̃`, `σ°_n = nπ`. -/
def sigmaOf (s : L2Seq) (n : ℤ) : ℂ := (n : ℂ) * (Real.pi : ℂ) + s n

theorem dev_sigmaOf (s : L2Seq) (n : ℤ) : prodDev (sigmaOf s) n = s n := by
  simp [prodDev, sigmaOf]

theorem summable_dev_sigmaOf (s : L2Seq) :
    Summable fun n : ℤ => ‖prodDev (sigmaOf s) n‖ ^ 2 := by
  have h := (lp.hasSum_norm (p := (2 : ENNReal)) (E := fun _ : ℤ => ℂ) (by simp) s).summable
  refine h.congr fun n => ?_
  rw [dev_sigmaOf]
  simp

/-! ### Finite roots -/

/-- **Finite roots.**  For a sequence with `σ_n - nπ ∈ ℓ²`, every value is taken finitely often. -/
theorem finite_roots {σ : ℤ → ℂ} (hσ : Summable fun n : ℤ => ‖prodDev σ n‖ ^ 2) (w : ℂ) :
    {n : ℤ | σ n = w}.Finite := by
  have ht : ∀ᶠ n : ℤ in cofinite, ‖prodDev σ n‖ ^ 2 < 1 :=
    hσ.tendsto_cofinite_zero.eventually (gt_mem_nhds one_pos)
  have hA : {n : ℤ | ¬ (‖prodDev σ n‖ ^ 2 < 1)}.Finite := Filter.eventually_cofinite.mp ht
  set N : ℕ := ⌈(‖w‖ + 1) / Real.pi⌉₊ with hN
  refine (hA.union (Finset.Icc (-(N : ℤ)) N).finite_toSet).subset fun n hn => ?_
  by_cases h1 : ‖prodDev σ n‖ ^ 2 < 1
  · right
    simp only [Finset.coe_Icc, Set.mem_Icc]
    have hn' : σ n = w := hn
    have hd : ‖prodDev σ n‖ < 1 := by
      by_contra hc
      have hc : 1 ≤ ‖prodDev σ n‖ := not_lt.mp hc
      nlinarith [norm_nonneg (prodDev σ n)]
    have hpi := Real.pi_pos
    have hnorm : ‖(n : ℂ) * (Real.pi : ℂ)‖ ≤ ‖w‖ + 1 := by
      have e : (n : ℂ) * (Real.pi : ℂ) = w - prodDev σ n := by
        unfold prodDev; rw [hn']; ring
      rw [e]
      calc ‖w - prodDev σ n‖ ≤ ‖w‖ + ‖prodDev σ n‖ := norm_sub_le _ _
        _ ≤ ‖w‖ + 1 := by linarith
    have habs : |(n : ℝ)| * Real.pi ≤ ‖w‖ + 1 := by
      have : ‖(n : ℂ) * (Real.pi : ℂ)‖ = |(n : ℝ)| * Real.pi := by
        rw [norm_mul, Complex.norm_intCast, Complex.norm_real, Real.norm_of_nonneg hpi.le]
      linarith
    have hle : |(n : ℝ)| ≤ (N : ℝ) := by
      have h2 : |(n : ℝ)| ≤ (‖w‖ + 1) / Real.pi := by
        rw [le_div_iff₀ hpi]; exact habs
      exact h2.trans (Nat.le_ceil _)
    have := abs_le.mp hle
    constructor
    · have : (-(N : ℝ)) ≤ (n : ℝ) := this.1
      exact_mod_cast this
    · have : (n : ℝ) ≤ (N : ℝ) := this.2
      exact_mod_cast this
  · left; exact h1

/-- The order of vanishing of the entire product is a finite natural number (not `⊤`). -/
theorem analyticOrderAt_entProd_ne_top {σ : ℤ → ℂ}
    (hσ : Summable fun n : ℤ => ‖prodDev σ n‖ ^ 2) (w : ℂ) :
    analyticOrderAt (fun z => ∏'[symmetricIcc ℤ] m : ℤ, prodFactor σ z m) w ≠ ⊤ := by
  rw [analyticOrderAt_entProd hσ w]
  exact (Set.Finite.encard_lt_top (finite_roots hσ w)).ne

/-! ### Zero criterion -/

/-- **`entProd_eq_zero_iff`.**  The product vanishes exactly at the `σ_n`. -/
theorem entProd_eq_zero_iff {σ : ℤ → ℂ} (hσ : Summable fun n : ℤ => ‖prodDev σ n‖ ^ 2) (z : ℂ) :
    ∏'[symmetricIcc ℤ] m : ℤ, prodFactor σ z m = 0 ↔ ∃ n, σ n = z := by
  have han : AnalyticAt ℂ (fun z => ∏'[symmetricIcc ℤ] m : ℤ, prodFactor σ z m) z :=
    (differentiable_entProd hσ).analyticAt z
  have h0 := han.analyticOrderAt_eq_zero
  rw [analyticOrderAt_entProd hσ z, Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem] at h0
  constructor
  · intro h
    by_contra hne
    push Not at hne
    exact (not_not.mpr h) (h0.mp (fun n hn => hne n hn))
  · rintro ⟨n, hn⟩
    by_contra h
    exact (h0.mpr h) n hn

end

end NlsGge.GK38.Lib
