import Mathlib

/-!
# L4a, part 1: symmetric products over `ℤ` and the pairing lemma

Source: Grébert–Kappeler book, Appendix C (preamble); GKP App. 20 preamble.  The book defines
`∏_{n∈ℤ}(1+a_n) := lim_{N→∞} ∏_{|n|≤N}(1+a_n)`, and states the pairing criterion
`Σ_{n≥1} |a_n + a_{-n}| + |a_n a_{-n}| < ∞` (obtained by grouping `1 + a_n` and `1 + a_{-n}`).

In Lean every such product is `∏'[symmetricIcc ℤ]` with a preceding `Multipliable … (symmetricIcc ℤ)`.

* `multipliable_symm_pair` is the pairing lemma with no nonvanishing hypothesis.  Its hypothesis
  `Summable ‖f(m+1) f(-(m+1)) - 1‖` is implied by the book's criterion
  (`multipliable_symm_pair_book`).
* `piN n = π_n` of GKP App. 20 (`π_0 = 1`, `π_n = nπ` otherwise).
-/

set_option autoImplicit false

open Filter Topology SummationFilter

namespace NlsGge.GK38.Lib

noncomputable section

/-- `π_n := nπ` for `n ≠ 0`, `π_0 := 1` (GKP App. 20; plan section 6.0). -/
def piN (n : ℤ) : ℝ := if n = 0 then 1 else n * Real.pi

theorem piN_zero : piN 0 = 1 := by simp [piN]

theorem piN_of_ne {n : ℤ} (h : n ≠ 0) : piN n = n * Real.pi := by simp [piN, h]

theorem piN_ne_zero (n : ℤ) : piN n ≠ 0 := by
  by_cases h : n = 0
  · simp [h, piN_zero]
  · rw [piN_of_ne h]; exact mul_ne_zero (by exact_mod_cast h) Real.pi_ne_zero

/-- The symmetric partial product over `|n| ≤ N` is `f 0` times the product of the paired factors. -/
theorem prod_Icc_symm_eq {α : Type*} [CommMonoid α] (f : ℤ → α) (N : ℕ) :
    ∏ n ∈ Finset.Icc (-(N : ℤ)) N, f n
      = f 0 * ∏ m ∈ Finset.range N, (f ((m : ℤ) + 1) * f (-((m : ℤ) + 1))) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h : Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ)
        = insert (-((N : ℤ) + 1)) (insert ((N : ℤ) + 1) (Finset.Icc (-(N : ℤ)) N)) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      omega
    rw [h, Finset.prod_insert, Finset.prod_insert, ih, Finset.prod_range_succ]
    · ac_rfl
    · simp only [Finset.mem_Icc]; omega
    · simp only [Finset.mem_insert, Finset.mem_Icc]; omega

/-- The paired factors `f (m+1) * f (-(m+1))` form a multipliable family when the deviations from `1`
are absolutely summable. -/
theorem multipliable_pairs {f : ℤ → ℂ}
    (h : Summable fun m : ℕ => ‖f ((m : ℤ) + 1) * f (-((m : ℤ) + 1)) - 1‖) :
    Multipliable fun m : ℕ => f ((m : ℤ) + 1) * f (-((m : ℤ) + 1)) := by
  have := multipliable_one_add_of_summable h
  simpa using this

/-- Value of the symmetric product: `f 0 * ∏'_{m ≥ 1} f m f (-m)`. -/
theorem hasProd_symm_pair {f : ℤ → ℂ}
    (h : Summable fun m : ℕ => ‖f ((m : ℤ) + 1) * f (-((m : ℤ) + 1)) - 1‖) :
    HasProd f (f 0 * ∏' m : ℕ, f ((m : ℤ) + 1) * f (-((m : ℤ) + 1))) (symmetricIcc ℤ) := by
  rw [hasProd_symmetricIcc_iff]
  simp_rw [prod_Icc_symm_eq]
  exact ((multipliable_pairs h).hasProd.tendsto_prod_nat).const_mul (f 0)

/-- **Pairing lemma** (book App. C preamble; plan L4a).  No nonvanishing hypothesis: a zero factor
`f m = 0` makes the paired products eventually `0`, and the symmetric product is `0`. -/
theorem multipliable_symm_pair {f : ℤ → ℂ}
    (h : Summable fun m : ℕ => ‖f ((m : ℤ) + 1) * f (-((m : ℤ) + 1)) - 1‖) :
    Multipliable f (symmetricIcc ℤ) :=
  (hasProd_symm_pair h).multipliable

theorem tprod_symm_pair {f : ℤ → ℂ}
    (h : Summable fun m : ℕ => ‖f ((m : ℤ) + 1) * f (-((m : ℤ) + 1)) - 1‖) :
    ∏'[symmetricIcc ℤ] m, f m = f 0 * ∏' m : ℕ, f ((m : ℤ) + 1) * f (-((m : ℤ) + 1)) :=
  (hasProd_symm_pair h).tprod_eq

/-- The book's pairing criterion `Σ_{n≥1} |a_n + a_{-n}| + |a_n a_{-n}| < ∞`. -/
theorem multipliable_symm_pair_book {a : ℤ → ℂ}
    (h : Summable fun m : ℕ => ‖a ((m : ℤ) + 1) + a (-((m : ℤ) + 1))‖
      + ‖a ((m : ℤ) + 1) * a (-((m : ℤ) + 1))‖) :
    Multipliable (fun n => 1 + a n) (symmetricIcc ℤ) := by
  refine multipliable_symm_pair (h.of_nonneg_of_le (fun _ => norm_nonneg _) fun m => ?_)
  have e : (1 + a ((m : ℤ) + 1)) * (1 + a (-((m : ℤ) + 1))) - 1
      = (a ((m : ℤ) + 1) + a (-((m : ℤ) + 1))) + a ((m : ℤ) + 1) * a (-((m : ℤ) + 1)) := by ring
  rw [e]
  exact norm_add_le _ _

end

end NlsGge.GK38.Lib
