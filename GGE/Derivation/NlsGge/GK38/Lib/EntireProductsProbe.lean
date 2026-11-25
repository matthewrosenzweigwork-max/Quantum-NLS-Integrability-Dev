import NlsGge.GK38.Lib.EntireProducts

/-!
# Regression probes for L4a (`EntireProducts`)

1. `probe_sine_product`: `σ_n = nπ` gives `∏'[sym] (nπ - z)/π_n = -sin z` (book (C.1)), together with
   the simple zeros `kπ` and the circle growth from `product_growth`.
2. `probe_zero_factor_*`: products with a zero factor are multipliable (value `0`); the concrete
   sequence `σ_1 = 0`, `σ_n = nπ` otherwise has a double zero at `0`.
3. `probe_conditional`: `∏ (1 + 1/m)` (not absolutely convergent) is a symmetric limit.
-/

set_option autoImplicit false

open Filter Topology SummationFilter

namespace NlsGge.GK38.Lib

noncomputable section

/-! ### 1. The sine product -/

theorem probe_sine_product (z : ℂ) :
    ∏'[symmetricIcc ℤ] m : ℤ, ((m : ℂ) * (Real.pi : ℂ) - z) / (piN m : ℂ) = -Complex.sin z :=
  (hasProd_sinProd z).tprod_eq

theorem probe_sine_hyp : Summable fun n : ℤ => ‖(fun n : ℤ => (n : ℂ) * (Real.pi : ℂ)) n
    - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2 := by simp

/-- `σ_n = nπ` has simple zeros exactly at `kπ` (`product_entire`, third part). -/
theorem probe_sine_simple_zero (k : ℤ) :
    analyticOrderAt (fun z : ℂ => ∏'[symmetricIcc ℤ] m : ℤ,
      ((fun n : ℤ => (n : ℂ) * (Real.pi : ℂ)) m - z) / (piN m : ℂ)) ((k : ℂ) * (Real.pi : ℂ)) = 1 := by
  rw [(product_entire _ probe_sine_hyp).2.2]
  have : {n : ℤ | (n : ℂ) * (Real.pi : ℂ) = (k : ℂ) * (Real.pi : ℂ)} = {k} := by
    ext n
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    simp [hpi]
  rw [this]
  simp

/-- Away from the zeros, the sine product is nonzero; at `0` it vanishes (zero factor `m = 0`). -/
theorem probe_sine_at_zero :
    ∏'[symmetricIcc ℤ] m : ℤ, ((m : ℂ) * (Real.pi : ℂ) - 0) / (piN m : ℂ) = 0 := by
  rw [probe_sine_product]; simp

/-- Growth: the instance of `product_growth` for `σ_n = nπ` is `0 ≤ ε ‖sin z‖`, consistent. -/
theorem probe_sine_growth :
    ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : ℂ, ‖z‖ = n * Real.pi + Real.pi / 2 →
      ‖(∏'[symmetricIcc ℤ] m : ℤ, ((m : ℂ) * (Real.pi : ℂ) - z) / (piN m : ℂ))
        + Complex.sin z‖ ≤ ε * ‖Complex.sin z‖ :=
  product_growth (fun n : ℤ => (n : ℂ) * (Real.pi : ℂ)) probe_sine_hyp

/-! ### 2. Products with a zero factor -/

/-- Abstract zero factor: `f 3 = 0`, all other factors `1`. -/
def probeZeroFactor (m : ℤ) : ℂ := if m = 3 then 0 else 1

theorem probe_zero_factor_multipliable : Multipliable probeZeroFactor (symmetricIcc ℤ) := by
  refine multipliable_symm_pair (summable_of_ne_finset_zero (s := {2}) fun m hm => ?_)
  have hm2 : m ≠ 2 := by simpa using hm
  have h1 : ((m : ℤ) + 1) ≠ 3 := by
    intro h; apply hm2; omega
  have h2 : (-((m : ℤ) + 1)) ≠ 3 := by omega
  simp only [probeZeroFactor, h1, h2, ↓reduceIte]
  simp

theorem probe_zero_factor_value : ∏'[symmetricIcc ℤ] m : ℤ, probeZeroFactor m = 0 := by
  have hm := probe_zero_factor_multipliable
  refine (hm.hasProd.unique ?_)
  rw [hasProd_symmetricIcc_iff]
  refine (tendsto_const_nhds (x := (0 : ℂ))).congr' ?_
  filter_upwards [eventually_ge_atTop 3] with N hN
  symm
  refine Finset.prod_eq_zero (i := 3) ?_ (by simp [probeZeroFactor])
  simp only [Finset.mem_Icc]
  omega

/-- Concrete zero factor: `σ_1 = 0` (a second root at `0`), `σ_n = nπ` otherwise. -/
def sigmaDouble (n : ℤ) : ℂ := if n = 1 then 0 else (n : ℂ) * (Real.pi : ℂ)

theorem sigmaDouble_hyp : Summable fun n : ℤ => ‖sigmaDouble n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2 := by
  refine summable_of_ne_finset_zero (s := {1}) fun n hn => ?_
  have : n ≠ 1 := by simpa using hn
  simp [sigmaDouble, this]

theorem probe_double_zero_multipliable (z : ℂ) :
    Multipliable (fun m : ℤ => (sigmaDouble m - z) / (piN m : ℂ)) (symmetricIcc ℤ) :=
  (product_entire sigmaDouble sigmaDouble_hyp).1 z

/-- The product vanishes at `0` (zero factors `m = 0` and `m = 1`). -/
theorem probe_double_zero_value :
    ∏'[symmetricIcc ℤ] m : ℤ, (sigmaDouble m - 0) / (piN m : ℂ) = 0 := by
  refine ((probe_double_zero_multipliable 0).hasProd.unique ?_)
  rw [hasProd_symmetricIcc_iff]
  refine (tendsto_const_nhds (x := (0 : ℂ))).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  symm
  refine Finset.prod_eq_zero (i := 1) ?_ (by simp [sigmaDouble])
  simp only [Finset.mem_Icc]
  omega

/-- ... and the order of vanishing at `0` is exactly `2` (zeros counted with multiplicity). -/
theorem probe_double_zero_order :
    analyticOrderAt (fun z : ℂ => ∏'[symmetricIcc ℤ] m : ℤ, (sigmaDouble m - z) / (piN m : ℂ)) 0
      = 2 := by
  rw [(product_entire sigmaDouble sigmaDouble_hyp).2.2]
  have : {n : ℤ | sigmaDouble n = 0} = {0, 1} := by
    ext n
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    by_cases h : n = 1
    · simp [sigmaDouble, h]
    · simp [sigmaDouble, h, hpi]
  rw [this, Set.encard_pair (by norm_num)]

/-- Growth also holds for the perturbed sequence (non-vacuity of the hypotheses of `product_growth`). -/
theorem probe_double_growth :
    ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : ℂ, ‖z‖ = n * Real.pi + Real.pi / 2 →
      ‖(∏'[symmetricIcc ℤ] m : ℤ, (sigmaDouble m - z) / (piN m : ℂ)) + Complex.sin z‖
        ≤ ε * ‖Complex.sin z‖ :=
  product_growth sigmaDouble sigmaDouble_hyp

/-! ### 3. A conditionally convergent product -/

/-- `∏ (1 + 1/m)`: `Σ 1/|m| = ∞`, yet `(1 + 1/m)(1 - 1/m) = 1 - 1/m²` is summable. -/
theorem probe_conditional : Multipliable (fun m : ℤ => 1 + 1 / (m : ℂ)) (symmetricIcc ℤ) := by
  refine multipliable_symm_pair ?_
  have h : ∀ m : ℕ, ‖(1 + 1 / (((m : ℤ) + 1 : ℤ) : ℂ)) * (1 + 1 / ((-((m : ℤ) + 1) : ℤ) : ℂ)) - 1‖
      = 1 / ((m : ℝ) + 1) ^ 2 := by
    intro m
    have hk : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    have : (1 + 1 / (((m : ℤ) + 1 : ℤ) : ℂ)) * (1 + 1 / ((-((m : ℤ) + 1) : ℤ) : ℂ)) - 1
        = -(1 / ((m : ℂ) + 1) ^ 2) := by
      push_cast
      field_simp
      ring
    rw [this, norm_neg, norm_div, norm_one, norm_pow]
    congr 2
    have : ((m : ℂ) + 1) = (((m : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  simp_rw [h]
  exact summable_inv_sq_succ

end

end NlsGge.GK38.Lib
