import NlsGge.GK38.Lib.EntireProductsCore
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd

/-!
# L4a, part 4a: the sine product and the quotient identity (book (C.1), proof of Lemma C.5)

* `hasProd_sinProd`: `sin z = -∏_{m∈ℤ} (mπ - z)/π_m`, as a symmetric limit (book (C.1)).
* `tprod_prodFactor_add_sin`: for `z ∉ πℤ` with `Σ ‖σ̃_m/(mπ - z)‖ < ∞`,
  `∏'[sym] (σ_m - z)/π_m + sin z = sin z * (1 - Q(z))`, `Q(z) = ∏_m (1 + σ̃_m/(mπ - z))`.
* `norm_tprod_one_add_sub_one_le`: `‖Q - 1‖ ≤ exp(Σ‖c_m‖) - 1` (book Lemma C.2, the crude version).
-/

set_option autoImplicit false

open Filter Topology SummationFilter

namespace NlsGge.GK38.Lib

noncomputable section

/-- The unperturbed sequence `σ°_n = nπ`. -/
def sigmaZero (n : ℤ) : ℂ := (n : ℂ) * (Real.pi : ℂ)

theorem dev_sigmaZero (n : ℤ) : prodDev sigmaZero n = 0 := by simp [prodDev, sigmaZero]

theorem pairTerm_sigmaZero (z : ℂ) (m : ℕ) :
    pairTerm sigmaZero z m = -z ^ 2 / (((m : ℂ) + 1) * (Real.pi : ℂ)) ^ 2 := by
  rw [pairTerm_eq]
  simp only [dev_sigmaZero, sub_self, zero_div, zero_sub, zero_sub]
  ring

theorem summable_dev_sigmaZero : Summable fun n : ℤ => ‖prodDev sigmaZero n‖ ^ 2 := by
  simp [dev_sigmaZero]

/-- Book (C.1): `sin z = -∏_{m∈ℤ} (mπ - z)/π_m` with the symmetric limit. -/
theorem hasProd_sinProd (z : ℂ) :
    HasProd (prodFactor sigmaZero z) (-Complex.sin z) (symmetricIcc ℤ) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [hasProd_symmetricIcc_iff]
  simp_rw [prod_Icc_symm_eq]
  have hE := (Complex.tendsto_euler_sin_prod (z / Real.pi)).neg
  rw [mul_div_cancel₀ _ hpi] at hE
  refine hE.congr fun N => ?_
  have h0 : prodFactor sigmaZero z 0 = -z := by simp [prodFactor, sigmaZero, piN_zero]
  rw [h0, neg_mul]
  congr 2
  refine Finset.prod_congr rfl fun j _ => ?_
  have hk : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  have := pairTerm_sigmaZero z j
  have e : prodFactor sigmaZero z ((j : ℤ) + 1) * prodFactor sigmaZero z (-((j : ℤ) + 1))
      = 1 + pairTerm sigmaZero z j := by simp [pairTerm]
  rw [e, this]
  field_simp
  ring

/-- Factor identity `(σ_m - z)/π_m = ((mπ - z)/π_m)(1 + σ̃_m/(mπ - z))`. -/
theorem prodFactor_eq_mul {σ : ℤ → ℂ} {z : ℂ} (m : ℤ) (hz : (m : ℂ) * (Real.pi : ℂ) ≠ z) :
    prodFactor σ z m = prodFactor sigmaZero z m * (1 + prodDev σ m / ((m : ℂ) * (Real.pi : ℂ) - z)) := by
  have hne : (m : ℂ) * (Real.pi : ℂ) - z ≠ 0 := sub_ne_zero.mpr hz
  unfold prodFactor prodDev sigmaZero
  field_simp
  ring

theorem norm_tprod_one_add_sub_one_le {ι : Type*} {c : ι → ℂ} (hc : Summable fun i => ‖c i‖) :
    ‖(∏' i, (1 + c i)) - 1‖ ≤ Real.exp (∑' i, ‖c i‖) - 1 := by
  have h := (multipliable_one_add_of_summable hc).hasProd
  refine le_of_tendsto' ((h.sub_const 1).norm) fun s => ?_
  refine (Finset.norm_prod_one_add_sub_one_le s c).trans ?_
  have : ∑ i ∈ s, ‖c i‖ ≤ ∑' i, ‖c i‖ := hc.sum_le_tsum s (fun _ _ => norm_nonneg _)
  have := Real.exp_le_exp.mpr this
  linarith

/-- Quotient identity (proof of book Lemma C.5). -/
theorem tprod_prodFactor_add_sin {σ : ℤ → ℂ} {z : ℂ}
    (hz : ∀ m : ℤ, (m : ℂ) * (Real.pi : ℂ) ≠ z)
    (hc : Summable fun m : ℤ => ‖prodDev σ m / ((m : ℂ) * (Real.pi : ℂ) - z)‖) :
    ∏'[symmetricIcc ℤ] m, prodFactor σ z m + Complex.sin z
      = Complex.sin z * (1 - ∏' m : ℤ, (1 + prodDev σ m / ((m : ℂ) * (Real.pi : ℂ) - z))) := by
  have hQ : HasProd (fun m : ℤ => 1 + prodDev σ m / ((m : ℂ) * (Real.pi : ℂ) - z))
      (∏' m : ℤ, (1 + prodDev σ m / ((m : ℂ) * (Real.pi : ℂ) - z))) (symmetricIcc ℤ) :=
    (multipliable_one_add_of_summable hc).hasProd.mono_left (symmetricIcc ℤ).le_atTop
  have hP := (hasProd_sinProd z).mul hQ
  have e : (fun m : ℤ => prodFactor sigmaZero z m * (1 + prodDev σ m / ((m : ℂ) * (Real.pi : ℂ) - z)))
      = prodFactor σ z := by
    funext m
    exact (prodFactor_eq_mul m (hz m)).symm
  rw [e] at hP
  rw [hP.tprod_eq]
  ring

end

end NlsGge.GK38.Lib
