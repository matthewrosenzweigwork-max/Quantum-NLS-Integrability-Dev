import NlsGge.GK38.Lib.SymmPair
import NlsGge.GK38.Lib.EntireProductsCore
import NlsGge.GK38.Lib.EntireProductsZeros
import NlsGge.GK38.Lib.EntireProductsSine
import NlsGge.GK38.Lib.EntireProductsCircle
import NlsGge.GK38.Lib.EntireProductsGrowth
import NlsGge.GK38.Lib.EntireRatio

/-!
# L4a: infinite products of entire functions over `ℤ` as symmetric limits

Plan section 6.1, piece L4a; Grébert–Kappeler book, Appendix C (GKP Appendix 20).
All products over `ℤ` are `∏'[symmetricIcc ℤ]`, with the `Multipliable … (symmetricIcc ℤ)` fact
proved first.  The development is split over several modules (all in `NlsGge.GK38.Lib`):

| module | content |
|---|---|
| `SymmPair` | `piN`, `multipliable_symm_pair`, `tprod_symm_pair`, `multipliable_symm_pair_book` |
| `EntireProductsCore` | `prodDev`, `prodFactor`, `pairTerm`, uniform bounds, `differentiable_entProd` |
| `EntireProductsZeros` | `analyticOrderAt_entProd` (zeros with multiplicity) |
| `EntireProductsSine` | `hasProd_sinProd` (book (C.1)), quotient identity |
| `EntireProductsCircle` | `circle_sum_bound` (`Σ_m |σ̃_m|/circDist(n,m) → 0`) |
| `EntireProductsGrowth` | `product_growth` (book Lemma C.5 / GKP Lemma 20.2) |
| `EntireRatio` | `entire_eq_of_ratio_tendsto_one` (maximum principle) |

This file contains `product_entire` (book Lemma C.1 / GKP Lemma 20.1 for the product `f_0`).
-/

set_option autoImplicit false

open Filter Topology SummationFilter

namespace NlsGge.GK38.Lib

noncomputable section

/-- **Book Lemma C.1 / GKP Lemma 20.1.**  For `σ = σ° + σ̃` with `σ̃ ∈ ℓ²`, the symmetric product
`∏'[symmetricIcc ℤ] (σ_m - z)/π_m` is multipliable for every `z`, defines an entire function, and its
zeros are exactly the `σ_n`, the order at `w` being the number of `n` with `σ n = w`. -/
theorem product_entire (σ : ℤ → ℂ)
    (hσ : Summable fun n : ℤ => ‖σ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) :
    (∀ z : ℂ, Multipliable (fun m : ℤ => (σ m - z) / (piN m : ℂ)) (symmetricIcc ℤ)) ∧
    Differentiable ℂ (fun z : ℂ => ∏'[symmetricIcc ℤ] m : ℤ, (σ m - z) / (piN m : ℂ)) ∧
    ∀ w : ℂ,
      analyticOrderAt (fun z : ℂ => ∏'[symmetricIcc ℤ] m : ℤ, (σ m - z) / (piN m : ℂ)) w
        = Set.encard {n : ℤ | σ n = w} :=
  ⟨fun z => multipliable_prodFactor hσ z, differentiable_entProd hσ,
    fun w => analyticOrderAt_entProd hσ w⟩

end

end NlsGge.GK38.Lib
