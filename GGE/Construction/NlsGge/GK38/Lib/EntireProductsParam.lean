import NlsGge.GK38.Lib.EntireProductsParama
import NlsGge.GK38.Lib.EntireProductsParamb
import NlsGge.GK38.Lib.EntireProductsParamc
import NlsGge.GK38.Lib.EntireProductsParamd
import NlsGge.GK38.Lib.EntireProductsParame

/-!
# L4c (part 1): parametric infinite products, book Appendix C

Plan section 6.1, piece L4c; Grébert–Kappeler book, Appendix C.  Part 1 (no dependence on L4b):

| module | content |
|---|---|
| `EntireProductsParama` | `L2Seq`, `sigmaOf`, `dev_sigmaOf`, `finite_roots`, `entProd_eq_zero_iff` |
| `EntireProductsParamb` | pointwise majorant `pairTerm_le_maj`, uniform bound `norm_entProd_le` on `ℓ²`-balls |
| `EntireProductsParamc` | Lemma C.1 jointly analytic: `analyticOnNhd_entProd_joint` |
| `EntireProductsParamd` | `omitProd` (`f_n`): `multipliable_omit`, `entProd_eq_mul_omitProd`, `analyticOnNhd_omitProd`, `analyticOrderAt_omitProd`, `omitProd_eq_zero_iff`, `analyticOnNhd_omitProd_inv` |
| `EntireProductsParame` | Lemma C.2, sharp: `norm_tprod_one_add_sub_one_le_sharp` |

Book Lemmas C.3 and C.4 (they use the Hilbert transform bound of L4b) are part 2.
-/
