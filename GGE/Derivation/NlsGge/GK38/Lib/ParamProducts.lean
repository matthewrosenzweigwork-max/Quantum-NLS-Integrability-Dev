import NlsGge.GK38.Lib.ParamProductsCore
import NlsGge.GK38.Lib.ParamProductsZeros
import NlsGge.GK38.Lib.ParamProductsEnt
import NlsGge.GK38.Lib.ParamProductsRoot

/-!
# L4c (part 2a): generic parametric symmetric products

Plan section 6.1, piece L4c part 2a (rev. 4.3).  A generic analyticity lemma for symmetric products
`∏'[symmetricIcc ℤ] m, F m x` of factors that are analytic in a parameter `x` of a complex normed
space and paired close to `1`, generalising L4c part 1 (method: linewise Weierstrass majorant +
uniform total mass + L3a), so that `entProd` and P1's canonical-root factors (`stdRoot`, not
`entProd` factors) are both instances.

| module | content |
|---|---|
| `ParamProductsCore` | `pairDev`; `analyticOnNhd_symm_tprod` (hypotheses `hline`, `hmass`), `analyticOnNhd_symm_tprod_of_mass` (total-mass form: `hpt`, `hQline`, `hQmass`); one-variable `differentiableOn_symm_tprod`; `norm_tprod_symm_le`; the splitting `tprod_symm_eq_prod_mul_tail` |
| `ParamProductsZeros` | `tprod_symm_eq_zero_iff`, `finite_zeros_of_summable_pairDev`, `analyticOrderAt_symm_tprod` (order `= ∑ᶠ m, analyticOrderAt (G m) w`), `symm_tprod_eq_zero_iff` |
| `ParamProductsEnt` | regression: `analyticOnNhd_entProd_joint_of_generic` (book Lemma C.1 from the generic lemma); `l2Q_hline`, `l2Q_hmass` |
| `ParamProductsRoot` | square-root-type factors `rootFac` (shape of `stdRoot(τ_m, γ_m², z)/π_m`): `norm_sqrt_one_sub_sub_one_le`, `analyticAt_rootFac`, `rootPair_le_maj` |
| `ParamProductsRootProbe` | probes: `probe_root_analytic`, `probe_root_zero`, `probe_root_ne_zero`, `probe_root_order`, `probe_order_sine`, `probe_order_double_generic` |

Nothing in this part depends on L4b.
-/
