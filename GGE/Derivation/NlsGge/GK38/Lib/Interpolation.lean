import NlsGge.GK38.Lib.InterpolationHilbertGen
import NlsGge.GK38.Lib.InterpolationLemma

/-!
# L4b: the Interpolation Lemma and the discrete Hilbert transform

Plan section 6.1, piece L4b; Grébert–Kappeler book, Appendix F, Lemma F.4 (Interpolation Lemma),
Lemma F.5 (Hilbert transform, `‖H‖ ≤ π`), Lemma F.6 (generalized Hilbert transform); GKP
Lemma 22.4, 22.5.  Mathlib has no Hilbert inequality; F.5 is proved here by the book's Fourier
argument.  The development is split over several modules (all in `NlsGge.GK38.Lib`):

| module | content |
|---|---|
| `InterpolationHilbert` | finite Hilbert form `∫₀¹ h x̌ ȳ`, `hilbertForm_bound` (`≤ π ‖x‖‖y‖`) |
| `InterpolationHilbertOp` | extension to `ℓ²(ℤ)`; `hilbertTransform_bdd` (F.5), `hilbertCLM` |
| `InterpolationHilbertGen` | `hilbertGen_bdd` (F.6; Schur test for the remainder `1/(m-n)²`) |
| `InterpolationContour` | Lagrange partial fractions + Cauchy: `circle_divided_difference` |
| `InterpolationTail` | tail products `T_N`, root separation `exists_window_sep`, `tail_diff_ne` |
| `InterpolationFormula` | `cfam`, `hasProd_cfam`, node algebra |
| `InterpolationHermite` | `hermite_remainder` (finite form of the residue sum) |
| `InterpolationLemma` | `interpolation_lemma` (F.4) |
| `InterpolationProbe` | regression probes (Hilbert transform of a finite sequence; interpolation of `sinc`; the `O(1)` form fails for `sin`) |

**Deviations from the plan statements (rev. 4.2).**  (1) `interpolation_lemma` has the growth
hypothesis `o(1)` (`∀ ε > 0, ∃ N, … ‖φ z‖ ≤ ε ‖sin z‖`) instead of the plan's `O(1)`
(`∃ K, … ≤ K ‖sin z‖`); the `O(1)` form is false (`φ = sin`, `σ_n = nπ`: book erratum, see
`InterpolationLemma` and `InterpolationProbe`).  (2) `hilbertGen_bdd` takes two bounds `Ms`, `Mr` for
`σ̃`, `ρ̂` as in the book (the plan used one `M`).
-/
