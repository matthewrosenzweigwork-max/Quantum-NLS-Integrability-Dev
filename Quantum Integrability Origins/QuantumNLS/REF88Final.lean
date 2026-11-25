import Mathlib
import QuantumNLS.REF88StageE
import QuantumNLS.REF88ItemIV

/-!
# REF88Final: `thm:global-physical-dynamics` (R-EF8C2837), final assembly

Source: `source-text/chapters/global/physical_cubic.tex` (sha256 `64ec3e0215716404f81e6dabec749fe6cab471b8ff7ed8284127f8160c275115`),
`\begin{theorem}...\end{theorem}` at lines 28-89 (the statement proper, lines 28-86 plus the closing lines).

`global_physical_dynamics hκ hΦ := REF88StageE.stageE hκ hΦ (REF88ItemIV.itemIV hκ hΦ)`.

CONDITIONAL STATUS (no acceptance claimed): the proof depends on the theorem `REF88Reg015Bridge.reg015Input_of_final`, i.e. on
`Reg015HFinal.REG015_final` (REG-015; independent review reported passed, rebuild queued), and through it on whatever that
module's chain depends on; it adds no hypothesis and no axiom beyond `propext`, `Classical.choice`, `Quot.sound`.

Hypotheses (printed lines 30-34): `hκ : 0 < κ` ("Fix `L,κ>0`", `L>0` is `[Fact (0 < L)]`);
`hΦ : PrintedChartLocal hκ Φ` = `Φ_κ : L² → ℓ²` global real-analytic (`analytic`), strong symplectic diffeomorphism (`symp`),
`|Φ_κ(u)_n|² = I_n^{(κ)}(u)` (`moduli`), and the printed local normalization of `thm:reset-open-transform` (Fourier derivative at `0`,
`fourier`, and the conjugation-reflection identity on a neighbourhood of `0`, `conj_local`).

Conjuncts of the conclusion, in order, with the printed lines (`ν` is one and the same family throughout):
1. `Φ(S^t u)_n = exp(-i t ν_n(I(u))) Φ(u)_n` when `I_n(u) > 0`, every real `t`, every `L²` field `u`: eq:global-NLS-rotations,
   lines 38-43 (`S^t` is `L2Flow.flowMap`, the global flow of lines 35-37).
2. `I_n(u) = 0 → Φ(S^t u)_n = 0`: "At `a_n=0` the corresponding coordinate remains zero", lines 46-48.
3. Any `ν'` realising the rotation of coordinate `n` for all `t` equals `ν_n(I(u))`: the frequency is a well-defined real
   number (line 44 "the real frequency `ν_n`"; no frequency is asserted at `a_n = 0`, lines 46-48).
4. `ν_n` is `ContinuousOn {a ∈ ℓ¹_+ : a_n > 0}` for the `ℓ¹` norm topology: lines 44-45.
5. Fixed-action tori are invariant under the chart flow, with `chartFlow 0 = id`, group law and continuity in `t` on each torus,
   including infinite support: lines 86-88 (first part: "define a strongly continuous group on each fixed-action torus").
6. Conservation of every weighted norm `∑ w_n |z_n|²` and strong continuity of the flow in it, for every nonnegative weight
   `w` with finite value (so in every `h^s`): lines 86-88 ("The rotations preserve all these spaces and define a strongly
   continuous group").
7. The absolute frequency formula `ν_n(a) = ℰ(K,x) + 𝒯(K,x) + ∑_{j∈F} x_j ω_{nj}(K,x)`, `n ∈ F`, for every finite positive
   action vector (every `u` with indexed masses supported exactly in `F`, `K = κ‖u‖²`, `x_j = a_j/m`, every unit profile `v` with the
   indexed probabilities `x` at `K`, every actual-gap datum `D`; the datum is shown to exist): lines 50-75
   (`ℰ = ∫Q²` is `qEnergy`, `𝒯 = 2ℰ - 2L∫QW` is `qT` with `W` the response of the bulk response form
   eq:global-quantum-response, lines 57-67; `ω_{nj}` is `Data.omega`, the actual quadratic adjacent-gap limit of
   lines 68-70; the contact coupling `K/N = κ‖u‖²/N` of lines 76-77 is the effective coupling in the construction of the datum,
   `REF88SRescale`, not a separate conjunct).
8. `RoughLimit ν`, "for general `L²` input each active frequency is the unique continuous limit of these finite-action
   formulas": lines 77-79 and 81 (no moment assertion for rough `L²`): finite-support `ℓ¹` approximants with `a_n > 0` exist, along
   every such sequence `ν_n` converges to `ν_n(a)` and `ν_n(a)` is its only limit.
9. `H1Pair L hκ ν`, "for `H¹` input, its difference on an active pair also equals the actual quadratic adjacent-gap limit":
   lines 79-80: for `u ∈ H¹`, `b < a` active, every actual-gap datum `D0` of the unit profile,
   `ν_a(I(u)) - ν_b(I(u)) = ω_{ab}`.
10. (second top-level conjunct) For every real `s ≥ 0`, `Φ_κ` restricts to a homeomorphism `H^s → h^s` (`toK hs (e u) = Φ u`):
    lines 83-85.
11. (third top-level conjunct) Every `L²` field with finitely supported indexed masses (finite action) lies in every `H^s`:
    the finite-action smoothness of the proof (lines 90 onwards, "Sobolev restrictions and finite-action smoothness"), recorded
    in the statement because the proof of conjunct 7 uses it; it is not a printed conjunct of lines 28-89.
Note on `ℰ`, `𝒯`, `ω`: the actual-law inputs (accepted R-C455C541, R-C88B5D59, R-1E0C40B3, DEF-052) enter only through
`ActualGapDataR26.Data` and `BulkResponseForm`; conjunct 7 holds for EVERY such datum and the nonemptiness of `Data` is proved.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ENNReal Topology
open Filter

namespace QuantumNLS.REF88Final

open QuantumNLS.StrongSymplectic QuantumNLS.L2Flow QuantumNLS.REF88Chart QuantumNLS.REF88Reg015
open QuantumNLS.REF88Finite QuantumNLS.REF88PrintedChart QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.Fourier QuantumNLS.REF88StageE
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.ActionTorus (PosL1)
open QuantumNLS.REF88PrintedChartLocal (PrintedChartLocal)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-- **R-EF8C2837, `thm:global-physical-dynamics`.**  See the module docstring for the conjunct/line map and the conditional
status (REG-015 through `REF88Reg015Bridge`). -/
theorem global_physical_dynamics {Φ : L2T L → K} (hκ : 0 < κ) (hΦ : PrintedChartLocal hκ Φ) :
    (∃ ν : ℤ → PosL1 → ℝ,
      (∀ (u : L2T L) (t : ℝ) (n : ℤ), 0 < (RootIndexedMasses.masses hκ u).1 n →
        Φ (flowMap hκ.le u t) n =
          Complex.exp (-Complex.I * ((t * ν n (RootIndexedMasses.masses hκ u) : ℝ) : ℂ)) *
            Φ u n) ∧
      (∀ (u : L2T L) (t : ℝ) (n : ℤ), (RootIndexedMasses.masses hκ u).1 n = 0 →
        Φ (flowMap hκ.le u t) n = 0) ∧
      (∀ (u : L2T L) (n : ℤ), 0 < (RootIndexedMasses.masses hκ u).1 n → ∀ ν' : ℝ,
        (∀ t : ℝ, Φ (flowMap hκ.le u t) n =
          Complex.exp (-Complex.I * ((t * ν' : ℝ) : ℂ)) * Φ u n) →
          ν' = ν n (RootIndexedMasses.masses hκ u)) ∧
      (∀ n : ℤ, ContinuousOn (ν n) {a : PosL1 | 0 < a.1 n}) ∧
      (∀ a : PosL1, ∀ z ∈ ActionTorus.actionTorus a, ∀ s t : ℝ,
        chartFlow hΦ.symp hκ.le t z ∈ ActionTorus.actionTorus a ∧ chartFlow hΦ.symp hκ.le 0 z = z ∧
        chartFlow hΦ.symp hκ.le (s + t) z = chartFlow hΦ.symp hκ.le s (chartFlow hΦ.symp hκ.le t z) ∧
        Continuous (fun t : ℝ => chartFlow hΦ.symp hκ.le t z)) ∧
      (∀ w : ℤ → ℝ, (∀ n, 0 ≤ w n) → ∀ z : K, (Summable fun n => w n * ‖z n‖ ^ 2) →
        (∀ t : ℝ, ∑' n, w n * ‖chartFlow hΦ.symp hκ.le t z n‖ ^ 2 = ∑' n, w n * ‖z n‖ ^ 2) ∧
        ∀ t0 : ℝ, Tendsto (fun t : ℝ => ∑' n, w n * ‖chartFlow hΦ.symp hκ.le t z n -
          chartFlow hΦ.symp hκ.le t0 z n‖ ^ 2) (𝓝 t0) (𝓝 0))
      ∧ (∀ (u : L2T L) (F : Finset ℤ), F.Nonempty →
        (∀ n, n ∈ F ↔ 0 < (RootIndexedMasses.masses hκ u).1 n) →
        ∀ (hK : 0 < κ * ‖u‖ ^ 2) (v : L2T L), ‖v‖ = 1 →
        (∀ n, QuantumNLS.F04SelBand.II hK v n = (RootIndexedMasses.masses hκ u).1 n / ‖u‖ ^ 2) →
        Nonempty (QuantumNLS.ActualGapDataR26.Data hK v) ∧
        ∀ D : QuantumNLS.ActualGapDataR26.Data hK v,
        ∀ n ∈ F, ν n (RootIndexedMasses.masses hκ u) =
          QuantumNLS.REF88QuantumDef.qEnergy (QuantumNLS.F04SelBand.Mu hK v) +
          QuantumNLS.REF88QuantumDef.qT D.bd D.F +
          ∑ j ∈ F, QuantumNLS.F04SelBand.II hK v j * D.omega n j)
      ∧ RoughLimit ν ∧ H1Pair L hκ ν) ∧
    (∀ (s : ℝ) (hs : 0 ≤ s), ∃ e : H02 L s ≃ₜ h02 L s,
      ∀ u : H02 L s, toK hs (e u) = Φ (H02.toL2 hs u)) ∧
    (∀ (u : L2T L), (∃ F : Finset ℤ, ∀ n, n ∉ F → (RootIndexedMasses.masses hκ u).1 n = 0) →
      ∀ (s : ℝ), 0 ≤ s → MemHsLp L s u) :=
  QuantumNLS.REF88StageE.stageE hκ hΦ (QuantumNLS.REF88ItemIV.itemIV hκ hΦ)

end QuantumNLS.REF88Final

#print axioms QuantumNLS.REF88Final.global_physical_dynamics
