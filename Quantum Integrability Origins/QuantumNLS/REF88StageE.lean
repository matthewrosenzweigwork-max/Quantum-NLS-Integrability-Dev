import Mathlib
import QuantumNLS.REF88StageD
import QuantumNLS.REF88Reg015Bridge

/-!
# REF88StageE: R-EF8C2837 final-shaped statement of `thm:global-physical-dynamics`

Source: `source-text/chapters/global/physical_cubic.tex` (sha256 `64ec3e0215716404f81e6dabec749fe6cab471b8ff7ed8284127f8160c275115`),
theorem statement lines 28-86.

Hypotheses of `stageE`: `hκ : 0 < κ`, the printed chart hypotheses with the LOCAL conjugation-reflection normalization
(`REF88PrintedChartLocal.PrintedChartLocal`), and ONE named hypothesis `ItemIVInput hκ Φ` carrying the printed conclusion of
item (iv) (physical_cubic.tex lines 77-81, proof paragraph 316-337).  The input `Reg015Input` of `REF88StageD.stageD` is
replaced by the theorem `REF88Reg015Bridge.reg015Input_of_final hκ` (conditional on `Reg015HFinal.REG015_final`).
No `REF88S*` module is imported.  The swap of `ItemIVInput` by a proof is meant to be a one-line change of the argument `hIV`.

`ItemIVInput hκ Φ` says: for every family `ν` that (a) is the printed rotation frequency
(`FreqRotation`: `Φ(S^t u)_n = e^{-itν_n(I(u))} Φ(u)_n` when `I_n(u) > 0`), (b) is continuous on the active domain
(`ν_n` on `{a ∈ ℓ¹_+ : a_n > 0}`) and (c) satisfies the finite-action formula `FiniteFormula`
(printed `eq:global-absolute-frequency` at every finite positive action vector, for every profile and every actual-gap datum),
the following two printed consequences hold:
* `RoughLimit` (lines 77-78 and 332-337): for an `ℓ¹_+` action vector `a` with `a_n > 0`, finite-action vectors converging to `a`
  exist, and along EVERY sequence of finite-action vectors with `n` active converging to `a` in `ℓ¹`, `ν_n` converges to `ν_n(a)`,
  which is the only limit (no moment hypothesis);
* `H1Pair` (lines 78-80 and 316-330): for every `H¹` field `u`, every active pair `b < a` and every actual-gap datum `D0` of the
  unit profile of `u`, `ν_a(I(u)) - ν_b(I(u)) = ω_{ab}`, the actual quadratic adjacent-gap limit.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ENNReal Topology
open Filter

namespace QuantumNLS.REF88StageE

open QuantumNLS.StrongSymplectic QuantumNLS.L2Flow QuantumNLS.REF88Chart QuantumNLS.REF88Reg015
open QuantumNLS.REF88Finite QuantumNLS.REF88PrintedChart QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.Fourier QuantumNLS.REF88QuantumDef QuantumNLS.REF88QuantumReduce
open QuantumNLS.REF88GradStructure QuantumNLS.REF88FieldRotation QuantumNLS.REF88QuantumTangent
open QuantumNLS.REF88StageDReduce QuantumNLS.REF88QuantumProfile QuantumNLS.REF88QuantumLine
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.F04SelBand (Mu II)
open QuantumNLS.ActualGapDataR26 (Data)
open QuantumNLS.ActionTorus (PosL1)
open QuantumNLS.REF88PrintedChartLocal (PrintedChartLocal)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-- Printed rotation formula `eq:global-NLS-rotations` for the family `ν`. -/
def FreqRotation (hκ : 0 < κ) (Φ : L2T L → K) (ν : ℤ → PosL1 → ℝ) : Prop :=
  ∀ (u : L2T L) (t : ℝ) (n : ℤ), 0 < (RootIndexedMasses.masses hκ u).1 n →
    Φ (flowMap hκ.le u t) n =
      Complex.exp (-Complex.I * ((t * ν n (RootIndexedMasses.masses hκ u) : ℝ) : ℂ)) * Φ u n

/-- Printed absolute-frequency formula `eq:global-absolute-frequency` at every finite positive action vector
(every unit profile with indexed probabilities `a/m` at `K = κ m`, every actual-gap datum). -/
def FiniteFormula (L : ℝ) [Fact (0 < L)] (hκ : 0 < κ) (ν : ℤ → PosL1 → ℝ) : Prop :=
  ∀ (u : L2T L) (F : Finset ℤ), F.Nonempty →
    (∀ n, n ∈ F ↔ 0 < (RootIndexedMasses.masses hκ u).1 n) →
    ∀ (hK : 0 < κ * ‖u‖ ^ 2) (v : L2T L), ‖v‖ = 1 →
    (∀ n, II hK v n = (RootIndexedMasses.masses hκ u).1 n / ‖u‖ ^ 2) →
    ∀ D : Data hK v, ∀ n ∈ F, ν n (RootIndexedMasses.masses hκ u) =
      qEnergy (Mu hK v) + qT D.bd D.F + ∑ j ∈ F, II hK v j * D.omega n j

/-- Item (iv), first clause: for general `L²` input, the active frequency `ν_n(a)` is the unique limit of the
finite-action values along `ℓ¹` finite-action approximations (no finite-moment hypothesis). -/
def RoughLimit (ν : ℤ → PosL1 → ℝ) : Prop :=
  ∀ (a : PosL1) (n : ℤ), 0 < a.1 n →
    (∃ aj : ℕ → PosL1, (∀ j, (∃ F : Finset ℤ, ∀ k, k ∉ F → (aj j).1 k = 0) ∧ 0 < (aj j).1 n) ∧
      Tendsto aj atTop (𝓝 a)) ∧
    ∀ aj : ℕ → PosL1, (∀ j, (∃ F : Finset ℤ, ∀ k, k ∉ F → (aj j).1 k = 0) ∧ 0 < (aj j).1 n) →
      Tendsto aj atTop (𝓝 a) →
        Tendsto (fun j => ν n (aj j)) atTop (𝓝 (ν n a)) ∧
        ∀ l : ℝ, Tendsto (fun j => ν n (aj j)) atTop (𝓝 l) → l = ν n a

/-- Item (iv), second clause: for `H¹` input, the frequency difference on an active pair `b < a` equals the actual
quadratic adjacent-gap limit `ω_{ab}` of every actual-gap datum of the unit profile. -/
def H1Pair (L : ℝ) [Fact (0 < L)] (hκ : 0 < κ) (ν : ℤ → PosL1 → ℝ) : Prop :=
  ∀ (u : H02 L 1) {a b : ℤ}, b < a →
    0 < (RootIndexedMasses.masses hκ u.val).1 a → 0 < (RootIndexedMasses.masses hκ u.val).1 b →
    ∀ (hK : 0 < κ * ‖u.val‖ ^ 2) (D0 : Data hK (FullMass.unitDir u.val)),
      ν a (RootIndexedMasses.masses hκ u.val) - ν b (RootIndexedMasses.masses hκ u.val) = D0.omega a b

/-- **Named hypothesis for item (iv)** (printed conclusion, physical_cubic.tex lines 77-81 and 316-337), for the
rotation frequency family of the printed theorem.  It is an explicit assumption of `stageE`; it is built by the separate
sol_multi `REF88S*` item-(iv) modules and is NOT proved here. -/
def ItemIVInput (hκ : 0 < κ) (Φ : L2T L → K) : Prop :=
  ∀ ν : ℤ → PosL1 → ℝ, FreqRotation hκ Φ ν → (∀ n, ContinuousOn (ν n) {a : PosL1 | 0 < a.1 n}) →
    FiniteFormula L hκ ν → RoughLimit ν ∧ H1Pair L hκ ν

/-- **STAGE E (final-shaped statement of `thm:global-physical-dynamics`).**  Hypotheses: `hκ`, the printed chart
hypotheses (`PrintedChartLocal`), and `hIV : ItemIVInput hκ Φ`.  `Reg015Input` is `reg015Input_of_final hκ`.
Conclusion: the conclusions of `REF88StageD.stageD`, together with `RoughLimit` and `H1Pair` for the same `ν`. -/
theorem stageE {Φ : L2T L → K} (hκ : 0 < κ) (hΦ : PrintedChartLocal hκ Φ) (hIV : ItemIVInput hκ Φ) :
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
      ∀ (s : ℝ), 0 ≤ s → MemHsLp L s u) := by
  obtain ⟨⟨ν, h1, h2, h3, h4, h5, h6, h7⟩, hS, hFin⟩ :=
    QuantumNLS.REF88StageD.stageD hκ (QuantumNLS.REF88Reg015Bridge.reg015Input_of_final hκ) hΦ
  have hform : FiniteFormula L hκ ν := fun u F hFne hF hK v hv hvI D n hn =>
    (h7 u F hFne hF hK v hv hvI).2 D n hn
  obtain ⟨hRough, hH1⟩ := hIV ν h1 h4 hform
  exact ⟨⟨ν, h1, h2, h3, h4, h5, h6, h7, hRough, hH1⟩, hS, hFin⟩

end QuantumNLS.REF88StageE

#print axioms QuantumNLS.REF88StageE.stageE
