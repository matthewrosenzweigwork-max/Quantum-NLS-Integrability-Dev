import Mathlib
import QuantumNLS.REF88Final
import QuantumNLS.GlobalCompatFinalR47a
import QuantumNLS.IndependentScalingConversionR42b
import QuantumNLS.RephasingFlow

/-!
# RC05Statement: statements for R-C05E2420 `thm:global-full-transform` (`principal_global.tex:2`)

Source: `source-text/chapters/principal_global.tex` (sha256 `ffab02b87a4f4b4608263dea38489a8deca1724fd5c4abe69d7deaa874175f0b`),
printed proof `source-text/chapters/global/main_theorem.tex` (sha256 `e80840d4a4c7386dd2e3377f2d2b55b68da3fd35256de7b550bde8bf1b644c80`).

This module contains DEFINITIONS ONLY (statements), no theorem about an unaccepted object:

* `GlobalClauses`            : the printed conclusions of `thm:global-actual-chart` (R-F5355ABD, `RF535Final.GlobalStatement`) for an
                               EXPLICIT pair `(Φ, Ψ)`: `RF535Final.statement_iff` (module `RC05Parts`) proves that
                               `GlobalStatement L κ hκ d Φl Ψl` is `(torus part) ∧ ∃ Φ Ψ, GlobalClauses ..`.
* `PhysDyn`                  : the conclusion of the accepted-pending headline `REF88Final.global_physical_dynamics`
                               (R-EF8C2837), copied verbatim; `RC05Parts.physDyn_of` proves it by `exact REF88Final.global_physical_dynamics`.
* `PhysicalFrequency`        : the all-time rotation law at active coordinates (first conjunct of `PhysDyn`), which pins `ν_n` uniquely.
* `FreqCovClauses`, `FreqCovInput` : the printed statement of R-877E839C `cor:global-frequency-covariance` (`compatibility.tex:158`)
                               as ONE named input `FreqCovInput` (R-877E839C is authored elsewhere and is not imported here).
* `IsGlobalChart`            : the printed uniqueness characterization of the global map (strong symplectic, real analytic, exact moduli,
                               Fourier differential at `0`, real identity), used to state the period conversion
                               (R-71F7DDC8 `norm:period-coupling`) for "the" maps `Φ_{L,κ}` at several periods.
* `PeriodConversion`         : the printed equation `norm:period-coupling-formula`.
* `RephasingStatement`       : the exact type of the accepted headline `RephasingFlow.norm_rephasing` (R-8DD5AE6E).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ENNReal Topology ComplexConjugate
open Filter Set Metric

namespace QuantumNLS.RC05Statement

open QuantumNLS.StrongSymplectic QuantumNLS.L2Flow
open QuantumNLS.REF88Chart hiding K
open QuantumNLS.REF88Reg015
open QuantumNLS.REF88Finite QuantumNLS.REF88PrintedChart QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.Fourier QuantumNLS.REF88StageE
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.ActionTorus (PosL1 actionTorus rotate)
open QuantumNLS.RootIndexedMasses (masses)
open QuantumNLS.D01LocalPrimitive (K)
open QuantumNLS.SymplecticBracket (omega hamField)
open QuantumNLS.RF535Final (Local023Body Iact Tact Tθ avgPrimitive)
open QuantumNLS.ResetNormalizationUniqueness (Cphys)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-! ## Item 1: the printed conclusions of `thm:global-actual-chart` for an explicit pair `(Φ, Ψ)` -/

/-- Verbatim copy of the second conjunct (`∃ Y F Φ Ψ, ..`) of `RF535Final.GlobalStatement`, with `(Φ, Ψ)` an explicit pair:
`Y`, `F` are the averaged-primitive vector field and its complete flow, `Φ_κ = e^{T/2} Φ_loc ∘ F_{-T}`,
`Φ_κ^{-1} = F_T ∘ Φ_loc^{-1} ∘ e^{-T/2}`, real-analytic diffeomorphism, exact actions, strong symplecticity,
invertible differentials, literal agreement with the local chart on the entire ball, realizability of every `a ∈ ℓ¹_+`
with fibre/torus identification, torus intertwining, individual orbit periods. -/
def GlobalClauses (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (d : ℝ) (Φl : L2T L → K) (Ψl : K → L2T L)
    (Φ : L2T L → K) (Ψ : K → L2T L) : Prop :=
  ∃ (Y : L2T L → L2T L) (F : ℝ → L2T L → L2T L),
    -- `Y` is the unique real vector field with `ι_Y ω = ᾱ`
    (∀ u h, omega (Y u) h = avgPrimitive (L := L) hκ u h) ∧
    (∀ u v, (∀ h, omega v h = avgPrimitive (L := L) hκ u h) → v = Y u) ∧
    -- `F_t` is the complete flow of `Y`
    (∀ u, F 0 u = u) ∧ (∀ u t, HasDerivAt (fun s => F s u) (Y (F t u)) t) ∧
    (∀ u (γ : ℝ → L2T L), γ 0 = u → (∀ t, HasDerivAt γ (Y (γ t)) t) → ∀ t, F t u = γ t) ∧
    -- `Φ_κ(u) = e^{T/2} Φ_loc(F_{-T} u)` and `Φ_κ^{-1}(z) = F_T(Φ_loc^{-1}(e^{-T/2} z))`, every admissible `T ≥ 0`
    (∀ (u : L2T L) (T : ℝ), 0 ≤ T → Real.exp (-T / 2) * ‖u‖ < d / Real.sqrt κ →
      Φ u = Real.exp (T / 2) • Φl (F (-T) u)) ∧
    (∀ (z : K) (T : ℝ), 0 ≤ T → Real.exp (-T / 2) * ‖z‖ < d / Real.sqrt κ →
      Ψ z = F T (Ψl (Real.exp (-T / 2) • z))) ∧
    -- real-analytic diffeomorphism `L² → ℓ²` with genuine inverse
    (∀ u, AnalyticAt ℝ Φ u) ∧ (∀ z, AnalyticAt ℝ Ψ z) ∧ (∀ u, Ψ (Φ u) = u) ∧ (∀ z, Φ (Ψ z) = z) ∧
    -- `|Φ(u)_n|² = I_n^{(κ)}(u)`, `‖Φ(u)‖² = ‖u‖²`
    (∀ u n, ‖Φ u n‖ ^ 2 = (masses hκ u).1 n) ∧ (∀ u, ‖Φ u‖ ^ 2 = ‖u‖ ^ 2) ∧
    -- strong symplecticity
    (∀ u (h k : L2T L), 2 * (inner ℂ (fderiv ℝ Φ u h) (fderiv ℝ Φ u k)).im = 2 * (inner ℂ h k).im) ∧
    -- full differentials are bounded inverse real-linear operators at every point
    (∀ u, ∃ e : L2T L ≃L[ℝ] K, HasFDerivAt Φ (e : L2T L →L[ℝ] K) u ∧
      HasFDerivAt Ψ (e.symm : K →L[ℝ] L2T L) (Φ u)) ∧
    -- agreement with the local chart on its entire ball
    (∀ u ∈ ball (0 : L2T L) (d / Real.sqrt κ), Φ u = Φl u) ∧
    (∀ z ∈ ball (0 : K) (d / Real.sqrt κ), Ψ z = Ψl z) ∧
    -- every nonnegative summable action sequence is realized; each exact fibre onto its full modulus torus
    (∀ a : PosL1, ∃ u : L2T L, masses hκ u = a) ∧
    (∀ a : PosL1, Φ '' {u : L2T L | masses hκ u = a} = actionTorus a) ∧
    -- the product action is intertwined with `(z_n) ↦ (e^{-iθ_n} z_n)`
    (∀ (ψ : QuantumNLS.Ext025B6TorusCoordinates.Torus) (u : L2T L),
      Φ (Tact (L := L) hκ ψ u) = rotate ψ⁻¹ (Φ u)) ∧
    (∀ (θ : QuantumNLS.ProductTorusGenerator.Linf) (u : L2T L) (n : ℤ),
      Φ (Tθ (L := L) hκ θ u) n = Complex.exp (-(θ n : ℂ) * Complex.I) * Φ u n) ∧
    -- individual orbits: least positive period `2π` for a positive action, fixed for a zero action
    (∀ (n : ℤ) (u : L2T L), 0 < (masses hκ u).1 n →
      Tact (L := L) hκ (Pi.mulSingle n (Circle.exp (2 * Real.pi))) u = u ∧
      ∀ t : ℝ, 0 < t → t < 2 * Real.pi → Tact (L := L) hκ (Pi.mulSingle n (Circle.exp t)) u ≠ u) ∧
    (∀ (n : ℤ) (u : L2T L), (masses hκ u).1 n = 0 →
      ∀ t : ℝ, Tact (L := L) hκ (Pi.mulSingle n (Circle.exp t)) u = u)

/-! ## Items 2, 3, 4: the conclusion of the physical-dynamics headline R-EF8C2837 -/

/-- Verbatim copy of the conclusion of `QuantumNLS.REF88Final.global_physical_dynamics` (R-EF8C2837,
`thm:global-physical-dynamics`), with `hΦ.symp` replaced by the explicit strong-symplecticity witness `hs`.
First top-level conjunct, in order: (1) the all-time rotation law `Φ(S^t u)_n = e^{-itν_n(I(u))} Φ(u)_n` for `I_n(u) > 0`;
(2) the zero coordinate stays zero; (3) uniqueness of the real frequency; (4) continuity of `ν_n` on `{a_n > 0}`; (5) fixed-action
tori invariant under the chart flow (group, strongly continuous); (6) conservation and strong continuity in every weighted norm;
(7) the finite-support quantum-root response formula for the absolute frequency (`ℰ + 𝒯 + Σ x_j ω_{nj}`, effective coupling
`κ‖u‖²`); (8) the unique continuous limit for general `L²` data (`RoughLimit`); (9) the actual quadratic Bethe adjacent-gap limit
on `H¹` data (`H1Pair`). Second conjunct: `H^s → h^s` homeomorphism, every `s ≥ 0`. Third: finite action lies in every `H^s`. -/
def PhysDyn {Φ : L2T L → K} (hκ : 0 < κ) (hs : IsStronglySymplectic Φ) : Prop :=
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
        chartFlow hs hκ.le t z ∈ ActionTorus.actionTorus a ∧ chartFlow hs hκ.le 0 z = z ∧
        chartFlow hs hκ.le (s + t) z = chartFlow hs hκ.le s (chartFlow hs hκ.le t z) ∧
        Continuous (fun t : ℝ => chartFlow hs hκ.le t z)) ∧
      (∀ w : ℤ → ℝ, (∀ n, 0 ≤ w n) → ∀ z : K, (Summable fun n => w n * ‖z n‖ ^ 2) →
        (∀ t : ℝ, ∑' n, w n * ‖chartFlow hs hκ.le t z n‖ ^ 2 = ∑' n, w n * ‖z n‖ ^ 2) ∧
        ∀ t0 : ℝ, Tendsto (fun t : ℝ => ∑' n, w n * ‖chartFlow hs hκ.le t z n -
          chartFlow hs hκ.le t0 z n‖ ^ 2) (𝓝 t0) (𝓝 0))
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
    (∀ (s : ℝ) (hs' : 0 ≤ s), ∃ e : H02 L s ≃ₜ h02 L s,
      ∀ u : H02 L s, toK hs' (e u) = Φ (H02.toL2 hs' u)) ∧
    (∀ (u : L2T L), (∃ F : Finset ℤ, ∀ n, n ∉ F → (RootIndexedMasses.masses hκ u).1 n = 0) →
      ∀ (s : ℝ), 0 ≤ s → MemHsLp L s u)

/-- The all-time rotation law of the global physical flow at active coordinates (the first conjunct of the first conjunct of
`PhysDyn`). At an active coordinate it determines `ν_n` uniquely, because every action vector is realized. -/
def PhysicalFrequency {Φ : L2T L → K} (hκ : 0 < κ) (ν : ℤ → PosL1 → ℝ) : Prop :=
  ∀ (u : L2T L) (t : ℝ) (n : ℤ), 0 < (RootIndexedMasses.masses hκ u).1 n →
    Φ (flowMap hκ.le u t) n =
      Complex.exp (-Complex.I * ((t * ν n (RootIndexedMasses.masses hκ u) : ℝ) : ℂ)) * Φ u n

/-! ## Item 5b: R-877E839C `cor:global-frequency-covariance` (`compatibility.tex:158`), one named input -/

/-- The printed conclusions of R-877E839C, for the family `ν^{(κ)}` of real frequencies of the global physical flow.
`(B_k a)_n = a_{n-k}` and `(Ra)_n = a_{-n}` are written as the relations `b_n = a_{n-k}` and `b_n = a_{-n}` between the action
sequences `b = B_k a`, `b = R a` (every `a ∈ ℓ¹_+` has these images).  "Whenever the displayed coordinate is active" is
`0 < b_n` (boost, reflection) and `0 < a_n` (scaling).  `p_n = 2πn/L` is `LocalSpectral.pm L n`.
Conjugation: the action permutation of `ū` is that of reflection, with the same frequency formula; common phase and spatial
translation leave the actions (hence the frequencies) unchanged. -/
def FreqCovClauses (L : ℝ) [Fact (0 < L)] (ν : ℝ → ℤ → PosL1 → ℝ) : Prop :=
  (∀ κ : ℝ, 0 < κ → ∀ (k : ℤ) (a b : PosL1), (∀ n, b.1 n = a.1 (n - k)) → ∀ n, 0 < b.1 n →
    ν κ n b = ν κ (n - k) a + QuantumNLS.LocalSpectral.pm L n ^ 2 - QuantumNLS.LocalSpectral.pm L (n - k) ^ 2) ∧
  (∀ κ : ℝ, 0 < κ → ∀ (a b : PosL1), (∀ n, b.1 n = a.1 (-n)) → ∀ n, 0 < b.1 n →
    ν κ n b = ν κ (-n) a) ∧
  (∀ κ : ℝ, 0 < κ → ∀ s : ℝ, 0 < s → ∀ (a b : PosL1), (∀ n, b.1 n = s ^ 2 * a.1 n) → ∀ n, 0 < a.1 n →
    ν κ n b = ν (κ * s ^ 2) n a) ∧
  (∀ (κ : ℝ) (hκ : 0 < κ) (u : L2T L),
    (∀ n, (masses hκ (star u)).1 n = (masses hκ u).1 (-n)) ∧
    ∀ n, 0 < (masses hκ (star u)).1 n → ν κ n (masses hκ (star u)) = ν κ (-n) (masses hκ u)) ∧
  (∀ (κ : ℝ) (hκ : 0 < κ) (u : L2T L) (γ y : ℝ),
    masses hκ (Complex.exp ((γ : ℂ) * Complex.I) • u) = masses hκ u ∧
    masses hκ (QuantumNLS.BornTranslation.trans y u) = masses hκ u ∧
    (∀ n, ν κ n (masses hκ (Complex.exp ((γ : ℂ) * Complex.I) • u)) = ν κ n (masses hκ u)) ∧
    (∀ n, ν κ n (masses hκ (QuantumNLS.BornTranslation.trans y u)) = ν κ n (masses hκ u)))

/-- **THE NAMED INPUT `R-877E839C`.**  "Assume also the global physical-flow theorem": for the extending family of the reviewed
local maps (`Family`, R-CA92819A) and any frequency family `ν^{(κ)}` realizing the all-time rotation law of the global physical
flow, the printed frequency covariances hold.  This declaration asserts nothing by itself.  The final R-C05E2420 replaces the
hypothesis `∀ L, FreqCovInput L` by the accepted R-877E839C (the only place where R-877E839C enters). -/
def FreqCovInput (L : ℝ) [Fact (0 < L)] : Prop :=
  ∀ (d CL : ℝ) (Φl : ℝ → L2T L → K) (Ψl : ℝ → K → L2T L) (Φ : ℝ → L2T L → K) (Ψ : ℝ → K → L2T L),
    Local023Body L d CL Φl Ψl → QuantumNLS.GlobalCompatR47a.Family d Φl Ψl Φ Ψ →
    ∀ ν : ℝ → ℤ → PosL1 → ℝ,
      (∀ (κ : ℝ) (hκ : 0 < κ), PhysicalFrequency hκ (Φ := Φ κ) (ν κ)) →
      FreqCovClauses L ν

/-! ## Item 5: physical-period conversion (R-71F7DDC8 `norm:period-coupling`) -/

/-- The printed characterization of the global map `Φ_{L,κ}` (uniqueness clause of `thm:global-compatibility`): a strongly
symplectic, real-analytic map with exact indexed moduli, Fourier differential at `0` and the real identity
`Φ(\overline{u(-·)}) = \overline{Φ(u)}`. -/
def IsGlobalChart (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (G : L2T L → K) : Prop :=
  IsStronglySymplectic G ∧ (∀ u, AnalyticAt ℝ G u) ∧
  (∀ u n, ‖G u n‖ ^ 2 = (masses hκ u).1 n) ∧
  (∀ v, fderiv ℝ G 0 v = QuantumNLS.Fourier.fourierL2 L v) ∧
  (∀ u, G (Cphys L u) = star (G u))

/-- `norm:period-coupling-formula`: for `Φ_{L,κ}`, `Φ_{1,κL}`, `Φ_{1,1}` the global maps (`IsGlobalChart`) at the three
(period, coupling) pairs, and every `u ∈ L²(𝕋_L)`,
`Φ_{L,κ}(u) = Φ_{1,κL}(√L u(L·)) = (κL)^{-1/2} Φ_{1,1}(L√κ u(L·))`
(`PeriodFieldR42b.period L u = √L u(L·)`, `unitPotential L κ u = L√κ u(L·)`, `IndependentScalingConversionR42b.unitPotential_ae`). -/
def PeriodConversion : Prop :=
  ∀ (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ)
    (G : L2T L → K) (G1 : L2T 1 → K) (G11 : L2T 1 → K),
    IsGlobalChart L κ hκ G → IsGlobalChart 1 (κ * L) (mul_pos hκ (Fact.out : 0 < L)) G1 →
    IsGlobalChart 1 1 one_pos G11 →
    ∀ u : L2T L,
      G u = G1 (QuantumNLS.PeriodFieldR42b.period L u) ∧
      G u = (Real.sqrt (κ * L))⁻¹ • G11 (QuantumNLS.IndependentScalingConversionR42b.unitPotential L κ u)

/-! ## Item 6: the rephasing freedom (R-8DD5AE6E) -/

/-- The exact type of the accepted headline `RephasingFlow.norm_rephasing` (R-8DD5AE6E `norm:rephasing`). -/
def RephasingStatement (c κ : ℝ) (hc : c ≠ 0) (hκ : 0 < κ) : Prop :=
  type_of% (QuantumNLS.RephasingFlow.norm_rephasing c κ hc hκ)

/-- Without the real identity the action-dependent canonical phase freedom remains: `G = U_{c,κ,1} ∘ Φ_κ` is strongly
symplectic, real analytic, has the exact moduli, Fourier differential at `0`, fixes every single-mode plane, differs from `Φ_κ`
by the action-dependent phase `e^{-2icκ(‖u‖² - I_n(u))}`, and violates the real identity. -/
def RephasingFreedom (hκ : 0 < κ) (Φ : L2T L → K) (c : ℝ) : Prop :=
  ∃ G : L2T L → K, IsStronglySymplectic G ∧ (∀ u, AnalyticAt ℝ G u) ∧
    (∀ u n, ‖G u n‖ ^ 2 = (masses hκ u).1 n) ∧
    (∀ v, fderiv ℝ G 0 v = QuantumNLS.Fourier.fourierL2 L v) ∧
    (∀ (a : ℂ) (k : ℤ), G (a • modeLp L k) = a • lp.single 2 k (1 : ℂ)) ∧
    (∀ u n, G u n = Complex.exp (-(2 * Complex.I * c * κ) * ((‖u‖ ^ 2 - (masses hκ u).1 n : ℝ) : ℂ)) * Φ u n) ∧
    (∃ u, G (Cphys L u) ≠ star (G u)) ∧ G ≠ Φ

end QuantumNLS.RC05Statement
