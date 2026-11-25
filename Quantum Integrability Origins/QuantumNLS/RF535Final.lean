import Mathlib
import QuantumNLS.RF535Hyp
import QuantumNLS.RF535Chart
import QuantumNLS.Local023Final
import QuantumNLS.ActionTorus

/-!
# R-F5355ABD `thm:global-actual-chart` (`source-text/chapters/global/actual_chart.tex:15`): global canonical reconstruction for the actual quantum actions

**Named theorem** `QuantumNLS.RF535Final.global_actual_chart` (`L > 0` is the only hypothesis `[Fact (0 < L)]`; no added hypothesis).

Statement.  (1) (non-vacuity) The LOCAL-023 local canonical chart exists: `Local023Body L d CL Φloc Ψloc` is verbatim the body of `Local023.reset_open_transform` (`local023` restates the accepted theorem through it by `exact`).
(2) For every such local chart (`d`, `Φloc`, `Ψloc`, the radius `δ = d/√κ` of the printed statement) and every coupling `κ > 0`, `GlobalStatement` holds:
* the bounded-angle Hamiltonians `H_θ = Σ θ_n I_n^{(κ)}` (`Hθ`, `θ ∈ ℓ^∞`) have complete flows (existence and uniqueness for all real times) whose time-one maps are the product-torus action `T_θ` (`Tθ`) of the accepted `thm:global-product-torus`; this action is the continuous action of `𝕋^ℤ` (`Tact`, `ψ ∈ ℤ → Circle`) with `Tact(e^{iθ}) = T_θ`, `Tact(ψψ') = Tact ψ ∘ Tact ψ'`, `Tact 1 = id`;
* `ᾱ_u(h) = ∫_{𝕋^ℤ} Im⟨T_ψ u, DT_ψ(u)h⟩ dψ` (`avgPrimitive`, normalized product Haar measure), `Y` is the unique vector field with `ω(Y u, ·) = ᾱ_u` (`ω = 2 Im⟨·,·⟩`), and `F` is its complete flow (`F 0 = id`, `∂_t F_t u = Y(F_t u)`, uniqueness of solutions);
* `Φ_κ(u) = e^{T/2} Φloc(F_{-T} u)` for every `T ≥ 0` with `e^{-T/2}‖u‖ < δ` (hence independent of `T`), `Φ_κ^{-1}(z) = F_T(Φloc^{-1}(e^{-T/2} z))` for every `T ≥ 0` with `e^{-T/2}‖z‖ < δ`; `Φ_κ : L² → ℓ²` is a real-analytic diffeomorphism (`Φ`, `Ψ` real analytic at every point, mutually inverse bijections of the whole spaces);
* `|Φ_κ(u)_n|² = I_n^{(κ)}(u)`, `‖Φ_κ(u)‖² = ‖u‖²`; `2 Im⟨DΦ_κ(u)h, DΦ_κ(u)k⟩ = 2 Im⟨h,k⟩`; at every point `DΦ_κ(u)` is a bounded real-linear isomorphism `e : L² ≃L ℓ²` with `D(Φ_κ^{-1})(Φ_κ u) = e⁻¹`; `Φ_κ` (and its inverse) agree with `Φloc` (`Ψloc`) on the entire ball `B_δ`;
* every `a ∈ ℓ¹_+` (`PosL1`) is realized, `Φ_κ` carries each exact fibre `{u : I(u) = a}` onto the full DEF-019 torus `actionTorus a = {z : |z_n|² = a_n}`; the product action is intertwined with coordinate rotations: `Φ_κ(T_ψ u) = rotate ψ⁻¹ (Φ_κ u)` (`z_n ↦ e^{-iθ_n} z_n` for `ψ_n = e^{iθ_n}`; and for bounded real angles `Φ_κ(T_θ u)_n = e^{-iθ_n} Φ_κ(u)_n`);
* individual orbits `t ↦ T_{e^{it}e_n} u`: if `I_n(u) > 0` then `2π` is a period and no `t ∈ (0, 2π)` is one (least positive period `2π`); if `I_n(u) = 0` every `t` is a period (the orbit is fixed).

Proof (printed proof, all inputs accepted nodes): `RF535Bridge` verifies the hypotheses of the accepted `thm:global-product-torus` (R-4C2E4AC7) from R-EC25334D (analyticity into `ℓ¹`), R-950BFB30 (nonnegativity, mass sum), R-0191D778 (properness), R-507DD869 (involution `{I_n,I_j}=0`) and R-C95830E3 (`2π` periods); `RF535Hyp` assembles `D01LocalPrimitive.Hyp (L2T L)` (R-701613DA's printed hypotheses 1-4), proving the printed `C_H`-invariance of every action by the accepted Hilbert analytic identity theorem and using LOCAL-023 as the entire-ball local chart; the accepted `Ext025A4D01Discharge.global_D01_reconstruction` gives flow, `Φ`, `Ψ`, formulas, actions, symplecticity, surjectivity; `RF535Chart` proves, from full symplecticity, the intertwining with coordinate rotations on the whole product torus, the fibre/torus identification and the orbit periods.

Fidelity notes.  (1) `Φloc` is quantified as any chart satisfying the LOCAL-023 conclusion (and its existence is part of the theorem); by the uniqueness clause (j) of LOCAL-023 it is the unique canonical chart.  (2) The printed "independent of `T`" is the universally quantified formula for every admissible `T`.  (3) "`ι_Y ω = ᾱ`" is `ω(Y u, h) = ᾱ_u(h)` with `ω(h,k) = 2 Im⟨h,k⟩` (DEF-015 convention of the product-torus source).  (4) The final "for clarity" derivative bounds `‖DΦ(u)‖ ≤ e^{T/2} e^{TB} ‖DΦloc(w)‖` of the printed proof are explanatory and are not clauses of the printed statement; they are not formalized.  (5) `Φ`, `Ψ` are the accepted D01 objects `Phi S`, `Psi S` for the constructed `S = actualHyp`; the statement existentially quantifies them with all defining properties.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology ENNReal
open Filter Set Metric MeasureTheory BoundedContinuousFunction

namespace QuantumNLS.RF535Final

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.ResetMoser QuantumNLS.ResetMoserClamp
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Fourier (fourierL2 modeLp)
open QuantumNLS.Local021 QuantumNLS.Local021R QuantumNLS.Local023
open QuantumNLS.LocalSpectral (pm)
open QuantumNLS.RootIndexedMasses (masses)
open QuantumNLS.ResetNormalizationUniqueness (IsStronglySymplecticOn Cphys)
open QuantumNLS.ActionTorus (PosL1 actionTorus rotate)
open QuantumNLS.ProductTorusGenerator (Linf)
open QuantumNLS.Ext025B6TorusCoordinates (Torus)

variable {L κ : ℝ} [Fact (0 < L)]

/-- The conclusion of LOCAL-023 `thm:reset-open-transform` (verbatim body of `Local023.reset_open_transform`):
the local canonical maps `Φ_{κ,loc} = Φ κ`, `Φ_{κ,loc}^{-1} = Ψ κ` on the entire balls of radius `δ = d/√κ`. -/
def Local023Body (L : ℝ) [Fact (0 < L)] (d CL : ℝ) (Φ : ℝ → L2T L → K) (Ψ : ℝ → K → L2T L) : Prop :=
      (∀ (κ : ℝ) (hκ : 0 < κ),
        -- (a) `Φ_κ : B_δ(L²) → B_δ(ℓ²)` is a real-analytic diffeomorphism, `δ = d/√κ`
        AnalyticOnNhd ℝ (Φ κ) (ball (0 : L2T L) (d / Real.sqrt κ)) ∧
        AnalyticOnNhd ℝ (Ψ κ) (ball (0 : K) (d / Real.sqrt κ)) ∧
        MapsTo (Φ κ) (ball (0 : L2T L) (d / Real.sqrt κ)) (ball (0 : K) (d / Real.sqrt κ)) ∧
        MapsTo (Ψ κ) (ball (0 : K) (d / Real.sqrt κ)) (ball (0 : L2T L) (d / Real.sqrt κ)) ∧
        (∀ u ∈ ball (0 : L2T L) (d / Real.sqrt κ), Ψ κ (Φ κ u) = u) ∧
        (∀ y ∈ ball (0 : K) (d / Real.sqrt κ), Φ κ (Ψ κ y) = y) ∧
        -- (b) the procedure: the LOCAL-020 families exist at coupling `κ`; on each of them the constructed LOCAL-017/LOCAL-021 data have all printed
        --     properties and `Φ = S⁻¹ ∘ ζ` of the procedure equals `Φ_κ` on the common domain
        (∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, 0 ≤ C ∧
          ∃ (a : ℤ → L2T L → ℝ) (b : ℤ → L2T L → ℂ) (rr : L2T L → (ℤ →ᵇ ℝ)),
            Fam020 L κ (Real.pi / L) ρ C hκ a b rr) ∧
        (∀ (ρ C : ℝ) (a : ℤ → L2T L → ℝ) (b : ℤ → L2T L → ℂ) (rr : L2T L → (ℤ →ᵇ ℝ)),
          0 < ρ → 0 ≤ C → Fam020 L κ (Real.pi / L) ρ C hκ a b rr →
          ∃ S : Setting L κ (Real.pi / L) hκ, S.ρ = ρ ∧ S.C = C ∧ S.a = a ∧ S.b = b ∧ S.rr = rr ∧
            SettingProps S ∧
            ∀ u : L2T L, ‖u‖ < S.rM → Real.sqrt κ * ‖u‖ < d → S.Phi u = Φ κ u) ∧
        -- (c) `|Φ_κ(u)_n|² = I_n^{(κ)}(u)`
        (∀ u ∈ ball (0 : L2T L) (d / Real.sqrt κ), ∀ n : ℤ, ‖Φ κ u n‖ ^ 2 = (masses hκ u).1 n) ∧
        -- (d) `‖Φ_κ(u)‖² = ‖u‖²`
        (∀ u ∈ ball (0 : L2T L) (d / Real.sqrt κ), ‖Φ κ u‖ ^ 2 = ‖u‖ ^ 2) ∧
        -- (e) `DΦ_κ(0) = 𝓕`
        (∀ h : L2T L, fderiv ℝ (Φ κ) 0 h = fourierL2 L h) ∧
        -- (f) `2 Im ⟨DΦ_κ(u)h, DΦ_κ(u)k⟩ = 2 Im ⟨h, k⟩`
        (∀ u ∈ ball (0 : L2T L) (d / Real.sqrt κ), ∀ h k : L2T L,
          2 * (inner ℂ (fderiv ℝ (Φ κ) u h) (fderiv ℝ (Φ κ) u k)).im = 2 * (inner ℂ h k).im) ∧
        -- (g) bounded invertible differentials, with `D(Φ_κ⁻¹)(Φ_κ(u))` the inverse, and the printed quadratic bound
        (∀ u ∈ ball (0 : L2T L) (d / Real.sqrt κ), ∃ e : L2T L ≃L[ℝ] K,
          ⇑e = ⇑(fderiv ℝ (Φ κ) u) ∧ HasFDerivAt (Ψ κ) (e.symm : K →L[ℝ] L2T L) (Φ κ u) ∧
          ‖fderiv ℝ (Φ κ) u - Setting.Fcl L‖ +
            ‖(e.symm : K →L[ℝ] L2T L) - ((Setting.Fcle L).symm : K →L[ℝ] L2T L)‖ ≤ CL * κ * ‖u‖ ^ 2) ∧
        -- (h) Fourier covariances: translations, integral boosts, reflection, conjugation, common phase, conjugation-reflection
        (∀ u ∈ ball (0 : L2T L) (d / Real.sqrt κ), ∀ n : ℤ,
          (∀ y : ℝ, Φ κ (QuantumNLS.BornTranslation.trans y u) n =
            Complex.exp (Complex.I * ((pm L n : ℝ) : ℂ) * (y : ℂ)) * Φ κ u n) ∧
          (∀ k : ℤ, Φ κ (QuantumNLS.RootMassBoostSymbol.boost k u) n = Φ κ u (n - k)) ∧
          Φ κ (QuantumNLS.ResetNormalizationUniqueness.reflectR L u) n = Φ κ u (-n) ∧
          Φ κ (star u) n = conj (Φ κ u (-n)) ∧
          (∀ φ : ℝ, Φ κ (Complex.exp ((φ : ℂ) * Complex.I) • u) n =
            Complex.exp ((φ : ℂ) * Complex.I) * Φ κ u n) ∧
          Φ κ (Cphys L u) n = conj (Φ κ u n)) ∧
        -- (i) `Φ_κ` is the ordinary Fourier transform on every Fourier plane
        (∀ (k : ℤ) (c : ℂ), ‖c‖ < d / Real.sqrt κ →
          Φ κ (c • modeLp L k) = fourierL2 L (c • modeLp L k)) ∧
        -- (j) uniqueness among canonical exact-modulus charts on a common ball, by `DΦ(0) = 𝓕` and `Φ(conj u(−·)) = conj Φ(u)`
        (∀ r0 : ℝ, 0 < r0 → r0 ≤ d / Real.sqrt κ → ∀ Ψ' : L2T L → K,
          IsStronglySymplecticOn (ball (0 : L2T L) r0) (ball (0 : K) r0) Ψ' →
          AnalyticOnNhd ℝ Ψ' (ball (0 : L2T L) r0) →
          (∀ u ∈ ball (0 : L2T L) r0, ∀ n : ℤ, ‖Ψ' u n‖ ^ 2 = (masses hκ u).1 n) →
          (∀ h : L2T L, fderiv ℝ Ψ' 0 h = fourierL2 L h) →
          (∀ u ∈ ball (0 : L2T L) r0, Ψ' (Cphys L u) = star (Ψ' u)) →
          ∀ u ∈ ball (0 : L2T L) r0, Ψ' u = Φ κ u)) ∧
      -- (k) scaling `Φ_κ(su) = sΦ_{κs²}(u)`
      (∀ (κ : ℝ), 0 < κ → ∀ s : ℝ, 0 < s → ∀ u : L2T L, ‖u‖ < d / Real.sqrt (κ * s ^ 2) →
        Φ κ (s • u) = s • Φ (κ * s ^ 2) u) ∧
      -- (l) the full `C¹` Fourier limit as `κ ↓ 0` on every fixed bounded `L²` ball
      (∀ ρ0 : ℝ, 0 < ρ0 → ∀ ε : ℝ, 0 < ε → ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ < κ0 →
        ∀ u : L2T L, ‖u‖ < ρ0 → ‖u‖ < d / Real.sqrt κ ∧
          ‖Φ κ u - Setting.Fcl L u‖ ≤ ε ∧ ‖fderiv ℝ (Φ κ) u - Setting.Fcl L‖ ≤ ε)

/-- The accepted LOCAL-023 theorem, restated through `Local023Body`. -/
theorem local023 (L : ℝ) [Fact (0 < L)] :
    ∃ d CL : ℝ, 0 < d ∧ 0 ≤ CL ∧ ∃ (Φ : ℝ → L2T L → K) (Ψ : ℝ → K → L2T L), Local023Body L d CL Φ Ψ :=
  QuantumNLS.Local023.reset_open_transform L

/-- The part of the LOCAL-023 conclusion that feeds the global reconstruction. -/
theorem localData {d CL : ℝ} {Φ : ℝ → L2T L → K} {Ψ : ℝ → K → L2T L} (hd : 0 < d)
    (h : Local023Body L d CL Φ Ψ) {κ : ℝ} (hκ : 0 < κ) :
    QuantumNLS.RF535Hyp.LocalData L κ hκ d (Φ κ) (Ψ κ) := by
  obtain ⟨hall, -, -⟩ := h
  obtain ⟨a1, a2, a3, a4, a5, a6, -, -, c, -, -, f, -, hh, -, -⟩ := hall κ hκ
  exact ⟨hd, a1, a2, a3, a4, a5, a6, c, f, fun u hu n => (hh u hu n).2.2.2.2.2⟩

/-! ## The actual objects -/

/-- `I^{(κ)} = (I_n^{(κ)})_n` as a map `L² → ℓ¹`. -/
abbrev Iact (hκ : 0 < κ) : L2T L → lp (fun _ : ℤ => ℝ) 1 := QuantumNLS.RF535Bridge.Iact hκ

/-- The product-torus action `T_ψ`, `ψ ∈ 𝕋^ℤ = ℤ → Circle`, of `thm:global-product-torus`. -/
abbrev Tact (hκ : 0 < κ) : Torus → L2T L → L2T L :=
  QuantumNLS.ProductTorusAction.act (fderiv ℝ (Iact (L := L) hκ))

/-- The bounded-angle Hamiltonian `H_θ(u) = Σ_n θ_n I_n^{(κ)}(u)`. -/
def Hθ (hκ : 0 < κ) (θ : Linf) (u : L2T L) : ℝ := ∑' n, θ n * (Iact (L := L) hκ u : ℤ → ℝ) n

/-- `T_θ`: the time-one map of the complete flow of `X_{H_θ}`. -/
abbrev Tθ (hκ : 0 < κ) (θ : Linf) : L2T L → L2T L :=
  QuantumNLS.ProductTorusFlow.T (fderiv ℝ (Iact (L := L) hκ)) θ

/-- The averaged physical primitive `ᾱ_u(h) = ∫_{𝕋^ℤ} Im⟨T_θ u, DT_θ(u) h⟩ dθ` (normalized product Haar measure). -/
def avgPrimitive (hκ : 0 < κ) (u h : L2T L) : ℝ :=
  ∫ ψ : Torus, (inner ℂ (Tact (L := L) hκ ψ u) (fderiv ℝ (Tact (L := L) hκ ψ) u h)).im
    ∂QuantumNLS.Ext025BHaar.productCircleHaar

/-- **The printed conclusions of `thm:global-actual-chart`** for the actual objects at coupling `κ`, given the
local canonical chart `Φ_{κ,loc} = Φl`, `Φ_{κ,loc}^{-1} = Ψl` on `B_{d/√κ}`. -/
def GlobalStatement (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (d : ℝ) (Φl : L2T L → K) (Ψl : K → L2T L) : Prop :=
  -- the complete bounded-angle Hamiltonians `H_θ` define the product-torus action `T_θ`
  ((∀ (θ : Linf) (u : L2T L), ∃ γ : ℝ → L2T L, γ 0 = u ∧
      (∀ t, HasDerivAt γ (hamField (Hθ (L := L) hκ θ) (γ t)) t) ∧
      (∀ γ' : ℝ → L2T L, γ' 0 = u → (∀ t, HasDerivAt γ' (hamField (Hθ (L := L) hκ θ) (γ' t)) t) → γ' = γ) ∧
      γ 1 = Tθ (L := L) hκ θ u) ∧
    (∀ (θ : Linf) (u : L2T L), Tact (L := L) hκ (fun n => Circle.exp (θ n)) u = Tθ (L := L) hκ θ u) ∧
    (∀ (ψ ψ' : Torus) (u : L2T L), Tact (L := L) hκ (ψ * ψ') u = Tact hκ ψ (Tact hκ ψ' u)) ∧
    (∀ u : L2T L, Tact (L := L) hκ 1 u = u) ∧
    Continuous (fun p : Torus × L2T L => Tact (L := L) hκ p.1 p.2) ∧
    -- the `n`th circle is the complete Hamiltonian flow of the indexed action `I_n` (`X_{I_n} = -i ∇ I_n`)
    (∀ (n : ℤ) (u : L2T L) (t : ℝ),
      HasDerivAt (fun s : ℝ => Tact (L := L) hκ (Pi.mulSingle n (Circle.exp s)) u)
        (hamField (fun v => (Iact (L := L) hκ v : ℤ → ℝ) n) (Tact (L := L) hκ (Pi.mulSingle n (Circle.exp t)) u)) t)) ∧
  ∃ (Y : L2T L → L2T L) (F : ℝ → L2T L → L2T L) (Φ : L2T L → K) (Ψ : K → L2T L),
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
    (∀ (ψ : Torus) (u : L2T L), Φ (Tact (L := L) hκ ψ u) = rotate ψ⁻¹ (Φ u)) ∧
    (∀ (θ : Linf) (u : L2T L) (n : ℤ),
      Φ (Tθ (L := L) hκ θ u) n = Complex.exp (-(θ n : ℂ) * Complex.I) * Φ u n) ∧
    -- individual orbits: least positive period `2π` for a positive action, fixed for a zero action
    (∀ (n : ℤ) (u : L2T L), 0 < (masses hκ u).1 n →
      Tact (L := L) hκ (Pi.mulSingle n (Circle.exp (2 * Real.pi))) u = u ∧
      ∀ t : ℝ, 0 < t → t < 2 * Real.pi → Tact (L := L) hκ (Pi.mulSingle n (Circle.exp t)) u ≠ u) ∧
    (∀ (n : ℤ) (u : L2T L), (masses hκ u).1 n = 0 →
      ∀ t : ℝ, Tact (L := L) hκ (Pi.mulSingle n (Circle.exp t)) u = u)


/-! ## Proof of the per-coupling statement -/

section Generic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem X_eq_hamField {I : E → lp (fun _ : ℤ => ℝ) 1} (hI : Differentiable ℝ I) (θ : Linf) (u : E) :
    QuantumNLS.ProductTorusGenerator.X (fderiv ℝ I) θ u =
      hamField (fun v => QuantumNLS.ProductTorusGenerator.pair θ (I v)) u := by
  unfold QuantumNLS.ProductTorusGenerator.X
  have h := (QuantumNLS.ProductTorusGenerator.pair θ).hasFDerivAt.comp u (hI u).hasFDerivAt
  rw [← QuantumNLS.RF535Bridge.Winv_fderiv]
  exact congrArg QuantumNLS.ProductTorusGenerator.Winv h.fderiv.symm

end Generic

theorem global_of_localData (hκ : 0 < κ) {d : ℝ} {Φl : L2T L → K} {Ψl : K → L2T L}
    (hl : QuantumNLS.RF535Hyp.LocalData L κ hκ d Φl Ψl) : GlobalStatement L κ hκ d Φl Ψl := by
  have hdiff : Differentiable ℝ (QuantumNLS.RF535Bridge.Iact (L := L) hκ) :=
    fun u => (QuantumNLS.RF535Bridge.hI hκ u (mem_univ u)).differentiableAt
  have hX : ∀ (θ : Linf) (v : L2T L),
      QuantumNLS.ProductTorusGenerator.X (fderiv ℝ (Iact (L := L) hκ)) θ v = hamField (Hθ (L := L) hκ θ) v :=
    fun θ v => X_eq_hamField hdiff θ v
  set S := QuantumNLS.RF535Hyp.actualHyp hκ hl with hS
  have D := QuantumNLS.Ext025A4D01Discharge.global_D01_reconstruction S
  obtain ⟨⟨hF0, hFd, hFan, hFact, hFnorm, hFsymp, hFabar⟩, ⟨hΦan, hΦsymp, hΦform, hΦball⟩,
    ⟨hΨan, hΨform, hΨΦ, hΦΨ⟩, ⟨hq, hnorm, hsymp, hα⟩, hsurj, hinvd⟩ := D
  have hΦ : QuantumNLS.RF535Chart.PhiData S (QuantumNLS.D01Reconstruction.Phi S) :=
    { diff := fun u => (hΦan u).differentiableAt
      mass := hq
      symp := hsymp
      surj := fun u w => ⟨fderiv ℝ (QuantumNLS.D01Reconstruction.Psi S) (QuantumNLS.D01Reconstruction.Phi S u) w,
        congrArg (fun T => T w) (hinvd u).2⟩ }
  have hrho : ∀ (n : ℤ) (t : ℝ) (u : L2T L),
      Tact (L := L) hκ (Pi.mulSingle n (Circle.exp t)) u = S.rho (Pi.single n (t : Real.Angle)) u := by
    intro n t u
    show _ = Tact (L := L) hκ (QuantumNLS.RF535Hyp.tc (Pi.single n (t : Real.Angle))) u
    rw [QuantumNLS.RF535Hyp.tc_single]
  have htc : ∀ ψ : Torus, QuantumNLS.RF535Hyp.tc (fun n => ((Complex.arg (ψ n : ℂ) : ℝ) : Real.Angle)) = ψ := by
    intro ψ
    funext n
    simp [QuantumNLS.RF535Hyp.tc, Circle.exp_arg]
  have hint : ∀ (ψ : Torus) (u : L2T L),
      QuantumNLS.D01Reconstruction.Phi S (Tact (L := L) hκ ψ u) = rotate ψ⁻¹ (QuantumNLS.D01Reconstruction.Phi S u) := by
    intro ψ u
    have h1 : Tact (L := L) hκ ψ u = S.rho (fun n => ((Complex.arg (ψ n : ℂ) : ℝ) : Real.Angle)) u := by
      show _ = Tact (L := L) hκ (QuantumNLS.RF535Hyp.tc (fun n => ((Complex.arg (ψ n : ℂ) : ℝ) : Real.Angle))) u
      rw [htc]
    rw [h1, QuantumNLS.RF535Chart.Phi_rho S hΦ]
    refine lp.ext (funext fun n => ?_)
    rw [Rot_apply, QuantumNLS.ActionTorus.rotate_apply]
    congr 1
    have h2 : (((-((Complex.arg (ψ n : ℂ) : ℝ) : Real.Angle)).toCircle : Circle) : ℂ) = (((ψ n)⁻¹ : Circle) : ℂ) := by
      rw [Real.Angle.toCircle_neg, Real.Angle.toCircle_coe, Circle.exp_arg]
    exact h2
  refine ⟨⟨fun θ u => ⟨fun t => QuantumNLS.ProductTorusFlow.flow (fderiv ℝ (Iact (L := L) hκ)) θ t u,
      QuantumNLS.ProductTorusFlow.flow_zero (QuantumNLS.RF535Bridge.flowHyp hκ) θ u,
      fun t => (QuantumNLS.ProductTorusFlow.hasDerivAt_flow (QuantumNLS.RF535Bridge.flowHyp hκ) θ u t).congr_deriv
        (hX θ _), fun γ' h0 hd => funext fun t =>
        (QuantumNLS.ProductTorusFlow.flow_eq_of_sol (QuantumNLS.RF535Bridge.flowHyp hκ) θ h0
          (fun t => (hd t).congr_deriv (hX θ _).symm) t).symm, rfl⟩,
    fun θ u => QuantumNLS.ProductTorusAction.act_exp (QuantumNLS.RF535Bridge.phyp hκ).hyp
      (QuantumNLS.RF535Bridge.hpos hκ) (QuantumNLS.RF535Bridge.hprop hκ) (QuantumNLS.RF535Bridge.hper hκ) θ u,
    fun ψ ψ' u => QuantumNLS.ProductTorusAction.act_mul (QuantumNLS.RF535Bridge.phyp hκ).hyp
      (QuantumNLS.RF535Bridge.hpos hκ) (QuantumNLS.RF535Bridge.hprop hκ) (QuantumNLS.RF535Bridge.hper hκ) ψ ψ' u,
    fun u => QuantumNLS.ProductTorusAction.act_one (QuantumNLS.RF535Bridge.phyp hκ).hyp
      (QuantumNLS.RF535Bridge.hpos hκ) (QuantumNLS.RF535Bridge.hprop hκ) (QuantumNLS.RF535Bridge.hper hκ) u,
    QuantumNLS.ProductTorusAction.act_continuous (QuantumNLS.RF535Bridge.phyp hκ).hyp
      (QuantumNLS.RF535Bridge.hpos hκ) (QuantumNLS.RF535Bridge.hprop hκ) (QuantumNLS.RF535Bridge.hper hκ), ?_⟩, ?_⟩
  · intro n u t
    have h := S.rho_flow n u t
    have e : (fun s : ℝ => S.rho (Pi.single n (s : Real.Angle)) u) =
        fun s => Tact (L := L) hκ (Pi.mulSingle n (Circle.exp s)) u := funext fun s => (hrho n s u).symm
    rw [e, ← hrho] at h
    exact h
  refine ⟨fun u => S.Y u, QuantumNLS.TerraMultiRound18Flow.flow S, QuantumNLS.D01Reconstruction.Phi S,
    QuantumNLS.D01Reconstruction.Psi S, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro u h
    exact omega_Winv (S.abar u) h
  · intro u v hv
    exact Winv_unique (S.abar u) v hv
  · exact fun u => (QuantumNLS.TerraMultiRound18Flow.flow_spec S u).1
  · exact fun u t => (QuantumNLS.TerraMultiRound18Flow.flow_spec S u).2 t
  · exact fun u γ h0 hd t => QuantumNLS.TerraMultiRound18Flow.flow_eq_of_sol S h0 hd t
  · exact fun u T hT hlt => hΦform u T hT hlt
  · exact fun z T hT hlt => hΨform z T hT hlt
  · exact hΦan
  · exact hΨan
  · exact hΨΦ
  · exact hΦΨ
  · exact fun u n => hq u n
  · intro u
    rw [hnorm u]
  · exact hsymp
  · intro u
    obtain ⟨h1, h2⟩ := hinvd u
    refine ⟨ContinuousLinearEquiv.equivOfInverse (fderiv ℝ (QuantumNLS.D01Reconstruction.Phi S) u)
      (fderiv ℝ (QuantumNLS.D01Reconstruction.Psi S) (QuantumNLS.D01Reconstruction.Phi S u))
      (fun x => congrArg (fun T => T x) h1)
      (fun y => congrArg (fun T => T y) h2), ?_, ?_⟩
    · exact ((hΦan u).differentiableAt).hasFDerivAt
    · exact ((hΨan _).differentiableAt).hasFDerivAt
  · exact fun u hu => hΦball u hu
  · intro z hz
    have h1 : Ψl z ∈ ball (0 : L2T L) (d / Real.sqrt κ) := hl.mapsΨ hz
    have h2 : QuantumNLS.D01Reconstruction.Phi S (Ψl z) = z := by
      rw [hΦball _ h1]
      exact hl.ΦΨ z hz
    calc QuantumNLS.D01Reconstruction.Psi S z
        = QuantumNLS.D01Reconstruction.Psi S (QuantumNLS.D01Reconstruction.Phi S (Ψl z)) := by rw [h2]
      _ = Ψl z := hΨΦ _
  · intro a
    obtain ⟨u, hu⟩ := hsurj a.1 a.2
    exact ⟨u, Subtype.ext hu⟩
  · intro a
    have e : {u : L2T L | masses hκ u = a} = {u | S.act u = a.1} := by
      ext u
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [e]
    exact QuantumNLS.RF535Chart.fibre_image S hΦΨ hq a.1
  · exact hint
  · intro θ u n
    have h1 := hint (fun n => Circle.exp (θ n)) u
    have h2 : Tθ (L := L) hκ θ u = Tact (L := L) hκ (fun n => Circle.exp (θ n)) u :=
      (QuantumNLS.ProductTorusAction.act_exp (QuantumNLS.RF535Bridge.phyp hκ).hyp
        (QuantumNLS.RF535Bridge.hpos hκ) (QuantumNLS.RF535Bridge.hprop hκ) (QuantumNLS.RF535Bridge.hper hκ) θ u).symm
    rw [h2, h1, QuantumNLS.ActionTorus.rotate_apply]
    congr 1
    rw [Pi.inv_apply, Circle.coe_inv_eq_conj, Circle.coe_exp, ← Complex.exp_conj]
    simp
  · intro n u hu
    refine ⟨?_, fun t ht0 ht1 hEq => ?_⟩
    · rw [hrho]
      exact (QuantumNLS.RF535Chart.orbit_positive S hΦ hΨΦ n u hu (2 * Real.pi)).2 ⟨1, by simp⟩
    · rw [hrho] at hEq
      obtain ⟨k, hk⟩ := (QuantumNLS.RF535Chart.orbit_positive S hΦ hΨΦ n u hu t).1 hEq
      have hpi := Real.pi_pos
      rcases le_or_gt k 0 with hk0 | hk0
      · have : (k : ℝ) ≤ 0 := by exact_mod_cast hk0
        nlinarith
      · have : (1 : ℝ) ≤ k := by exact_mod_cast hk0
        nlinarith
  · intro n u hu t
    rw [hrho]
    exact QuantumNLS.RF535Chart.orbit_zero S hΦ hΨΦ n u hu t


/-- **Theorem `thm:global-actual-chart`** (R-F5355ABD, `actual_chart.tex:15`), global canonical reconstruction
for the actual quantum actions.  Only `L > 0`. -/
theorem global_actual_chart (L : ℝ) [Fact (0 < L)] :
    (∃ d CL : ℝ, 0 < d ∧ 0 ≤ CL ∧ ∃ (Φloc : ℝ → L2T L → K) (Ψloc : ℝ → K → L2T L), Local023Body L d CL Φloc Ψloc) ∧
    ∀ (d CL : ℝ) (Φloc : ℝ → L2T L → K) (Ψloc : ℝ → K → L2T L), 0 < d → 0 ≤ CL →
      Local023Body L d CL Φloc Ψloc →
      ∀ (κ : ℝ) (hκ : 0 < κ), GlobalStatement L κ hκ d (Φloc κ) (Ψloc κ) :=
  ⟨local023 L, fun _ _ _ _ hd _ h _ hκ => global_of_localData hκ (localData hd h hκ)⟩

end QuantumNLS.RF535Final

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.RF535Final.global_actual_chart
#print axioms QuantumNLS.RF535Final.global_of_localData
#print axioms QuantumNLS.RF535Final.local023
#print axioms QuantumNLS.RF535Final.localData
