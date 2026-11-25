import Mathlib
import QuantumNLS.RapidityTransport
import QuantumNLS.QuantileTransport

/-!
# DEF-052: quadratic bulk-response form

Source: `DEFINITIONS_LEDGER.md:1272` (DEF-052), canonical occurrence `chapters/root_response/F03.tex`,
label `CC:F03:limit-form` (with `CC:F03:section`, `CC:F03:core`, `CC:F03:limit-equation`).  Ledger text: "Let `Q` be the
increasing quantile of the limiting probability measure.  The form is
`L∫FH + κ∬(F(t)−F(s))(H(t)−H(s))/(Q(t)−Q(s))² dt ds` on the real `L²(0,1)` functions of finite form energy.
The response solves this form equation with right-hand side `∫QH` for every test in the form domain.  The
finite-second-moment and density assumptions, treatment of zero denominators, and core are exactly those in
Section `CC:F03:section`."

## What is realized (definitions only; no theorem conclusions)
Prerequisites used read-only: DEF-012 `RapidityTransport.HasFiniteMoment` (finite `p`-th moment, `p = 2`), and the
realized increasing quantile `QuantileTransport.quantile σ s = inf{x : σ(-∞,x] ≥ s}`.  The limiting measure
`μ_{κ,u}` of DEF-010 is **not** realized in the repository (DEF-010 only names it): it is the explicit parameter `μ`.

* `unitInterval = volume.restrict (0,1)` and `L2Unit = Lp ℝ 2 unitInterval`: the real `L²(0,1)`.
* `CoreDensity μ` (the density assumptions of `CC:F03:core`): `μ = ρ dx`, `ρ` bounded, continuous and nonnegative; the
  positive set `{ρ>0}` is a union of pairwise disjoint bounded open intervals `(a_i,b_i)` with locally finite endpoint
  set; `ρ` is smooth on every such interval; at every endpoint `e` there is a neighbourhood on which only one side
  of `e` carries positive density and `ρ(x) ≤ C_e |x−e|^{1/2}`.
* `BulkMeasure μ` (the standing assumptions of the section): `μ` is a probability measure without atoms, of finite
  second moment (DEF-012), satisfying `CoreDensity`.
* `bulkQuantile μ = QuantileTransport.quantile μ`, the increasing quantile `Q` on `(0,1)`.
* **Zero denominators**: the difference quotient `quot Q F t s = (F t − F s)/(Q t − Q s)` is Lean's real division, so
  it is `0` on `{Q t = Q s}`, as in "the value on the diagonal is immaterial".  (The section shows, for atomless `μ`,
  that this set is a null set; that is a theorem and is not asserted here.)
* `formEnergy Q F = ∬ |quot Q F t s|² dt ds ∈ [0,∞]` (`CC:F03:limit-form`) and the form domain
  `formDomain Q = {F ∈ L²(0,1) : formEnergy Q F < ∞}`.
* `bulkForm L κ Q F H = L ∫FH + κ ∬ (F(t)−F(s))(H(t)−H(s))/(Q(t)−Q(s))² dt ds` (the printed form).
* `IsBulkResponse L κ Q W`: `W ∈ formDomain` and `bulkForm L κ Q W H = ∫ Q H` for every `H ∈ formDomain`
  (`CC:F03:limit-equation`).  Existence and uniqueness of such `W` (Riesz) are theorems of the section and are not
  stated here.
* `IsFormCore L κ Q S`: the subspace/family `S ⊆ L²(0,1)` is a core, i.e. dense in the form domain for the form norm
  `(L‖F‖² + κ·formEnergy F)^{1/2}`; `IsSmoothQuantilePullback Q F` the family `h∘Q`, `h ∈ C_c^∞(ℝ;ℝ)`, that
  `CC:F03:core` takes as the core (pull-back of `C_c^∞(ℝ;ℝ)` under the quantile map).  That it is a core is the
  content of `CC:F03:core` and is not asserted.
* `BulkResponseData`: bundles `L, κ > 0` and a limiting measure with the standing assumptions (`BulkMeasure`);
  `BulkResponseData.Q`, `BulkResponseData.IsResponse` are its quantile and its form equation.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace QuantumNLS.BulkResponseForm

/-! ### The real `L²(0,1)` -/

/-- Lebesgue measure on `(0,1)`. -/
def unitInterval : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)

/-- The real Hilbert space `L²(0,1)`. -/
abbrev L2Unit : Type := Lp ℝ 2 unitInterval

/-! ### The standing assumptions on the limiting measure -/

/-- The density assumptions of `CC:F03:core`. -/
structure CoreDensity (μ : Measure ℝ) : Prop where
  /-- `μ = ρ dx` with `ρ` bounded, continuous and nonnegative. -/
  exists_density : ∃ ρ : ℝ → ℝ, Continuous ρ ∧ (∀ x, 0 ≤ ρ x) ∧ (∃ C : ℝ, ∀ x, ρ x ≤ C) ∧
    μ = volume.withDensity (fun x => ENNReal.ofReal (ρ x)) ∧
    -- positive set = disjoint union of bounded open intervals with locally finite endpoints
    (∃ (ι : Type) (a b : ι → ℝ), (∀ i, a i < b i) ∧
      {x | 0 < ρ x} = ⋃ i, Ioo (a i) (b i) ∧
      (∀ i j, i ≠ j → Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))) ∧
      (∀ x : ℝ, ∃ U ∈ 𝓝 x, (U ∩ (range a ∪ range b)).Finite) ∧
      -- ρ is smooth on every such interval (positive there by the union description)
      (∀ i, ContDiffOn ℝ ∞ ρ (Ioo (a i) (b i))) ∧
      -- at each endpoint: one-sided density and the square-root vanishing rate
      (∀ e ∈ range a ∪ range b, ∃ U ∈ 𝓝 e, ∃ C : ℝ,
        ((∀ x ∈ U, x < e → ρ x = 0) ∨ (∀ x ∈ U, e < x → ρ x = 0)) ∧
        ∀ x ∈ U, ρ x ≤ C * |x - e| ^ (1 / 2 : ℝ)))

/-- The standing assumptions of `CC:F03:section`: a probability measure without atoms, with finite second
moment (DEF-012), satisfying the density assumptions. -/
structure BulkMeasure (μ : Measure ℝ) : Prop where
  isProbability : IsProbabilityMeasure μ
  noAtoms : NullSingletonClass μ
  finiteSecondMoment : QuantumNLS.RapidityTransport.HasFiniteMoment 2 μ
  coreDensity : CoreDensity μ

/-- The increasing quantile `Q` of `μ` on `(0,1)`. -/
def bulkQuantile (μ : Measure ℝ) : ℝ → ℝ := QuantumNLS.QuantileTransport.quantile μ

/-! ### The form -/

/-- The difference quotient `(F(t) − F(s))/(Q(t) − Q(s))`; real division, so `0` where `Q t = Q s`. -/
def quot (Q F : ℝ → ℝ) (t s : ℝ) : ℝ := (F t - F s) / (Q t - Q s)

/-- The form energy `𝓔(F) = ∬ |F(t)−F(s)|²/|Q(t)−Q(s)|² dt ds ∈ [0,∞]`. -/
def formEnergy (Q F : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ p : ℝ × ℝ, ENNReal.ofReal ((quot Q F p.1 p.2) ^ 2) ∂(unitInterval.prod unitInterval)

/-- The form domain: the real `L²(0,1)` functions of finite form energy. -/
def formDomain (Q : ℝ → ℝ) : Set L2Unit :=
  {F | formEnergy Q (F : ℝ → ℝ) < ⊤}

/-- The printed form `L∫FH + κ∬(F(t)−F(s))(H(t)−H(s))/(Q(t)−Q(s))² dt ds`. -/
def bulkForm (L κ : ℝ) (Q F H : ℝ → ℝ) : ℝ :=
  L * ∫ t, F t * H t ∂unitInterval +
    κ * ∫ p : ℝ × ℝ, quot Q F p.1 p.2 * quot Q H p.1 p.2 ∂(unitInterval.prod unitInterval)

/-- `W` is the response: `W` lies in the form domain and solves
`L⟨W,H⟩ + κ∬… = ⟨Q,H⟩` for every test `H` in the form domain (`CC:F03:limit-equation`). -/
def IsBulkResponse (L κ : ℝ) (Q : ℝ → ℝ) (W : L2Unit) : Prop :=
  W ∈ formDomain Q ∧
    ∀ H ∈ formDomain Q, bulkForm L κ Q (W : ℝ → ℝ) (H : ℝ → ℝ) = ∫ t, Q t * H t ∂unitInterval

/-- The pull-back `h ∘ Q`, `h ∈ C_c^∞(ℝ;ℝ)`, of the smooth compactly supported functions under the quantile map. -/
def IsSmoothQuantilePullback (Q : ℝ → ℝ) (F : L2Unit) : Prop :=
  ∃ h : ℝ → ℝ, ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧ (F : ℝ → ℝ) =ᵐ[unitInterval] h ∘ Q

/-- `S` is a core of the form on its domain: it is dense for the form norm
`(L‖F‖² + κ·𝓔(F))^{1/2}`. -/
def IsFormCore (L κ : ℝ) (Q : ℝ → ℝ) (S : Set L2Unit) : Prop :=
  S ⊆ formDomain Q ∧ ∀ F ∈ formDomain Q, ∀ ε : ℝ, 0 < ε → ∃ G ∈ S,
    ENNReal.ofReal (L * ‖F - G‖ ^ 2) + ENNReal.ofReal κ * formEnergy Q ((F - G : L2Unit) : ℝ → ℝ) <
      ENNReal.ofReal ε

/-- The standing data of DEF-052: `L, κ > 0`, a limiting measure with the standing assumptions, and its quantile. -/
structure BulkResponseData where
  L : ℝ
  κ : ℝ
  hL : 0 < L
  hκ : 0 < κ
  μ : Measure ℝ
  hμ : BulkMeasure μ

/-- The quantile `Q` of the data. -/
def BulkResponseData.Q (D : BulkResponseData) : ℝ → ℝ := bulkQuantile D.μ

/-- The response of the data (a solution of the form equation; none is asserted to exist). -/
def BulkResponseData.IsResponse (D : BulkResponseData) (W : L2Unit) : Prop :=
  IsBulkResponse D.L D.κ D.Q W

end QuantumNLS.BulkResponseForm

#print axioms QuantumNLS.BulkResponseForm.formEnergy
#print axioms QuantumNLS.BulkResponseForm.bulkForm
#print axioms QuantumNLS.BulkResponseForm.IsBulkResponse
#print axioms QuantumNLS.BulkResponseForm.IsFormCore
#print axioms QuantumNLS.BulkResponseForm.BulkResponseData.IsResponse
