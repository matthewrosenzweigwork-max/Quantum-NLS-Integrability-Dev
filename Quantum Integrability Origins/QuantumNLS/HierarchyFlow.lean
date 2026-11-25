import QuantumNLS.ClassicalCharges
import QuantumNLS.BetheSpectralCharges

/-!
# DEF-024: fixed smooth joint hierarchy flow

`DEFINITIONS_LEDGER.md` DEF-024 (`chapters/definitions.tex`, `def:report-24`):

"For a fixed finite set of nonnegative orders `𝓡`, the joint classical flow is the composition of
the Hamiltonian flows of `I_{r+1}^{(κ)}`, and the quantum flow is
`U_N(t) = exp(−i Σ_{r∈𝓡} t_r Q_{N,r})`. The correspondence tests a fixed smooth unit initial field
and a fixed compact box of times. Existence and commutation of the higher classical flows are proved
with finite loss."

Ambient: fixed smooth `u`; finite `𝓡`; compact joint-time box. Topology: smooth topology for
profiles; strong quantum unitaries. Convention: not a statement of rough-data higher hierarchy
well-posedness or of growing charge order.

Realization (definitions only; **no theorem conclusion** — existence and commutation of the higher
classical flows are NOT asserted):
* `hamiltonian L κ r u = Re I_{r+1}^{(κ)}(u)`, the DEF-022 charge (`ClassicalCharges.charge`, frozen
  `ca5e1365…`, read-only), as a real functional on smooth periodic profiles;
* `IsSmoothGradient`: the DEF-015 gradient convention `dF(u)[h] = 2 Re⟨∇F(u), h⟩` (inner product
  `∫_0^L \bar f g`, linear in the second slot), tested on smooth periodic directions;
* `IsHamFlow`: a Hamiltonian flow `Φ_s` of `F` on smooth periodic fields, `Φ_0 = id`,
  `∂_s Φ_s u = X_F(Φ_s u) = −i∇F(Φ_s u)`, jointly smooth in `(s, x)` (smooth topology);
* `HamFlows`: a family of Hamiltonian flows of `I_{r+1}^{(κ)}`, `r ∈ 𝓡`;
  `jointClassicalFlow`: their composition `Φ^{(r_1)}_{t_{r_1}} ∘ ⋯ ∘ Φ^{(r_k)}_{t_{r_k}}` over
  `𝓡 = {r_1 < ⋯ < r_k}`;
* `jointSymbol`, `jointGenerator`: `Σ_{r∈𝓡} t_r Q_{N,r}` as the DEF-008 spectral multiplier of the
  symbol `Σ_r t_r Λ_{N,r}(m)` on its maximal domain (DEF-008 polynomial-combination convention), with
  the DEF-008 charges `Q_{N,r}` of BCH1 (`BetheSpectralCharges.charge`, frozen `28c42244…`, read-only)
  in a supplied complete Bethe basis `b` (as DEF-007/DEF-008) at coupling `κ/N`;
  `quantumFlow`: `U_N(t) = exp(−i Σ_r t_r Q_{N,r})`, the BCH1 spectral unitary, defined on every
  vector (`quantumFlow_coord`: its coefficients are `e^{−iΣ_r t_r Λ_{N,r}(m)} ⟨Ψ_m, ψ⟩`);
* `TestData`: a fixed smooth unit initial field and a fixed compact box of times.
-/

set_option autoImplicit false
noncomputable section

open scoped ComplexConjugate InnerProductSpace ContDiff

namespace QuantumNLS.HierarchyFlow

open QuantumNLS.ClassicalCharges QuantumNLS.BetheSpectralCharges QuantumNLS.BetheCoefficientTransform
  QuantumNLS.BetheLabels

/-! ## 1. Classical side -/

/-- The `L²(𝕋_L)` pairing `⟨f, g⟩ = ∫_0^L \bar f g` (linear in the second slot, DEF-001/DEF-015). -/
def pair (L : ℝ) (f g : ℝ → ℂ) : ℂ := ∫ x in (0 : ℝ)..L, conj (f x) * g x

/-- The real functional `Re I_{r+1}^{(κ)}` (DEF-022) on smooth periodic profiles. -/
def hamiltonian (L κ : ℝ) (r : ℕ) (u : ℝ → ℂ) : ℝ := (ClassicalCharges.charge L κ u (r + 1)).re

/-- DEF-015 gradient on the smooth periodic class: `g` is smooth periodic and
`dF(u)[h] = d/dε F(u + εh)|_{ε=0} = 2 Re⟨g, h⟩` for every smooth periodic direction `h`. -/
def IsSmoothGradient (L : ℝ) (F : (ℝ → ℂ) → ℝ) (u g : ℝ → ℂ) : Prop :=
  SmoothPeriodic L g ∧ ∀ h : ℝ → ℂ, SmoothPeriodic L h →
    HasDerivAt (fun ε : ℝ => F (fun x => u x + (ε : ℂ) * h x)) (2 * (pair L g h).re) 0

/-- **Hamiltonian flow** of `F` on smooth periodic fields: `Φ_0 u = u`, `(s, x) ↦ Φ_s u (x)` is
jointly smooth, every `Φ_s u` is smooth periodic, and `∂_s Φ_s u = X_F(Φ_s u) = −i ∇F(Φ_s u)`. -/
def IsHamFlow (L : ℝ) (F : (ℝ → ℂ) → ℝ) (Φ : ℝ → (ℝ → ℂ) → (ℝ → ℂ)) : Prop :=
  ∀ u : ℝ → ℂ, SmoothPeriodic L u →
    Φ 0 u = u ∧ ContDiff ℝ ∞ (fun p : ℝ × ℝ => Φ p.1 u p.2) ∧
      ∀ s : ℝ, SmoothPeriodic L (Φ s u) ∧
        ∃ g : ℝ → ℂ, IsSmoothGradient L F (Φ s u) g ∧
          ∀ x : ℝ, HasDerivAt (fun s' => Φ s' u x) (-Complex.I * g x) s

/-- A family of Hamiltonian flows of the charges `I_{r+1}^{(κ)}`, `r ∈ 𝓡`. -/
structure HamFlows (L κ : ℝ) (𝓡 : Finset ℕ) where
  /-- `Φ r s` is the time-`s` map of the flow of `I_{r+1}^{(κ)}`. -/
  Φ : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ)
  ham : ∀ r ∈ 𝓡, IsHamFlow L (hamiltonian L κ r) (Φ r)

/-- **The joint classical flow**: the composition of the Hamiltonian flows of `I_{r+1}^{(κ)}`,
`r ∈ 𝓡` (in increasing order of `r`), at the joint time `t`. -/
def jointClassicalFlow {L κ : ℝ} {𝓡 : Finset ℕ} (F : HamFlows L κ 𝓡) (t : ℕ → ℝ) :
    (ℝ → ℂ) → (ℝ → ℂ) :=
  ((𝓡.sort (· ≤ ·)).map fun r => F.Φ r (t r)).foldr (· ∘ ·) id

/-! ## 2. Quantum side -/

variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- The joint symbol `Σ_{r∈𝓡} t_r Λ_{N,r}(m)` at coupling `κ/N`. -/
def jointSymbol (L : ℝ) (N : ℕ) (κ : ℝ) (𝓡 : Finset ℕ) (t : ℕ → ℝ) (m : MArr N) : ℝ :=
  ∑ r ∈ 𝓡, t r * eigenvalue L N (κ / N) r m

/-- `Σ_{r∈𝓡} t_r Q_{N,r}` on the maximal domain of its symbol (DEF-008). -/
def jointGenerator (b : BetheBasis L N) (κ : ℝ) (𝓡 : Finset ℕ) (t : ℕ → ℝ) :
    HN L N →ₗ.[ℂ] HN L N :=
  multiplier b (jointSymbol L N κ 𝓡 t)

/-- **The quantum flow** `U_N(t) = exp(−i Σ_{r∈𝓡} t_r Q_{N,r})` (a unitary on the whole space). -/
def quantumFlow (b : BetheBasis L N) (κ : ℝ) (𝓡 : Finset ℕ) (t : ℕ → ℝ) : HN L N ≃ₗᵢ[ℂ] HN L N :=
  evolution b (jointSymbol L N κ 𝓡 t) 1

/-- Unfolding: `⟨Ψ_m, U_N(t)ψ⟩ = e^{−i Σ_r t_r Λ_{N,r}(m)} ⟨Ψ_m, ψ⟩`. -/
theorem quantumFlow_coord (b : BetheBasis L N) (κ : ℝ) (𝓡 : Finset ℕ) (t : ℕ → ℝ) (ψ : HN L N)
    (m : MArr N) :
    ⟪b m, quantumFlow b κ 𝓡 t ψ⟫_ℂ =
      Complex.exp (-((∑ r ∈ 𝓡, t r * eigenvalue L N (κ / N) r m : ℝ) : ℂ) * Complex.I) *
        ⟪b m, ψ⟫_ℂ := by
  rw [quantumFlow, evolution_coord, DiagonalMultiplier.phase, one_mul, jointSymbol]

/-- The generator's symbol is the `t`-combination of the DEF-008 charge symbols `Λ_{N,r}`, the
eigenvalues of `Q_{N,r} = charge b (κ/N) r`. -/
theorem jointGenerator_eq (b : BetheBasis L N) (κ : ℝ) (𝓡 : Finset ℕ) (t : ℕ → ℝ) :
    jointGenerator b κ 𝓡 t = multiplier b (fun m => ∑ r ∈ 𝓡, t r * eigenvalue L N (κ / N) r m) :=
  rfl

/-! ## 3. The tested data -/

/-- A fixed smooth unit initial field and a fixed compact box of times for the orders `𝓡`. -/
structure TestData (L : ℝ) where
  /-- The finite set of nonnegative orders. -/
  𝓡 : Finset ℕ
  /-- The smooth initial field. -/
  u : ℝ → ℂ
  smooth : SmoothPeriodic L u
  /-- Unit `L²(𝕋_L)` norm (mass-`L` normalization). -/
  unit : ∫ x in (0 : ℝ)..L, ‖u x‖ ^ 2 = 1
  /-- The box half-widths. -/
  T : ℕ → ℝ
  T_nonneg : ∀ r, 0 ≤ T r

/-- The compact box of joint times `{t : |t_r| ≤ T_r (r ∈ 𝓡), t_r = 0 (r ∉ 𝓡)}`. -/
def TestData.box {L : ℝ} (D : TestData L) : Set (ℕ → ℝ) :=
  Set.pi Set.univ fun r => if r ∈ D.𝓡 then Set.Icc (-D.T r) (D.T r) else {0}

theorem TestData.isCompact_box {L : ℝ} (D : TestData L) : IsCompact D.box := by
  refine isCompact_univ_pi fun r => ?_
  by_cases hr : r ∈ D.𝓡
  · simp only [hr, ↓reduceIte]; exact isCompact_Icc
  · simp only [hr, ↓reduceIte]; exact isCompact_singleton

#print axioms quantumFlow_coord
#print axioms TestData.isCompact_box

end QuantumNLS.HierarchyFlow
