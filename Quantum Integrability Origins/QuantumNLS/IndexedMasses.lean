import Mathlib
import QuantumNLS.SpatialTransfer
import QuantumNLS.ResetNormalizationBinding

/-!
# DEF-014: indexed spectral masses and action sequences

Source: `DEFINITIONS_LEDGER.md:291` (DEF-014), `chapters/definitions.tex`, `def:report-14`.  Ledger text: the
separator `b_n(u)` is the unique real point where `Re γ_u = (n + 1/2)π`; the indexed mass is
`a_n(u) = M_{κ,u}((b_{n−1}, b_n))`; the construction chapters write `I_n^{(κ)}(u)` for the same object, and the
correspondence uses `a_n = |w_n|²`; these indexed masses are distinct from the Riccati charges `I_j^{(κ)}`.

## What is realized (parametrically in `M` and the boundary phase)
* `BoundaryPhase`: the real boundary function `φ = Re γ_u : ℝ → ℝ` together with exactly what makes the
  separator unique and existent: `φ` strictly monotone (hypothesis `strictMono`), continuous, and
  `φ → ±∞` at `±∞`.  *Uniqueness of `b_n` needs `Re γ_u` strictly monotone on `ℝ`; this is a hypothesis of the
  structure (a theorem of the quantum transfer limit in the source, not proved from the definition).*
  Where `M` permits, it is proved: `BoundaryPhase.ofLipschitz`: if `Re G_M` has boundary function `g` that is
  `K`-Lipschitz with `κ K < L/2`, then `φ(λ) = Lλ/2 − κ g(λ)` is a `BoundaryPhase` (strictly increasing with slope
  `≥ L/2 − κK`, continuous, `→ ±∞`).
* `separator P n` (`b_n`): the unique real point with `φ(b_n) = (n + 1/2)π` (`exists_unique_separator`,
  `separator_spec`, `separator_unique`); `separator_strictMono` (`b_{n−1} < b_n`).
* `indexedMass M P n = M (Ioo b_{n−1} b_n)` (`a_n`, in `ℝ≥0∞`) and `indexedMassReal` (finite `M`): pairwise
  disjoint intervals (`pairwiseDisjoint_Ioo`), nonnegative, `∑ a_n ≤ M(ℝ)` (`tsum_indexedMass_le`: a nonnegative
  `ℓ¹` sequence), `indexedMass_zero` (`M = 0 ⇒ a_n = 0`).
* `SelectedPhase L κ M`: a `BoundaryPhase` whose function is the real-part boundary value of DEF-013's
  `boundaryPhase L κ M z = Lz/2 − κ G_M(z)` as `Im z ↓ 0` (`IsBoundaryRealPart`).

## Binding target for LOCAL-022
The correspondence `a_n = |w_n|²` is recorded as `ChartMasses` (`‖Φ u n‖² = a_n(u)`), and
`reset_normalization_uniqueness_indexed` instantiates the abstract `q` of `reset_normalization_uniqueness_phys`
(`ResetNormalizationBinding`) with `q_n(u) = (indexedMass (Mfam u) (Pfam u) n).toReal`, closing binding (b) of
LOCAL-022 *relative to the parametric full-mass measures `Mfam u = M_{κ,u}` and phases `Pfam u`*: the measure
`M_{κ,u}` itself (DEF-010 limit) and the strict monotonicity of `Re γ_u` (a quantum-transfer-limit theorem) remain
parameters/hypotheses.  Not realized here: the construction of `M_{κ,u}` from `u`, and the Riccati charges.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace QuantumNLS.IndexedMasses

/-- The boundary function `φ = Re γ_u : ℝ → ℝ`, with the hypotheses that make the level sets single points. -/
structure BoundaryPhase where
  φ : ℝ → ℝ
  strictMono : StrictMono φ
  continuous : Continuous φ
  tendsto_atTop : Tendsto φ atTop atTop
  tendsto_atBot : Tendsto φ atBot atBot

/-- The level `(n + 1/2)π`. -/
def level (n : ℤ) : ℝ := ((n : ℝ) + 1 / 2) * Real.pi

namespace BoundaryPhase

variable (P : BoundaryPhase)

theorem surjective : Function.Surjective P.φ :=
  P.continuous.surjective P.tendsto_atTop P.tendsto_atBot

/-- **Existence and uniqueness of the separator `b_n`.** -/
theorem exists_unique_separator (n : ℤ) : ∃! b : ℝ, P.φ b = level n := by
  obtain ⟨b, hb⟩ := P.surjective (level n)
  exact ⟨b, hb, fun b' hb' => P.strictMono.injective (hb'.trans hb.symm)⟩

/-- The separator `b_n(u)`: the unique real point where `Re γ_u = (n + 1/2)π`. -/
def separator (n : ℤ) : ℝ := (P.exists_unique_separator n).exists.choose

theorem separator_spec (n : ℤ) : P.φ (P.separator n) = level n :=
  (P.exists_unique_separator n).exists.choose_spec

theorem separator_unique {n : ℤ} {b : ℝ} (hb : P.φ b = level n) : b = P.separator n :=
  (P.exists_unique_separator n).unique hb (P.separator_spec n)

theorem level_strictMono : StrictMono level := fun m n h => by
  unfold level
  have : (m : ℝ) < n := by exact_mod_cast h
  nlinarith [Real.pi_pos]

theorem separator_strictMono : StrictMono P.separator := fun m n h => by
  have := level_strictMono h
  rw [← P.separator_spec m, ← P.separator_spec n] at this
  exact P.strictMono.lt_iff_lt.mp this

/-- The indexed mass `a_n = M((b_{n−1}, b_n))`. -/
def indexedMass (M : Measure ℝ) (n : ℤ) : ℝ≥0∞ := M (Ioo (P.separator (n - 1)) (P.separator n))

/-- The real-valued indexed mass (for a finite measure). -/
def indexedMassReal (M : Measure ℝ) (n : ℤ) : ℝ := (P.indexedMass M n).toReal

theorem pairwiseDisjoint_Ioo :
    Pairwise (Function.onFun Disjoint fun n : ℤ => Ioo (P.separator (n - 1)) (P.separator n)) := by
  intro m n hmn
  rcases lt_or_gt_of_ne hmn with h | h
  · refine Set.disjoint_left.mpr fun x hx hy => ?_
    have h1 : P.separator m ≤ P.separator (n - 1) := P.separator_strictMono.monotone (by omega)
    linarith [hx.2, hy.1]
  · refine Set.disjoint_left.mpr fun x hx hy => ?_
    have h1 : P.separator n ≤ P.separator (m - 1) := P.separator_strictMono.monotone (by omega)
    linarith [hx.1, hy.2]

/-- `∑ a_n ≤ M(ℝ)`: the indexed masses form a nonnegative `ℓ¹` sequence. -/
theorem tsum_indexedMass_le (M : Measure ℝ) : ∑' n, P.indexedMass M n ≤ M univ :=
  tsum_meas_le_meas_iUnion_of_disjoint M (fun n => measurableSet_Ioo)
    P.pairwiseDisjoint_Ioo |>.trans (measure_mono (subset_univ _))

theorem indexedMass_zero (n : ℤ) : P.indexedMass (0 : Measure ℝ) n = 0 := by
  simp [indexedMass]

theorem summable_indexedMassReal (M : Measure ℝ) [IsFiniteMeasure M] :
    Summable (P.indexedMassReal M) := by
  refine ENNReal.summable_toReal ?_
  exact ne_top_of_le_ne_top (measure_ne_top M univ) (P.tsum_indexedMass_le M)

end BoundaryPhase

section Lipschitz

open scoped NNReal

/-- **Where `M` permits.**  If the real part of the boundary value of the Cauchy transform is a `K`-Lipschitz
function `g` with `κ K < L/2`, then `φ(x) = L x/2 − κ g(x)` is a `BoundaryPhase`. -/
def BoundaryPhase.ofLipschitz (L κ : ℝ) (g : ℝ → ℝ) (K : ℝ≥0) (hg : LipschitzWith K g) (hκ : 0 ≤ κ)
    (hc : κ * K < L / 2) : BoundaryPhase :=
  have hslope : ∀ a b : ℝ, a ≤ b →
      (L / 2 - κ * K) * (b - a) ≤ (L * b / 2 - κ * g b) - (L * a / 2 - κ * g a) := by
    intro a b hab
    have h1 : |g b - g a| ≤ K * |b - a| := by
      have := hg.dist_le_mul b a
      simpa [Real.dist_eq] using this
    have h2 : |b - a| = b - a := abs_of_nonneg (sub_nonneg.mpr hab)
    rw [h2] at h1
    have h3 : g b - g a ≤ K * (b - a) := (le_abs_self _).trans h1
    nlinarith [mul_le_mul_of_nonneg_left h3 hκ]
  have hpos : 0 < L / 2 - κ * K := by linarith
  { φ := fun x => L * x / 2 - κ * g x
    strictMono := fun a b hab => by
      have := hslope a b hab.le
      have : 0 < (L / 2 - κ * K) * (b - a) := mul_pos hpos (sub_pos.mpr hab)
      linarith [hslope a b hab.le]
    continuous := by have := hg.continuous; fun_prop
    tendsto_atTop := by
      refine tendsto_atTop_mono' atTop ?_ (tendsto_atTop_add_const_left atTop
        (L * 0 / 2 - κ * g 0) (Tendsto.const_mul_atTop hpos tendsto_id))
      filter_upwards [eventually_ge_atTop 0] with x hx
      have := hslope 0 x hx
      simp only [id] at *
      linarith
    tendsto_atBot := by
      refine tendsto_atBot_mono' atBot ?_ (tendsto_atBot_add_const_left atBot
        (L * 0 / 2 - κ * g 0) (Tendsto.const_mul_atBot hpos tendsto_id))
      filter_upwards [eventually_le_atBot 0] with x hx
      have := hslope x 0 hx
      simp only [id] at *
      linarith }

end Lipschitz


section Selected

/-- `φ` is the real-part boundary value of DEF-013's `boundaryPhase L κ M z = Lz/2 − κ G_M(z)` as `Im z ↓ 0`. -/
def IsBoundaryRealPart (L κ : ℝ) (M : Measure ℝ) (φ : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, Tendsto (fun ε : ℝ => (QuantumNLS.SpatialTransfer.boundaryPhase L κ M
    ((x : ℂ) + (ε : ℂ) * Complex.I)).re) (𝓝[>] 0) (𝓝 (φ x))

/-- The selected phase of DEF-013/014: a `BoundaryPhase` which is the boundary real part of `γ` for `M`. -/
structure SelectedPhase (L κ : ℝ) (M : Measure ℝ) extends BoundaryPhase where
  boundary : IsBoundaryRealPart L κ M φ

/-- The binding target `a_n = |w_n|²`: a chart `Φ` into `ℓ²(ℤ)` has squared moduli the indexed masses. -/
def ChartMasses {X : Type*} (Φ : X → QuantumNLS.ResetNormalizationUniqueness.S2 ℤ) (a : ℤ → X → ℝ) : Prop :=
  ∀ u n, ‖Φ u n‖ ^ 2 = a n u

end Selected

section Binding

open QuantumNLS.ResetNormalizationUniqueness AddCircle

/-- **LOCAL-022 binding (b), relative to the parametric full-mass measures.**  The abstract `q` of
`reset_normalization_uniqueness_phys` is instantiated by the DEF-014 indexed masses
`q_n(u) = a_n(u) = M_{κ,u}((b_{n−1}(u), b_n(u)))` for a family of finite measures `Mfam u` (= `M_{κ,u}`) and boundary
phases `Pfam u` (the measure `M_{κ,u}` and the strict monotonicity of `Re γ_u` are the parameters). -/
theorem reset_normalization_uniqueness_indexed (L : ℝ) [Fact (0 < L)] {r : ℝ} (hr : 0 < r)
    (Mfam : Lp ℂ 2 (volume : Measure (AddCircle L)) → Measure ℝ) (hM0 : Mfam 0 = 0)
    (Pfam : Lp ℂ 2 (volume : Measure (AddCircle L)) → BoundaryPhase)
    (Φ₁ Φ₂ : Lp ℂ 2 (volume : Measure (AddCircle L)) → S2 ℤ)
    (hΦ₁ : IsStronglySymplecticOn (Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r)
      (Metric.ball (0 : S2 ℤ) r) Φ₁)
    (hΦ₂ : IsStronglySymplecticOn (Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r)
      (Metric.ball (0 : S2 ℤ) r) Φ₂)
    (han₁ : AnalyticOnNhd ℝ Φ₁ (Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r))
    (han₂ : AnalyticOnNhd ℝ Φ₂ (Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r))
    (hm₁ : ∀ u ∈ Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r, ∀ n,
      ‖Φ₁ u n‖ ^ 2 = (Pfam u).indexedMassReal (Mfam u) n)
    (hm₂ : ∀ u ∈ Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r, ∀ n,
      ‖Φ₂ u n‖ ^ 2 = (Pfam u).indexedMassReal (Mfam u) n)
    (hD₁ : ∀ h, fderiv ℝ Φ₁ 0 h = QuantumNLS.Fourier.fourierL2 L h)
    (hD₂ : ∀ h, fderiv ℝ Φ₂ 0 h = QuantumNLS.Fourier.fourierL2 L h)
    (hc₁ : ∀ u ∈ Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r,
      Φ₁ (Cphys L u) = star (Φ₁ u))
    (hc₂ : ∀ u ∈ Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r,
      Φ₂ (Cphys L u) = star (Φ₂ u)) :
    ∀ u ∈ Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r, Φ₁ u = Φ₂ u :=
  reset_normalization_uniqueness_phys L hr (fun n u => (Pfam u).indexedMassReal (Mfam u) n)
    (fun n => by simp [BoundaryPhase.indexedMassReal, BoundaryPhase.indexedMass, hM0])
    Φ₁ Φ₂ hΦ₁ hΦ₂ han₁ han₂ hm₁ hm₂ hD₁ hD₂ hc₁ hc₂

end Binding

end QuantumNLS.IndexedMasses

#print axioms QuantumNLS.IndexedMasses.BoundaryPhase.exists_unique_separator
#print axioms QuantumNLS.IndexedMasses.BoundaryPhase.separator_strictMono
#print axioms QuantumNLS.IndexedMasses.BoundaryPhase.pairwiseDisjoint_Ioo
#print axioms QuantumNLS.IndexedMasses.BoundaryPhase.tsum_indexedMass_le
#print axioms QuantumNLS.IndexedMasses.BoundaryPhase.summable_indexedMassReal
#print axioms QuantumNLS.IndexedMasses.BoundaryPhase.ofLipschitz
#print axioms QuantumNLS.IndexedMasses.reset_normalization_uniqueness_indexed
