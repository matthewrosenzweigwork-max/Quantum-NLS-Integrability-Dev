import Mathlib
import QuantumNLS.IndexedScalarMeasure

/-!
# DEF-043 repaired: separation only at an explicit set of regular cuts

Source: `chapters/propagation/label_periods.tex`, `def:PF-indexed-scalar` (DEF-043).  Terra r110 observed that
`IndexedScalarMeasure.separation` (module `IndexedScalarMeasure`, frozen, sha256 bf40a2dd...) assumes the indexed
separation at *every* exterior point `x ∉ supp μ` with `2πa < F(x) < 2π(a+1)`, which would be stronger than the source
if the source's "regular cuts" form a proper subset.

**What the source says about "regular cut".**  `def:PF-indexed-scalar` uses "at each regular cut `x`" without a
definition; elsewhere (`core/scalar_window_differentials.tex`, `quantitative/label_geometry.tex`,
`propagation/label_periods.tex` lines 316-323) "regular cut(s)" are specific points in the interior of classical
bands (cutpoints chosen on the two sides of a gap, window endpoints), i.e. a *chosen* subset of the exterior of
`supp μ`.  The source gives no intrinsic definition, so the set of regular cuts is made an explicit field.

## Realization
`IndexedScalarMeasureCuts L κ` has all the fields of `IndexedScalarMeasure` except that `separation` is assumed only
for `x ∈ cuts`, where `cuts : Set ℝ` is an explicit field with `cuts ⊆ (supp μ)ᶜ` (`cuts_sub`).

## Proved
* `IndexedScalarMeasure.toCuts`: the original structure gives one with `cuts = (supp μ)ᶜ`;
* `IndexedScalarMeasureCuts.toFull`: conversely, with `cuts = (supp μ)ᶜ` it is the original structure, so
  `IndexedScalarMeasure` is exactly the special case `RegularCut = (supp μ)ᶜ` (`toFull_toCuts`, `toCuts_toFull`);
* `IndexedScalarMeasureCuts.mono`: shrinking the set of cuts weakens the hypothesis (every structure with cut set
  `S` yields one with any `S' ⊆ S`).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open QuantumNLS.IndexedScalarMeasure

namespace QuantumNLS.IndexedScalarMeasureCuts

/-- DEF-043 with separation assumed only at an explicit set `cuts` of regular cuts. -/
structure IndexedScalarMeasureCuts (L κ : ℝ) where
  hL : 0 < L
  hκ : 0 < κ
  μ : Measure ℝ
  isProb : IsProbabilityMeasure μ
  noAtoms : NoAtoms μ
  reG : ℝ → ℝ
  boundary : LocallyUniformBoundary μ reG ∨ BoundedAEBoundary μ reG
  integer_ae : ∀ᵐ t ∂μ, ∃ k : ℤ, indexLabel L κ reG t = k
  cuts : Set ℝ
  cuts_sub : cuts ⊆ (μ.support)ᶜ
  separation : ∀ x ∈ cuts, ∀ a : ℤ,
    2 * Real.pi * a < exteriorForce L κ μ x → exteriorForce L κ μ x < 2 * Real.pi * (a + 1) →
      (∀ᵐ t ∂μ, t < x → indexLabel L κ reG t ≤ a) ∧
      (∀ᵐ t ∂μ, x < t → (a : ℝ) + 1 ≤ indexLabel L κ reG t)

variable {L κ : ℝ}

/-- The original structure is the case `cuts = (supp μ)ᶜ`. -/
def _root_.QuantumNLS.IndexedScalarMeasure.IndexedScalarMeasure.toCuts
    (S : IndexedScalarMeasure L κ) : IndexedScalarMeasureCuts L κ where
  hL := S.hL
  hκ := S.hκ
  μ := S.μ
  isProb := S.isProb
  noAtoms := S.noAtoms
  reG := S.reG
  boundary := S.boundary
  integer_ae := S.integer_ae
  cuts := (S.μ.support)ᶜ
  cuts_sub := subset_rfl
  separation := fun x hx => S.separation x hx

/-- With `cuts = (supp μ)ᶜ`, a structure with cuts is the original structure. -/
def toFull (S : IndexedScalarMeasureCuts L κ) (h : S.cuts = (S.μ.support)ᶜ) :
    IndexedScalarMeasure L κ where
  hL := S.hL
  hκ := S.hκ
  μ := S.μ
  isProb := S.isProb
  noAtoms := S.noAtoms
  reG := S.reG
  boundary := S.boundary
  integer_ae := S.integer_ae
  separation := fun x hx => S.separation x (h ▸ hx)

theorem toCuts_cuts (S : IndexedScalarMeasure L κ) : S.toCuts.cuts = (S.μ.support)ᶜ := rfl

theorem toFull_toCuts (S : IndexedScalarMeasure L κ) :
    toFull S.toCuts (toCuts_cuts S) = S := rfl

theorem toCuts_toFull (S : IndexedScalarMeasureCuts L κ) (h : S.cuts = (S.μ.support)ᶜ) :
    (toFull S h).toCuts.cuts = S.cuts := by
  rw [toCuts_cuts, h]; rfl

/-- Shrinking the set of regular cuts weakens the hypothesis. -/
def mono (S : IndexedScalarMeasureCuts L κ) {S' : Set ℝ} (h : S' ⊆ S.cuts) :
    IndexedScalarMeasureCuts L κ where
  hL := S.hL
  hκ := S.hκ
  μ := S.μ
  isProb := S.isProb
  noAtoms := S.noAtoms
  reG := S.reG
  boundary := S.boundary
  integer_ae := S.integer_ae
  cuts := S'
  cuts_sub := h.trans S.cuts_sub
  separation := fun x hx => S.separation x (h hx)

end QuantumNLS.IndexedScalarMeasureCuts

#print axioms QuantumNLS.IndexedScalarMeasureCuts.toFull
#print axioms QuantumNLS.IndexedScalarMeasureCuts.toFull_toCuts
#print axioms QuantumNLS.IndexedScalarMeasureCuts.mono
