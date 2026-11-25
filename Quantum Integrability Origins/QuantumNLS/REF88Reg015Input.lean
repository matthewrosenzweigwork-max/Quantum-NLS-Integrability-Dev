import Mathlib
import QuantumNLS.SobolevSpaces
import QuantumNLS.RootIndexedMasses
import QuantumNLS.PhysicalQuantumMeasure
import QuantumNLS.StrongSymplectic
import QuantumNLS.REF88Chart

/-!
# REF88Reg015Input: the ONE named input `Reg015Input` (REG-015 `CC:all-fractional:theorem`)

PRE-START RULE module.  REG-015 (`source-text/chapters/regularity/all_orders.tex`, line 107,
`\\ReportID{REG-015}`, `\\label{CC:all-fractional:theorem}`) is not yet accepted (its chain
REG-010 -> REG-011 -> REG-013 -> REG-015 is built by other roles).  Its EXACT printed statement is
transcribed as the Prop `Reg015Input`; nothing is weakened or strengthened.  The FINAL named theorem of
R-EF8C2837 must replace the hypothesis `hR : Reg015Input L κ hκ` by the accepted REG-015 theorem once the
integrator provides it.

Printed statement (all_orders.tex:107-121):

  For every real `s ≥ 0` and every `u ∈ L²(𝕋_L)`,
    `u ∈ H^s  ⟺  ∫ (1+|t|)^{2s} dM_u(t) < ∞  ⟺  ∑_n (1+|p_n|)^{2s} I_n(u) < ∞`.
  The indexed action map is continuous from `H^s` into the corresponding weighted `ℓ¹` space and sends
  bounded sets to bounded sets.  If, separately, a homeomorphism `Φ : L² → V ⊂ ℓ²` onto its image
  satisfies `|Φ_n(u)|² = I_n(u)`, its restriction is a homeomorphism from `H^s` onto `V ∩ h^s`, with the
  subspace weighted `ℓ²` topology.  No assertion that `V = ℓ²` is included.

Formalization choices (stated, none changes the mathematical content):
* `H^s` is the DEF-002 Hilbert space `H02 L s`, `h^s` is `h02 L s`, both with weights `(1+|2πn/L|)^{2s}`
  (`Fourier.sobolevWeight`); "`u ∈ H^s`" for `u ∈ L²` is `Fourier.MemHsLp L s u`.
* `M_u` is `PhysicalQuantumMeasure.measure hκ u` (as in the accepted REG-014/REG-004 setting), `I_n(u)` is
  `(RootIndexedMasses.masses hκ u).1 n`.
* "`∫ (1+|t|)^{2s} dM_u < ∞`" is `Integrable` of that nonnegative function against `M_u`.
* "continuous from `H^s` into the weighted `ℓ¹`" is the `ε`-`δ` statement in the weighted `ℓ¹` norm
  `∑_n (1+|p_n|)^{2s} |I_n(u) - I_n(u₀)|` (with its summability), "bounded sets to bounded sets" is
  the bound of `∑_n (1+|p_n|)^{2s} I_n(u)`.
* "homeomorphism onto its image" is `Topology.IsEmbedding Φ`; the conclusion is a homeomorphism
  `e : H^s ≃ₜ {w : h^s // w ∈ V}` (subspace topology of `h^s`) compatible with `Φ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ENNReal Topology
open MeasureTheory Filter

namespace QuantumNLS.REF88Reg015

open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight QuantumNLS.Fourier
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.REF88Chart (K)
open QuantumNLS.StrongSymplectic

variable {L : ℝ} [Fact (0 < L)]

/-- The inclusion `h^s ↪ ℓ²(ℤ)` (`s ≥ 0`), coordinatewise the identity. -/
def toK {s : ℝ} (hs : 0 ≤ s) (w : h02 L s) : K :=
  toL2 (def002 L 0) (h02_mono L hs w)

lemma toK_apply {s : ℝ} (hs : 0 ≤ s) (w : h02 L s) (n : ℤ) : (toK hs w : ℤ → ℂ) n = w.val n := by
  unfold toK
  rw [toL2_apply]
  simp [def002, sobolevWeight_zero]
  rfl

/-- **The named input.**  The EXACT printed statement of REG-015 `CC:all-fractional:theorem`
(`all_orders.tex:107`), at fixed `L > 0` and physical coupling `κ > 0`. -/
def Reg015Input (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) : Prop :=
  ∀ (s : ℝ) (hs : 0 ≤ s),
    -- the three-way equivalence, for every `u ∈ L²`
    (∀ u : L2T L,
      (MemHsLp L s u ↔ Integrable (fun t : ℝ => (1 + |t|) ^ (2 * s))
          (PhysicalQuantumMeasure.measure hκ u)) ∧
      (Integrable (fun t : ℝ => (1 + |t|) ^ (2 * s)) (PhysicalQuantumMeasure.measure hκ u) ↔
        Summable (fun n : ℤ => sobolevWeight L s n * (RootIndexedMasses.masses hκ u).1 n))) ∧
    -- the indexed action map is continuous from `H^s` into the weighted `ℓ¹`
    (∀ u₀ : H02 L s, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ u : H02 L s, ‖u - u₀‖ < δ →
      Summable (fun n : ℤ => sobolevWeight L s n *
        |(RootIndexedMasses.masses hκ (H02.toL2 hs u)).1 n -
          (RootIndexedMasses.masses hκ (H02.toL2 hs u₀)).1 n|) ∧
      ∑' n : ℤ, sobolevWeight L s n *
        |(RootIndexedMasses.masses hκ (H02.toL2 hs u)).1 n -
          (RootIndexedMasses.masses hκ (H02.toL2 hs u₀)).1 n| < ε) ∧
    -- ... and sends bounded sets to bounded sets
    (∀ B : Set (H02 L s), Bornology.IsBounded B → ∃ C : ℝ, ∀ u ∈ B,
      ∑' n : ℤ, sobolevWeight L s n * (RootIndexedMasses.masses hκ (H02.toL2 hs u)).1 n ≤ C) ∧
    -- the conditional homeomorphism (no assertion that `V = ℓ²`)
    (∀ Φ : L2T L → K, Topology.IsEmbedding Φ →
      (∀ (u : L2T L) (n : ℤ), ‖Φ u n‖ ^ 2 = (RootIndexedMasses.masses hκ u).1 n) →
      ∃ e : H02 L s ≃ₜ {w : h02 L s // ∃ u : L2T L, Φ u = toK hs w},
        ∀ u : H02 L s, toK hs (e u).1 = Φ (H02.toL2 hs u))

/-! ### Consequences used by R-EF8C2837 -/

variable {κ : ℝ}

/-- First clause of the printed proof: every finite-action field belongs to every `H^s`
("This implication uses the verified action regularity, not the mass identity alone"). -/
theorem finite_action_mem_Hs (hκ : 0 < κ) (hR : Reg015Input L κ hκ) (u : L2T L)
    (hfin : ∃ F : Finset ℤ, ∀ n, n ∉ F → (RootIndexedMasses.masses hκ u).1 n = 0)
    (s : ℝ) (hs : 0 ≤ s) : MemHsLp L s u := by
  obtain ⟨hequiv, -⟩ := hR s hs
  obtain ⟨F, hF⟩ := hfin
  have hsum : Summable (fun n : ℤ => sobolevWeight L s n * (RootIndexedMasses.masses hκ u).1 n) := by
    apply summable_of_ne_finset_zero (s := F)
    intro n hn
    rw [hF n hn, mul_zero]
  exact ((hequiv u).1).2 (((hequiv u).2).2 hsum)

/-- Second printed clause: the global chart restricts to a homeomorphism `H^s → h^s` for every real
`s ≥ 0` (the separate map hypothesis of REG-015 is the assumed global `L²` homeomorphism with exact
moduli; here `V = ℓ²`). -/
theorem sobolev_homeomorphism (hκ : 0 < κ) (hR : Reg015Input L κ hκ) {Φ : L2T L → K}
    (hΦ : IsStronglySymplectic Φ) (hcΦ : Continuous Φ)
    (hcΨ : Continuous (QuantumNLS.REF88Chart.chartInv hΦ))
    (hmod : ∀ (u : L2T L) (n : ℤ), ‖Φ u n‖ ^ 2 = (RootIndexedMasses.masses hκ u).1 n)
    (s : ℝ) (hs : 0 ≤ s) :
    ∃ e : H02 L s ≃ₜ h02 L s, ∀ u : H02 L s, toK hs (e u) = Φ (H02.toL2 hs u) := by
  let hhom : L2T L ≃ₜ K :=
    { toFun := Φ
      invFun := QuantumNLS.REF88Chart.chartInv hΦ
      left_inv := QuantumNLS.REF88Chart.chartInv_left hΦ
      right_inv := QuantumNLS.REF88Chart.chartInv_right hΦ
      continuous_toFun := hcΦ
      continuous_invFun := hcΨ }
  have hco : (⇑hhom : L2T L → K) = Φ := rfl
  have hemb : Topology.IsEmbedding Φ := hco ▸ hhom.isEmbedding
  obtain ⟨e, he⟩ := (hR s hs).2.2.2 Φ hemb hmod
  have hsurj : ∀ w : h02 L s, ∃ u : L2T L, Φ u = toK hs w := fun w =>
    ⟨QuantumNLS.REF88Chart.chartInv hΦ (toK hs w), QuantumNLS.REF88Chart.chartInv_right hΦ _⟩
  let f : {w : h02 L s // ∃ u : L2T L, Φ u = toK hs w} ≃ₜ h02 L s :=
    { toFun := fun w => w.1
      invFun := fun w => ⟨w, hsurj w⟩
      left_inv := fun w => rfl
      right_inv := fun w => rfl
      continuous_toFun := continuous_subtype_val
      continuous_invFun := Continuous.subtype_mk continuous_id _ }
  exact ⟨e.trans f, fun u => he u⟩

#print axioms finite_action_mem_Hs
#print axioms sobolev_homeomorphism

end QuantumNLS.REF88Reg015
