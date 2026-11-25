import Mathlib
import QuantumNLS.F02Tightness
import QuantumNLS.RootOccupationLimit

/-!
# CC:F02:tightness (R-E22E10B6): the printed theorem for the actual Bethe product law, with `I = I^{(κ)}(u)` and no `e_N` hypothesis

Source: `source-text/chapters/root_response/F02.tex`, Theorem `CC:F02:tightness` (line 219) and its proof: "The full occupation theorem states `e_N → 0` under this original law for every unit `L²` input."

Combination of two read-only modules:
* `F02Tightness` (R-E22E10B6, Round 66): the good bound on `A_N`, `P(A_N^c) ≤ e_N/r`, the tail bound, for an arbitrary law and an arbitrary real `I`, and their limits under the hypothesis `e_N → 0`;
* `RootOccupationLimit.root_occupation_limit` (R-E6DFC650, sonnet_fourier): `E ‖m/N − I‖_{ℓ¹} → 0` under the Born law of the physical basis, with `I_n = I_n^{(κ)}(u) = RootIndexedMasses.masses hκ u`.

`tightness_actual`: for a unit `u ∈ L²(𝕋_L)` (`‖u‖ = 1`), `I_n = I_n^{(κ)}(u)`, distinct integers `a ≠ b` with `I_a, I_b > 0`, `r = ½ min{I_a, I_b}`, and the actual law `P_{N,u} = bornMeasure (physBasis L hκ N) u hu`
(`c_N = κ/N`), with `e_N = E ‖m/N − I‖_{ℓ¹}` (`eN`), `A_N = {m_a/N ≥ r, m_b/N ≥ r}` and `G_N^{ab}(m) = Q_2(m) − Q_2(m − e_a + e_b)` (`gap`):
(good-bound) `|G_N^{ab}(m)| ≤ K_{ab}(r)` on `A_N`; (good-probability) `P(A_N^c) ≤ e_N/r → 0`; (tail-probability) `P{m_a ≥ 1, |G_N^{ab}| > K_{ab}(r)} ≤ e_N/r → 0`; and `e_N → 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace QuantumNLS.F02TightnessActual

open QuantumNLS.BetheLabels (MArr)
open QuantumNLS.EmpiricalRapidity (bornMeasure)
open QuantumNLS.BulkResponseActual (physBasis)
open QuantumNLS.RootOccupationLimit (occDist occVec summable_occDist occDist_nonneg occDist_le_two bornG_eq
  integrable_of_bdd root_occupation_limit)
open QuantumNLS.F02Tightness
open PhysicalTensor (L2T)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-- `I^{(κ)}(u)` as a function on `ℤ`. -/
def Ival (hκ : 0 < κ) (u : L2T L) (n : ℤ) : ℝ := (QuantumNLS.RootIndexedMasses.masses hκ u).1 n

theorem ellOne_eq (hκ : 0 < κ) (u : L2T L) {N : ℕ} (m : MArr N) :
    ellOne (Ival hκ u) m = ENNReal.ofReal (occDist hκ u N m) := by
  unfold ellOne occDist
  rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => abs_nonneg _) (summable_occDist hκ u N m)]
  rfl

/-- **`e_N → 0`** for the actual Born law and `I = I^{(κ)}(u)`: the full occupation theorem (R-E6DFC650) in the form used by the tightness theorem. -/
theorem eN_born_tendsto (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) :
    Tendsto (fun N : ℕ => eN (bornMeasure (physBasis L hκ N) u hu) (Ival hκ u)) atTop (𝓝 0) := by
  let g : QuantumNLS.BetheOccupationGauge.Gauge := fun _ _ => ⟨1, by simp⟩
  have h := (root_occupation_limit hκ u hu g).2.1 1 one_pos
  have h' : Tendsto (fun N : ℕ => ∫ m, occDist hκ u N m ∂(bornMeasure (physBasis L hκ N) u hu))
      atTop (𝓝 0) := by
    refine h.congr fun N => ?_
    rw [bornG_eq hκ g u hu N]
    simp only [Real.rpow_one]
    rfl
  have h2 := ENNReal.tendsto_ofReal h'
  rw [ENNReal.ofReal_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  unfold eN
  have hint := integrable_of_bdd (bornMeasure (physBasis L hκ N) u hu) (fun m => occDist hκ u N m) 2
    (fun m => by rw [abs_of_nonneg (occDist_nonneg hκ u N m)]; exact occDist_le_two hκ u hu hN m)
  rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall (occDist_nonneg hκ u N))]
  refine lintegral_congr fun m => ?_
  exact (ellOne_eq hκ u m).symm

/-- **`CC:F02:tightness`** (R-E22E10B6) for the actual Bethe product law, with `I = I^{(κ)}(u)`: all printed conclusions, no `e_N` hypothesis. -/
theorem tightness_actual (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {a b : ℤ} (hab : a ≠ b)
    (hIa : 0 < Ival hκ u a) (hIb : 0 < Ival hκ u b) :
    (∀ N : ℕ, 0 < N → ∀ m ∈ AN N a b (min (Ival hκ u a) (Ival hκ u b) / 2),
      |gap L κ a b m| ≤ Kab L κ (min (Ival hκ u a) (Ival hκ u b) / 2) a b) ∧
    (∀ N : ℕ, 0 < N →
      bornMeasure (physBasis L hκ N) u hu (AN N a b (min (Ival hκ u a) (Ival hκ u b) / 2))ᶜ ≤
        eN (bornMeasure (physBasis L hκ N) u hu) (Ival hκ u) /
          ENNReal.ofReal (min (Ival hκ u a) (Ival hκ u b) / 2)) ∧
    (∀ N : ℕ, 0 < N →
      bornMeasure (physBasis L hκ N) u hu {m : MArr N | 1 ≤ m.1 a ∧
          Kab L κ (min (Ival hκ u a) (Ival hκ u b) / 2) a b < |gap L κ a b m|} ≤
        eN (bornMeasure (physBasis L hκ N) u hu) (Ival hκ u) /
          ENNReal.ofReal (min (Ival hκ u a) (Ival hκ u b) / 2)) ∧
    Tendsto (fun N : ℕ => eN (bornMeasure (physBasis L hκ N) u hu) (Ival hκ u)) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => bornMeasure (physBasis L hκ N) u hu
        (AN N a b (min (Ival hκ u a) (Ival hκ u b) / 2))ᶜ) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => bornMeasure (physBasis L hκ N) u hu {m : MArr N | 1 ≤ m.1 a ∧
        Kab L κ (min (Ival hκ u a) (Ival hκ u b) / 2) a b < |gap L κ a b m|}) atTop (𝓝 0) := by
  have hL : 0 < L := Fact.out
  have he := eN_born_tendsto hκ u hu
  have hlim := tightness_tendsto hL hκ hab hIa hIb (fun N => bornMeasure (physBasis L hκ N) u hu) he
  exact ⟨fun N hN => (tightness hL hκ hN hab hIa hIb (bornMeasure (physBasis L hκ N) u hu)).1,
    fun N hN => (tightness hL hκ hN hab hIa hIb (bornMeasure (physBasis L hκ N) u hu)).2.1,
    fun N hN => (tightness hL hκ hN hab hIa hIb (bornMeasure (physBasis L hκ N) u hu)).2.2,
    he, hlim.1, hlim.2⟩

end QuantumNLS.F02TightnessActual

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.F02TightnessActual.eN_born_tendsto
#print axioms QuantumNLS.F02TightnessActual.tightness_actual
