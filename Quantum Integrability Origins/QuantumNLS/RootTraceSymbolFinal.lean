import Mathlib
import QuantumNLS.RootTraceSymbolQuantum
import QuantumNLS.RootTraceSymbolSpatial
import QuantumNLS.PhysicalTraceSymbolDependency

/-!
# R-7E0532E7 `eq:root-trace-symbol` (`eq:root-trace-symbol`, `ROOT_spectral_density.tex`)

**`traceSymbol_all`**: for `κ ≥ 0`, every physical `L²(𝕋_L)` class `u` (no normalization) and EVERY `z ∈ ℂ`,

`exp(-(i z L/2)) · NormalizedTransfer.productSymbol L κ u z = L2SpatialTransfer.discriminant κ u z`.

Consequently the Sol interface `PhysicalTraceSymbolDependency.TraceSymbolIdentity L κ u` (a statement on the high half-plane only)
holds (`traceSymbolIdentity`), and so does its consequence for the canonical quantum measure.

Route (all modules new, no EXT-025 contract): the quantum side `RootTraceSymbolQuantum.kps_eq` (alternating-chamber torus integrals
= iterated interval integrals `Wr`), the spatial side `RootTraceSymbolSpatial.trace_eq` (interaction picture, Dyson iterates are the
same `Wr`), and the bookkeeping of the `r = 0` terms.  Hence no identity-theorem extension from a high half-plane is needed.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open MeasureTheory Set Filter ComplexConjugate

namespace QuantumNLS.RootTraceSymbolFinal

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.RootChamberIntegral (Wr)
open QuantumNLS.L2SpatialTransfer (profile intervalIntegrable_profile)

variable {L : ℝ} [Fact (0 < L)]

theorem Wr_zero (f g : ℝ → ℂ) (c : ℂ) (ℓ : ℝ) : Wr f g c 0 ℓ = 1 := rfl

/-- **`eq:root-trace-symbol`** for every `z ∈ ℂ`. -/
theorem traceSymbol_all {κ : ℝ} (hκ : 0 ≤ κ) (u : L2T L) (z : ℂ) :
    Complex.exp (-(Complex.I * z * L / 2)) * QuantumNLS.NormalizedTransfer.productSymbol L κ u z =
      QuantumNLS.L2SpatialTransfer.discriminant κ u z := by
  have hL : 0 < L := Fact.out
  have hv := intervalIntegrable_profile u
  obtain ⟨hsa, hsb, -, -⟩ := QuantumNLS.RootTraceSymbolSpatial.transfer_entries (κ := κ) hκ hL.le hv z
  set a : ℕ → ℂ := fun r => (κ : ℂ) ^ r * Wr (fun s => conj (profile u s)) (profile u) z r L with ha
  set b : ℕ → ℂ := fun r => (κ : ℂ) ^ r * Wr (profile u) (fun s => conj (profile u s)) (-z) r L with hb
  have hdisc : QuantumNLS.L2SpatialTransfer.discriminant κ u z =
      Matrix.trace (QuantumNLS.RootDiscriminantL1.TT κ (profile u) z L) := rfl
  rw [hdisc, QuantumNLS.RootTraceSymbolSpatial.trace_eq hκ hL hv z]
  have hterm : ∀ j : ℕ, QuantumNLS.NormalizedTransfer.symbolTerm L κ u z (j + 1) =
      a (j + 1) + Complex.exp (Complex.I * z * L) * b (j + 1) := by
    intro j
    unfold QuantumNLS.NormalizedTransfer.symbolTerm
    rw [QuantumNLS.RootTraceSymbolQuantum.kps_eq]
    simp only [ha, hb]
    push_cast
    ring
  unfold QuantumNLS.NormalizedTransfer.productSymbol
  simp_rw [hterm]
  have hsa' : Summable (fun j => a (j + 1)) := (summable_nat_add_iff 1).2 hsa
  have hsb' : Summable (fun j => Complex.exp (Complex.I * z * L) * b (j + 1)) :=
    ((summable_nat_add_iff 1).2 hsb).mul_left _
  rw [Summable.tsum_add hsa' hsb', tsum_mul_left]
  have hA : ∑' r, a r = 1 + ∑' j, a (j + 1) := by
    rw [hsa.tsum_eq_zero_add]; simp [ha, Wr_zero]
  have hB : ∑' r, b r = 1 + ∑' j, b (j + 1) := by
    rw [hsb.tsum_eq_zero_add]; simp [hb, Wr_zero]
  have hE2 : QuantumNLS.RootInteractionL1.E2c z L = Complex.exp (-(Complex.I * z * L / 2)) := by
    unfold QuantumNLS.RootInteractionL1.E2c QuantumNLS.RootInteractionL1.a1c
    congr 1; ring
  have hE1 : QuantumNLS.RootInteractionL1.E1c z L =
      Complex.exp (-(Complex.I * z * L / 2)) * Complex.exp (Complex.I * z * L) := by
    unfold QuantumNLS.RootInteractionL1.E1c QuantumNLS.RootInteractionL1.a1c
    rw [← Complex.exp_add]; congr 1; ring
  have hA' : ∑' r : ℕ, (κ : ℂ) ^ r * Wr (fun s => conj (profile u s)) (profile u) z r L = ∑' r, a r := rfl
  have hB' : ∑' r : ℕ, (κ : ℂ) ^ r * Wr (profile u) (fun s => conj (profile u s)) (-z) r L = ∑' r, b r := rfl
  rw [hA', hB', hE1, hE2, hA, hB]
  ring

/-- The Sol interface proposition (high half-plane form) is a consequence. -/
theorem traceSymbolIdentity {κ : ℝ} (hκ : 0 ≤ κ) (u : L2T L) :
    QuantumNLS.PhysicalTraceSymbolDependency.TraceSymbolIdentity L κ u :=
  fun z _ => traceSymbol_all hκ u z

/-- The canonical quantum cosine identity on the high half-plane, unconditionally. -/
theorem high_cosine {κ : ℝ} (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) {z : ℂ}
    (hz : QuantumNLS.RootMeasureComplex.HighHalf L (κ * ‖u‖ ^ 2) z) :
    2 * Complex.cos (QuantumNLS.SpatialTransfer.boundaryPhase L κ
        (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) z) =
      QuantumNLS.L2SpatialTransfer.discriminant κ u z :=
  QuantumNLS.PhysicalTraceSymbolDependency.high_cosine hκ hu (traceSymbolIdentity hκ.le u) hz

end QuantumNLS.RootTraceSymbolFinal

#print axioms QuantumNLS.RootTraceSymbolFinal.traceSymbol_all
#print axioms QuantumNLS.RootTraceSymbolFinal.traceSymbolIdentity
#print axioms QuantumNLS.RootTraceSymbolFinal.high_cosine
