import Mathlib
import QuantumNLS.RB7Smooth
import QuantumNLS.R275Unconditional
import QuantumNLS.RootScalarUniquenessR28
import QuantumNLS.PhysicalL2Normalization

/-!
# R-7B122087 `thm:hierarchy`: invariance of `I_{r+1}` under coordinate rotations from the scalar moment and uniqueness identities (own TODO A4)

Printed: "For rapidly decreasing coordinates, the scalar moment and uniqueness identities show that `F_r` is invariant under all coordinatewise rotations."

* `charge_eq_of_masses`: for smooth periodic `f, g` with the same indexed masses `I_n`, `charge L κ f (j+1) = charge L κ g (j+1)` (every `j`): accepted
  `R275Unconditional.R_275B7656` (`I_{j+1}(f) = ∫ t^j dM_f`) and accepted `RootScalarUniquenessR28.root_scalar_uniqueness` (equal masses ⇒ equal measure),
  `PhysicalL2Normalization.measure_eq_Mmeas` (the two literal measures coincide).
* `memHsLp_of_nonneg`: membership in all `H^s`, `s ≥ 0`, gives membership for every real `s` (weights `≤ 1` for `s ≤ 0`).
* `I_eq_of_moduli`: for the chart data (`Φ`, `Ψ` mutually inverse, `|Φ_n(u)|² = I_n(u)`) and the first clause of REG-015 (`u ∈ H^s ⇔ Σ(1+|p_n|)^{2s} I_n(u) < ∞`,
  the NAMED INPUT), if `z` is rapidly decreasing and `z'` has the same coordinate moduli, then every functional `I` which agrees with `Re charge L κ · (j+1)` on smooth
  periodic profiles has `I (Ψ z) = I (Ψ z')`.  Both `Ψ z` and `Ψ z'` are smooth periodic by `RB7Smooth.smooth_of_memHs`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate
open MeasureTheory

namespace QuantumNLS.RB7

open QuantumNLS.Fourier QuantumNLS.ClassicalCharges QuantumNLS.SmoothScalarMomentsPhysical QuantumNLS.PhysicalTensor
open QuantumNLS.Sobolev

variable {L κ : ℝ} [Fact (0 < L)]

theorem charge_eq_of_masses (hκ : 0 < κ) {f g : ℝ → ℂ} (hf : SmoothPeriodic L f) (hg : SmoothPeriodic L g)
    (hm : ∀ n, (QuantumNLS.RootIndexedMasses.masses hκ (smoothL2 hf)).1 n =
      (QuantumNLS.RootIndexedMasses.masses hκ (smoothL2 hg)).1 n) (j : ℕ) :
    charge L κ f (j + 1) = charge L κ g (j + 1) := by
  have hμ : QuantumNLS.PhysicalQuantumMeasure.measure hκ (smoothL2 hf) =
      QuantumNLS.PhysicalQuantumMeasure.measure hκ (smoothL2 hg) :=
    (QuantumNLS.RootScalarUniquenessR28.root_scalar_uniqueness hκ).1 _ _ hm
  have hμ' : QuantumNLS.FullMass.Mmeas κ (smoothL2 hf) = QuantumNLS.FullMass.Mmeas κ (smoothL2 hg) := by
    rw [← QuantumNLS.PhysicalL2Normalization.measure_eq_Mmeas hκ, ← QuantumNLS.PhysicalL2Normalization.measure_eq_Mmeas hκ]
    exact hμ
  have h1 := (QuantumNLS.R275Unconditional.R_275B7656 κ hκ hf).2 j
  have h2 := (QuantumNLS.R275Unconditional.R_275B7656 κ hκ hg).2 j
  rw [← h1.2, ← h2.2, hμ']

theorem memHsLp_of_nonneg (u : L2T L) (h : ∀ s : ℝ, 0 ≤ s → MemHsLp L s u) (s : ℝ) : MemHsLp L s u := by
  by_cases hs : 0 ≤ s
  · exact h s hs
  · have h0 := h 0 le_rfl
    unfold MemHsLp MemHs at *
    refine Summable.of_nonneg_of_le (fun n => by unfold sobolevWeight; positivity) (fun n => ?_) h0
    have hx : 1 ≤ 1 + |2 * Real.pi * (n : ℝ) / L| := by linarith [abs_nonneg (2 * Real.pi * (n : ℝ) / L)]
    have : sobolevWeight L s n ≤ sobolevWeight L 0 n := by
      unfold sobolevWeight
      exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)

/-- **Chart data**: the global actual chart of R-F5355ABD in the form used here. -/
structure ChartData (hκ : 0 < κ) where
  Φ : L2T L → lp (fun _ : ℤ => ℂ) 2
  Ψ : lp (fun _ : ℤ => ℂ) 2 → L2T L
  ΦΨ : ∀ z, Φ (Ψ z) = z
  mass : ∀ u n, ‖Φ u n‖ ^ 2 = (QuantumNLS.RootIndexedMasses.masses hκ u).1 n

/-- **The first clause of REG-015** in the form used here (NAMED INPUT): `u ∈ H^s ⇔ Σ (1+|p_n|)^{2s} I_n(u) < ∞`. -/
def Reg015Moments (hκ : 0 < κ) : Prop :=
  ∀ s : ℝ, 0 ≤ s → ∀ u : L2T L, (∃ v : H02 L s, v.val = u) ↔
    Summable (fun n : ℤ => (1 + |2 * Real.pi * (n : ℝ) / L|) ^ (2 * s) *
      (QuantumNLS.RootIndexedMasses.masses hκ u).1 n)

theorem smooth_of_rapid (hκ : 0 < κ) (C : ChartData (L := L) hκ) (hreg : Reg015Moments (L := L) hκ)
    (z : lp (fun _ : ℤ => ℂ) 2)
    (hz : ∀ s : ℝ, 0 ≤ s → Summable fun n : ℤ => (1 + |2 * Real.pi * (n : ℝ) / L|) ^ (2 * s) * ‖z n‖ ^ 2) :
    ∃ (f : ℝ → ℂ) (hf : SmoothPeriodic L f), smoothL2 hf = C.Ψ z := by
  refine smooth_of_memHs _ (memHsLp_of_nonneg _ (fun s hs => ?_))
  have h := (hreg s hs (C.Ψ z)).2 (by
    refine (hz s hs).congr (fun n => ?_)
    rw [← C.mass, C.ΦΨ])
  obtain ⟨v, hv⟩ := h
  rw [← hv]
  exact (mem_fieldSub_def002 (L := L) (s := s) v.val).1 v.2

theorem I_eq_of_moduli (hκ : 0 < κ) (C : ChartData (L := L) hκ) (hreg : Reg015Moments (L := L) hκ)
    (j : ℕ) (I : L2T L → ℝ) (hI : ∀ (f : ℝ → ℂ) (hf : SmoothPeriodic L f), I (smoothL2 hf) = (charge L κ f (j + 1)).re)
    (z z' : lp (fun _ : ℤ => ℂ) 2)
    (hz : ∀ s : ℝ, 0 ≤ s → Summable fun n : ℤ => (1 + |2 * Real.pi * (n : ℝ) / L|) ^ (2 * s) * ‖z n‖ ^ 2)
    (hmod : ∀ n, ‖z' n‖ = ‖z n‖) :
    I (C.Ψ z) = I (C.Ψ z') := by
  have hz' : ∀ s : ℝ, 0 ≤ s → Summable fun n : ℤ => (1 + |2 * Real.pi * (n : ℝ) / L|) ^ (2 * s) * ‖z' n‖ ^ 2 :=
    fun s hs => (hz s hs).congr (fun n => by rw [hmod n])
  obtain ⟨f, hf, hfe⟩ := smooth_of_rapid hκ C hreg z hz
  obtain ⟨g, hg, hge⟩ := smooth_of_rapid hκ C hreg z' hz'
  rw [← hfe, ← hge, hI f hf, hI g hg]
  congr 1
  rw [charge_eq_of_masses hκ hf hg _ j]
  intro n
  rw [hfe, hge, ← C.mass, ← C.mass, C.ΦΨ, C.ΦΨ, hmod n]

end QuantumNLS.RB7

#print axioms QuantumNLS.RB7.charge_eq_of_masses
#print axioms QuantumNLS.RB7.smooth_of_rapid
#print axioms QuantumNLS.RB7.I_eq_of_moduli
