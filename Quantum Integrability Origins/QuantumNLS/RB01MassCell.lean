import Mathlib
import QuantumNLS.RB01Moments
import QuantumNLS.RootIndexedMassesCollapsed

/-! R-EC25334D (`thm:global-B01-actions`), stage RB01-16: identification of the gap mass with the indexed
quantum action (source `collective_actions.tex:466-495`, "Identification with the quantum phase labels":
"identifies the two central endpoints as the gap of phase nπ. Definition (root-indexed-mass) thus identifies its
mass with I_n ... For a collapsed gap both the inherited mass and the right side ... are zero").

For every `κ > 0`, every `q ∈ L²(𝕋_L)` and every label `n` (no high-label restriction is needed here; the
high-label input is the location of `b^±` from `RB01RootCount.root_count`):
* `lev_sub_cell`: the level set `{θ = nπ} = [b⁻, b⁺]` lies in the `n`th separator cell;
* `dens_zero_off_gap`: on the cell, outside `[b⁻, b⁺]`, the density `ρ = (πκ)⁻¹ hfun |Δ|` vanishes
  (a positive-density point has an open band-free neighborhood inside the cell, on which the phase is `nπ`
  by `RootIndexedMassesCollapsed.phase_label`);
* **`mass_eq_integral`**: `I_n(q) = (RootIndexedMasses.masses hκ q).1 n = ∫_{b⁻}^{b⁺} ρ(x) dx`
  (`RootIndexedMassesFull.root_indexed_masses`: `I_n = M(cell n)`; `RootGapLevelSets.measure_eq_dens`:
  `M = ρ dx`).  For a collapsed gap `b⁻ = b⁺` both sides are `0`. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Filter Topology Set Metric

namespace QuantumNLS.RB01MassCell

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.RB01RootCount (bm bp lev_eq)
open QuantumNLS.RootGapLevelSets (lev dens_pos_iff measure_eq_dens)
open QuantumNLS.RootDensityIdentification (dens dens_nonneg continuous_dens)
open QuantumNLS.RootIndexedMassesCollapsed (cell Dre continuous_Dre phase_label)

variable {L κ : ℝ} [Fact (0 < L)]

theorem lev_sub_cell (hκ : 0 < κ) (q : L2T L) (n : ℤ) {x : ℝ} (hx : x ∈ lev hκ q n) : x ∈ cell hκ q n := by
  have hθ : QuantumNLS.RootIndexedPhase.theta hκ q x = (n : ℝ) * Real.pi := hx
  have hπ := Real.pi_pos
  refine ⟨((QuantumNLS.PhysicalSourceFinal.sourceFacts hκ q).phase.separator_lt_iff x (n - 1)).2
      (?_ : (((n - 1 : ℤ) : ℝ) + 1 / 2) * Real.pi < QuantumNLS.RootIndexedPhase.theta hκ q x),
    ((QuantumNLS.PhysicalSourceFinal.sourceFacts hκ q).phase.lt_separator_iff x n).2
      (?_ : QuantumNLS.RootIndexedPhase.theta hκ q x < ((n : ℝ) + 1 / 2) * Real.pi)⟩
  · rw [hθ]; push_cast; linarith
  · rw [hθ]; linarith

theorem dens_zero_off_gap (hκ : 0 < κ) (q : L2T L) (n : ℤ) {x : ℝ} (hxC : x ∈ cell hκ q n)
    (hxn : x ∉ Icc (bm hκ q n) (bp hκ q n)) : dens κ q x = 0 := by
  obtain ⟨hle, hS⟩ := lev_eq hκ q n
  by_contra hne
  have hpos : 0 < dens κ q x := lt_of_le_of_ne (dens_nonneg hκ q x) (Ne.symm hne)
  have hg : 2 < |Dre κ q x| := (dens_pos_iff hκ q x).1 hpos
  have hopen : IsOpen (cell hκ q n ∩ {y | 2 < |Dre κ q y|}) :=
    isOpen_Ioo.inter (isOpen_lt continuous_const (continuous_Dre κ q).abs)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen x ⟨hxC, hg⟩
  have hsub : Ioo (x - ε) (x + ε) ⊆ cell hκ q n := by
    intro y hy
    rw [← Real.ball_eq_Ioo] at hy
    exact (hball hy).1
  have hgap : ∀ y ∈ Ioo (x - ε) (x + ε), 2 < |Dre κ q y| := by
    intro y hy
    rw [← Real.ball_eq_Ioo] at hy
    exact (hball hy).2
  have hab : x - ε < x + ε := by linarith
  have hxab : x ∈ Ioo (x - ε) (x + ε) := ⟨by linarith, by linarith⟩
  have hθ := phase_label hκ q n ⟨x - ε, x + ε, hab, hsub, hgap⟩ (x - ε) (x + ε) hab hsub hgap x hxab
  have hxl : x ∈ lev hκ q n := hθ
  rw [hS] at hxl
  exact hxn hxl

/-- **The gap mass is the indexed action**: `I_n(q) = ∫_{b⁻}^{b⁺} ρ`. -/
theorem mass_eq_integral (hκ : 0 < κ) (q : L2T L) (n : ℤ) :
    (QuantumNLS.RootIndexedMasses.masses hκ q).1 n = ∫ x in bm hκ q n..bp hκ q n, dens κ q x := by
  obtain ⟨hle, hS⟩ := lev_eq hκ q n
  have hm := (QuantumNLS.RootIndexedMassesFull.root_indexed_masses hκ q).1 n
  have hm' : (QuantumNLS.RootIndexedMasses.masses hκ q).1 n =
      (QuantumNLS.PhysicalQuantumMeasure.measure hκ q (cell hκ q n)).toReal := hm
  rw [hm']
  set a := bm hκ q n
  set b := bp hκ q n
  have hIcc : Icc a b ⊆ cell hκ q n := fun x hx => lev_sub_cell hκ q n (by rw [hS]; exact hx)
  have heq : (cell hκ q n).indicator (fun x => ENNReal.ofReal (dens κ q x)) =
      (Icc a b).indicator (fun x => ENNReal.ofReal (dens κ q x)) := by
    funext x
    by_cases hxI : x ∈ Icc a b
    · rw [indicator_of_mem hxI, indicator_of_mem (hIcc hxI)]
    · rw [indicator_of_notMem hxI]
      by_cases hxC : x ∈ cell hκ q n
      · rw [indicator_of_mem hxC, dens_zero_off_gap hκ q n hxC hxI, ENNReal.ofReal_zero]
      · rw [indicator_of_notMem hxC]
  have hmeas : QuantumNLS.PhysicalQuantumMeasure.measure hκ q (cell hκ q n) =
      ENNReal.ofReal (∫ x in Icc a b, dens κ q x) := by
    have hCm : MeasurableSet (cell hκ q n) := measurableSet_Ioo
    rw [measure_eq_dens hκ q, withDensity_apply _ hCm, ← lintegral_indicator hCm]
    change ∫⁻ x, (cell hκ q n).indicator (fun x => ENNReal.ofReal (dens κ q x)) x = _
    rw [heq, lintegral_indicator measurableSet_Icc]
    rw [ofReal_integral_eq_lintegral_ofReal ((continuous_dens κ q).integrableOn_Icc)
      (ae_of_all _ (fun x => dens_nonneg hκ q x))]
  rw [hmeas, ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Icc (fun x _ => dens_nonneg hκ q x)),
    intervalIntegral.integral_of_le hle, integral_Icc_eq_integral_Ioc]

end QuantumNLS.RB01MassCell

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.RB01MassCell.lev_sub_cell
#print axioms QuantumNLS.RB01MassCell.dens_zero_off_gap
#print axioms QuantumNLS.RB01MassCell.mass_eq_integral
