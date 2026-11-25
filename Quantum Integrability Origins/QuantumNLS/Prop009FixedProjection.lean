import Mathlib
import QuantumNLS.Prop009ProbeDev
import QuantumNLS.Prop009ProbeBorn
import QuantumNLS.Prop017Physical
import QuantumNLS.Prop019Deviation
import QuantumNLS.MPFamily

/-!
# PROP-026 mixed binding, item (2): the fixed-action projection `P^I_N` and the fixed-contour deviation `ρ^I_N`

Source: `mixed_propagation.tex:196-218` (`eq:MP-fixed-mass`, `eq:MP-fixed-deviation`): for each `j ≥ 1` apply `lem:B4-finite-probes` to all
selected fixed contours and choose finitely many probes whose good event forces root-free neighbourhoods and transfer deviations below
`1/j`; at the probes the complement probability tends to zero (`lem:B4-high-moments`); choose increasing thresholds `N_j` with complement
probability `≤ 1/j` for `N ≥ N_j`, use the `j`-th collection for `N_j ≤ N < N_{j+1}`; `P^I_N` is its common spectral projection.

New module; imports (all read-only): `Prop009ProbeDev` (part A: `finite_probes_dev`, `onShell_of_arr`), `Prop009ProbeBorn` (part B:
`event_compl_tendsto`, `diag_schedule`), `Prop017Physical.event_projection` (diagonal projection onto an event, the review), `Prop019Deviation.transfer_deviation`
(spectral variance in the Bethe basis, the review), `MPFamily` (the `BgFam` background).  No EXT-025 contract and no new hypotheses besides the two
carried explicitly: `hμ : IsLimitingRapidityMeasure ... μ` (the accepted limiting measure `μ_{κ,u}`) and `hS : μ = S.μ` for the
`IndexedScalarMeasureCuts` datum `S` (pending DEF-014 item (1), carried as an explicit hypothesis, not assumed elsewhere).

* `fixed_projection`: an event sequence `E_N ⊆ M_N` (the `j(N)`-th finite-probe event) and `ρ_N → 0` such that (i) `P_{N,u}(E_Nᶜ) → 0`
  (`eq:MP-fixed-mass`: `η^I_N = ‖(1 − P^I_N)u^{⊗N}‖² = P_{N,u}(E_Nᶜ)` by `event_projection`), (ii) eventually in `N`, for every `φ ∈ H_N` with
  no Bethe component outside `E_N` and every fixed contour `Γ_i` and every `w ∈ Γ_i`:
  `‖(S_N(w) − s(w))φ‖ ≤ ρ_N‖φ‖` (`eq:MP-fixed-deviation`, transfer part), (iii) `P^I_N` exists: the diagonal projection `PE` with
  `PE Ψ_m = 1_{m∈E_N} Ψ_m`, idempotent, self-adjoint, `‖(1 − PE)u^{⊗N}‖² = P_{N,u}(E_Nᶜ)`.
* `hdevf_of_fixed`: the exact `hdevf` hypothesis shape of `MPLinearizationContours.mp_linearization_contours`, with `εf = ρ_N`.
The derivative part `‖(S_N' − s')P^I_N‖` of `eq:MP-fixed-deviation` is NOT needed by `mp_linearization_contours` (whose `hdevf` is the
transfer deviation only) and is not proved here.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ComplexConjugate

namespace QuantumNLS.Prop009FixedProjection

open QuantumNLS.PhysicalTensor (L2T physSector)
open QuantumNLS.BetheLabels (MArr)
open QuantumNLS.EmpiricalRapidity (bornMeasure)
open QuantumNLS.BulkResponseActual (physBasis IsLimitingRapidityMeasure)
open QuantumNLS.Prop017Quantum (qAct)
open QuantumNLS.PeriodReconstructionCore (sNf sf)
open QuantumNLS.PeriodReconstruction (Gam)
open QuantumNLS.IndexedScalarMeasure QuantumNLS.IndexedScalarMeasureCuts
open QuantumNLS.UnconditionalBetheBasis (meanField_physicalBasis)
open QuantumNLS.NormalizedTransfer (normalizedTransfer)
open QuantumNLS.Prop009ProbeBorn (probeEvent event_compl_tendsto diag_schedule)
open QuantumNLS.Prop009ProbeDev (finite_probes_dev onShell_of_arr)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

open Classical in
theorem fixed_projection (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) (S : IndexedScalarMeasureCuts L κ)
    (hS : (μ : Measure ℝ) = S.μ) {r : ℕ} {n : Fin r → ℤ} {xm xp h : Fin r → ℝ}
    (hxm : ∀ i, xm i ∈ S.cuts) (hxp : ∀ i, xp i ∈ S.cuts) (hlt : ∀ i, xm i < xp i) (hh : ∀ i, 0 < h i)
    (h1 : ∀ i, 2 * Real.pi * (n i - 1) < exteriorForce L κ S.μ (xm i))
    (h2 : ∀ i, exteriorForce L κ S.μ (xm i) < 2 * Real.pi * n i)
    (h3 : ∀ i, 2 * Real.pi * n i < exteriorForce L κ S.μ (xp i))
    (h4 : ∀ i, exteriorForce L κ S.μ (xp i) < 2 * Real.pi * (n i + 1)) :
    ∃ (E : ∀ N : ℕ, Set (MArr N)) (ρ : ℕ → ℝ), (∀ N, 0 ≤ ρ N) ∧ Tendsto ρ atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => (bornMeasure (physBasis L hκ N) u hu).real (E N)ᶜ) atTop (𝓝 0) ∧
      (∀ (N : ℕ) (hN : 0 < N), ∃ PE : QuantumNLS.KernelDefinition.BoundedSymmetricKernel (L2T L) N,
        (∀ m, PE (meanField_physicalBasis L N hN hκ m) =
          (if m ∈ E N then (1 : ℂ) else 0) • meanField_physicalBasis L N hN hκ m) ∧
        PE * PE = PE ∧ ContinuousLinearMap.adjoint PE = PE ∧
        ‖(1 - PE) (QuantumNLS.HighMomentsOps.wvec N u)‖ ^ 2 =
          (bornMeasure (physBasis L hκ N) u hu).real (E N)ᶜ) ∧
      ∀ᶠ N : ℕ in atTop, ∀ (hN : 1 ≤ N) (φ : physSector L N),
        (∀ m ∉ E N, ⟪meanField_physicalBasis L N hN hκ m, φ⟫_ℂ = 0) →
        ∀ i, ∀ w ∈ Gam (xm i) (xp i) (h i),
          ‖(normalizedTransfer L κ N w - sf L κ (EmpiricalRapidity.cauchyTransform S.μ) w •
            (1 : QuantumNLS.KernelDefinition.BoundedSymmetricKernel (L2T L) N)) φ‖ ≤ ρ N * ‖φ‖ := by
  have hL : 0 < L := Fact.out
  choose m z hz ε hε N0 d hd H using fun j : ℕ => finite_probes_dev S hxm hxp hlt hh h1 h2 h3 h4
    (τ := 1 / ((j : ℝ) + 1)) (by positivity)
  -- the probe events and their Born probabilities
  have hEc : ∀ j : ℕ, Tendsto (fun N : ℕ => (bornMeasure (physBasis L hκ N) u hu).real
      (probeEvent (L := L) (κ := κ) S.μ (z j) (ε j) N)ᶜ) atTop (𝓝 0) := by
    intro j
    have := event_compl_tendsto hκ u hu hμ (hz j) (hε j)
    rwa [hS] at this
  have hev : ∀ j : ℕ, ∀ᶠ N : ℕ in atTop, N0 j ≤ N ∧
      (bornMeasure (physBasis L hκ N) u hu).real
        (probeEvent (L := L) (κ := κ) S.μ (z j) (ε j) N)ᶜ ≤ 1 / ((j : ℝ) + 1) := by
    intro j
    refine (eventually_ge_atTop (N0 j)).and ?_
    exact (hEc j).eventually (Iic_mem_nhds (by positivity))
  obtain ⟨J, hJ, hPJ⟩ := diag_schedule _ hev
  set E : ∀ N : ℕ, Set (MArr N) := fun N => probeEvent (L := L) (κ := κ) S.μ (z (J N)) (ε (J N)) N with hE
  set ρ : ℕ → ℝ := fun N => 1 / ((J N : ℝ) + 1) with hρ
  have hρ0 : ∀ N, 0 ≤ ρ N := fun N => by positivity
  have hρlim : Tendsto ρ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat.comp hJ
  have hmass : Tendsto (fun N : ℕ => (bornMeasure (physBasis L hκ N) u hu).real (E N)ᶜ) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun N => measureReal_nonneg) ?_ hρlim
    filter_upwards [hPJ] with N hN using hN.2
  refine ⟨E, ρ, hρ0, hρlim, hmass, fun N hN => QuantumNLS.Prop017Physical.event_projection hκ hN u hu (E N), ?_⟩
  filter_upwards [hPJ, eventually_ge_atTop 1] with N hN hN1
  intro hNN φ hφ i w hw
  obtain ⟨hN0, -⟩ := hN
  have hNpos : 0 < N := hNN
  -- every label of the event gives an on-shell configuration obeying the probe bound
  have hmem : ∀ a ∈ E N, (∀ j, d (J N) ≤ ‖w - ((qAct L κ N a j : ℝ) : ℂ)‖) ∧
      ‖sNf L (κ / N) (qAct L κ N a) w - sf L κ (EmpiricalRapidity.cauchyTransform S.μ) w‖ ≤ ρ N := by
    intro a ha
    obtain ⟨B, hB⟩ := onShell_of_arr hL hκ hNpos a
    have hprobe : ∀ j, ‖sNf L (κ / N) B.q (z (J N) j) -
        sf L κ (EmpiricalRapidity.cauchyTransform S.μ) (z (J N) j)‖ < ε (J N) := by
      intro j; rw [hB]; exact ha j
    have := H (J N) N hNpos hN0 B hprobe i
    rw [hB] at this
    exact ⟨this.1 w hw, this.2 w hw⟩
  refine QuantumNLS.Prop019Deviation.transfer_deviation hκ hNN (E N) w _ (hρ0 N) (fun a ha j h0 => ?_)
    (fun a ha => (hmem a ha).2) φ hφ
  have := (hmem a ha).1 j
  have hd0 := hd (J N)
  rw [h0, sub_self, norm_zero] at this
  linarith

/-- The exact `hdevf` shape of `MPLinearizationContours.mp_linearization_contours` with `εf = ρ_N`: for the common-projection state `φ`
(unit vector with no Bethe component outside `E_N`) and fixed pieces `Pf` lying on the fixed contours, with `B.s = sf` on them. -/
theorem hdevf_of_fixed {N : ℕ} (hN : 1 ≤ N) (hκ : 0 < κ) (E : Set (MArr N)) {ρN : ℝ} (G : ℂ → ℂ)
    (Zc : Set ℂ) (hfix : ∀ φ : physSector L N,
        (∀ m ∉ E, ⟪meanField_physicalBasis L N hN hκ m, φ⟫_ℂ = 0) → ∀ w ∈ Zc,
          ‖(normalizedTransfer L κ N w - sf L κ G w •
            (1 : QuantumNLS.KernelDefinition.BoundedSymmetricKernel (L2T L) N)) φ‖ ≤ ρN * ‖φ‖)
    (φ : physSector L N) (hφ : ‖φ‖ = 1)
    (hsupp : ∀ m ∉ E, ⟪meanField_physicalBasis L N hN hκ m, φ⟫_ℂ = 0)
    {Z : Set ℂ} {d₀ s₁ a₀ c₁ : ℝ} (B : QuantumNLS.MPFamily.BgFam Z d₀ s₁ a₀ c₁)
    (hBs : ∀ w ∈ Zc, B.s w = sf L κ G w) (w : ℂ) (hw : w ∈ Zc) :
    ‖(normalizedTransfer L κ N w - B.s w •
      (1 : QuantumNLS.KernelDefinition.BoundedSymmetricKernel (L2T L) N)) φ‖ ≤ ρN := by
  have := hfix φ hsupp w hw
  rw [hφ, mul_one] at this
  rw [hBs w hw]
  exact this

end QuantumNLS.Prop009FixedProjection

#print axioms QuantumNLS.Prop009FixedProjection.fixed_projection
#print axioms QuantumNLS.Prop009FixedProjection.hdevf_of_fixed
