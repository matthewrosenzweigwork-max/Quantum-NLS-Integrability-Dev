import Mathlib
import QuantumNLS.REF88StageDReduce
import QuantumNLS.REF88QuantumLine
import QuantumNLS.REF88QuantumCouple
import QuantumNLS.REF88QuantumProfile
import QuantumNLS.REF88PrintedChartLocal

/-!
# REF88StageD: R-EF8C2837 stage D, item (iii) (quantum-frequency clause) with `HD` discharged

Source: `source-text/chapters/global/physical_cubic.tex` (sha256 `64ec3e02...`), theorem statement lines 28-86 and
the proof paragraph "Quantum derivatives at arbitrary finite mass" (lines 215-315).

`quantumDerivatives_of_chart` is the hypothesis `HD` of `REF88StageDReduce.stageD_of_derivatives`, proved:
the two printed derivative facts `∂_{e_a-e_b} ℰ = ω_{ab}` (`REF88QuantumLine.line_derivative`) and `K ∂_K ℰ = 𝒯`
(`REF88QuantumCouple.coupling_derivative`), with the printed profile `v(K,x)` supplied by `REF88QuantumProfile.exists_profile`
(from the chart: global surjectivity, exact moduli, REG-015 input), and the `H¹` property of the given unit profile `v`
derived from its finitely supported indexed probabilities (`oneH1_of_scaled`, REG-015 input).

`stageD` has the hypotheses of `stageC` (`hκ`, `Reg015Input`, and the printed chart hypotheses with the LOCAL conjugation-reflection normalization,
`REF88PrintedChartLocal.PrintedChartLocal`; the global identity is proved there from analyticity) and the conclusions of `stageC` plus
the printed frequency formula `ν_n(a) = ℰ + 𝒯 + ∑_{j∈F} x_j ω_{nj}` for every finite positive action vector.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ENNReal Topology
open Filter

namespace QuantumNLS.REF88StageD

open QuantumNLS.StrongSymplectic QuantumNLS.L2Flow QuantumNLS.REF88Chart QuantumNLS.REF88Reg015
open QuantumNLS.REF88Finite QuantumNLS.REF88PrintedChart QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.Fourier QuantumNLS.REF88QuantumDef QuantumNLS.REF88QuantumReduce
open QuantumNLS.REF88GradStructure QuantumNLS.REF88FieldRotation QuantumNLS.REF88QuantumTangent
open QuantumNLS.REF88StageDReduce QuantumNLS.REF88QuantumProfile QuantumNLS.REF88QuantumLine
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.F04SelBand (Mu II)
open QuantumNLS.ActualGapDataR26 (Data)
open QuantumNLS.REF88PrintedChartLocal (PrintedChartLocal printedChart_of_local)
open QuantumNLS.ProductEnergyPreparation (OneH1)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

theorem oneH1_of_finite_masses (hκ : 0 < κ) (hR : Reg015Input L κ hκ) (w : L2T L) (F : Finset ℤ)
    (hF0 : ∀ n, n ∉ F → (RootIndexedMasses.masses hκ w).1 n = 0) : OneH1 w := by
  have hu2 : MemHsLp L 2 w := finite_action_mem_Hs hκ hR w ⟨F, hF0⟩ 2 (by norm_num)
  exact (RootEnergyVariation.m21 (g2 hu2)).summable

/-- A unit profile whose indexed probabilities at coupling `K' = κ m` vanish off a finite set is an `H¹` field
(rescale to mass `m` and use the REG-015 input). -/
theorem oneH1_of_scaled (hκ : 0 < κ) (hR : Reg015Input L κ hκ) {m : ℝ} (hm : 0 < m) {K' : ℝ}
    (hK : 0 < K') (hKm : K' = κ * m) (v : L2T L) (hv : ‖v‖ = 1) (F : Finset ℤ)
    (hF0 : ∀ n, n ∉ F → II hK v n = 0) : OneH1 v := by
  set w : L2T L := ((Real.sqrt m : ℝ) : ℂ) • v with hw
  have hsq : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have hwn : ‖w‖ = Real.sqrt m := by
    rw [hw, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsq, hv, mul_one]
  have hwn2 : ‖w‖ ^ 2 = m := by rw [hwn, Real.sq_sqrt hm.le]
  have hw0 : w ≠ 0 := by
    intro h; rw [h, norm_zero] at hwn; exact hsq.ne' hwn.symm
  have hKw : 0 < κ * ‖w‖ ^ 2 := by rw [hwn2]; exact mul_pos hκ hm
  have hud : FullMass.unitDir w = v := by
    unfold FullMass.unitDir
    rw [hw, smul_smul, hwn]
    have : (((Real.sqrt m)⁻¹ : ℝ) : ℂ) * ((Real.sqrt m : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ hsq.ne']; simp
    rw [this, one_smul]
  have hF1 : ∀ n, n ∉ F → (RootIndexedMasses.masses hκ w).1 n = 0 := by
    intro n hn
    show II hκ w n = 0
    have h1 := II_unitDir hκ hw0 hKw n
    have h2 := II_congr_coupling (show κ * ‖w‖ ^ 2 = K' by rw [hwn2, hKm]) hKw hK (FullMass.unitDir w) n
    rw [hud] at h1 h2
    have h3 : II hκ w n = ‖w‖ ^ 2 * II hKw v n := h1
    rw [h3, h2, hF0 n hn, mul_zero]
  have hH : OneH1 w := oneH1_of_finite_masses hκ hR w F hF1
  rw [← hud]
  exact oneH1_unitDir' hH

/-- The unit profiles of a finite-action field are `H¹`, supported in `F`, with the printed positivity. -/
theorem profile_facts (hκ : 0 < κ) (hR : Reg015Input L κ hκ) (u : L2T L) (F : Finset ℤ)
    (hF : ∀ n, n ∈ F ↔ 0 < (RootIndexedMasses.masses hκ u).1 n) (hK : 0 < κ * ‖u‖ ^ 2) (v : L2T L)
    (hv : ‖v‖ = 1) (hvI : ∀ n, II hK v n = (RootIndexedMasses.masses hκ u).1 n / ‖u‖ ^ 2) :
    OneH1 v ∧ (∀ n, n ∉ F → II hK v n = 0) ∧ (∀ n ∈ F, 0 < II hK v n) := by
  have hu2 : 0 < ‖u‖ ^ 2 := by
    by_contra h
    have : ‖u‖ ^ 2 = 0 := le_antisymm (not_lt.1 h) (sq_nonneg _)
    rw [this, mul_zero] at hK
    exact lt_irrefl _ hK
  have hxF : ∀ n, n ∉ F → II hK v n = 0 := by
    intro n hn
    rw [hvI n]
    have h0 : (RootIndexedMasses.masses hκ u).1 n = 0 := by
      by_contra hne
      exact hn ((hF n).2 (lt_of_le_of_ne ((RootIndexedMasses.root_indexed_masses_proved_clauses hκ u).2.1 n)
        (Ne.symm hne)))
    rw [h0, zero_div]
  refine ⟨oneH1_of_scaled hκ hR hu2 hK rfl v hv F hxF, hxF, fun n hn => ?_⟩
  rw [hvI n]
  exact div_pos ((hF n).1 hn) hu2

/-- The quantum-data witness: every such unit profile carries an actual-gap datum (accepted R-1E0C40B3
`ActualGapDataR26.data_exists`, applicable because the profile is a unit `H¹` field). -/
theorem data_witness (hκ : 0 < κ) (hR : Reg015Input L κ hκ) (u : L2T L) (F : Finset ℤ)
    (hF : ∀ n, n ∈ F ↔ 0 < (RootIndexedMasses.masses hκ u).1 n) (hK : 0 < κ * ‖u‖ ^ 2) (v : L2T L)
    (hv : ‖v‖ = 1) (hvI : ∀ n, II hK v n = (RootIndexedMasses.masses hκ u).1 n / ‖u‖ ^ 2) :
    Nonempty (Data hK v) :=
  ActualGapDataR26.data_exists hK v hv (profile_facts hκ hR u F hF hK v hv hvI).1

/-- **`HD` of `stageD_of_derivatives`, proved**: the two printed derivative facts at every finite positive action
vector, from the chart. -/
theorem quantumDerivatives_of_chart {Φ : L2T L → K} (hκ : 0 < κ) (hR : Reg015Input L κ hκ)
    (hΦ : PrintedChart hκ Φ) :
    ∀ (u : L2T L) (F : Finset ℤ), F.Nonempty →
      (∀ n, n ∈ F ↔ 0 < (RootIndexedMasses.masses hκ u).1 n) →
      ∀ (hK : 0 < κ * ‖u‖ ^ 2) (v : L2T L), ‖v‖ = 1 →
      (∀ n, II hK v n = (RootIndexedMasses.masses hκ u).1 n / ‖u‖ ^ 2) →
      ∀ D : Data hK v, QuantumDerivatives (κ * ‖u‖ ^ 2) hK v D F := by
  intro u F hFne hF hK v hv hvI D
  have hAv : Avail L F := fun K' hK' x' hx0 hxF hx1 =>
    exists_profile hκ hΦ.symp hΦ.moduli hR F K' hK' x' hx0 hxF hx1
  obtain ⟨hH, hxF, hpos⟩ := profile_facts hκ hR u F hF hK v hv hvI
  refine ⟨fun a b ha hb hba => ?_, ?_⟩
  · exact REF88QuantumLine.line_derivative hAv hK hv hH D ha hb hba hxF (hpos a ha) (hpos b hb)
  · exact REF88QuantumCouple.coupling_derivative hAv hK hv hH D hxF

/-- **STAGE D.**  The conclusions of `stageC` (same `ν`), together with the printed frequency formula
`ν_n(a) = ℰ(K,x) + 𝒯(K,x) + ∑_{j∈F} x_j ω_{nj}(K,x)` for every finite positive action vector (every unit profile `v`
with the indexed probabilities `a/m` at `K = κ m`, every actual-gap datum `D`).  Hypotheses: exactly those of
`REF88StageC.stageC`. -/
theorem stageD {Φ : L2T L → K} (hκ : 0 < κ) (hR : Reg015Input L κ hκ)
    (hΦ : PrintedChartLocal hκ Φ) :
    (∃ ν : ℤ → ActionTorus.PosL1 → ℝ,
      (∀ (u : L2T L) (t : ℝ) (n : ℤ), 0 < (RootIndexedMasses.masses hκ u).1 n →
        Φ (flowMap hκ.le u t) n =
          Complex.exp (-Complex.I * ((t * ν n (RootIndexedMasses.masses hκ u) : ℝ) : ℂ)) *
            Φ u n) ∧
      (∀ (u : L2T L) (t : ℝ) (n : ℤ), (RootIndexedMasses.masses hκ u).1 n = 0 →
        Φ (flowMap hκ.le u t) n = 0) ∧
      (∀ (u : L2T L) (n : ℤ), 0 < (RootIndexedMasses.masses hκ u).1 n → ∀ ν' : ℝ,
        (∀ t : ℝ, Φ (flowMap hκ.le u t) n =
          Complex.exp (-Complex.I * ((t * ν' : ℝ) : ℂ)) * Φ u n) →
          ν' = ν n (RootIndexedMasses.masses hκ u)) ∧
      (∀ n : ℤ, ContinuousOn (ν n) {a : ActionTorus.PosL1 | 0 < a.1 n}) ∧
      (∀ a : ActionTorus.PosL1, ∀ z ∈ ActionTorus.actionTorus a, ∀ s t : ℝ,
        chartFlow hΦ.symp hκ.le t z ∈ ActionTorus.actionTorus a ∧ chartFlow hΦ.symp hκ.le 0 z = z ∧
        chartFlow hΦ.symp hκ.le (s + t) z = chartFlow hΦ.symp hκ.le s (chartFlow hΦ.symp hκ.le t z) ∧
        Continuous (fun t : ℝ => chartFlow hΦ.symp hκ.le t z)) ∧
      (∀ w : ℤ → ℝ, (∀ n, 0 ≤ w n) → ∀ z : K, (Summable fun n => w n * ‖z n‖ ^ 2) →
        (∀ t : ℝ, ∑' n, w n * ‖chartFlow hΦ.symp hκ.le t z n‖ ^ 2 = ∑' n, w n * ‖z n‖ ^ 2) ∧
        ∀ t0 : ℝ, Tendsto (fun t : ℝ => ∑' n, w n * ‖chartFlow hΦ.symp hκ.le t z n -
          chartFlow hΦ.symp hκ.le t0 z n‖ ^ 2) (𝓝 t0) (𝓝 0))
      ∧ (∀ (u : L2T L) (F : Finset ℤ), F.Nonempty →
        (∀ n, n ∈ F ↔ 0 < (RootIndexedMasses.masses hκ u).1 n) →
        ∀ (hK : 0 < κ * ‖u‖ ^ 2) (v : L2T L), ‖v‖ = 1 →
        (∀ n, QuantumNLS.F04SelBand.II hK v n = (RootIndexedMasses.masses hκ u).1 n / ‖u‖ ^ 2) →
        Nonempty (QuantumNLS.ActualGapDataR26.Data hK v) ∧
        ∀ D : QuantumNLS.ActualGapDataR26.Data hK v,
        ∀ n ∈ F, ν n (RootIndexedMasses.masses hκ u) =
          QuantumNLS.REF88QuantumDef.qEnergy (QuantumNLS.F04SelBand.Mu hK v) +
          QuantumNLS.REF88QuantumDef.qT D.bd D.F +
          ∑ j ∈ F, QuantumNLS.F04SelBand.II hK v j * D.omega n j)) ∧
    (∀ (s : ℝ) (hs : 0 ≤ s), ∃ e : H02 L s ≃ₜ h02 L s,
      ∀ u : H02 L s, toK hs (e u) = Φ (H02.toL2 hs u)) ∧
    (∀ (u : L2T L), (∃ F : Finset ℤ, ∀ n, n ∉ F → (RootIndexedMasses.masses hκ u).1 n = 0) →
      ∀ (s : ℝ), 0 ≤ s → MemHsLp L s u)
  := by
  have hΦ' : PrintedChart hκ Φ := printedChart_of_local hκ hΦ
  obtain ⟨⟨ν, h1, h2, h3, h4, h5, h6, h7⟩, hS, hFin⟩ :=
    stageD_of_derivatives hκ hR hΦ' (quantumDerivatives_of_chart hκ hR hΦ')
  refine ⟨⟨ν, h1, h2, h3, h4, h5, h6, ?_⟩, hS, hFin⟩
  intro u F hFne hF hK v hv hvI
  exact ⟨data_witness hκ hR u F hF hK v hv hvI, fun D n hn => h7 u F hFne hF hK v hv hvI D n hn⟩

end QuantumNLS.REF88StageD

#print axioms QuantumNLS.REF88StageD.oneH1_of_scaled
#print axioms QuantumNLS.REF88StageD.data_witness
#print axioms QuantumNLS.REF88StageD.quantumDerivatives_of_chart
#print axioms QuantumNLS.REF88StageD.stageD
