import Mathlib
import QuantumNLS.REF88EnergyContour
import QuantumNLS.RootEnergyMoment
import QuantumNLS.RootIndexedMasses
import QuantumNLS.RootScalarUniquenessR28

/-!
# REF88EnergyBound: the contour energy `E_F`, `H_κ ≥ E_F`, equality at the base point (R-EF8C2837)

Source: `source-text/chapters/global/physical_cubic.tex`, proof, paragraph "Bounded contour energies near
arbitrary mass" (printed lines 38 to 77):

  "The residue identity and positivity give, for every `H¹` field in that neighborhood,
   `H_κ(u) := ∫(|u'|²+κ|u|⁴) = ∫_ℝ x² dM_{κ,u}(x) ≥ E_F(u)`.  At `u_*` equality holds because all other
   indexed masses are zero."

`contourEnergy σ F v = ∑_{j∈F} ∫_{(σ(j-1),σ(j))} t² dM_{κ,v}(t)`; at `σ = sep u_*` this is the printed
`E_F(v) = ∑_{j∈F} (2πi)⁻¹ ∮_{Γ_j} z² G_v(z) dz` (REF88EnergyContour: `analyticAt_cellEnergy`), valid
wherever the circles are valid.  Here:

* `analyticAt_contourEnergy`: `E_F` is real analytic at `u_*` (finite sum of the accepted cell energies).
* `contourEnergy_le`: `E_F(v) ≤ ∫ t² dM_v = H_κ(v)` for every `H¹` field `v` (disjoint cells, `t² ≥ 0`,
  accepted `RootEnergyMoment.root_energy_moment` `∫ x² dM = H_κ`).
* `contourEnergy_eq_at_base`: if `u_*` is `H¹` with all indexed masses outside `F` zero then
  `E_F(u_*) = H_κ(u_*)` (all mass of `M_{u_*}` lies in the cells of `F`).
* `contourEnergy_eq_of_masses`: `E_F(v)` depends only on the indexed masses of `v` (accepted R-063C168E
  scalar uniqueness `M_{κ,u} = M_{κ,v}` when `I_n(u) = I_n(v)`), i.e. only on the action sequence.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section

open Set Filter Topology MeasureTheory

namespace QuantumNLS.REF88EnergyBound

open PhysicalTensor (L2T)
open QuantumNLS.REF88EnergyContour
open QuantumNLS.ProductEnergyPreparation (OneH1)

variable {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ)

/-- `E_F(v) = ∑_{j∈F} ∫_{(σ(j-1),σ(j))} t² dM_{κ,v}`. -/
def contourEnergy (σ : ℤ → ℝ) (F : Finset ℤ) (v : L2T L) : ℝ :=
  ∑ j ∈ F, cellEnergy hκ (σ (j - 1)) (σ j) v

theorem analyticAt_contourEnergy (F : Finset ℤ) (u : L2T L) :
    AnalyticAt ℝ (contourEnergy hκ (sep hκ u) F) u := by
  unfold contourEnergy
  have : ∀ j ∈ F, AnalyticAt ℝ (fun v : L2T L => cellEnergy hκ (sep hκ u (j - 1)) (sep hκ u j) v) u :=
    fun j _ => analyticAt_cellEnergy hκ j u
  exact Finset.analyticAt_fun_sum F this

theorem sep_strictMono (u : L2T L) : StrictMono (sep hκ u) :=
  (PhysicalSourceFinal.sourceFacts hκ u).phase.separator_strictMono

theorem cells_pairwiseDisjoint {σ : ℤ → ℝ} (hσ : StrictMono σ) (F : Finset ℤ) :
    (↑F : Set ℤ).PairwiseDisjoint (fun j => Ioo (σ (j - 1)) (σ j)) := by
  intro j _ k _ hjk
  rw [Function.onFun, Set.disjoint_left]
  intro t htj htk
  rcases lt_or_gt_of_ne hjk with h | h
  · have : σ j ≤ σ (k - 1) := hσ.monotone (by omega)
    linarith [htj.2, htk.1]
  · have : σ k ≤ σ (j - 1) := hσ.monotone (by omega)
    linarith [htk.2, htj.1]

theorem contourEnergy_eq_setIntegral {σ : ℤ → ℝ} (hσ : StrictMono σ) (F : Finset ℤ) (v : L2T L)
    (hI : Integrable (fun t : ℝ => t ^ 2) (PhysicalQuantumMeasure.measure hκ v)) :
    contourEnergy hκ σ F v =
      ∫ t in ⋃ j ∈ F, Ioo (σ (j - 1)) (σ j), t ^ 2 ∂(PhysicalQuantumMeasure.measure hκ v) := by
  unfold contourEnergy cellEnergy
  rw [integral_biUnion_finset F (fun j _ => measurableSet_Ioo) (cells_pairwiseDisjoint hσ F)
    (fun j _ => hI.integrableOn)]

/-- **`E_F ≤ H_κ`**: the contour energy of disjoint cells is bounded by the full second moment. -/
theorem contourEnergy_le {σ : ℤ → ℝ} (hσ : StrictMono σ) (F : Finset ℤ) (v : L2T L)
    (hI : Integrable (fun t : ℝ => t ^ 2) (PhysicalQuantumMeasure.measure hκ v)) :
    contourEnergy hκ σ F v ≤ ∫ t, t ^ 2 ∂(PhysicalQuantumMeasure.measure hκ v) := by
  rw [contourEnergy_eq_setIntegral hκ hσ F v hI]
  exact setIntegral_le_integral hI (Eventually.of_forall fun t => sq_nonneg t)

/-- The moment identity of the accepted R-484B3F6D on the physical measure. -/
theorem moment_of_oneH1 (v : L2T L) (hH : OneH1 v) :
    Integrable (fun t : ℝ => t ^ 2) (PhysicalQuantumMeasure.measure hκ v) ∧
      (∫ t, t ^ 2 ∂(PhysicalQuantumMeasure.measure hκ v)) =
        ChargeEnergy.energyH1 κ (v : AddCircle L → ℂ) := by
  have h := RootEnergyMoment.root_energy_moment hκ v hH
  rw [PhysicalL2Normalization.measure_eq_Mmeas]
  exact ⟨h.1, h.2.1⟩

/-- `E_F(v) ≤ H_κ(v)` for every `H¹` field. -/
theorem contourEnergy_le_energy {σ : ℤ → ℝ} (hσ : StrictMono σ) (F : Finset ℤ) (v : L2T L)
    (hH : OneH1 v) :
    contourEnergy hκ σ F v ≤ ChargeEnergy.energyH1 κ (v : AddCircle L → ℂ) := by
  obtain ⟨hI, he⟩ := moment_of_oneH1 hκ v hH
  rw [← he]
  exact contourEnergy_le hκ hσ F v hI

/-- At the base point all the mass sits in the cells of `F`, so `E_F(u_*) = H_κ(u_*)`. -/
theorem contourEnergy_eq_at_base (u : L2T L) (F : Finset ℤ)
    (hF : ∀ n, n ∉ F → (RootIndexedMasses.masses hκ u).1 n = 0)
    (hI : Integrable (fun t : ℝ => t ^ 2) (PhysicalQuantumMeasure.measure hκ u)) :
    contourEnergy hκ (sep hκ u) F u = ∫ t, t ^ 2 ∂(PhysicalQuantumMeasure.measure hκ u) := by
  have hσ := sep_strictMono hκ u
  rw [contourEnergy_eq_setIntegral hκ hσ F u hI]
  set μ := PhysicalQuantumMeasure.measure hκ u with hμ
  set S : Set ℝ := ⋃ j ∈ F, Ioo (sep hκ u (j - 1)) (sep hκ u j) with hS
  have hSm : MeasurableSet S := Finset.measurableSet_biUnion F fun j _ => measurableSet_Ioo
  obtain ⟨hmass, -, hsum, htot, -⟩ := RootIndexedMasses.root_indexed_masses_proved_clauses hκ u
  -- mass of the cells in `F`
  have hcell : ∀ j, μ (Ioo (sep hκ u (j - 1)) (sep hκ u j)) = ENNReal.ofReal ((RootIndexedMasses.masses hκ u).1 j) := by
    intro j
    have h1 := hmass j
    rw [h1]
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have hμS : μ S = ENNReal.ofReal (∑ j ∈ F, (RootIndexedMasses.masses hκ u).1 j) := by
    rw [hS, measure_biUnion_finset (cells_pairwiseDisjoint hσ F) (fun j _ => measurableSet_Ioo)]
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => (RootIndexedMasses.masses hκ u).2 j)]
    exact Finset.sum_congr rfl fun j _ => hcell j
  have hsumF : ∑ j ∈ F, (RootIndexedMasses.masses hκ u).1 j = ‖u‖ ^ 2 := by
    rw [← htot]
    exact (tsum_eq_sum (fun n hn => hF n hn)).symm
  have hμu : μ univ = ENNReal.ofReal (‖u‖ ^ 2) := PhysicalQuantumMeasure.measure_univ hκ u
  have hμSu : μ S = μ univ := by rw [hμS, hsumF, hμu]
  have hcompl : μ Sᶜ = 0 := by
    have := measure_add_measure_compl (μ := μ) hSm
    rw [hμSu] at this
    have hfin : μ univ ≠ ⊤ := measure_ne_top _ _
    have h2 : μ univ + μ Sᶜ = μ univ + 0 := by rw [add_zero]; exact this
    exact (ENNReal.add_right_inj hfin |>.mp h2)
  have hae : ∀ᵐ t ∂μ, t ∈ S := by
    rw [ae_iff]
    exact hcompl
  rw [Measure.restrict_eq_self_of_ae_mem hae]

/-- `E_F(v)` depends only on the indexed masses of `v` (scalar uniqueness R-063C168E: equal indexed
masses give equal quantum measures). -/
theorem contourEnergy_eq_of_masses (σ : ℤ → ℝ) (F : Finset ℤ) {u v : L2T L}
    (h : ∀ n, (RootIndexedMasses.masses hκ u).1 n = (RootIndexedMasses.masses hκ v).1 n) :
    contourEnergy hκ σ F u = contourEnergy hκ σ F v := by
  have hm := (RootScalarUniquenessR28.root_scalar_uniqueness (L := L) hκ).1 u v h
  unfold contourEnergy cellEnergy
  rw [hm]

/-- The selected separators depend only on the quantum measure, hence only on the indexed masses. -/
theorem sep_eq_of_masses {u v : L2T L}
    (h : ∀ n, (RootIndexedMasses.masses hκ u).1 n = (RootIndexedMasses.masses hκ v).1 n) :
    sep hκ u = sep hκ v := by
  have hm := (RootScalarUniquenessR28.root_scalar_uniqueness (L := L) hκ).1 u v h
  funext n
  exact RootIndexedMasses.separator_eq_of_measure_eq hκ hm n

/-- Analyticity of `E_F` at any `u'` whose separators equal those of the base field `u`. -/
theorem analyticAt_contourEnergy_of_sep (F : Finset ℤ) {u u' : L2T L} (h : sep hκ u' = sep hκ u) :
    AnalyticAt ℝ (contourEnergy hκ (sep hκ u) F) u' := by
  rw [← h]
  exact analyticAt_contourEnergy hκ F u'

#print axioms analyticAt_contourEnergy
#print axioms contourEnergy_le_energy
#print axioms contourEnergy_eq_at_base
#print axioms contourEnergy_eq_of_masses
#print axioms sep_eq_of_masses

end QuantumNLS.REF88EnergyBound
