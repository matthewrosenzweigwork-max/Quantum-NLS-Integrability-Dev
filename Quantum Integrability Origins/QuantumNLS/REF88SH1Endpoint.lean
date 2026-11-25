import QuantumNLS.REF88SH1Approximation
import QuantumNLS.REF88SSampleW2
import QuantumNLS.REF88SRescale
import QuantumNLS.REF88SNormalizedActions

/-! R-EF8C2837 item (iv): H¹ approximants -> actual samples -> endpoint hW2,
with effective coupling and all normalizations explicit. No empirical hW2 assumption.
The finite-frequency identity is item (iii), authored separately; this module does not assume it.
Author sol_multi round23; independent reviewer terra_review. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
namespace QuantumNLS.REF88SH1Endpoint
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Sobolev
open QuantumNLS.ActualGapDataR26 (Data)
open QuantumNLS.F04SelBand (Mu II)
open QuantumNLS.QuantileTransport (W2 empirical)
open QuantumNLS.BetheLabels (MArr arrRoots)
open QuantumNLS.REF88SQuantiles
variable {L κ : ℝ} [Fact (0 < L)]

/-- Concrete endpoint convergence from H¹ alone. This is the hW2 term required by the
accepted varying-coupling theorem, targeting the unit profile u/‖u‖ at K=κ‖u‖². -/
theorem H1_actual_endpoint (hκ : 0 < κ) (v : ℕ → H02 L 1) (u : H02 L 1)
    (hv : Tendsto v atTop (𝓝 u)) (hu : u.val ≠ 0) (hv0 : ∀ j, (v j).val ≠ 0)
    {a b : ℤ} (hab : a ≠ b)
    (ha : ∀ j, 0 < II hκ (v j).val a) (hb : ∀ j, 0 < II hκ (v j).val b) :
    ∃ (hK : 0 < κ * ‖u.val‖ ^ 2)
      (hKs : ∀ j, 0 < κ * ‖(v j).val‖ ^ 2)
      (D : ∀ j, Data (hKs j) (FullMass.unitDir (v j).val))
      (k : ℕ → ℕ) (η : ∀ n : ℕ, MArr (n + 1)),
      Monotone k ∧ Tendsto k atTop atTop ∧
      Tendsto (fun n => κ * ‖(v (k n)).val‖ ^ 2) atTop (𝓝 (κ * ‖u.val‖ ^ 2)) ∧
      Tendsto (fun n => RootOccupationLimit.occDist (hKs (k n))
        (FullMass.unitDir (v (k n)).val) (n + 1) (η n)) atTop (𝓝 0) ∧
      Tendsto (fun n => ∑' m : ℤ, |(((η n).1 m : ℕ) : ℝ) / ((n : ℝ) + 1) -
        II hK (FullMass.unitDir u.val) m|) atTop (𝓝 0) ∧
      Tendsto (fun n => W2 (empirical (n + 1)
        (arrRoots L ((κ * ‖(v (k n)).val‖ ^ 2) / ((n : ℝ) + 1)) (η n)))
          (Mu hK (FullMass.unitDir u.val))) atTop (𝓝 0) ∧
      Tendsto (fun n => F02Tightness.gap L (κ * ‖(v (k n)).val‖ ^ 2) a b (η n) -
        (D (k n)).omega a b) atTop (𝓝 0) := by
  classical
  let hK : 0 < κ * ‖u.val‖ ^ 2 := mul_pos hκ (sq_pos_of_pos (norm_pos_iff.2 hu))
  let hKs : ∀ j, 0 < κ * ‖(v j).val‖ ^ 2 := fun j => mul_pos hκ (sq_pos_of_pos (norm_pos_iff.2 (hv0 j)))
  let w (j : ℕ) := FullMass.unitDir (v j).val
  have hw : ∀ j, ‖w j‖ = 1 := fun j => FullMass.norm_unitDir (hv0 j)
  have hH : ∀ j, ProductEnergyPreparation.OneH1 (w j) := fun j =>
    REF88SRescale.oneH1_unitDir (oneH1 (v j))
  have hd : ∀ j, Nonempty (Data (hKs j) (w j)) := fun j =>
    ActualGapDataR26.data_exists (hKs j) (w j) (hw j) (hH j)
  let D : ∀ j, Data (hKs j) (w j) := fun j => Classical.choice (hd j)
  have hpa : ∀ j, 0 < II (hKs j) (w j) a := by
    intro j
    have hi := REF88QuantumDef.II_unitDir hκ (hv0 j) (hKs j) a
    change 0 < II (hKs j) (FullMass.unitDir (v j).val) a
    have hp : 0 < ‖(v j).val‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.2 (hv0 j))
    nlinarith [ha j]
  have hpb : ∀ j, 0 < II (hKs j) (w j) b := by
    intro j
    have hi := REF88QuantumDef.II_unitDir hκ (hv0 j) (hKs j) b
    change 0 < II (hKs j) (FullMass.unitDir (v j).val) b
    have hp : 0 < ‖(v j).val‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.2 (hv0 j))
    nlinarith [hb j]
  haveI : IsProbabilityMeasure (Mu hK (FullMass.unitDir u.val)) :=
    F04SelBand.Mu_prob hK _ (FullMass.norm_unitDir hu)
  have hμ : Tendsto (fun j => W2 (Mu (hKs j) (w j)) (Mu hK (FullMass.unitDir u.val)))
      atTop (𝓝 0) := by
    have h := normalized_W2 hκ hu hv0 hv
    simpa only [normalized_unitDir hκ hu hK, fun j => normalized_unitDir hκ (hv0 j) (hKs j)] using h
  obtain ⟨k,η,hmono,hk,hocc,hW,hgap⟩ := REF88SSampleW2.actual_diagonal_endpoint
    (fun j => κ * ‖(v j).val‖ ^ 2) hKs w hw hH D hab hpa hpb _ hμ
  have hL2 := ((H02.toL2 (L := L) (by norm_num : (0 : ℝ) ≤ 1)).continuous.tendsto u).comp hv
  have hcoupling : Tendsto (fun j => κ * ‖(v j).val‖ ^ 2) atTop (𝓝 (κ * ‖u.val‖ ^ 2)) :=
    (hL2.norm.pow 2).const_mul κ
  have hI := REF88SNormalizedActions.normalized_l1 hκ hu hv0 hL2 hK hKs
  have hη := REF88SNormalizedActions.occupations_to_target
    (fun n => hKs (k n)) (fun n => w (k n)) hK (FullMass.unitDir u.val) η hocc (hI.comp hk)
  exact ⟨hK,hKs,D,k,η,hmono,hk,hcoupling.comp hk,hocc,hη,hW,hgap⟩

/-- Positive limiting endpoint proportions make the donor occupation positive eventually. -/
theorem donor_eventually {K : ℝ} (hK : 0 < K) (u : L2T L)
    (η : ∀ n : ℕ, MArr (n + 1))
    (hη : Tendsto (fun n => ∑' m : ℤ, |(((η n).1 m : ℕ) : ℝ) / ((n : ℝ) + 1) - II hK u m|)
      atTop (𝓝 0)) {b : ℤ} (hb : 0 < II hK u b) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ (η n).1 b := by
  have ho := DetGapMain.occ_tendsto hK u η hη b
  filter_upwards [ho.eventually (lt_mem_nhds hb)] with n hn
  have hp : (0 : ℝ) < (η n).1 b := by
    have h := (lt_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).1 hn
    simpa only [zero_mul] using h
  exact_mod_cast hp

/-- The finitely many early arrays may be filled without changing any limit.
This supplies the all-n donor condition in VarFinal; no extra donor hypothesis is added. -/
theorem patch_donor {K : ℝ} (hK : 0 < K) (u : L2T L)
    (η : ∀ n : ℕ, MArr (n + 1))
    (hη : Tendsto (fun n => ∑' m : ℤ, |(((η n).1 m : ℕ) : ℝ) / ((n : ℝ) + 1) - II hK u m|)
      atTop (𝓝 0)) {b : ℤ} (hb : 0 < II hK u b) :
    ∃ p : ∀ n : ℕ, MArr (n + 1), (∀ n, 1 ≤ (p n).1 b) ∧
      ∀ᶠ n : ℕ in atTop, p n = η n := by
  classical
  let p : ∀ n : ℕ, MArr (n + 1) := fun n =>
    if 1 ≤ (η n).1 b then η n else ActualGapDataR26.singleArr (n + 1) b
  refine ⟨p,fun n => ?_,(donor_eventually hK u η hη hb).mono fun n hn => by simp [p,hn]⟩
  dsimp only [p]
  split_ifs with hn
  · exact hn
  · simp [ActualGapDataR26.singleArr]

#print axioms donor_eventually
#print axioms patch_donor
#print axioms H1_actual_endpoint
end QuantumNLS.REF88SH1Endpoint
