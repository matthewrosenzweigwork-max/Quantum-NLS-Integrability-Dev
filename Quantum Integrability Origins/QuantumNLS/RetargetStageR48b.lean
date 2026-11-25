import QuantumNLS.RetargetPropagationR48b
import QuantumNLS.RetargetScalarR48b
import QuantumNLS.RetargetScheduleR48b

/-! Simultaneous seed and action tests on one finite label stage with the
literal physical product vectors and the actual quantum-derived chart. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false
noncomputable section
open Set Filter Topology
open scoped ComplexConjugate ENNReal

namespace QuantumNLS.RetargetStageR48b
open PhysicalTensor BetheCoefficientTransform Occupation OccupationHilbert FullOccupationAffinity
open FiniteCellSupport FiniteCellGauge
open DynSeedClassicalR47b RetargetUniformSeedR48b RetargetEdgeR48b RetargetCellR48b
open RetargetWeightsR48b
open Def044D1SpectralR51a (basis)
variable {L κ : ℝ} [Fact (0 < L)]

def coefficients (hκ : 0 < κ) (n : ℕ) (u : L2T L) : H (n+1) :=
  J (basis hκ n) (HighMomentsOps.wvec (n+1) u)

def coordinate (hκ : 0 < κ) (u : L2T L) (a : ℤ) : ℂ :=
  (Def021ChartR41b.chart L κ hκ).Φ u a

theorem coefficients_unit (hκ : 0 < κ) (n : ℕ) (u : L2T L) (hu : ‖u‖ = 1) :
    ‖coefficients hκ n u‖ = 1 := by
  unfold coefficients
  rw [LinearIsometryEquiv.norm_map]
  change ‖(TensorCarrier.htpow (n+1) u : TensorCarrier.HilbertTensorPower ℂ (L2T L) (n+1))‖ = 1
  simp [TensorCarrier.norm_htpow, hu]

theorem coordinate_le_one (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (a : ℤ) :
    ‖coordinate hκ u a‖ ≤ 1 := by
  let C := Def021ChartR41b.chart L κ hκ
  have h : ‖C.Φ u‖ = 1 := (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    ((C.norm u).trans (by rw [hu]))
  exact (lp.norm_apply_le_norm (by norm_num) (C.Φ u) a).trans_eq h

theorem count_coordinates (hκ : 0 < κ) (n : ℕ) (a : ℤ) :
    inCoefficients (basis (L := L) hκ n)
      (Prop010ContourBindingR11.B L hκ (Nat.succ_pos n) a) = E (n+1) a a := by
  let b := basis (L := L) hκ n
  let B := Prop010ContourBindingR11.B L hκ (Nat.succ_pos n) a
  have hE : E (n+1) a a = weight (n+1) a a := by
    apply ContinuousLinearMap.ext
    intro v
    apply lp.ext
    funext d
    change E (n+1) a a v d = weight (n+1) a a v d
    rw [E_diag_apply]
    rfl
  rw [hE]
  apply ExactShiftResidual.ext_single
  intro m
  let i := (marrArr (n+1)).symm m
  have hi : marrArr (n+1) i = m := (marrArr (n+1)).apply_symm_apply m
  have hb : B (b i) = (coef (n+1) a a (marrArr (n+1) i).1 : ℂ) • b i := by
    rw [coef_diag]
    exact Prop010ContourBindingR11.B_basis L hκ (Nat.succ_pos n) a i
  have hc : inCoefficients b B (J b (b i)) =
      (coef (n+1) a a (marrArr (n+1) i).1 : ℂ) • J b (b i) := by
    rw [inCoefficients_apply, LinearIsometryEquiv.symm_apply_apply, hb, map_smul]
  rw [J_basis] at hc
  have hw := weight_single (n+1) a a (marrArr (n+1) i)
  have he := hc.trans hw.symm
  simpa only [hi, single_classical] using he

theorem eventual_actions (hκ : 0 < κ) (R : ℝ) (I : Finset ℤ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ u ∈ R52CFCompact.profileClass L R, ∀ a : ↥I,
      ‖E (n+1) a.1 a.1 (coefficients hκ n u) -
        ((‖coordinate hκ u a.1‖^2 : ℝ) : ℂ) • coefficients hκ n u‖ ≤ δ := by
  have hall : ∀ᶠ n in atTop, ∀ a : ↥I, ∀ u ∈ R52CFCompact.profileClass L R,
      ‖E (n+1) a.1 a.1 (coefficients hκ n u) -
        ((‖coordinate hκ u a.1‖^2 : ℝ) : ℂ) • coefficients hκ n u‖ ≤ δ := by
    rw [Filter.eventually_all]
    intro a
    obtain ⟨N₀, hN₀⟩ := (R52CFMain.finite_count_propagation L hκ I R 1 0 0).2 a.1 δ hδ
    filter_upwards [eventually_ge_atTop N₀] with n hn
    intro u hu
    have h := hN₀ (n+1) (Nat.succ_pos n) (hn.trans (Nat.le_succ _)) u hu
    have ha : ‖coordinate hκ u a.1‖^2 = RootMassInvolutionR8.mass hκ a.1 u :=
      (Def021ChartR41b.chart L κ hκ).actions u a.1
    rw [ha]
    change ‖E (n+1) a.1 a.1 (J (basis hκ n) (HighMomentsOps.wvec (n+1) u)) -
      _ • J (basis hκ n) (HighMomentsOps.wvec (n+1) u)‖ ≤ δ
    rw [← count_coordinates (L := L) hκ n a.1, residual_inCoefficients]
    simpa only [sub_apply, smul_apply, one_apply_eq_self] using h
  filter_upwards [hall] with n hn
  exact fun u hu a => hn a u hu

theorem eventual_completed_seeds (hκ : 0 < κ) (R : ℝ) (I : Finset ℤ) (hI : 0 < I.card)
    (ell : ℕ) (hell : 0 < ell) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n in atTop, ∃ c : SelectedSeeds I (n+1), ∀ u ∈ R52CFCompact.profileClass L R,
      let w := fun a : ↥I => coordinate hκ u a.1
      let g := coefficients hκ n u
      ∀ (a b : ℤ) (hab : a ≠ b), a ∈ FiniteCellFinal.good I ell w →
        b ∈ FiniteCellFinal.good I ell w →
        ‖seedTransfer (extendSeeds I c) a b hab g -
          ((FiniteCellFinal.phases I w a).1 * conj (FiniteCellFinal.phases I w b).1) • g‖ ≤ η / I.card := by
  classical
  let s₀ := (1 : ℝ) / (2 * (ell : ℝ))
  let e := s₀ * (η / (I.card : ℝ))
  have hs₀ : 0 < s₀ := by dsimp [s₀]; positivity
  have he : 0 < e := mul_pos hs₀ (div_pos hη (Nat.cast_pos.mpr hI))
  have hfull := RetargetPropagationR48b.uniform_angles (L := L) hκ R
  let P := {p : ↥I × ↥I // p.1.1 < p.2.1}
  have hfamily : ∀ᶠ n in atTop, ∀ p : P,
      ∃ c : Donor (n+1) p.1.1.1 → ℂ, ∀ u ∈ R52CFCompact.profileClass L R,
        let z := coordinate hκ u p.1.1.1
        let w := coordinate hκ u p.1.2.1
        let g := coefficients hκ n u
        let ζ := pairPhase z w
        let s := Real.sqrt (‖z‖^2 * ‖w‖^2)
        s * ‖completedSeed p.1.1.1 p.1.2.1 c g - ζ.1 • g‖ ≤ e ∧
          s * ‖(completedSeed p.1.1.1 p.1.2.1 c).adjoint g - conj ζ.1 • g‖ ≤ e := by
    rw [Filter.eventually_all]
    intro p
    filter_upwards [eventual_seed hκ R p.1.1.1 p.1.2.1 p.2.ne hfull e he] with n hn
    obtain ⟨A, hA, herr⟩ := hn
    obtain ⟨c, hc⟩ := graded_polar_bounds (basis hκ n) A _ _ p.2.ne hA
    refine ⟨c, ?_⟩
    intro u hu
    let ζ := pairPhase (coordinate hκ u p.1.1.1) (coordinate hκ u p.1.2.1)
    let s := Real.sqrt (‖coordinate hκ u p.1.1.1‖^2 * ‖coordinate hκ u p.1.2.1‖^2)
    have hs : (s : ℂ) * ζ.1 = DynSeedClassicalR47b.symbol hκ p.1.1.1 p.1.2.1 u :=
      pair_factor _ _
    have hh := hc (HighMomentsOps.wvec (n+1) u) ζ s (Real.sqrt_nonneg _)
    rw [hs] at hh
    exact ⟨hh.1.trans (herr u hu), hh.2.trans (herr u hu)⟩
  filter_upwards [hfamily] with n hn
  choose c hc using hn
  let data : SelectedSeeds I (n+1) := fun a b ha hb hab => c ⟨(⟨a,ha⟩, ⟨b,hb⟩), hab⟩
  refine ⟨data, ?_⟩
  intro u hu w g a b hab ha hb
  have haI := (Finset.mem_filter.mp ha).1
  have hbI := (Finset.mem_filter.mp hb).1
  have ha₀ : s₀ ≤ ‖w ⟨a,haI⟩‖^2 := by
    rw [← FiniteCellFinal.actions_selected I w ⟨a,haI⟩]
    exact (Finset.mem_filter.mp ha).2
  have hb₀ : s₀ ≤ ‖w ⟨b,hbI⟩‖^2 := by
    rw [← FiniteCellFinal.actions_selected I w ⟨b,hbI⟩]
    exact (Finset.mem_filter.mp hb).2
  rw [FiniteCellFinal.phases_selected I w ⟨a,haI⟩, FiniteCellFinal.phases_selected I w ⟨b,hbI⟩]
  change ‖seedTransfer (extendSeeds I data) a b hab g -
    (pairPhase (w ⟨a,haI⟩) (w ⟨b,hbI⟩)).1 • g‖ ≤ η / I.card
  have hscale {y s : ℝ} (hy : 0 ≤ y) (hs : s₀ ≤ s) (hyb : s*y ≤ e) : y ≤ η / I.card := by
    have hh := (mul_le_mul_of_nonneg_right hs hy).trans hyb
    exact (mul_le_mul_iff_of_pos_left hs₀).mp hh
  have hsab : s₀ ≤ Real.sqrt (‖w ⟨a,haI⟩‖^2 * ‖w ⟨b,hbI⟩‖^2) := by
    apply Real.le_sqrt_of_sq_le
    rw [pow_two]
    exact mul_le_mul ha₀ hb₀ hs₀.le (sq_nonneg _)
  by_cases hab' : a < b
  · let p : P := ⟨(⟨a,haI⟩, ⟨b,hbI⟩), hab'⟩
    have hbnd := (hc p u hu).1
    have hr : seedTransfer (extendSeeds I data) a b hab = completedSeed a b (c p) := by
      unfold seedTransfer completedSeed
      simp only [seedPhase, dite_eq_left hab', extendSeeds_selected I data a b haI hbI hab']
      rfl
    rw [hr]
    exact hscale (norm_nonneg _) hsab hbnd
  · have hba : b < a := by omega
    let p : P := ⟨(⟨b,hbI⟩, ⟨a,haI⟩), hba⟩
    have hbnd := (hc p u hu).2
    have hr : seedTransfer (extendSeeds I data) b a hab.symm = completedSeed b a (c p) := by
      unfold seedTransfer completedSeed
      simp only [seedPhase, dite_eq_left hba, extendSeeds_selected I data b a hbI haI hba]
      rfl
    rw [← seedTransfer_adjoint _ b a hab.symm, hr,
      phase_reverse (w ⟨b,hbI⟩) (w ⟨a,haI⟩)]
    rw [mul_comm] at hsab
    exact hscale (norm_nonneg _) hsab hbnd

end QuantumNLS.RetargetStageR48b

#print axioms QuantumNLS.RetargetStageR48b.eventual_actions
#print axioms QuantumNLS.RetargetStageR48b.eventual_completed_seeds

end

/-! Assemble the universal gauge and schedule on the tested smooth classes.
The parameter selected in each sector is one full-array scalar function. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false
noncomputable section
open Set Filter Topology
open scoped ComplexConjugate

namespace QuantumNLS.RetargetAssemblyR48b
open PhysicalTensor Occupation OccupationHilbert FullOccupationAffinity FiniteCellGauge
open RetargetAnglesR48b RetargetStageR48b RetargetWeightsR48b RetargetCellR48b RetargetTuneR48b
variable {L κ : ℝ} [Fact (0 < L)]

def stageBound (j : ℕ) : ℝ := ((j : ℝ) + 1)⁻¹

theorem stageBound_tendsto : Tendsto stageBound atTop (𝓝 0) := by
  change Tendsto (fun j : ℕ => ((j : ℝ) + 1)⁻¹) atTop (𝓝 0)
  simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

theorem labels_card (j : ℕ) (hj : 0 < j) : 2 ≤ (labels j).card := by
  have hpos : (0 : ℤ) < j := by exact_mod_cast hj
  apply Finset.one_lt_card.mpr
  refine ⟨0, (mem_labels j 0).2 (by simp), j, (mem_labels j j).2 (by simp), hpos.ne⟩

/-- The stage predicates quantify over the ball, both labels, and all complete
arrays only after the gauge has been fixed. -/
def Stage (hκ : 0 < κ) (j n : ℕ) (q : Arr (n+1) → Phase) : Prop :=
  ∀ u ∈ R52CFCompact.profileClass L j, ∀ a b : ↥(labels j),
    let g := coefficients hκ n u
    let z := coordinate hκ u a.1
    let w := coordinate hκ u b.1
    ‖cartesian q a.1 b.1 g - (z * conj w) • g‖ ≤ stageBound j ∧
    (a.1 ≠ b.1 → stageBound j ≤ ‖z‖^2 → stageBound j ≤ ‖w‖^2 →
      ‖FiniteCellGauge.W q a.1 b.1 g - (pairPhase z w).1 • g‖ ≤ stageBound j)

theorem stage_exists (hκ : 0 < κ) (j : ℕ) (hj : 0 < j) :
    ∀ᶠ n in atTop, ∃ q, Stage (L := L) hκ j n q := by
  let I := labels j
  let ε := stageBound j
  have hε : 0 < ε := by unfold ε stageBound; positivity
  have hI : 2 ≤ I.card := labels_card j hj
  obtain ⟨ell, δ, hell, hδ, hcut, hbudget⟩ := tune I ε ε hε hε
  filter_upwards [eventually_ge_atTop ell, eventual_actions (L := L) hκ j I δ hδ,
    eventual_completed_seeds (L := L) hκ j I (by omega) ell (by omega) δ hδ] with n hN ha hc
  obtain ⟨c, hc⟩ := hc
  let q := q_N I ell c
  refine ⟨q, ?_⟩
  intro u hu a b
  let w := fun i : ↥I => coordinate hκ u i.1
  let g := coefficients hκ n u
  have hN' : ell ≤ n+1 := hN.trans (Nat.le_succ _)
  have h := cell_cartesian I ell hI hell hN' c g w δ δ hδ.le hδ.le
    (coefficients_unit hκ n u hu.2.1) (fun i => coordinate_le_one hκ u hu.2.1 i.1)
    (ha u hu) (hc u hu)
  have hwhy : ((n+1 : ℕ) : ℝ)⁻¹ ≤ (ell : ℝ)⁻¹ :=
    inv_anti₀ (by exact_mod_cast (show 0 < ell by omega)) (by exact_mod_cast hN')
  refine ⟨(h.1 a b).trans ?_, fun hab hza hzb => ?_⟩
  · exact (show max δ (Real.sqrt (2*δ + ((n+1 : ℕ) : ℝ)⁻¹) +
        max (FiniteCellFinal.printedBound I ell δ δ) (2 * Real.sqrt (4 / (ell : ℝ)))) ≤ budget I ell δ from by
        unfold budget
        gcongr).trans hbudget.le
  · exact (h.2 a b hab (hcut.le.trans hza) (hcut.le.trans hzb)).trans
      ((phase_le_budget I ell δ).trans hbudget.le)

/-- The single stage choice applies to all fixed smooth radii simultaneously.
The final rough-profile passage is at the already fixed particle number. -/
theorem smooth_intermediate (hκ : 0 < κ) :
    ∃ (s : ℕ → ℕ) (q : ∀ n, Arr (n+1) → Phase),
      Monotone s ∧ Tendsto s atTop atTop ∧ ∀ n, 0 < s n → Stage (L := L) hκ (s n) n (q n) :=
  RetargetScheduleR48b.select_family (fun _ _ => phaseOne)
    (Stage (L := L) hκ) (stage_exists hκ)

end QuantumNLS.RetargetAssemblyR48b

#print axioms QuantumNLS.RetargetAssemblyR48b.smooth_intermediate

end

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (name, _) in env.constants.toList do
    if
        name.toString.startsWith "QuantumNLS.RetargetStageR48b." ||
        name.toString.startsWith "_private.QuantumNLS.RetargetStageR48b." ||
        name.toString.startsWith "QuantumNLS.RetargetAssemblyR48b." ||
        name.toString.startsWith "_private.QuantumNLS.RetargetAssemblyR48b." then
      pending := pending.push name
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    unless seen.contains name do
      seen := seen.insert name
      if (name.toString.splitOn "HeldGP14Tonelli").length > 1 then
        throwError "Rejected dependency: {name}"
      if let some info := env.find? name then
        match info with
        | .axiomInfo _ =>
          unless name == ``propext || name == ``Classical.choice || name == ``Quot.sound do
            throwError "Nonstandard dependency: {name}"
        | _ => pure ()
        pending := pending ++ info.type.getUsedConstants
        if let some value := info.value? (allowOpaque := true) then
          pending := pending ++ value.getUsedConstants
      else
        throwError "Missing dependency: {name}"
  Lean.logInfo m!"R48b aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only."
