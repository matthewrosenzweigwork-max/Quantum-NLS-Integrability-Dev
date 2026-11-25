import QuantumNLS.CellLocalization
import QuantumNLS.RootOccupationLimit

/-! REG-003 `CC:limiting-cell-localization` (root_confinement.tex:142), unconditional.

`CellLocalization` (review record d0cf18de, read-only) is conditional on the identification
`hlab` of the limiting joint label with the indexed cell and omits the closure clause.  Here:
* `hlab` is discharged: the label function `n` supplied by PROP-002 (`weak_joint_limit_DEF043`,
  the joint-limit identification used in `RootOccupationDet`/`RootOccupationLimit`, R-E6DFC650)
  satisfies `n = k` a.e. on the `k`th indexed cell of `RootIndexedPhase`/`RootIndexedMasses`
  (`label_iff_cell`); the on-shell sequence with `nu_N => mu` is produced from the convergence
  in probability of `IsLimitingRapidityMeasure` (`exists_seq`);
* total mass `m = ‖u‖²` by the printed normalization (prop:root-full-mass): `M_u = m * mu'` for
  the unit direction at coupling `kappa m` (`measure_smul`), with the same boundary phase
  (`boundary_norm`) and hence the same separators and cells (`separator_norm`); zero mass is
  trivial;
* the closure clause: the closure of the positive-density part of the `n`th cell lies in the
  localization interval (`closure_clause`), via the continuous density of `RootDensityIdentification`;
* the named theorem `reg003`. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
namespace QuantumNLS.Reg003
open QuantumNLS.RootOccupationDet QuantumNLS.RootOccupationLimit QuantumNLS.LabelJointLimit
  QuantumNLS.LabelJointWeak QuantumNLS.LabelWeakJointLimit QuantumNLS.IndexedScalarMeasure
  QuantumNLS.IndexedScalarMeasureCuts
open QuantumNLS.BetheLabels (MArr)
open QuantumNLS.EmpiricalRapidity (bornMeasure)
open QuantumNLS.BulkResponseActual (physBasis empiricalProb IsLimitingRapidityMeasure)
open PhysicalTensor (L2T)

variable {L κ : ℝ} [Fact (0 < L)]

/-- The `n`th indexed cell `(a_{n-1}(u), a_n(u))`. -/
def cell (hκ : 0 < κ) (u : L2T L) (n : ℤ) : Set ℝ :=
  Ioo (RootIndexedPhase.separator hκ u (n - 1)) (RootIndexedPhase.separator hκ u n)

theorem cell_measurable (hκ : 0 < κ) (u : L2T L) (n : ℤ) : MeasurableSet (cell hκ u n) :=
  measurableSet_Ioo

theorem cell_disjoint (hκ : 0 < κ) (u : L2T L) :
    Pairwise (Function.onFun Disjoint (cell hκ u)) := by
  have hm := (PhysicalSourceFinal.sourceFacts hκ u).phase.separator_strictMono
  intro i j hij
  rw [Function.onFun, Set.disjoint_left]
  intro x hxi hxj
  simp only [cell, mem_Ioo] at hxi hxj
  rcases lt_or_gt_of_ne hij with h | h
  · have : RootIndexedPhase.separator hκ u i ≤ RootIndexedPhase.separator hκ u (j - 1) :=
      hm.monotone (by omega)
    linarith [hxi.2, hxj.1]
  · have : RootIndexedPhase.separator hκ u j ≤ RootIndexedPhase.separator hκ u (i - 1) :=
      hm.monotone (by omega)
    linarith [hxj.2, hxi.1]

/-- On a point where the integer label equals `θ/π`, the label is `k` exactly on the `k`th cell. -/
theorem label_iff_cell (hκ : 0 < κ) (u : L2T L) {n : ℝ → ℤ} {t : ℝ}
    (ht : (n t : ℝ) = indexLabel L κ (Prop026Bound.reG hκ u) t) (k : ℤ) :
    n t = k ↔ t ∈ cell hκ u k := by
  rw [Prop026Bound.label_eq] at ht
  have hpi := Real.pi_pos
  have hθ : RootIndexedPhase.theta hκ u t = (n t : ℝ) * Real.pi :=
    ((eq_div_iff hpi.ne').mp ht).symm
  have e1 : RootIndexedPhase.separator hκ u (k - 1) < t ↔
      (((k - 1 : ℤ) : ℝ) + 1 / 2) * Real.pi < RootIndexedPhase.theta hκ u t :=
    (PhysicalSourceFinal.sourceFacts hκ u).phase.separator_lt_iff t (k - 1)
  have e2 : t < RootIndexedPhase.separator hκ u k ↔
      RootIndexedPhase.theta hκ u t < ((k : ℝ) + 1 / 2) * Real.pi :=
    (PhysicalSourceFinal.sourceFacts hκ u).phase.lt_separator_iff t k
  simp only [cell, mem_Ioo]
  rw [e1, e2, hθ]
  push_cast
  constructor
  · intro h
    rw [h]
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    have a1 : (k : ℝ) - 1 / 2 < (n t : ℝ) := by
      by_contra hc
      push Not at hc
      nlinarith
    have a2 : (n t : ℝ) < (k : ℝ) + 1 / 2 := by
      by_contra hc
      push Not at hc
      nlinarith
    have b1 : k - 1 < n t := by
      have : ((k - 1 : ℤ) : ℝ) < (n t : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have b2 : n t < k + 1 := by
      have : (n t : ℝ) < ((k + 1 : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    omega

/-- The cells cover the quantum measure almost everywhere (the separators are countable and
the measure is atomless). -/
theorem cover_ae (hκ : 0 < κ) (u : L2T L) :
    ∀ᵐ t ∂(PhysicalQuantumMeasure.measure hκ u), ∃ k, t ∈ cell hκ u k := by
  have := PhysicalUnconditionalTrace.atomless hκ u
  have hnull : (PhysicalQuantumMeasure.measure hκ u)
      (range (RootIndexedPhase.separator hκ u)) = 0 :=
    (countable_range _).measure_zero _
  filter_upwards [compl_mem_ae_iff.2 hnull] with t ht
  have hpi := Real.pi_pos
  set x : ℝ := RootIndexedPhase.theta hκ u t / Real.pi - 1 / 2 with hx
  refine ⟨⌈x⌉, ?_⟩
  have e1 : RootIndexedPhase.separator hκ u (⌈x⌉ - 1) < t ↔
      (((⌈x⌉ - 1 : ℤ) : ℝ) + 1 / 2) * Real.pi < RootIndexedPhase.theta hκ u t :=
    (PhysicalSourceFinal.sourceFacts hκ u).phase.separator_lt_iff t (⌈x⌉ - 1)
  have e2 : t < RootIndexedPhase.separator hκ u ⌈x⌉ ↔
      RootIndexedPhase.theta hκ u t < ((⌈x⌉ : ℝ) + 1 / 2) * Real.pi :=
    (PhysicalSourceFinal.sourceFacts hκ u).phase.lt_separator_iff t ⌈x⌉
  simp only [cell, mem_Ioo]
  refine ⟨e1.2 ?_, e2.2 ?_⟩
  · have := Int.ceil_lt_add_one x
    push_cast
    have h2 : (⌈x⌉ : ℝ) - 1 < x := by linarith
    rw [hx] at h2
    have h3 : ((⌈x⌉ : ℝ) - 1 + 1 / 2) < RootIndexedPhase.theta hκ u t / Real.pi := by linarith
    rw [lt_div_iff₀ hpi] at h3
    exact h3
  · have h1 := Int.le_ceil x
    have hne : RootIndexedPhase.theta hκ u t ≠ ((⌈x⌉ : ℝ) + 1 / 2) * Real.pi := by
      intro h
      apply ht
      refine ⟨⌈x⌉, ?_⟩
      symm
      exact (PhysicalSourceFinal.sourceFacts hκ u).phase.separator_unique h
    refine lt_of_le_of_ne ?_ hne
    rw [hx] at h1
    have h3 : RootIndexedPhase.theta hκ u t / Real.pi ≤ (⌈x⌉ : ℝ) + 1 / 2 := by linarith
    rw [div_le_iff₀ hpi] at h3
    exact h3

/-! ### 1. An on-shell sequence with `nu_N => mu` -/

theorem exists_seq (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) :
    ∃ (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (B : ∀ k, OnShellBethe L κ (N k)),
      Tendsto N atTop atTop ∧ Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ) := by
  have hi := (BornConvergence.tendstoInProbabilityWeak_iff _ _ _).1 hμ
  have hpick : ∀ k : ℕ, ∃ N : ℕ, ∃ hN : 0 < N, k + 1 ≤ N ∧ ∃ B : OnShellBethe L κ N,
      levyProkhorovDist (rootP B hN).toMeasure μ.toMeasure ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have h := hi _ hk
    have h1 : ∀ᶠ N : ℕ in atTop, bornMeasure (physBasis L hκ N) u hu
        {m | 1 / ((k : ℝ) + 1) < levyProkhorovDist (empiricalProb L κ N m).toMeasure μ.toMeasure} <
          1 := h.eventually (gt_mem_nhds one_pos)
    obtain ⟨N, hN1, hNk⟩ := (h1.and (eventually_ge_atTop (k + 1))).exists
    have hNpos : 0 < N := by omega
    by_cases hex : ∃ m : MArr N, ¬ (1 / ((k : ℝ) + 1) <
        levyProkhorovDist (empiricalProb L κ N m).toMeasure μ.toMeasure)
    · obtain ⟨m, hm⟩ := hex
      obtain ⟨B, hB, -⟩ := exists_bridge (L := L) hκ hNpos m
      exact ⟨N, hNpos, hNk, B, by rw [hB]; exact not_lt.1 hm⟩
    · push Not at hex
      exfalso
      have : {m : MArr N | 1 / ((k : ℝ) + 1) <
          levyProkhorovDist (empiricalProb L κ N m).toMeasure μ.toMeasure} = univ :=
        eq_univ_of_forall hex
      rw [this, measure_univ] at hN1
      exact lt_irrefl _ hN1
  choose N hN hk B hd using hpick
  refine ⟨N, hN, B, ?_, ?_⟩
  · exact tendsto_atTop_mono (fun k => (Nat.le_succ k).trans (hk k)) tendsto_id
  · intro U hU
    obtain ⟨r, hr, hrU⟩ := exists_lp_ball μ U hU
    obtain ⟨K, hK⟩ := exists_nat_gt (1 / r)
    rw [Filter.mem_map, Filter.mem_atTop_sets]
    refine ⟨K, fun k hkK => hrU _ ?_⟩
    have hKk : (K : ℝ) ≤ k := by exact_mod_cast hkK
    have : 1 / r < (k : ℝ) + 1 := by linarith
    have h3 : 1 / ((k : ℝ) + 1) < r := (one_div_lt (by positivity) hr).2 this
    exact lt_of_le_of_lt (hd k) h3

/-! ### 2. Unit input: localization on the indexed cells -/

theorem loc_unit (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) (k : ℤ) :
    ∀ᵐ t ∂(μ : Measure ℝ), t ∈ cell hκ u k →
      t ∈ Icc (2 * Real.pi * k / L - 2 * Real.sqrt (κ / L))
        (2 * Real.pi * k / L + 2 * Real.sqrt (κ / L)) := by
  have hμe : (μ : Measure ℝ) = PhysicalQuantumMeasure.measure hκ u :=
    (Prop026Bound.physical_eq_limit hκ u hu hμ).symm
  obtain ⟨N, hN, B, hNtop, hconv⟩ := exists_seq hκ u hu hμ
  set S := Prop026Bound.scalarCuts hκ u hu with hS
  have hμS : (μ : Measure ℝ) = S.μ := hμe
  obtain ⟨⟨n, hnm, hnI⟩, hlim⟩ := weak_joint_limit_DEF043 S hconv hμS hNtop
  have hj := hlim n hnI
  have hnI' : ∀ᵐ t ∂(μ : Measure ℝ),
      (n t : ℝ) = indexLabel L κ (Prop026Bound.reG hκ u) t := by
    rw [hμS]; exact hnI
  have hlab : ∀ k : ℤ, ∀ᵐ t ∂(μ : Measure ℝ), t ∈ cell hκ u k → n t = k := by
    intro k
    filter_upwards [hnI'] with t ht hmem
    exact (label_iff_cell hκ u ht k).2 hmem
  have hcov : ∀ᵐ t ∂(μ : Measure ℝ), ∃ k, t ∈ cell hκ u k := by
    rw [hμe]; exact cover_ae hκ u
  have hL : 0 < L := Fact.out
  have h := CellLocalization.cell_localization hL hκ hnm hN B hj (cell := cell hκ u)
    (cell_measurable hκ u) (cell_disjoint hκ u) hcov hlab
  exact h.1 k

/-! ### 3. The printed normalization for total mass `m = ‖u‖²` -/

theorem kn_pos (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) : 0 < κ * ‖u‖ ^ 2 :=
  mul_pos hκ (pow_pos (norm_pos_iff.2 hu) 2)

theorem measure_smul (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) {μ' : ProbabilityMeasure ℝ}
    (hμ' : IsLimitingRapidityMeasure L (κ * ‖u‖ ^ 2) (kn_pos hκ hu) (FullMass.unitDir u)
      (FullMass.norm_unitDir hu) μ') :
    PhysicalQuantumMeasure.measure hκ u = ENNReal.ofReal (‖u‖ ^ 2) • (μ' : Measure ℝ) := by
  rw [PhysicalL2Normalization.measure_eq_Mmeas, FullMass.Mmeas_of_ne κ hu]
  congr 1
  apply congrArg (fun ν : ProbabilityMeasure ℝ => (ν : Measure ℝ))
  exact (FreeLimit.muKappa_spec (FullMass.unitDir u) (FullMass.norm_unitDir hu)
    (kn_pos hκ hu)).unique hμ'

theorem boundary_norm (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) {μ' : ProbabilityMeasure ℝ}
    (hμ' : IsLimitingRapidityMeasure L (κ * ‖u‖ ^ 2) (kn_pos hκ hu) (FullMass.unitDir u)
      (FullMass.norm_unitDir hu) μ') (x : ℝ) :
    PhysicalContinuousBoundary.boundary hκ u x =
      PhysicalContinuousBoundary.boundary (kn_pos hκ hu) (FullMass.unitDir u) x := by
  have hμe : (μ' : Measure ℝ) =
      PhysicalQuantumMeasure.measure (kn_pos hκ hu) (FullMass.unitDir u) :=
    (Prop026Bound.physical_eq_limit (kn_pos hκ hu) _ (FullMass.norm_unitDir hu) hμ').symm
  have hfun : SpatialTransfer.boundaryPhase L κ (PhysicalQuantumMeasure.measure hκ u) =
      SpatialTransfer.boundaryPhase L (κ * ‖u‖ ^ 2)
        (PhysicalQuantumMeasure.measure (kn_pos hκ hu) (FullMass.unitDir u)) := by
    funext z
    unfold SpatialTransfer.boundaryPhase
    have hc : EmpiricalRapidity.cauchyTransform (ENNReal.ofReal (‖u‖ ^ 2) • (μ' : Measure ℝ)) z =
        ((‖u‖ ^ 2 : ℝ) : ℂ) * EmpiricalRapidity.cauchyTransform (μ' : Measure ℝ) z := by
      unfold EmpiricalRapidity.cauchyTransform
      rw [integral_smul_measure, ENNReal.toReal_ofReal (sq_nonneg _), Complex.real_smul]
    rw [measure_smul hκ hu hμ', ← hμe, hc]
    push_cast
    ring
  have : NeBot (𝓝[PhysicalPhaseHolomorphic.upper] (x : ℂ)) := ComplexCosineBoundary.upper_neBot x
  have h1 := PhysicalContinuousBoundary.boundary_limit hκ u x
  have h2 := PhysicalContinuousBoundary.boundary_limit (kn_pos hκ hu) (FullMass.unitDir u) x
  rw [hfun] at h1
  exact tendsto_nhds_unique h1 h2

theorem separator_norm (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) {μ' : ProbabilityMeasure ℝ}
    (hμ' : IsLimitingRapidityMeasure L (κ * ‖u‖ ^ 2) (kn_pos hκ hu) (FullMass.unitDir u)
      (FullMass.norm_unitDir hu) μ') (n : ℤ) :
    RootIndexedPhase.separator hκ u n =
      RootIndexedPhase.separator (kn_pos hκ hu) (FullMass.unitDir u) n := by
  apply (PhysicalSourceFinal.sourceFacts (kn_pos hκ hu) (FullMass.unitDir u)).phase.separator_unique
  change (PhysicalContinuousBoundary.boundary (kn_pos hκ hu) (FullMass.unitDir u) _).re = _
  rw [← boundary_norm hκ hu hμ']
  exact (PhysicalSourceFinal.sourceFacts hκ u).phase.separator_spec n

theorem cell_norm (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) {μ' : ProbabilityMeasure ℝ}
    (hμ' : IsLimitingRapidityMeasure L (κ * ‖u‖ ^ 2) (kn_pos hκ hu) (FullMass.unitDir u)
      (FullMass.norm_unitDir hu) μ') (n : ℤ) :
    cell (kn_pos hκ hu) (FullMass.unitDir u) n = cell hκ u n := by
  simp only [cell, separator_norm hκ hu hμ']

/-- Localization of the full-mass measure on every indexed cell, `C = 2 sqrt(kappa m / L)`. -/
theorem loc_general (hκ : 0 < κ) (u : L2T L) (k : ℤ) :
    ∀ᵐ t ∂(PhysicalQuantumMeasure.measure hκ u), t ∈ cell hκ u k →
      t ∈ Icc (2 * Real.pi * k / L - 2 * Real.sqrt (κ * ‖u‖ ^ 2 / L))
        (2 * Real.pi * k / L + 2 * Real.sqrt (κ * ‖u‖ ^ 2 / L)) := by
  by_cases hu : u = 0
  · subst hu
    rw [PhysicalQuantumMeasure.measure_zero]
    simp
  · obtain ⟨μ', hμ'⟩ := RootMeasureExistence.exists_limiting_measure (kn_pos hκ hu)
      (FullMass.unitDir u) (FullMass.norm_unitDir hu)
    have h := loc_unit (kn_pos hκ hu) (FullMass.unitDir u) (FullMass.norm_unitDir hu) hμ' k
    rw [cell_norm hκ hu hμ'] at h
    rw [measure_smul hκ hu hμ']
    exact Measure.smul_absolutelyContinuous.ae_le h

/-! ### 4. The closure clause -/

theorem masses_pos_ne_zero (hκ : 0 < κ) {u : L2T L} {n : ℤ}
    (h : 0 < (RootIndexedMasses.masses hκ u).1 n) : u ≠ 0 := by
  rintro rfl
  rw [(RootIndexedMasses.root_indexed_masses_proved_clauses hκ (0 : L2T L)).1 n,
    PhysicalQuantumMeasure.measure_zero] at h
  simp at h

theorem closure_clause (hκ : 0 < κ) (u : L2T L) (n : ℤ)
    (hn : 0 < (RootIndexedMasses.masses hκ u).1 n) :
    closure (cell hκ u n ∩ {x | 0 < RootDensityIdentification.dens κ u x}) ⊆
      Icc (2 * Real.pi * n / L - 2 * Real.sqrt (κ * ‖u‖ ^ 2 / L))
        (2 * Real.pi * n / L + 2 * Real.sqrt (κ * ‖u‖ ^ 2 / L)) := by
  have hu := masses_pos_ne_zero hκ hn
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hxn
  set V : Set ℝ := cell hκ u n ∩ {x | 0 < RootDensityIdentification.dens κ u x} ∩
    (Icc (2 * Real.pi * n / L - 2 * Real.sqrt (κ * ‖u‖ ^ 2 / L))
      (2 * Real.pi * n / L + 2 * Real.sqrt (κ * ‖u‖ ^ 2 / L)))ᶜ with hV
  have hVo : IsOpen V := by
    refine (isOpen_Ioo.inter (isOpen_lt continuous_const
      (RootDensityIdentification.continuous_dens κ u))).inter isClosed_Icc.isOpen_compl
  have hxV : x ∈ V := ⟨hx, hxn⟩
  have hpos : 0 < (PhysicalQuantumMeasure.measure hκ u) V := by
    rw [RootDensityIdentification.root_density hκ hu, withDensity_apply _ hVo.measurableSet]
    have hmeas : Measurable fun t => ENNReal.ofReal (RootDensityIdentification.dens κ u t) :=
      ENNReal.measurable_ofReal.comp (RootDensityIdentification.continuous_dens κ u).measurable
    rw [lintegral_pos_iff_support hmeas]
    have hsub : V ⊆ Function.support fun t => ENNReal.ofReal (RootDensityIdentification.dens κ u t) := by
      intro y hy
      have : 0 < RootDensityIdentification.dens κ u y := hy.1.2
      simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact this
    calc 0 < volume V := hVo.measure_pos volume ⟨x, hxV⟩
      _ = (volume.restrict V) V := (Measure.restrict_apply_self _ _).symm
      _ ≤ _ := measure_mono hsub
  have hz : (PhysicalQuantumMeasure.measure hκ u) V = 0 := by
    have h := loc_general hκ u n
    rw [ae_iff] at h
    refine measure_mono_null ?_ h
    intro y hy
    exact fun hh => hy.2 (hh hy.1.1)
  exact absurd hz hpos.ne'

theorem support_sub_of_null {μ : Measure ℝ} {F : Set ℝ} (hF : IsClosed F) (h : μ Fᶜ = 0) :
    μ.support ⊆ F := by
  intro x hx
  by_contra hxF
  exact (Measure.notMem_support_iff_exists.2 ⟨Fᶜ, hF.isOpen_compl.mem_nhds hxF, h⟩) hx

/-! ### 5. REG-003 -/

/-- **REG-003 `CC:limiting-cell-localization` (root_confinement.tex:142).**  For every `u ∈ L²(𝕋_L)`
(mass `m = ‖u‖²`) and `κ > 0`, with `M_u = PhysicalQuantumMeasure.measure hκ u`, the indexed
cells `(a_{n-1}(u), a_n(u))` and masses `I_n(u) = RootIndexedMasses.masses hκ u`, and
`C = 2 sqrt(κ m / L)`:
(1) `M_u` restricted to the `n`th cell is supported in `[2πn/L − C, 2πn/L + C]`
(a.e. localization and support inclusion);
(2) closure clause: if `I_n(u) > 0` the closure of the positive-density part of the `n`th cell lies in
that interval (so both endpoints of its positive-density interval do);
(3) for every real `s ≥ 0` the two moment comparisons, in `[0, ∞]`. -/
theorem reg003 (hκ : 0 < κ) (u : L2T L) :
    (∀ n : ℤ, ∀ᵐ t ∂(PhysicalQuantumMeasure.measure hκ u), t ∈ cell hκ u n →
      t ∈ Icc (2 * Real.pi * n / L - 2 * Real.sqrt (κ * ‖u‖ ^ 2 / L))
        (2 * Real.pi * n / L + 2 * Real.sqrt (κ * ‖u‖ ^ 2 / L))) ∧
    (∀ n : ℤ, ((PhysicalQuantumMeasure.measure hκ u).restrict (cell hκ u n)).support ⊆
      Icc (2 * Real.pi * n / L - 2 * Real.sqrt (κ * ‖u‖ ^ 2 / L))
        (2 * Real.pi * n / L + 2 * Real.sqrt (κ * ‖u‖ ^ 2 / L))) ∧
    (∀ n : ℤ, 0 < (RootIndexedMasses.masses hκ u).1 n →
      closure (cell hκ u n ∩ {x | 0 < RootDensityIdentification.dens κ u x}) ⊆
        Icc (2 * Real.pi * n / L - 2 * Real.sqrt (κ * ‖u‖ ^ 2 / L))
          (2 * Real.pi * n / L + 2 * Real.sqrt (κ * ‖u‖ ^ 2 / L))) ∧
    ∀ s : ℝ, 0 ≤ s →
      (ENNReal.ofReal ((1 + 2 * Real.sqrt (κ * ‖u‖ ^ 2 / L)) ^ (-s)) *
          ∑' n : ℤ, ENNReal.ofReal ((1 + |2 * Real.pi * n / L|) ^ s *
            (RootIndexedMasses.masses hκ u).1 n) ≤
        ∫⁻ x, ENNReal.ofReal ((1 + |x|) ^ s) ∂(PhysicalQuantumMeasure.measure hκ u)) ∧
      (∫⁻ x, ENNReal.ofReal ((1 + |x|) ^ s) ∂(PhysicalQuantumMeasure.measure hκ u) ≤
        ENNReal.ofReal ((1 + 2 * Real.sqrt (κ * ‖u‖ ^ 2 / L)) ^ s) *
          ∑' n : ℤ, ENNReal.ofReal ((1 + |2 * Real.pi * n / L|) ^ s *
            (RootIndexedMasses.masses hκ u).1 n)) := by
  have hloc := loc_general hκ u
  have hloc' : ∀ k : ℤ, ∀ᵐ t ∂(PhysicalQuantumMeasure.measure hκ u), t ∈ cell hκ u k →
      |t - 2 * Real.pi * k / L| ≤ 2 * Real.sqrt (κ * ‖u‖ ^ 2 / L) := fun k =>
    (hloc k).mono fun t ht hmem => abs_le.2 ⟨by linarith [(ht hmem).1], by linarith [(ht hmem).2]⟩
  have hmoment : ∀ s : ℝ, 0 ≤ s → _ := fun s hs =>
    CellLocalization.moment_comparison (μ := PhysicalQuantumMeasure.measure hκ u)
      (cell_measurable hκ u) (cell_disjoint hκ u) (cover_ae hκ u)
      (p := fun k : ℤ => 2 * Real.pi * k / L) (C := 2 * Real.sqrt (κ * ‖u‖ ^ 2 / L))
      (by positivity) hloc' hs
  have hterm : ∀ (s : ℝ), 0 ≤ s → ∀ k : ℤ,
      ENNReal.ofReal ((1 + |2 * Real.pi * k / L|) ^ s) * (PhysicalQuantumMeasure.measure hκ u) (cell hκ u k) =
        ENNReal.ofReal ((1 + |2 * Real.pi * k / L|) ^ s * (RootIndexedMasses.masses hκ u).1 k) := by
    intro s hs k
    have h1 := (RootIndexedMasses.root_indexed_masses_proved_clauses hκ u).1 k
    have hfin : (PhysicalQuantumMeasure.measure hκ u) (cell hκ u k) ≠ ⊤ := by
      have := (PhysicalSourceFinal.sourceFacts hκ u).finite
      exact measure_ne_top _ _
    have h2 : ENNReal.ofReal ((RootIndexedMasses.masses hκ u).1 k) =
        (PhysicalQuantumMeasure.measure hκ u) (cell hκ u k) := by
      rw [h1]; exact ENNReal.ofReal_toReal hfin
    rw [← h2, ← ENNReal.ofReal_mul (by positivity)]
  refine ⟨hloc, fun n => ?_, fun n hn => closure_clause hκ u n hn, fun s hs => ?_⟩
  · apply support_sub_of_null isClosed_Icc
    rw [Measure.restrict_apply isClosed_Icc.measurableSet.compl]
    have h := hloc n
    rw [ae_iff] at h
    refine measure_mono_null ?_ h
    intro y hy
    exact fun hh => hy.1 (hh hy.2)
  · have h := hmoment s hs
    simp_rw [hterm s hs] at h
    exact h

end QuantumNLS.Reg003
#print axioms QuantumNLS.Reg003.exists_seq
#print axioms QuantumNLS.Reg003.cover_ae
#print axioms QuantumNLS.Reg003.label_iff_cell
#print axioms QuantumNLS.Reg003.loc_unit
#print axioms QuantumNLS.Reg003.boundary_norm
#print axioms QuantumNLS.Reg003.loc_general
#print axioms QuantumNLS.Reg003.closure_clause
#print axioms QuantumNLS.Reg003.reg003
