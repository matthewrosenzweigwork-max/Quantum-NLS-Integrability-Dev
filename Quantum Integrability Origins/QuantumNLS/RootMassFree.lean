import QuantumNLS.RootIndexedMasses
import QuantumNLS.Prop026Bound

/-! Free-coupling limit of the physical indexed interval masses. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
namespace QuantumNLS.RootMassFree
open PhysicalTensor (L2T)
open RootIndexedMasses (masses)
variable {L : ℝ} [Fact (0 < L)]

abbrev Coupling := {κ : ℝ // 0 < κ}
def zeroCoupling : Filter Coupling := comap Subtype.val (𝓝 0)
theorem coupling_tendsto : Tendsto (Subtype.val : Coupling → ℝ) zeroCoupling (𝓝 0) :=
  tendsto_comap

def cell (n : ℤ) : ℝ := 2 * MonotoneIndexedMasses.level n / L

theorem cell_phase (n : ℤ) : L * cell (L := L) n / 2 = MonotoneIndexedMasses.level n := by
  unfold cell
  field_simp [(Fact.out : 0 < L).ne']

theorem coupling_zero_trace (u : L2T L) (z : ℂ) :
    L2SpatialTransfer.discriminant 0 u z = 2 * Complex.cos ((L : ℂ)*z/2) := by
  have he : SpatialTransfer.balCoef 0 (L2SpatialTransfer.profile u) z =
      SpatialTransfer.balCoef 0 (L2SpatialTransfer.profile (0 : L2T L)) z := by
    funext x
    simp [SpatialTransfer.balCoef, SpatialTransfer.coef]
  change Matrix.trace (L1SpatialTransfer.transfer _ L) = _
  rw [he]
  exact PhysicalVacuumSourceFacts.discriminant_zero 0 z

theorem free_cell_band (u : L2T L) (n : ℤ) :
    |(L2SpatialTransfer.discriminant 0 u (cell (L := L) n : ℂ)).re| < 2 := by
  rw [coupling_zero_trace]
  have he : (L : ℂ)*(cell (L := L) n : ℂ)/2 =
      (MonotoneIndexedMasses.level n : ℂ) := by
    exact_mod_cast cell_phase (L := L) n
  rw [he, ← Complex.ofReal_cos]
  simp [BandPhaseBridge.cos_level]

/-- The selected phase at each fixed free cell boundary has its free limit. -/
theorem phase_cell_limit (u : L2T L) (n : ℤ) :
    Tendsto (fun k : Coupling => RootIndexedPhase.theta k.2 u (cell (L := L) n))
      zeroCoupling (𝓝 (MonotoneIndexedMasses.level n)) := by
  let f : ℝ × ℝ → ℝ := fun p => |(L2SpatialTransfer.discriminant p.1 u (p.2 : ℂ)).re|
  have hmap : Continuous (fun p : ℝ × ℝ => (((p.1,u) : ℝ × L2T L), (p.2 : ℂ))) := by fun_prop
  have hc : Continuous f := (Complex.continuous_re.comp
    (DEF014Joint.continuous_discriminant_joint.comp hmap)).abs
  obtain ⟨δ,hδ,hband⟩ := DEF014Phase.common_neighborhood f hc 0 (cell (L := L) n) (free_cell_band u n)
  have hb : ∀ᶠ k : Coupling in zeroCoupling, ∀ t : ℝ,
      |t-cell (L := L) n| < δ →
      |(L2SpatialTransfer.discriminant k.1 u (t : ℂ)).re| < 2 := coupling_tendsto.eventually hband
  have hm : Tendsto (fun k : Coupling => FullMass.Mfin k.1 u) zeroCoupling
      (𝓝 (FullMass.Mfin 0 u)) := by
    have hp : Tendsto (fun k : Coupling => ((⟨k.1,k.2.le⟩ : {κ : ℝ // 0 ≤ κ}),u))
        zeroCoupling (𝓝 ((⟨0,le_rfl⟩ : {κ : ℝ // 0 ≤ κ}),u)) :=
      by
        rw [nhds_prod_eq]
        exact (tendsto_subtype_rng.mpr coupling_tendsto).prodMk tendsto_const_nhds
    exact (FullMassLimit.continuous_Mfin.tendsto ((⟨0,le_rfl⟩ : {κ : ℝ // 0 ≤ κ}),u)).comp hp
  have hi := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hm)
    (DEF014Phase.kernel (cell (L := L) n) δ hδ)
  have ht : Tendsto (fun k : Coupling => L*cell (L := L) n/2 - k.1 *
      ∫ t, DEF014Phase.kernel (cell (L := L) n) δ hδ t ∂(FullMass.Mfin k.1 u : Measure ℝ))
      zeroCoupling (𝓝 (MonotoneIndexedMasses.level n)) := by
    have hh := (coupling_tendsto.mul hi).const_sub (L*cell (L := L) n/2)
    simpa only [zero_mul,sub_zero,cell_phase] using hh
  apply ht.congr'
  filter_upwards [hb] with k hk
  have he := DEF014Phase.phase_eq_integral
    ((⟨k.1,k.2⟩ : Coupling),u) hδ hk
  simpa only [DEF014Phase.phase, DEF014Phase.measure,
    PhysicalL2Normalization.measure_eq_Mmeas,FullMass.Mfin,FiniteMeasure.toMeasure_mk,RootIndexedPhase.theta] using he.symm

/-- At almost every point carrying physical mass the phase is an integer multiple of pi. -/
theorem integer_phase (k : Coupling) (u : L2T L) :
    ∀ᵐ t ∂(PhysicalQuantumMeasure.measure k.2 u),
      ∃ j : ℤ, RootIndexedPhase.theta k.2 u t = j * Real.pi := by
  by_cases hu : u = 0
  · simp [hu]
  · filter_upwards [Prop026Bound.integer_ae k.2 hu] with t ht
    obtain ⟨j,hj⟩ := ht
    rw [Prop026Bound.label_eq] at hj
    refine ⟨j, ?_⟩
    exact (div_eq_iff Real.pi_ne_zero).mp hj

/-- Any cut between the adjacent integer labels selects the same mass as the separator. -/
theorem cut_equiv (k : Coupling) (u : L2T L) (n : ℤ) (b : ℝ)
    (hb0 : (n : ℝ)*Real.pi < RootIndexedPhase.theta k.2 u b)
    (hb1 : RootIndexedPhase.theta k.2 u b < ((n : ℝ)+1)*Real.pi) :
    ∀ᵐ t ∂(PhysicalQuantumMeasure.measure k.2 u),
      (RootIndexedPhase.separator k.2 u n < t ↔ b < t) ∧
      (t < RootIndexedPhase.separator k.2 u n ↔ t < b) := by
  let P := (PhysicalSourceFinal.sourceFacts k.2 u).phase
  have hm := PhysicalContinuousBoundary.monotone_all k.2 u
  filter_upwards [integer_phase k u] with t ht
  obtain ⟨j,hj⟩ := ht
  have hbne : t ≠ b := by
    intro he; subst t
    have : (n : ℝ) < j ∧ (j : ℝ) < n+1 := by constructor <;> nlinarith [Real.pi_pos]
    have hh : n < j ∧ j < n+1 := by exact_mod_cast this
    omega
  have hsne : t ≠ RootIndexedPhase.separator k.2 u n := by
    intro he
    have hp := P.separator_spec n
    change RootIndexedPhase.theta k.2 u (RootIndexedPhase.separator k.2 u n) = _ at hp
    rw [← he,hj] at hp
    exact BandPhaseBridge.level_ne_integer_pi n j hp.symm
  have hl : RootIndexedPhase.separator k.2 u n < t ↔ b < t := by
    rw [P.separator_lt_iff]
    change MonotoneIndexedMasses.level n < RootIndexedPhase.theta k.2 u t ↔ b < t
    rw [hj]
    constructor
    · intro h
      have hnj : n < j := by
        have : (n : ℝ) < j := by
          dsimp [MonotoneIndexedMasses.level, IndexedMasses.level] at h
          nlinarith [Real.pi_pos]
        exact_mod_cast this
      have hnj' : (n : ℝ)+1 ≤ j := by exact_mod_cast hnj
      by_contra hn
      have := hm (le_of_not_gt hn)
      change RootIndexedPhase.theta k.2 u t ≤ RootIndexedPhase.theta k.2 u b at this
      rw [hj] at this
      nlinarith [Real.pi_pos]
    · intro h
      have ht := hm h.le
      change RootIndexedPhase.theta k.2 u b ≤ RootIndexedPhase.theta k.2 u t at ht
      rw [hj] at ht
      have hnj : n < j := by
        have : (n : ℝ) < j := by nlinarith [Real.pi_pos]
        exact_mod_cast this
      have hnj' : (n : ℝ)+1 ≤ j := by exact_mod_cast hnj
      dsimp [MonotoneIndexedMasses.level, IndexedMasses.level]
      nlinarith [Real.pi_pos]
  refine ⟨hl, ?_⟩
  constructor
  · intro h
    by_contra hn
    have hbt : b < t := lt_of_le_of_ne (le_of_not_gt hn) hbne.symm
    exact (not_lt_of_ge h.le) (hl.mpr hbt)
  · intro h
    by_contra hn
    have hst : RootIndexedPhase.separator k.2 u n < t :=
      lt_of_le_of_ne (le_of_not_gt hn) hsne.symm
    exact (not_lt_of_ge h.le) (hl.mp hst)

theorem eventually_fixed_cell (u : L2T L) (n : ℤ) :
    ∀ᶠ k : Coupling in zeroCoupling, (masses k.2 u).1 n =
      (PhysicalQuantumMeasure.measure k.2 u (Ioo (cell (L := L) (n-1)) (cell (L := L) n))).toReal := by
  have hbr (j : ℤ) : ∀ᶠ k : Coupling in zeroCoupling,
      (j : ℝ)*Real.pi < RootIndexedPhase.theta k.2 u (cell (L := L) j) ∧
      RootIndexedPhase.theta k.2 u (cell (L := L) j) < ((j : ℝ)+1)*Real.pi := by
    have hn : Ioo ((j : ℝ)*Real.pi) (((j : ℝ)+1)*Real.pi) ∈ 𝓝 (MonotoneIndexedMasses.level j) := by
      apply Ioo_mem_nhds <;> dsimp [MonotoneIndexedMasses.level,IndexedMasses.level] <;> nlinarith [Real.pi_pos]
    exact (phase_cell_limit u j).eventually hn
  filter_upwards [hbr (n-1),hbr n] with k hk0 hk1
  change (PhysicalQuantumMeasure.measure k.2 u (Ioo
    (RootIndexedPhase.separator k.2 u (n-1)) (RootIndexedPhase.separator k.2 u n))).toReal = _
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [cut_equiv k u (n-1) _ hk0.1 hk0.2,cut_equiv k u n _ hk1.1 hk1.2] with t ht0 ht1
  simp only [mem_Ioo,ht0.1,ht1.2]
end QuantumNLS.RootMassFree
#print axioms QuantumNLS.RootMassFree.eventually_fixed_cell

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootMassFree." ||
        n.toString.startsWith "_private.QuantumNLS.RootMassFree." then
      pending := pending.push n
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"RootMassFree audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
