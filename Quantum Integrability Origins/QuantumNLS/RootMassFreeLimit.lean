import QuantumNLS.RootMassFree

/-! The full ell1 free limit, with the normalized Fourier convention of DEF-001. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace QuantumNLS.RootMassFreeLimit
open PhysicalTensor (L2T)
open RootMassFree RootIndexedMasses
variable {L : ℝ} [Fact (0 < L)]

/-- The positive-coupling limit filter is nontrivial. -/
theorem zeroCoupling_neBot : NeBot zeroCoupling := by
  apply Filter.comap_neBot
  intro S hS
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hS
  refine ⟨⟨δ/2,by linarith⟩,hball ?_⟩
  simp only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (by linarith : 0 < δ/2)]
  linarith

/-- The squared Fourier intensities in the physical ell1 carrier. -/
def intensities (u : L2T L) : ActionTorus.PosL1 :=
  ⟨⟨fun n => ‖Fourier.coeff L u n‖^2, by
    apply memℓp_gen
    simpa only [ENNReal.toReal_one,Real.rpow_one,Real.norm_eq_abs,
      abs_sq] using (OneParticleBorn.hasSum_coeff_sq u).summable⟩,
    fun n => sq_nonneg _⟩

theorem momentum_mem_cell (j n : ℤ) :
    2*Real.pi*(j : ℝ)/L ∈ Ioo (cell (L := L) (n-1)) (cell (L := L) n) ↔ j = n := by
  have hL : 0 < L := Fact.out
  have hπ := Real.pi_pos
  simp only [mem_Ioo,cell,MonotoneIndexedMasses.level,IndexedMasses.level]
  rw [div_lt_div_iff_of_pos_right hL,div_lt_div_iff_of_pos_right hL]
  push_cast
  constructor
  · intro h
    have hj0 : (n : ℝ)-1 < j := by nlinarith [h.1]
    have hj1 : (j : ℝ) < n+1 := by nlinarith [h.2]
    have : n-1 < j ∧ j < n+1 := by exact_mod_cast And.intro hj0 hj1
    omega
  · rintro rfl
    constructor <;> nlinarith

theorem momentum_ne_cell (j n : ℤ) : 2*Real.pi*(j : ℝ)/L ≠ cell (L := L) n := by
  intro he
  have hL : 0 < L := Fact.out
  dsimp [cell,MonotoneIndexedMasses.level,IndexedMasses.level] at he
  have h := (div_left_inj' hL.ne').mp he
  have hπ := Real.pi_pos
  have hj0 : (n : ℝ) < j := by nlinarith
  have hj1 : (j : ℝ) < n+1 := by nlinarith
  have : n < j ∧ j < n+1 := by exact_mod_cast And.intro hj0 hj1
  omega

theorem free_cell_mass (u : L2T L) (n : ℤ) :
    FreeLimit.freeMeasure L u (Ioo (cell (L := L) (n-1)) (cell (L := L) n)) =
      ENNReal.ofReal (‖Fourier.coeff L u n‖^2) := by
  rw [FreeLimit.freeMeasure,Measure.sum_apply _ measurableSet_Ioo]
  have hd (j : ℤ) :
      (Ioo (cell (L := L) (n-1)) (cell (L := L) n)).indicator (1 : ℝ → ℝ≥0∞)
        (2*Real.pi*(j : ℝ)/L) = if j=n then 1 else 0 := by
    simp only [Set.indicator_apply,momentum_mem_cell,Pi.one_apply]
  simp only [Measure.smul_apply,smul_eq_mul,Measure.dirac_apply' _ measurableSet_Ioo,hd]
  simp

theorem free_cell_null (u : L2T L) (n : ℤ) :
    FreeLimit.freeMeasure L u {cell (L := L) n} = 0 := by
  rw [FreeLimit.freeMeasure,Measure.sum_apply _ (measurableSet_singleton _)]
  apply ENNReal.tsum_eq_zero.mpr
  intro j
  simp [Measure.smul_apply,Measure.dirac_apply',momentum_ne_cell j n]

theorem cell_order (n : ℤ) : cell (L := L) (n-1) < cell (L := L) n := by
  apply div_lt_div_of_pos_right _ (Fact.out : 0 < L)
  dsimp [MonotoneIndexedMasses.level,IndexedMasses.level]
  push_cast
  nlinarith [Real.pi_pos]

/-- Continuity-set specialization of the already proved quantum weak free limit. -/
theorem measure_cell_limit (u : L2T L) (n : ℤ) :
    Tendsto (fun k : Coupling =>
      (PhysicalQuantumMeasure.measure k.2 u (Ioo (cell (L := L) (n-1)) (cell (L := L) n))).toReal)
      zeroCoupling (𝓝 (‖Fourier.coeff L u n‖^2)) := by
  by_cases hu : u = 0
  · subst u
    have he : Fourier.coeff L (0 : L2T L) n = 0 := by
      rw [← Fourier.fourierL2_apply, map_zero]; rfl
    rw [he]
    simpa using (tendsto_const_nhds (x := (0 : ℝ)) :
      Tendsto (fun _ : Coupling => (0 : ℝ)) zeroCoupling (𝓝 0))
  · let v := FullMass.unitDir u
    have hv := FullMass.norm_unitDir hu
    have hm : 0 < ‖u‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
    have hk : Tendsto (fun k : Coupling => k.1*‖u‖^2) zeroCoupling (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      exact ⟨by simpa using coupling_tendsto.mul_const (‖u‖^2),
        Eventually.of_forall fun k => mul_pos k.2 hm⟩
    have hprob := (FreeLimit.tendsto_muKappa_free v hv).comp hk
    have hfront : (FreeLimit.freeProb v hv : Measure ℝ)
        (frontier (Ioo (cell (L := L) (n-1)) (cell (L := L) n))) = 0 := by
      rw [frontier_Ioo (cell_order n)]
      exact measure_union_null (free_cell_null v (n-1)) (free_cell_null v n)
    have hi := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hprob hfront
    have hr := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hi
    have hs := hr.const_mul (‖u‖^2)
    have he (k : Coupling) :
        (PhysicalQuantumMeasure.measure k.2 u (Ioo (cell (L := L) (n-1)) (cell (L := L) n))).toReal =
        ‖u‖^2 * ((FreeLimit.muKappa v hv (k.1*‖u‖^2) : Measure ℝ)
          (Ioo (cell (L := L) (n-1)) (cell (L := L) n))).toReal := by
      rw [PhysicalL2Normalization.measure_eq_Mmeas,FullMass.Mmeas_of_ne _ hu,
        Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_ofReal (sq_nonneg _)]
    have hs' : Tendsto (fun k : Coupling =>
        (PhysicalQuantumMeasure.measure k.2 u (Ioo (cell (L := L) (n-1)) (cell (L := L) n))).toReal)
        zeroCoupling (𝓝 (‖u‖^2 * ((FreeLimit.freeProb v hv : Measure ℝ)
          (Ioo (cell (L := L) (n-1)) (cell (L := L) n))).toReal)) :=
      hs.congr' (Eventually.of_forall fun k => (he k).symm)
    rw [show (FreeLimit.freeProb v hv : Measure ℝ) = FreeLimit.freeMeasure L v from rfl,
      free_cell_mass,ENNReal.toReal_ofReal (sq_nonneg _)] at hs'
    have hec : ‖u‖^2 * ‖Fourier.coeff L v n‖^2 = ‖Fourier.coeff L u n‖^2 := by
      have h := FullMass.coeff_smul ((‖u‖ : ℝ) : ℂ) v n
      rw [FullMass.smul_unitDir hu] at h
      rw [h,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),mul_pow]
    rwa [hec] at hs'

/-- As positive coupling tends to zero the actual indexed masses converge in ell1
norm to the squared Fourier intensities, for every physical input including vacuum. -/
theorem indexed_masses_free (u : L2T L) :
    Tendsto (fun k : Coupling => masses k.2 u) zeroCoupling (𝓝 (intensities u)) := by
  apply DEF014Continuity.tendsto_posL1
  · intro n
    exact (measure_cell_limit u n).congr' ((eventually_fixed_cell u n).mono fun k hk => hk.symm)
  · have hi := (OneParticleBorn.hasSum_coeff_sq u).tsum_eq
    have hm (k : Coupling) : (∑' n, (masses k.2 u).1 n) = ‖u‖^2 :=
      (PhysicalSourceFinal.sourceFacts k.2 u).sum_masses
    simpa only [hm,show (∑' n, (intensities u).1 n) = ‖u‖^2 from hi] using
      (tendsto_const_nhds (x := ‖u‖^2) : Tendsto (fun _ : Coupling => ‖u‖^2) zeroCoupling (𝓝 (‖u‖^2)))

end QuantumNLS.RootMassFreeLimit
#print axioms QuantumNLS.RootMassFreeLimit.indexed_masses_free

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootMassFreeLimit." ||
        n.toString.startsWith "_private.QuantumNLS.RootMassFreeLimit." then
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
  Lean.logInfo m!"RootMassFreeLimit audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
