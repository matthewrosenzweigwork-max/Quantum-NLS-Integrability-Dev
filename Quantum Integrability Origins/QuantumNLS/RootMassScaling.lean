import QuantumNLS.RootIndexedMasses

/-! Exact amplitude scaling of the physical measure and indexed masses. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace QuantumNLS.RootMassScaling
open PhysicalTensor (L2T)
open EmpiricalRapidity (cauchyTransform)
open RootMeasureComplex (fz HighHalf)
variable {L κ : ℝ} [Fact (0 < L)]

theorem cauchy_smul_emp (c : ℝ≥0∞) (μ : Measure ℝ) (z : ℂ) :
    cauchyTransform (c • μ) z = c.toReal • cauchyTransform μ z := by
  unfold cauchyTransform
  exact integral_smul_measure _ _

/-- Scaling the amplitude rescales both total mass and effective coupling. -/
theorem measure_smul (hκ : 0 < κ) (c : ℂ) (hc : c ≠ 0) (u : L2T L) :
    PhysicalQuantumMeasure.measure hκ (c • u) = ENNReal.ofReal (‖c‖^2) •
      PhysicalQuantumMeasure.measure (mul_pos hκ (sq_pos_of_pos (norm_pos_iff.mpr hc))) u := by
  simp_rw [PhysicalL2Normalization.measure_eq_Mmeas]
  by_cases hu : u = 0
  · simp [hu,FullMass.Mmeas_zero]
  · have hcu : c • u ≠ 0 := smul_ne_zero hc hu
    let η : ℝ := max 1 (max (4*(κ*‖c • u‖^2)) (Real.log 16/L))
    have hη : 0 < η := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    let _ : IsFiniteMeasure (ENNReal.ofReal (‖c‖^2) • FullMass.Mmeas (κ*‖c‖^2) u) :=
      ⟨by
        simp only [Measure.smul_apply,smul_eq_mul]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
    apply CauchyUniqueness.cauchy_ext _ _ hη
    intro t
    let z : ℂ := (t : ℂ)+(η : ℂ)*Complex.I
    have him : z.im = η := by simp [z]
    have hhigh : HighHalf L (κ*‖c • u‖^2) z := by
      constructor
      · rw [him]; exact (le_max_left _ _).trans (le_max_right _ _)
      · rw [him]
        have hh : Real.log 16/L ≤ η := (le_max_right _ _).trans (le_max_right _ _)
        exact (div_le_iff₀ (Fact.out : 0 < L)).mp hh |>.trans_eq (mul_comm _ _)
    have hn : κ*‖c • u‖^2 = (κ*‖c‖^2)*‖u‖^2 := by rw [norm_smul,mul_pow]; ring
    have hhighu : HighHalf L ((κ*‖c‖^2)*‖u‖^2) z := hn ▸ hhigh
    obtain ⟨_,_,huniq⟩ := FullMass.mass_characterization hκ hcu hhigh
    obtain ⟨hbound,heq,_⟩ := FullMass.mass_characterization
      (mul_pos hκ (sq_pos_of_pos (norm_pos_iff.mpr hc))) hu hhighu
    rw [FullMass.cauchy_smul,ENNReal.toReal_ofReal (sq_nonneg _),Complex.real_smul]
    apply Eq.symm
    apply huniq
    · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),norm_smul,mul_pow]
      have hh := mul_le_mul_of_nonneg_left hbound (sq_nonneg ‖c‖)
      convert hh using 1; ring
    · rw [FullMass.fz_scale,FullMass.productSymbol_smul]
      exact heq

/-- The selected phase is unchanged under the matching effective-coupling rescaling. -/
theorem boundary_smul (hκ : 0 < κ) (c : ℂ) (hc : c ≠ 0) (u : L2T L) (x : ℝ) :
    PhysicalContinuousBoundary.boundary hκ (c • u) x =
      PhysicalContinuousBoundary.boundary (mul_pos hκ (sq_pos_of_pos (norm_pos_iff.mpr hc))) u x := by
  have he : SpatialTransfer.boundaryPhase L κ (PhysicalQuantumMeasure.measure hκ (c • u)) =
      SpatialTransfer.boundaryPhase L (κ*‖c‖^2)
        (PhysicalQuantumMeasure.measure (mul_pos hκ (sq_pos_of_pos (norm_pos_iff.mpr hc))) u) := by
    funext z
    rw [SpatialTransfer.boundaryPhase,measure_smul hκ c hc u,cauchy_smul_emp,
      ENNReal.toReal_ofReal (sq_nonneg _),Complex.real_smul,SpatialTransfer.boundaryPhase]
    push_cast
    ring
  have hb := (PhysicalSourceFinal.sourceFacts hκ (c • u)).boundary x
  change Tendsto (fun ε : ℝ => SpatialTransfer.boundaryPhase L κ
    (PhysicalQuantumMeasure.measure hκ (c • u)) ((x : ℂ)+(ε : ℂ)*Complex.I))
    (𝓝[>] 0) (𝓝 (PhysicalContinuousBoundary.boundary hκ (c • u) x)) at hb
  rw [he] at hb
  exact tendsto_nhds_unique hb ((PhysicalSourceFinal.sourceFacts
    (mul_pos hκ (sq_pos_of_pos (norm_pos_iff.mpr hc))) u).boundary x)

theorem separator_smul (hκ : 0 < κ) (c : ℂ) (hc : c ≠ 0) (u : L2T L) (n : ℤ) :
    RootIndexedPhase.separator hκ (c • u) n =
      RootIndexedPhase.separator (mul_pos hκ (sq_pos_of_pos (norm_pos_iff.mpr hc))) u n := by
  apply (PhysicalSourceFinal.sourceFacts (mul_pos hκ (sq_pos_of_pos (norm_pos_iff.mpr hc))) u).phase.separator_unique
  change (PhysicalContinuousBoundary.boundary _ u _).re = _
  rw [← boundary_smul hκ c hc u]
  exact (PhysicalSourceFinal.sourceFacts hκ (c • u)).phase.separator_spec n

/-- Exact scaling of each literal physical indexed interval mass. -/
theorem masses_smul (hκ : 0 < κ) (c : ℂ) (hc : c ≠ 0) (u : L2T L) (n : ℤ) :
    (RootIndexedMasses.masses hκ (c • u)).1 n = ‖c‖^2 *
      (RootIndexedMasses.masses (mul_pos hκ (sq_pos_of_pos (norm_pos_iff.mpr hc))) u).1 n := by
  change (PhysicalQuantumMeasure.measure hκ (c • u) (Ioo
    (RootIndexedPhase.separator hκ (c • u) (n-1))
    (RootIndexedPhase.separator hκ (c • u) n))).toReal = _
  rw [measure_smul hκ c hc u,separator_smul hκ c hc u (n-1),separator_smul hκ c hc u n,Measure.smul_apply,smul_eq_mul,
    ENNReal.toReal_mul,ENNReal.toReal_ofReal (sq_nonneg _)]
  rfl
end QuantumNLS.RootMassScaling
#print axioms QuantumNLS.RootMassScaling.masses_smul

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootMassScaling." ||
        n.toString.startsWith "_private.QuantumNLS.RootMassScaling." then
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
  Lean.logInfo m!"RootMassScaling audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
