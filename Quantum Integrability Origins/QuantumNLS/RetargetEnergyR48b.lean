import QuantumNLS.R52CFCompact
import QuantumNLS.Ext025A3Fields
import QuantumNLS.RootEnergyMomentExpectation
import QuantumNLS.HaarSpectralTail
import QuantumNLS.BoundedBetheTransfer
import QuantumNLS.TerraMultiRound87Normalize

/-! Product energy and projection onto the actual Bethe energy mask. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
noncomputable section
open Set MeasureTheory
open scoped BigOperators InnerProductSpace ENNReal Classical

namespace QuantumNLS.RetargetEnergyR48b
open PhysicalTensor QuantumNLS.Fourier Sobolev Sobolev.PosWeight
open TensorCarrier HaarSpectralTail BetheCoefficientTransform BetheLabels
open ProductEnergyPreparation ChargeEnergy
open RootEnergyMomentExpectation

variable {L κ : ℝ} [Fact (0 < L)] {N : ℕ}

/-- A period-dependent energy bound on the source's actual tested ball.
A fixed finite bound is sufficient before taking the energy cutoff to infinity. -/
theorem profile_energy_bound (hκ : 0 < κ) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ R52CFCompact.profileClass L R,
      OneH1 u ∧ energyH1 κ (u : AddCircle L → ℂ) ≤ C := by
  let A : ℝ := cL L * |R|
  refine ⟨R^2 + κ * A^2, by positivity, ?_⟩
  intro u hu
  obtain ⟨f, hf, he⟩ := hu.1
  have hH : OneH1 u := he ▸ PhysicalProductPreparation.oneH1_smooth hf
  have hs : MemHsLp L 1 u := he ▸ R52CFCompact.memHs_smooth hf
  let v : H02 L 1 := WField.mk u hs
  let y := H02.toH04 (L := L) (s := 1) zero_le_one v
  have hv : ‖v‖ ≤ |R| := (sq_le_sq₀ (norm_nonneg _) (abs_nonneg _)).mp
    (by rw [H02.norm_sq_eq, sq_abs]; exact hu.2.2)
  have hy : ‖y‖ ≤ |R| := (H02.norm_toH04_le zero_le_one v).trans hv
  have ha : 0 ≤ A := mul_nonneg (cL_nonneg L) (abs_nonneg _)
  have haebound : ∀ᵐ x ∂(volume : Measure (AddCircle L)), ‖u x‖ ≤ A := by
    filter_upwards [sobolevEmbedding_ae y] with x hx
    change u x = sobolevEmbedding y x at hx
    rw [hx]
    exact (ContinuousMap.norm_coe_le_norm _ _).trans
      ((norm_sobolevEmbedding_le y).trans (mul_le_mul_of_nonneg_left hy (cL_nonneg L)))
  have hkin : kinetic (u : AddCircle L → ℂ) ≤ R^2 := by
    rw [kinetic_eq]
    have hh (n : ℤ) : freq L n ^ 2 * ‖fourierL2 L u n‖ ^ 2 ≤
        sobolevWeight L 1 n * ‖fourierL2 L u n‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      rw [R52CFCompact.sobolevWeight_one]
      unfold freq
      nlinarith [sq_abs (2 * Real.pi * (n : ℝ) / L), abs_nonneg (2 * Real.pi * (n : ℝ) / L)]
    have hsum : Summable (fun n : ℤ => freq L n ^ 2 * ‖fourierL2 L u n‖ ^ 2) :=
      Summable.of_nonneg_of_le (fun _ => by positivity) hh hs
    exact (hsum.tsum_le_tsum hh hs).trans hu.2.2
  have hq : quartic (u : AddCircle L → ℂ) ≤ A^2 := by
    unfold quartic
    have hsq := (Lp.memLp u).integrable_norm_pow (p := 2) (by norm_num)
    have hb : ∫ x, A^2 * ‖u x‖ ^ 2 ∂(volume : Measure (AddCircle L)) =
        A^2 := by
      rw [integral_const_mul, ← Fourier.lp_norm_sq, hu.2.1]
      ring
    rw [← hb]
    apply integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun _ => by positivity)
      (hsq.const_mul _)
    filter_upwards [haebound] with x hx
    have hh := (sq_le_sq₀ (norm_nonneg (u x)) ha).2 hx
    have ht := mul_le_mul_of_nonneg_right hh (sq_nonneg ‖u x‖)
    nlinarith
  exact ⟨hH, add_le_add hkin (mul_le_mul_of_nonneg_left hq hκ.le)⟩

/-- The cutoff uses the energy eigenvalue of the same full Bethe array. -/
theorem sampleEnergy_eq (hN : 0 < N) (hκ : 0 < κ) (m : MArr N) :
    sampleEnergy L κ N m = EnergyProjection.energyEig L κ N (NormalityBridge.label m) / N := by
  unfold sampleEnergy EnergyProjection.energyEig
  rw [RootEnergyMomentFinite.source_energy hN hκ m]
  simp only [div_eq_mul_inv]
  ring

/-- Identify any operator with the literal accepted Bethe energy diagonal
with the orthogonal coefficient projection. -/
theorem mask_identification (hκ : 0 < κ) (hN : 0 < N) (E : ℝ)
    (P : HN L N →L[ℂ] HN L N)
    (hP : ∀ m, P (bas L hκ hN m) = mask L κ N E m • bas L hκ hN m) :
    P = BoundedBetheTransfer.projection (bas L hκ hN) (adm L κ N E) := by
  classical
  apply NormalityBridge.clm_ext_basis (bas L hκ hN)
  intro m
  rw [hP m, BoundedBetheTransfer.projection_basis]
  rfl

/-- Squared Hilbert norm discarded by a coordinate projection. -/
theorem projection_defect {ι H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (b : HilbertBasis ι ℂ H) (S : Set ι) (v : H) :
    ‖v - BoundedBetheTransfer.projection b S v‖ ^ 2 =
      ∑' i, if i ∈ S then 0 else ‖b.repr v i‖ ^ 2 := by
  classical
  let x := v - BoundedBetheTransfer.projection b S v
  have h : ‖x‖ ^ 2 = ∑' i, ‖b.repr x i‖ ^ 2 :=
    (by simpa only [HilbertBasis.repr_apply_apply] using
      (HilbertDiagOp.parseval_hasSum b x).tsum_eq.symm)
  change ‖x‖ ^ 2 = _
  rw [h]
  apply tsum_congr
  intro i
  rw [show x = v - BoundedBetheTransfer.projection b S v from rfl,
    map_sub, lp.coeFn_sub, Pi.sub_apply, BoundedBetheTransfer.projection_coord]
  by_cases hi : i ∈ S <;> simp [hi]

/-- Born-law Markov bound in vector norm, for the literal mask of R-F1423202. -/
theorem product_cutoff (hκ : 0 < κ) (hN : 0 < N) {E C : ℝ} (hE : 0 < E)
    (P : HN L N →L[ℂ] HN L N)
    (hP : ∀ m, P (bas L hκ hN m) = mask L κ N E m • bas L hκ hN m)
    (u : L2T L) (hu : ‖u‖ = 1) (hH : OneH1 u)
    (hC : energyH1 κ (u : AddCircle L → ℂ) ≤ C) :
    ‖productVec L N u - P (productVec L N u)‖ ^ 2 ≤ C / E := by
  classical
  let b := bas L hκ hN
  let ψ := productVec L N u
  let S := adm L κ N E
  have hBasis : BulkResponseActual.physBasis L hκ N = b := by
    unfold BulkResponseActual.physBasis
    rw [dite_eq_left (show 1 ≤ N from hN)]
  have hx := RootEnergyMomentExpectation.born_energy_hasSum hN hκ u hu hH
  rw [hBasis] at hx
  rw [mask_identification hκ hN E P hP, projection_defect]
  have hpoint (m : MArr N) : (if m ∈ S then 0 else ‖b.repr ψ m‖ ^ 2) ≤
      bornLaw b u m * sampleEnergy L κ N m / E := by
    by_cases hm : m ∈ S
    · rw [ite_eq_left hm]
      exact div_nonneg (mul_nonneg (bornLaw_nonneg _ _ _) (sampleEnergy_nonneg _)) hE.le
    · rw [ite_eq_right hm, HilbertBasis.repr_apply_apply]
      change bornLaw b u m ≤ bornLaw b u m * sampleEnergy L κ N m / E
      apply (le_div_iff₀ hE).2
      apply mul_le_mul_of_nonneg_left _ (bornLaw_nonneg _ _ _)
      rw [sampleEnergy_eq hN hκ]
      apply (le_div_iff₀ (Nat.cast_pos.mpr hN)).2
      have hm' : (N : ℝ) * E < EnergyProjection.energyEig L κ N (NormalityBridge.label m) :=
        lt_of_not_ge hm
      simpa only [mul_comm] using hm'.le
  have hsum : Summable (fun m : MArr N => if m ∈ S then (0 : ℝ) else ‖b.repr ψ m‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => by split_ifs <;> positivity) hpoint (hx.summable.div_const E)
  calc
    _ ≤ ∑' m, bornLaw b u m * sampleEnergy L κ N m / E :=
      hsum.tsum_le_tsum hpoint (hx.summable.div_const E)
    _ = (energyH1 κ (u : AddCircle L → ℂ) - κ * quartic (u : AddCircle L → ℂ) / N) / E := by
      rw [tsum_div_const, hx.tsum_eq]
    _ ≤ C / E := by
      apply div_le_div_of_nonneg_right _ hE.le
      exact (sub_le_self _ (div_nonneg (mul_nonneg hκ.le (quartic_nonneg _)) (Nat.cast_nonneg _))).trans hC

/-- Normalize inside the fixed energy subspace while controlling the distance
to the original state by the actual discarded part. -/
theorem normalize_mask (hκ : 0 < κ) (hN : 0 < N) (E : ℝ)
    (P : HN L N →L[ℂ] HN L N)
    (hP : ∀ m, P (bas L hκ hN m) = mask L κ N E m • bas L hκ hN m)
    (v : HN L N) (hv : ‖v‖ = 1) (hdef : ‖v - P v‖ < 1) :
    ∃ w : HN L N, ‖w‖ = 1 ∧ P w = w ∧ ‖v - w‖ ≤ 2 * ‖v - P v‖ := by
  classical
  let b := bas L hκ hN
  let S := adm L κ N E
  have hproj : P = BoundedBetheTransfer.projection b S := mask_identification hκ hN E P hP
  have hid : P (P v) = P v := by
    rw [hproj]
    exact congrArg (fun T : HN L N →L[ℂ] HN L N => T v)
      (BoundedBetheTransfer.projection_idempotent b S)
  have had : P.adjoint = P := by
    rw [hproj]
    exact BoundedBetheTransfer.projection_selfAdjoint b S
  have hp : 0 < ‖P v‖ := by
    by_contra hn
    have hz : P v = 0 := norm_eq_zero.mp (le_antisymm (le_of_not_gt hn) (norm_nonneg _))
    rw [hz, sub_zero, hv] at hdef
    exact (lt_irrefl 1) hdef
  have hi : ⟪v, P v⟫_ℂ = ⟪P v, P v⟫_ℂ := by
    calc
      ⟪v, P v⟫_ℂ = ⟪v, P (P v)⟫_ℂ := by rw [hid]
      _ = ⟪P.adjoint v, P v⟫_ℂ := by rw [ContinuousLinearMap.adjoint_inner_left]
      _ = _ := by rw [had]
  have ho : ⟪v - P v, P v⟫_ℂ = 0 := by
    rw [inner_sub_left, hi, sub_self]
  have hpyth : ‖v‖ ^ 2 = ‖P v‖ ^ 2 + ‖v - P v‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (v - P v) (P v) ho
    rw [sub_add_cancel] at h
    linarith
  let w := (‖P v‖⁻¹ : ℝ) • P v
  obtain ⟨hw, hdist⟩ := TerraMultiRound87Normalize.normalize_projection v (P v) hv hp hpyth
  refine ⟨w, hw, ?_, hdist⟩
  change P ((‖P v‖⁻¹ : ℝ) • P v) = (‖P v‖⁻¹ : ℝ) • P v
  have he : (‖P v‖⁻¹ : ℝ) • P v = (((‖P v‖⁻¹ : ℝ) : ℂ) • P v) :=
    (Complex.coe_smul (‖P v‖⁻¹ : ℝ) (P v)).symm
  rw [he, map_smul, hid]

end QuantumNLS.RetargetEnergyR48b

#print axioms QuantumNLS.RetargetEnergyR48b.profile_energy_bound
#print axioms QuantumNLS.RetargetEnergyR48b.product_cutoff
#print axioms QuantumNLS.RetargetEnergyR48b.normalize_mask

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "QuantumNLS.RetargetEnergyR48b." ||
        name.toString.startsWith "_private.QuantumNLS.RetargetEnergyR48b." then
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
