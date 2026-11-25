import QuantumNLS.PhysicalL2Normalization
import QuantumNLS.L2DiscriminantRegularity

/-! A derived atomlessness criterion for the actual canonical measure.
The all-upper-half-plane cosine equation is an explicit premise here.
Deriving that equation from the named high-half-plane TraceSymbolIdentity
is still an outstanding analytic continuation step, not a hidden assumption
in a SourceFacts constructor. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace QuantumNLS.PhysicalPhaseAtomlessness

/-- The squared modulus formula behind the local phase-height bound. -/
theorem norm_cos_sq (z : ℂ) :
    ‖Complex.cos z‖ ^ 2 = Real.cos z.re ^ 2 + Real.sinh z.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.cos_eq]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im,
    Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.cosh_ofReal_re,
    Complex.cosh_ofReal_im, Complex.sinh_ofReal_re, Complex.sinh_ofReal_im,
    Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero,
    mul_one, zero_sub, neg_mul, mul_neg, neg_neg]
  linear_combination Real.cos z.re ^ 2 * Real.cosh_sq z.im +
    Real.sinh z.im ^ 2 * Real.sin_sq_add_cos_sq z.re

/-- Positive imaginary phase is bounded by the modulus of its cosine. -/
theorem im_le_norm_cos {z : ℂ} (hz : 0 ≤ z.im) : z.im ≤ ‖Complex.cos z‖ := by
  have h := norm_cos_sq z
  have hs := Real.self_le_sinh_iff.mpr hz
  have hsy : 0 ≤ Real.sinh z.im := Real.sinh_nonneg_iff.mpr hz
  nlinarith [sq_nonneg (Real.cos z.re), norm_nonneg (Complex.cos z)]

/-- Each atom forces the canonical phase height to grow like 1/eta.
This uses the actual Cauchy integral and positivity of the measure. -/
theorem atom_height_lower {L κ : ℝ} (hL : 0 ≤ L) (hκ : 0 ≤ κ)
    (M : Measure ℝ) [IsFiniteMeasure M] (x η : ℝ) (hη : 0 < η) :
    κ * M.real {x} ≤ η *
      (SpatialTransfer.boundaryPhase L κ M ((x : ℂ) + (η : ℂ) * Complex.I)).im := by
  let z : ℂ := (x : ℂ) + (η : ℂ) * Complex.I
  have hzi : z.im = η := by simp [z]
  have hzn : z.im ≠ 0 := by rw [hzi]; exact hη.ne'
  let f : ℝ → ℝ := fun t => -((z - (t : ℂ))⁻¹).im
  have hi : Integrable f M := (EmpiricalRapidity.integrable_cauchyIntegrand M z hzn).im.neg
  have hp : ∀ t, 0 ≤ f t := by
    intro t
    dsimp [f]
    rw [EmpiricalRapidity.im_cauchyIntegrand, neg_div, neg_neg]
    exact div_nonneg (by rw [hzi]; exact hη.le) (Complex.normSq_nonneg _)
  have hmono := integral_mono_measure (Measure.restrict_le_self (s := ({x} : Set ℝ)))
    (Filter.Eventually.of_forall hp) hi
  rw [integral_singleton] at hmono
  have hfx : f x = η⁻¹ := by
    dsimp [f, z]
    have he : (x : ℂ) + (η : ℂ) * Complex.I - (x : ℂ) = (η : ℂ) * Complex.I := by ring
    rw [he, mul_inv_rev]
    simp [Complex.mul_im, Complex.inv_im, Complex.normSq_ofReal]
  have hg : ∫ t, f t ∂M = -(EmpiricalRapidity.cauchyTransform M z).im := by
    unfold EmpiricalRapidity.cauchyTransform
    rw [integral_neg]
    congr 1
    exact (Complex.imCLM.integral_comp_comm
      (EmpiricalRapidity.integrable_cauchyIntegrand M z hzn))
  rw [hfx, hg, smul_eq_mul] at hmono
  have hm := mul_le_mul_of_nonneg_left hmono hκ
  have hphase : (SpatialTransfer.boundaryPhase L κ M z).im =
      L * η / 2 - κ * (EmpiricalRapidity.cauchyTransform M z).im := by
    simp [SpatialTransfer.boundaryPhase, Complex.mul_im, hzi]
  change κ * M.real {x} ≤ η * (SpatialTransfer.boundaryPhase L κ M z).im
  rw [hphase]
  have hm' := mul_le_mul_of_nonneg_left hm hη.le
  have he : η * (κ * (M.real {x} * η⁻¹)) = κ * M.real {x} := by field_simp
  rw [he] at hm'
  nlinarith [mul_nonneg hL hη.le]

/-- A finite positive measure with bounded canonical phase height on every
vertical unit segment has no atoms. No density representation is assumed. -/
theorem atomless_of_bounded_height {L κ : ℝ} (hL : 0 ≤ L) (hκ : 0 < κ)
    (M : Measure ℝ) [IsFiniteMeasure M]
    (hb : ∀ x : ℝ, ∃ C : ℝ, ∀ η : ℝ, 0 < η → η ≤ 1 →
      (SpatialTransfer.boundaryPhase L κ M ((x : ℂ) + (η : ℂ) * Complex.I)).im ≤ C) :
    NullSingletonClass M := by
  constructor
  intro x
  have hfin : M {x} ≠ ⊤ := measure_ne_top _ _
  obtain ⟨C, hC⟩ := hb x
  have hlim : Tendsto (fun η : ℝ => η * C) (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_id.mul_const C).mono_left
      (show (𝓝[>] (0 : ℝ)) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have ha : κ * M.real {x} ≤ 0 := by
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with η hη hη1
    exact (atom_height_lower hL hκ.le M x η hη).trans
      (mul_le_mul_of_nonneg_left (hC η hη hη1) hη.le)
  have hx : M.real {x} = 0 := by
    nlinarith [measureReal_nonneg (μ := M) (s := ({x} : Set ℝ))]
  exact ((ENNReal.toReal_eq_zero_iff _).mp hx).resolve_right hfin

variable {L κ : ℝ} [Fact (0 < L)]

/-- Atomlessness of the canonical physical measure follows from the full
upper-half-plane cosine equation and the proved continuity of the actual
L2 discriminant. The high-to-full continuation remains separate. -/
theorem canonical_atomless_of_upper_cosine (hκ : 0 < κ) (u : PhysicalTensor.L2T L)
    (hcos : ∀ z : ℂ, 0 < z.im →
      2 * Complex.cos (SpatialTransfer.boundaryPhase L κ (PhysicalQuantumMeasure.measure hκ u) z) =
        L2SpatialTransfer.discriminant κ u z) :
    NullSingletonClass (PhysicalQuantumMeasure.measure hκ u) := by
  apply atomless_of_bounded_height (Fact.out : 0 < L).le hκ
  intro x
  let F : ℝ → ℂ := fun η => L2SpatialTransfer.discriminant κ u
    ((x : ℂ) + (η : ℂ) * Complex.I)
  have hc : Continuous F := (L2DiscriminantRegularity.continuous_discriminant κ u).comp (by fun_prop)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C / 2, fun η hη hη1 => ?_⟩
  have hz : 0 < ((x : ℂ) + (η : ℂ) * Complex.I).im := by simpa using hη
  have hp := PhysicalQuantumMeasure.im_phase_pos hκ u hz
  have hnorm := congrArg norm (hcos _ hz)
  rw [norm_mul] at hnorm
  norm_num only [Complex.norm_ofNat] at hnorm
  have hi := im_le_norm_cos hp.le
  have hd := hC η (show η ∈ Icc (0 : ℝ) 1 from ⟨hη.le, hη1⟩)
  dsimp [F] at hd
  linarith

end QuantumNLS.PhysicalPhaseAtomlessness

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.PhysicalPhaseAtomlessness.norm_cos_sq
#print axioms QuantumNLS.PhysicalPhaseAtomlessness.im_le_norm_cos
#print axioms QuantumNLS.PhysicalPhaseAtomlessness.atom_height_lower
#print axioms QuantumNLS.PhysicalPhaseAtomlessness.atomless_of_bounded_height
#print axioms QuantumNLS.PhysicalPhaseAtomlessness.canonical_atomless_of_upper_cosine

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.PhysicalPhaseAtomlessness." then
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
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
