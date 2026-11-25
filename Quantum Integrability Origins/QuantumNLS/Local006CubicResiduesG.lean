import QuantumNLS.Local006FirstCoefficientE
import Mathlib.Analysis.Complex.CauchyIntegral

/-! Exact residues of the paths that contribute through degree three.
The second-order projection sign is negative. Paths which revisit the free
mode contribute the two normalization subtractions to the cubic moment. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Set Metric Complex
open scoped BigOperators
namespace QuantumNLS.Local006.CubicResiduesG
open QuantumNLS.Local005 QuantumNLS.LocalSpectral

def residue (c : ℂ) (r : ℝ) (f : ℂ → ℂ) : ℂ :=
  (2 * Real.pi * I : ℂ)⁻¹ • ∮ z in C(c, r), f z

lemma inv_differentiableOn {c a : ℂ} {r : ℝ} (ha : r < dist a c) :
    DifferentiableOn ℂ (fun z : ℂ => (z - a)⁻¹) (closedBall c r) := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.inv
  · exact (differentiableAt_id.sub_const a)
  · intro h
    have he : z = a := sub_eq_zero.mp h
    subst z
    exact (not_le.mpr ha) (mem_closedBall.mp hz)

lemma residue_two {c a : ℂ} {r : ℝ} (hr : 0 < r) (ha : r < dist a c) :
    residue c r (fun z => (z - c)⁻¹ ^ 2 * (z - a)⁻¹) = -((c - a)⁻¹ ^ 2) := by
  have hca : c - a ≠ 0 := by
    intro h
    have he : c = a := sub_eq_zero.mp h
    subst a
    simpa using hr.trans ha
  have hd := inv_differentiableOn ha
  have hi := hd.deriv_eq_smul_circleIntegral hr
  have he := (((hasDerivAt_id c).sub_const a).inv hca).deriv
  simp only [one_div, ← inv_pow, smul_eq_mul] at hi
  change deriv (fun z : ℂ => (z - a)⁻¹) c = -1 / (c - a) ^ 2 at he
  rw [residue, hi, smul_eq_mul, he]
  field_simp [Complex.two_pi_I_ne_zero, hca]
  <;> ring

lemma residue_three_regular {c a b : ℂ} {r : ℝ} (hr : 0 < r)
    (ha : r < dist a c) (hb : r < dist b c) :
    residue c r (fun z => (z - c)⁻¹ * (z - a)⁻¹ * (z - b)⁻¹) =
      (c - a)⁻¹ * (c - b)⁻¹ := by
  have hd := (inv_differentiableOn ha).mul (inv_differentiableOn hb)
  have hi := hd.circleIntegral_sub_inv_smul (mem_ball_self hr)
  simp only [smul_eq_mul, Pi.mul_apply] at hi
  have he : (fun z : ℂ => (z - c)⁻¹ * (z - a)⁻¹ * (z - b)⁻¹) =
      fun z => (z - c)⁻¹ * ((z - a)⁻¹ * (z - b)⁻¹) := by
    funext z; ring
  rw [residue, he, hi, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_mul]

lemma residue_three_left {c b : ℂ} {r : ℝ} (hr : 0 < r) (hb : r < dist b c) :
    residue c r (fun z => (z - c)⁻¹ * (z - c)⁻¹ * (z - b)⁻¹) =
      -((c - b)⁻¹ ^ 2) := by
  simpa only [pow_two] using residue_two hr hb

lemma residue_three_right {c a : ℂ} {r : ℝ} (hr : 0 < r) (ha : r < dist a c) :
    residue c r (fun z => (z - c)⁻¹ * (z - a)⁻¹ * (z - c)⁻¹) =
      -((c - a)⁻¹ ^ 2) := by
  have he : (fun z : ℂ => (z - c)⁻¹ * (z - a)⁻¹ * (z - c)⁻¹) =
      fun z => (z - c)⁻¹ ^ 2 * (z - a)⁻¹ := by funext z; ring
  rw [he]
  exact residue_two hr ha

lemma residue_three_all_free (c : ℂ) (r : ℝ) :
    residue c r (fun z => (z - c)⁻¹ * (z - c)⁻¹ * (z - c)⁻¹) = 0 := by
  have he : (fun z : ℂ => (z - c)⁻¹ * (z - c)⁻¹ * (z - c)⁻¹) =
      fun z => (z - c) ^ (-3 : ℤ) := by
    funext z
    simp [zpow_neg, pow_succ, mul_assoc]
  rw [residue, he, circleIntegral.integral_sub_zpow_of_ne (by norm_num), smul_zero]

/-- One formula covers every possible return of a length-three path to its
free mode. The two nonzero poles may coincide with each other. -/
theorem cubic_path_residue {c a b : ℂ} {r : ℝ} (hr : 0 < r)
    (ha : a = c ∨ r < dist a c) (hb : b = c ∨ r < dist b c) :
    residue c r (fun z => (z - c)⁻¹ * (z - a)⁻¹ * (z - b)⁻¹) =
      if a = c then (if b = c then 0 else -((c - b)⁻¹ ^ 2))
      else if b = c then -((c - a)⁻¹ ^ 2) else (c - a)⁻¹ * (c - b)⁻¹ := by
  rcases ha with rfl | ha
  · rcases hb with rfl | hb
    · simp only [ite_true]
      exact residue_three_all_free _ _
    · have hbc : b ≠ a := by intro h; subst b; simpa using hr.trans hb
      simp only [ite_true, if_neg hbc]
      exact residue_three_left hr hb
  · have hac : a ≠ c := by intro h; subst a; simpa using hr.trans ha
    rw [if_neg hac]
    rcases hb with rfl | hb
    · rw [if_pos rfl]
      exact residue_three_right hr ha
    · have hbc : b ≠ c := by intro h; subst b; simpa using hr.trans hb
      rw [if_neg hbc]
      exact residue_three_regular hr ha hb

open QuantumNLS.ResetFreeResolventLOCAL001

lemma shifted_pole_outside {L r : ℝ} (hL : 0 < L) (hs : r < spacing L / 2)
    (n q : ℤ) (hq : q ≠ 0) :
    r < dist (pm L (sourceMode n q) : ℂ) (pm L n : ℂ) := by
  have he : (pm L (sourceMode n q) : ℂ) - (pm L n : ℂ) =
      ((spacing L * (q : ℝ) : ℝ) : ℂ) := by
    rw [sourceMode, pm_even_shift]
    ring
  rw [dist_eq_norm, he, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (spacing_pos hL)]
  have hq1 : (1 : ℝ) ≤ |(q : ℝ)| := by
    exact_mod_cast (Int.one_le_abs hq)
  have hd := spacing_pos hL
  nlinarith

/-- The degree-two projection residue, including the zero-shift case. -/
theorem projection_two_scalar {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hs : r < spacing L / 2) (n : ℤ) (q : Fin (2 - 1) → ℤ) :
    contourScalar L r .projection n q =
      if q 0 = 0 then 0 else -(((pm L n : ℂ) - (pm L (sourceMode n (q 0)) : ℂ))⁻¹ ^ 2) := by
  have he : contourScalar L r .projection n q =
      residue (pm L n : ℂ) r (fun z => (z - (pm L n : ℂ))⁻¹ ^ 2 *
        (z - (pm L (sourceMode n (q 0)) : ℂ))⁻¹) := by
    simp [contourScalar, residue, endpointOrder, Fin.prod_univ_one]
  rw [he]
  by_cases hq : q 0 = 0
  · rw [if_pos hq, hq]
    simpa [sourceMode, pow_two] using residue_three_all_free (pm L n : ℂ) r
  · rw [if_neg hq]
    exact residue_two hr (shifted_pole_outside hL hs n (q 0) hq)

/-- Exactly the length-three moment scalar occurring in the frozen Fourier
word; no generic residue hypotheses remain for these actual poles. -/
theorem moment_three_scalar {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hs : r < spacing L / 2) (n : ℤ) (q : Fin (3 - 1) → ℤ) :
    contourScalar L r .moment n q =
      if q 0 = 0 then (if q 1 = 0 then 0 else
        -(((pm L n : ℂ) - (pm L (sourceMode n (q 1)) : ℂ))⁻¹ ^ 2))
      else if q 1 = 0 then -(((pm L n : ℂ) - (pm L (sourceMode n (q 0)) : ℂ))⁻¹ ^ 2)
      else ((pm L n : ℂ) - (pm L (sourceMode n (q 0)) : ℂ))⁻¹ *
        ((pm L n : ℂ) - (pm L (sourceMode n (q 1)) : ℂ))⁻¹ := by
  have he : contourScalar L r .moment n q =
      residue (pm L n : ℂ) r (fun z => (z - (pm L n : ℂ))⁻¹ *
        (z - (pm L (sourceMode n (q 0)) : ℂ))⁻¹ *
        (z - (pm L (sourceMode n (q 1)) : ℂ))⁻¹) := by
    simp only [contourScalar, endpointOrder, pow_one, Fin.prod_univ_two, residue]
    congr 2
    funext z
    change (z - (pm L n : ℂ))⁻¹ *
      (∏ x : Fin 2, (z - (pm L (sourceMode n (q x)) : ℂ))⁻¹) = _
    rw [Fin.prod_univ_two]
    ring
  rw [he]
  by_cases h0 : q 0 = 0
  · rw [if_pos h0, h0]
    simp only [sourceMode, mul_zero, add_zero]
    by_cases h1 : q 1 = 0
    · rw [if_pos h1, h1]
      simpa [sourceMode] using residue_three_all_free (pm L n : ℂ) r
    · rw [if_neg h1]
      exact residue_three_left hr (shifted_pole_outside hL hs n (q 1) h1)
  · rw [if_neg h0]
    by_cases h1 : q 1 = 0
    · rw [if_pos h1, h1]
      simpa [sourceMode] using residue_three_right hr (shifted_pole_outside hL hs n (q 0) h0)
    · rw [if_neg h1]
      exact residue_three_regular hr (shifted_pole_outside hL hs n (q 0) h0)
        (shifted_pole_outside hL hs n (q 1) h1)

open QuantumNLS.ResolventWordCoefficientLOCAL005

/-- The frozen length-three Fourier word has exactly the printed three input
labels, with the middle slot conjugated on the physical real slice. -/
theorem cubic_word_labels (L r κ : ℝ) (u : Fin 3 → ℤ → ℂ) (n : ℤ)
    (q : Fin (3 - 1) → ℤ) :
    pathCoefficient L r κ .moment 0 u n q =
      (8 * I * (Real.sqrt (κ / L) : ℂ) ^ 3) *
        u 0 (n + q 0) * u 1 (n + q 0 + q 1) * u 2 (n + q 1) *
          contourScalar L r .moment n q := by
  simp [pathCoefficient, Fin.prod_univ_three, slotPhase, componentAfter,
    wordLabel, previousShift, nextShift]
  ring_nf
  simp [show I ^ 3 = -I by norm_num [pow_succ]]

/-- Exact actual source cubic moment before applying the two inverse-square-
root factors. It retains the returning paths; dropping them would be wrong. -/
theorem source_cubic_moment {L r κ : ℝ} [Fact (0 < L)] (hL : 0 < L)
    (hκ : 0 < κ) (hr : 0 < r) (hs : r < spacing L / 2)
    (u : QuantumNLS.ResetFreeResolventLOCAL001.CompletionB.ScalarInterval L) (n : ℤ) :
    QuantumNLS.Local005.SourceD.entryFunctional n 1 0
      (QuantumNLS.Local005.SourceD.orderedSourceWord hL hκ hr hs .moment
        (fun _ => u) n 3) =
      ∑' q : Fin (3 - 1) → ℤ,
        (8 * I * (Real.sqrt (κ / L) : ℂ) ^ 3) *
          QuantumNLS.Local005.SourceC.physicalFourier u (n + q 0) *
          star (QuantumNLS.Local005.SourceC.physicalFourier u (n + q 0 + q 1)) *
          QuantumNLS.Local005.SourceC.physicalFourier u (n + q 1) *
          (if q 0 = 0 then (if q 1 = 0 then 0 else
            -(((pm L n : ℂ) - (pm L (sourceMode n (q 1)) : ℂ))⁻¹ ^ 2))
          else if q 1 = 0 then -(((pm L n : ℂ) - (pm L (sourceMode n (q 0)) : ℂ))⁻¹ ^ 2)
          else ((pm L n : ℂ) - (pm L (sourceMode n (q 0)) : ℂ))⁻¹ *
            ((pm L n : ℂ) - (pm L (sourceMode n (q 1)) : ℂ))⁻¹) := by
  rw [QuantumNLS.Local005.SourceD.orderedSourceWord_entry_posdegree hL hκ hr hs n
    (fun _ => u) (by norm_num : 1 ≤ 3) .moment 1 0]
  simp only [coefficientEntry, show componentAfter 3 (0 : Fin 2) = 1 from rfl, if_pos rfl]
  apply tsum_congr
  intro q
  rw [cubic_word_labels, moment_three_scalar hL hr hs]
  simp [QuantumNLS.Local005.SourceC.physicalInputs,
    QuantumNLS.Local005.SourceC.physicalSlot, componentAfter]

end QuantumNLS.Local006.CubicResiduesG
#print axioms QuantumNLS.Local006.CubicResiduesG.residue_two
#print axioms QuantumNLS.Local006.CubicResiduesG.cubic_path_residue
#print axioms QuantumNLS.Local006.CubicResiduesG.projection_two_scalar
#print axioms QuantumNLS.Local006.CubicResiduesG.moment_three_scalar
#print axioms QuantumNLS.Local006.CubicResiduesG.source_cubic_moment

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local006.CubicResiduesG." ||
        n.toString.startsWith "_private.QuantumNLS.Local006CubicResiduesG" then
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
  Lean.logInfo m!"Local006CubicResiduesG audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
