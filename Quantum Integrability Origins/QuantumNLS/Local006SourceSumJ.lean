import QuantumNLS.Local006PositiveSlotsJ
import Mathlib.Analysis.Calculus.SmoothSeries

/-! Termwise source differentiation on a full physical ball. The summed
 positive operators are identified with the actual S/K coefficient derivatives. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal
namespace QuantumNLS.Local006.SourceSumJ
open QuantumNLS.Local005 QuantumNLS.Local005.SourceC QuantumNLS.Local005.SourceD
  QuantumNLS.Local006.CoefficientLiftE QuantumNLS.Local006.SequenceAlgebraE
  QuantumNLS.Local006.SequenceEvaluationE QuantumNLS.Local006.PositiveMajorantG
  QuantumNLS.Local006.SourceMajorantG QuantumNLS.Local006.SolidMajorantH
  QuantumNLS.Local006.SourceBindingH QuantumNLS.Local006.BinomialBindingH
  QuantumNLS.Local006.IndependentSlotsJ QuantumNLS.Local006.SlotDerivativeJ
  QuantumNLS.Local006.PositiveSlotsJ
  QuantumNLS.ResetFreeResolventLOCAL001 QuantumNLS.ResetFreeResolventLOCAL001.CompletionB

variable {L r κ : ℝ} [Fact (0 < L)]

lemma sourceDerivative_norm (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) (u : ScalarInterval L) (d : ℕ) :
    ‖sourceDerivative hL hκ hr hs kind u d‖ ≤
      (d+1 : ℝ) * wordConstant L r κ ^ (d+1) * ‖u‖^d := by
  have hC := (wordConstant_pos hL hr hκ).le
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hpos := positiveDerivative_positive hL hκ hr hs kind
    (intervalFourierIso L u) (intervalFourierIso L v) d
  have hdom := physical_derivative_domination hL hκ hr hs kind u v d
  calc
    _ ≤ ‖positiveDerivative hL hκ hr hs kind (intervalFourierIso L u) d
        (moduli (intervalFourierIso L v))‖ := solid_norm hpos hdom
    _ ≤ ‖positiveDerivative hL hκ hr hs kind (intervalFourierIso L u) d‖ *
        ‖moduli (intervalFourierIso L v)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ((d+1 : ℝ) * wordConstant L r κ ^ (d+1) * ‖intervalFourierIso L u‖^d) *
        ‖moduli (intervalFourierIso L v)‖ :=
      mul_le_mul_of_nonneg_right (positiveDerivative_norm hL hκ hr hs kind _ d) (norm_nonneg _)
    _ = _ := by rw [moduli_norm, (intervalFourierIso L).norm_map, (intervalFourierIso L).norm_map]

lemma sourceDerivative_summable (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) (u : ScalarInterval L)
    (hu : wordConstant L r κ * ‖u‖ < 1) :
    Summable (fun d => ‖sourceDerivative hL hκ hr hs kind u d‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (sourceDerivative_norm hL hκ hr hs kind u)
    (QuantumNLS.Local006.TransposeMajorantG.differentiated_geometric_summable
      (wordConstant_pos hL hr hκ).le (norm_nonneg u) hu)

/-- A full physical ball, with every differentiated source slot summed.
Uniform derivative bounds follow from the proved LOCAL-005 constants. -/
theorem sourceSum_hasFDerivAt (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) (u : ScalarInterval L)
    (hu : ‖u‖ < 1 / (8 * wordConstant L r κ)) :
    HasFDerivAt (sourceSum hL hκ hr hs kind)
      (∑' d, sourceDerivative hL hκ hr hs kind u d) u := by
  let C := wordConstant L r κ
  let R := 1 / (8*C)
  have hC : 0 < C := wordConstant_pos hL hr hκ
  have hR : 0 < R := by dsimp [R]; positivity
  have hsmall : C * R < 1 := by dsimp [R]; field_simp; linarith
  have hb := QuantumNLS.Local006.TransposeMajorantG.differentiated_geometric_summable
    hC.le hR.le hsmall
  apply hasFDerivAt_tsum_of_isPreconnected hb isOpen_ball (convex_ball (0 : ScalarInterval L) R).isPreconnected
    (fun d v hv => actualCoeff_hasFDerivAt hL hκ hr hs kind v d) ?_
    (mem_ball_self hR) ?_ (mem_ball_zero_iff.mpr hu)
  · intro d v hv
    exact (sourceDerivative_norm hL hκ hr hs kind v d).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (mem_ball_zero_iff.mp hv).le d) (by positivity))
  · have hz : ∀ d, actualCoeff hL hκ hr hs kind (0 : ScalarInterval L) d = 0 := by
      intro d
      rw [← sourceMultilinear_diagonal]
      exact (sourceMultilinear hL hκ hr hs (Nat.succ_pos d) kind).map_coord_zero
        (0 : Fin (d+1)) (by rfl)
    simpa only [hz] using (summable_zero : Summable (fun _ : ℕ => (0 : Mixed)))

/-- The summed positive Fourier operator bounds the actual derivative of the
full source series, with both sums justified in their Banach targets. -/
theorem sourceSum_derivative_domination (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) (u v : ScalarInterval L)
    (hu : ‖u‖ < 1 / (8 * wordConstant L r κ)) :
    Majorizes ((∑' d, positiveDerivative hL hκ hr hs kind (intervalFourierIso L u) d)
      (moduli (intervalFourierIso L v)))
      (matrix (fderiv ℝ (sourceSum hL hκ hr hs kind) u v)) := by
  have hC := wordConstant_pos hL hr hκ
  have hq : wordConstant L r κ * ‖u‖ < 1 := by
    have h := mul_lt_mul_of_pos_left hu hC
    have he : wordConstant L r κ * (1 / (8 * wordConstant L r κ)) = 1/8 := by field_simp
    rw [he] at h
    linarith
  have hp := positiveDerivative_summable hL hκ hr hs kind (intervalFourierIso L u)
    (by simpa only [(intervalFourierIso L).norm_map] using hq)
  have hd := sourceDerivative_summable hL hκ hr hs kind u hq
  rw [(sourceSum_hasFDerivAt hL hκ hr hs kind u hu).fderiv]
  have hpa := (ContinuousLinearMap.apply ℂ Mixed (moduli (intervalFourierIso L v))).hasSum hp.of_norm.hasSum
  have hda := (ContinuousLinearMap.apply ℝ Mixed v).hasSum hd.of_norm.hasSum
  have hpn : Summable (fun d => ‖positiveDerivative hL hκ hr hs kind (intervalFourierIso L u) d
      (moduli (intervalFourierIso L v))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun d => ContinuousLinearMap.le_opNorm _ _)
      (hp.mul_right ‖moduli (intervalFourierIso L v)‖)
  have hdn : Summable (fun d => ‖sourceDerivative hL hκ hr hs kind u d v‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun d => ContinuousLinearMap.le_opNorm _ _)
      (hd.mul_right ‖v‖)
  have hep : (∑' d, positiveDerivative hL hκ hr hs kind (intervalFourierIso L u) d
      (moduli (intervalFourierIso L v))) =
      (∑' d, positiveDerivative hL hκ hr hs kind (intervalFourierIso L u) d)
        (moduli (intervalFourierIso L v)) := hpa.tsum_eq
  have hed : (∑' d, sourceDerivative hL hκ hr hs kind u d v) =
      (∑' d, sourceDerivative hL hκ hr hs kind u d) v := hda.tsum_eq
  rw [← hep, ← hed]
  exact majorizes_tsum hpn hdn (fun d => physical_derivative_domination hL hκ hr hs kind u v d)

end QuantumNLS.Local006.SourceSumJ

#print axioms QuantumNLS.Local006.SourceSumJ.sourceSum_hasFDerivAt
#print axioms QuantumNLS.Local006.SourceSumJ.sourceSum_derivative_domination
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local006.SourceSumJ." ||
        n.toString.startsWith "_private.QuantumNLS.Local006SourceSumJ" then
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
  Lean.logInfo m!"Local006SourceSumJ audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."

