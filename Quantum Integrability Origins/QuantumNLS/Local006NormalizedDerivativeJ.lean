import QuantumNLS.Local006NormalizationKernelJ

/-! Differentiate every actual normalized source word and sum the resulting
 independent-slot positive Fourier kernels on a full physical ball. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal
namespace QuantumNLS.Local006.NormalizedDerivativeJ
open QuantumNLS.Local005 QuantumNLS.Local005.SourceC QuantumNLS.Local005.SourceD
  QuantumNLS.Local006.CoefficientLiftE QuantumNLS.Local006.SequenceAlgebraE
  QuantumNLS.Local006.SequenceEvaluationE QuantumNLS.Local006.PositiveMajorantG
  QuantumNLS.Local006.SourceMajorantG QuantumNLS.Local006.SolidMajorantH
  QuantumNLS.Local006.SourceBindingH QuantumNLS.Local006.BinomialBindingH
  QuantumNLS.Local006.NormalizedBindingH QuantumNLS.Local006.IndependentSlotsJ
  QuantumNLS.Local006.SlotDerivativeJ QuantumNLS.Local006.PositiveSlotsJ
  QuantumNLS.Local006.SourceSumJ QuantumNLS.Local006.NormalizationKernelJ
  QuantumNLS.ResetFreeResolventLOCAL001 QuantumNLS.ResetFreeResolventLOCAL001.CompletionB

variable {L r κ : ℝ} [Fact (0 < L)]

def radius (L r κ : ℝ) : ℝ := 1 / (8 * wordConstant L r κ)

def sourceKernelSum (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) (u : ScalarInterval L) : Seq2 →L[ℂ] Mixed :=
  ∑' d, positiveDerivative hL hκ hr hs kind (intervalFourierIso L u) d

def derivativeBound (L r κ : ℝ) : ℝ :=
  ∑' d : ℕ, (d+1 : ℝ) * wordConstant L r κ ^ (d+1) * radius L r κ ^ d

lemma radius_pos (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r) : 0 < radius L r κ := by
  have h := wordConstant_pos hL hr hκ
  unfold radius
  positivity

lemma radius_small (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r) :
    wordConstant L r κ * radius L r κ = 1/8 := by
  have h := wordConstant_pos hL hr hκ
  unfold radius
  field_simp

lemma input_small (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r) {u : ScalarInterval L}
    (hu : ‖u‖ < radius L r κ) : wordConstant L r κ * ‖u‖ < 1/8 := by
  simpa only [radius_small hL hκ hr] using mul_lt_mul_of_pos_left hu (wordConstant_pos hL hr hκ)

lemma degreeBound_summable (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r) :
    Summable (fun d : ℕ => (d+1 : ℝ) * wordConstant L r κ ^ (d+1) * radius L r κ ^ d) :=
  QuantumNLS.Local006.TransposeMajorantG.differentiated_geometric_summable
    (wordConstant_pos hL hr hκ).le (radius_pos hL hκ hr).le
    (by rw [radius_small hL hκ hr]; norm_num)

lemma derivativeBound_nonneg (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r) :
    0 ≤ derivativeBound L r κ := by
  have hC := (wordConstant_pos hL hr hκ).le
  have hR := (radius_pos hL hκ hr).le
  exact tsum_nonneg (fun d => by positivity)

lemma sourceKernelSum_summable (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) (u : ScalarInterval L)
    (hu : ‖u‖ < radius L r κ) :
    Summable (fun d => ‖positiveDerivative hL hκ hr hs kind (intervalFourierIso L u) d‖) := by
  apply positiveDerivative_summable hL hκ hr hs kind
  rw [(intervalFourierIso L).norm_map]
  exact (input_small hL hκ hr hu).trans (by norm_num)

lemma sourceKernelSum_norm (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) (u : ScalarInterval L)
    (hu : ‖u‖ < radius L r κ) :
    ‖sourceKernelSum hL hκ hr hs kind u‖ ≤ derivativeBound L r κ := by
  have h := sourceKernelSum_summable hL hκ hr hs kind u hu
  have hC := (wordConstant_pos hL hr hκ).le
  calc
    _ ≤ ∑' d, ‖positiveDerivative hL hκ hr hs kind (intervalFourierIso L u) d‖ := norm_tsum_le_tsum_norm h
    _ ≤ derivativeBound L r κ := h.tsum_le_tsum (fun d =>
      (positiveDerivative_norm hL hκ hr hs kind _ d).trans (by
        rw [(intervalFourierIso L).norm_map]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hu.le d) (by positivity)))
      (degreeBound_summable hL hκ hr)

lemma sourceKernelSum_positive (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) (u : ScalarInterval L)
    (hu : ‖u‖ < radius L r κ) (v : Seq2) :
    Positive (sourceKernelSum hL hκ hr hs kind u (moduli v)) := by
  have h := sourceKernelSum_summable hL hκ hr hs kind u hu
  have he : (∑' d, positiveDerivative hL hκ hr hs kind (intervalFourierIso L u) d (moduli v)) =
      sourceKernelSum hL hκ hr hs kind u (moduli v) :=
    ((ContinuousLinearMap.apply ℂ Mixed (moduli v)).hasSum h.of_norm.hasSum).tsum_eq
  rw [← he]
  apply positive_tsum
  · exact ((ContinuousLinearMap.apply ℂ Mixed (moduli v)).hasSum h.of_norm.hasSum).summable
  · intro d
    exact positiveDerivative_positive hL hκ hr hs kind _ v d

def actualWordDerivative (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (u : ScalarInterval L) (jl : ℕ × ℕ) : ScalarInterval L →L[ℝ] Mixed :=
  wordDerivative (sourceSum hL hκ hr hs .projection u) (sourceSum hL hκ hr hs .moment u)
    (fderiv ℝ (sourceSum hL hκ hr hs .projection) u) (fderiv ℝ (sourceSum hL hκ hr hs .moment) u) jl

def actualWordKernel (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (u : ScalarInterval L) (jl : ℕ × ℕ) : Seq2 →L[ℂ] Mixed :=
  wordKernel (sourceEnvelope hL hκ hr hs .projection u) (sourceEnvelope hL hκ hr hs .moment u)
    (sourceKernelSum hL hκ hr hs .projection u) (sourceKernelSum hL hκ hr hs .moment u) jl

lemma actualWordKernel_positive (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (u : ScalarInterval L) (hu : ‖u‖ < radius L r κ)
    (jl : ℕ × ℕ) (v : Seq2) : Positive (actualWordKernel hL hκ hr hs u jl (moduli v)) := by
  exact wordKernel_positive
    (sourceSum_majorizes hL hκ hr hs .projection u (input_small hL hκ hr hu)).1
    (sourceSum_majorizes hL hκ hr hs .moment u (input_small hL hκ hr hu)).1
    (sourceKernelSum_positive hL hκ hr hs .projection u hu)
    (sourceKernelSum_positive hL hκ hr hs .moment u hu) jl v

lemma actualWordKernel_majorizes (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (u : ScalarInterval L) (hu : ‖u‖ < radius L r κ)
    (jl : ℕ × ℕ) (v : ScalarInterval L) :
    Majorizes (actualWordKernel hL hκ hr hs u jl (moduli (intervalFourierIso L v)))
      (matrix (actualWordDerivative hL hκ hr hs u jl v)) := by
  have hp := sourceSum_majorizes hL hκ hr hs .projection u (input_small hL hκ hr hu)
  have hm := sourceSum_majorizes hL hκ hr hs .moment u (input_small hL hκ hr hu)
  exact wordKernel_majorizes (intervalFourierIso L) hp.1 hm.1 hp.2.2.2 hm.2.2.2
    (sourceKernelSum_positive hL hκ hr hs .projection u hu)
    (sourceKernelSum_positive hL hκ hr hs .moment u hu)
    (fun v => sourceSum_derivative_domination hL hκ hr hs .projection u v hu)
    (fun v => sourceSum_derivative_domination hL hκ hr hs .moment u v hu) jl v

lemma actualWordKernel_norm (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (u : ScalarInterval L) (hu : ‖u‖ < radius L r κ) (jl : ℕ × ℕ) :
    ‖actualWordKernel hL hκ hr hs u jl‖ ≤
      4*(jl.1+jl.2+1 : ℝ)*derivativeBound L r κ*((1/2 : ℝ)^jl.1*(1/2 : ℝ)^jl.2) := by
  have hp := sourceSum_majorizes hL hκ hr hs .projection u (input_small hL hκ hr hu)
  have hm := sourceSum_majorizes hL hκ hr hs .moment u (input_small hL hκ hr hu)
  exact wordKernel_norm (hp.2.1.trans (by norm_num)) (hm.2.1.trans (by norm_num))
    (derivativeBound_nonneg hL hκ hr) (sourceKernelSum_norm hL hκ hr hs .projection u hu)
    (sourceKernelSum_norm hL hκ hr hs .moment u hu) jl

lemma actualWordDerivative_norm (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (u : ScalarInterval L) (hu : ‖u‖ < radius L r κ) (jl : ℕ × ℕ) :
    ‖actualWordDerivative hL hκ hr hs u jl‖ ≤ ‖actualWordKernel hL hκ hr hs u jl‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  exact (solid_norm (actualWordKernel_positive hL hκ hr hs u hu jl (intervalFourierIso L v))
    (actualWordKernel_majorizes hL hκ hr hs u hu jl v)).trans
    (by simpa only [moduli_norm, (intervalFourierIso L).norm_map] using
      (actualWordKernel hL hκ hr hs u jl).le_opNorm (moduli (intervalFourierIso L v)))

lemma actualWord_hasFDerivAt (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (u : ScalarInterval L) (hu : ‖u‖ < radius L r κ) (jl : ℕ × ℕ) :
    HasFDerivAt (fun v => normalizedWord (sourceSum hL hκ hr hs .projection v)
      (sourceSum hL hκ hr hs .moment v) jl) (actualWordDerivative hL hκ hr hs u jl) u :=
  normalizedWord_hasFDerivAt (sourceSum_hasFDerivAt hL hκ hr hs .projection u hu).differentiableAt.hasFDerivAt
    (sourceSum_hasFDerivAt hL hκ hr hs .moment u hu).differentiableAt.hasFDerivAt jl

lemma sourceSum_zero (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) : sourceSum hL hκ hr hs kind 0 = 0 := by
  unfold sourceSum
  have hz (d : ℕ) : actualCoeff hL hκ hr hs kind (0 : ScalarInterval L) d = 0 := by
    rw [← sourceMultilinear_diagonal]
    exact (sourceMultilinear hL hκ hr hs (Nat.succ_pos d) kind).map_coord_zero (0 : Fin (d+1)) rfl
  simp only [hz, tsum_zero]

lemma actualWords_hasSum (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (u : ScalarInterval L) (hu : ‖u‖ < radius L r κ) :
    HasSum (normalizedWord (sourceSum hL hκ hr hs .projection u) (sourceSum hL hκ hr hs .moment u))
      (normalizedSource hL hκ hr hs u) := by
  have hp := sourceSum_majorizes hL hκ hr hs .projection u (input_small hL hκ hr hu)
  have hm := sourceSum_majorizes hL hκ hr hs .moment u (input_small hL hκ hr hu)
  exact normalizedWord_hasSum _ _ (by linarith [hp.2.2.1])
    (normalizedWord_summable hp.1 hm.1 hp.2.2.2 hm.2.2.2 (by linarith [hp.2.1]))

theorem normalizedSource_hasFDerivAt (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (u : ScalarInterval L) (hu : ‖u‖ < radius L r κ) :
    HasFDerivAt (normalizedSource hL hκ hr hs)
      (∑' jl, actualWordDerivative hL hκ hr hs u jl) u := by
  have hR := radius_pos hL hκ hr
  have hsum : HasFDerivAt (fun v => ∑' jl, normalizedWord (sourceSum hL hκ hr hs .projection v)
      (sourceSum hL hκ hr hs .moment v) jl) (∑' jl, actualWordDerivative hL hκ hr hs u jl) u := by
    apply hasFDerivAt_tsum_of_isPreconnected (wordBound_summable (derivativeBound L r κ))
      isOpen_ball (convex_ball (0 : ScalarInterval L) (radius L r κ)).isPreconnected
      (fun jl v hv => actualWord_hasFDerivAt hL hκ hr hs v (mem_ball_zero_iff.mp hv) jl)
      (fun jl v hv => (actualWordDerivative_norm hL hκ hr hs v (mem_ball_zero_iff.mp hv) jl).trans
        (actualWordKernel_norm hL hκ hr hs v (mem_ball_zero_iff.mp hv) jl))
      (mem_ball_self hR) ?_ (mem_ball_zero_iff.mpr hu)
    have hz (jl : ℕ × ℕ) : normalizedWord (sourceSum hL hκ hr hs .projection (0 : ScalarInterval L))
        (sourceSum hL hκ hr hs .moment 0) jl = 0 := by
      rw [sourceSum_zero hL hκ hr hs .moment]
      change mulRight _ (mulLeft _ 0) = 0
      rw [map_zero, map_zero]
    simpa only [hz] using (summable_zero : Summable (fun _ : ℕ × ℕ => (0 : Mixed)))
  apply hsum.congr_of_eventuallyEq
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hu)] with v hv
  exact (actualWords_hasSum hL hκ hr hs v (mem_ball_zero_iff.mp hv)).tsum_eq.symm

lemma actualWordKernel_summable (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (u : ScalarInterval L) (hu : ‖u‖ < radius L r κ) :
    Summable (fun jl : ℕ × ℕ => ‖actualWordKernel hL hκ hr hs u jl‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (actualWordKernel_norm hL hκ hr hs u hu)
    (wordBound_summable (derivativeBound L r κ))

theorem normalizedSource_derivative_domination (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (u v : ScalarInterval L) (hu : ‖u‖ < radius L r κ) :
    Majorizes ((∑' jl, actualWordKernel hL hκ hr hs u jl) (moduli (intervalFourierIso L v)))
      (matrix (fderiv ℝ (normalizedSource hL hκ hr hs) u v)) := by
  have hp := actualWordKernel_summable hL hκ hr hs u hu
  have hd : Summable (fun jl => ‖actualWordDerivative hL hκ hr hs u jl‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (actualWordDerivative_norm hL hκ hr hs u hu) hp
  have hep : (∑' jl, actualWordKernel hL hκ hr hs u jl (moduli (intervalFourierIso L v))) =
      (∑' jl, actualWordKernel hL hκ hr hs u jl) (moduli (intervalFourierIso L v)) :=
    ((ContinuousLinearMap.apply ℂ Mixed (moduli (intervalFourierIso L v))).hasSum hp.of_norm.hasSum).tsum_eq
  have hed : (∑' jl, actualWordDerivative hL hκ hr hs u jl v) =
      (∑' jl, actualWordDerivative hL hκ hr hs u jl) v :=
    ((ContinuousLinearMap.apply ℝ Mixed v).hasSum hd.of_norm.hasSum).tsum_eq
  rw [(normalizedSource_hasFDerivAt hL hκ hr hs u hu).fderiv, ← hep, ← hed]
  apply majorizes_tsum
  · exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun jl => ContinuousLinearMap.le_opNorm _ _)
      (hp.mul_right ‖moduli (intervalFourierIso L v)‖)
  · exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun jl => ContinuousLinearMap.le_opNorm _ _)
      (hd.mul_right ‖v‖)
  · exact fun jl => actualWordKernel_majorizes hL hκ hr hs u hu jl v

end QuantumNLS.Local006.NormalizedDerivativeJ

#print axioms QuantumNLS.Local006.NormalizedDerivativeJ.normalizedSource_hasFDerivAt
#print axioms QuantumNLS.Local006.NormalizedDerivativeJ.normalizedSource_derivative_domination
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local006.NormalizedDerivativeJ." ||
        n.toString.startsWith "_private.QuantumNLS.Local006NormalizedDerivativeJ" then
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
  Lean.logInfo m!"Local006NormalizedDerivativeJ audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."

