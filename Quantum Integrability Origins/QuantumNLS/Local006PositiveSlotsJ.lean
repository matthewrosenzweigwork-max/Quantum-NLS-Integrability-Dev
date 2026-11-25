import QuantumNLS.Local006SlotDerivativeJ

/-! The absolute Fourier-path coefficients themselves as bounded multilinear
 maps. Inserting a Fourier direction gives bounded positive kernel operators. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open scoped BigOperators ENNReal
namespace QuantumNLS.Local006.PositiveSlotsJ
open QuantumNLS.Local005 QuantumNLS.Local005.SourceC QuantumNLS.Local005.SourceD
  QuantumNLS.Local006.CoefficientLiftE
  QuantumNLS.Local006.SequenceAlgebraE QuantumNLS.Local006.SequenceEvaluationE
  QuantumNLS.Local006.PositiveMajorantG QuantumNLS.Local006.SourceMajorantG
  QuantumNLS.Local006.SolidMajorantH QuantumNLS.Local006.BinomialBindingH
  QuantumNLS.ResetFreeResolventLOCAL001 QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
  QuantumNLS.ResolventWordEstimateStage2LOCAL005

variable {L r κ : ℝ}

lemma seq_summable (u : Seq2) : Summable (fun m => ‖u m‖^2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.memℓp u).summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)

lemma input_norm {k : ℕ} (u : Fin k → Seq2) (t : Fin k) :
    inputL2Norm (fun i => (u i : ℤ → ℂ)) t = ‖u t‖ := by
  unfold inputL2Norm
  have h := lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (u t)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

/-- Positive coefficient at a single independent Fourier path. -/
def pathForm (kind : WordKind) {k : ℕ} (n : ℤ) (q : Fin (k-1) → ℤ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin k => Seq2) ℂ :=
  (((2 * Real.sqrt (κ/L))^k * ‖contourScalar L r kind n q‖ : ℝ) : ℂ) •
    (ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin k) ℂ).compContinuousLinearMap
      (fun t => lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2
        (QuantumNLS.ResolventWordCoefficientLOCAL005.wordLabel n q t))

lemma pathForm_apply (kind : WordKind) {k : ℕ} (n : ℤ) (q : Fin (k-1) → ℤ)
    (u : Fin k → Seq2) :
    pathForm (L := L) (r := r) (κ := κ) kind n q u =
      (((2 * Real.sqrt (κ/L))^k * ‖contourScalar L r kind n q‖ : ℝ) : ℂ) *
        ∏ t, u t (QuantumNLS.ResolventWordCoefficientLOCAL005.wordLabel n q t) := by
  simp [pathForm, ContinuousMultilinearMap.mkPiAlgebra_apply, lp.evalCLM]

lemma pathForm_norm (kind : WordKind) {k : ℕ} (n : ℤ) (q : Fin (k-1) → ℤ)
    (u : Fin k → Seq2) :
    ‖pathForm (L := L) (r := r) (κ := κ) kind n q u‖ =
      contourAbsTerm L r κ kind (fun t => (u t : ℤ → ℂ)) n q := by
  simp [pathForm_apply, contourAbsTerm, amplitude, norm_mul, norm_prod, abs_mul, abs_pow,
    abs_of_nonneg (Real.sqrt_nonneg (κ/L)), mul_assoc, mul_left_comm, mul_comm]

lemma pathForm_summable (hL : 0 < L) (hr : 0 < r) (hs : r < spacing L / 2)
    (kind : WordKind) {k : ℕ} (u : Fin k → Seq2) (n : ℤ) :
    Summable (fun q => ‖pathForm (L := L) (r := r) (κ := κ) kind n q u‖) := by
  simpa only [pathForm_norm] using
    (contour_majorant_data hL hr hs κ kind (fun t => (u t : ℤ → ℂ))
      (fun t => seq_summable (u t)) n).1

def pathSumEntry (kind : WordKind) {k : ℕ} (u : Fin k → Seq2)
    (n : ℤ) (a b : Fin 2) : ℂ :=
  if a = componentAfter k b then ∑' q, pathForm (L := L) (r := r) (κ := κ) kind n q u else 0

lemma pathSumEntry_bound (hL : 0 < L) (hr : 0 < r) (hs : r < spacing L / 2)
    (kind : WordKind) {k : ℕ} (u : Fin k → Seq2) (n : ℤ) (a b : Fin 2) :
    ‖pathSumEntry (L := L) (r := r) (κ := κ) kind u n a b‖ ≤
      if a = componentAfter k b then contourMajorant L r κ kind k (fun t => (u t : ℤ → ℂ)) n else 0 := by
  unfold pathSumEntry
  split_ifs
  · simpa only [contourMajorant, pathForm_norm] using
      norm_tsum_le_tsum_norm (pathForm_summable hL hr hs kind u n)
  · simp

lemma pathSumEntry_add (hL : 0 < L) (hr : 0 < r) (hs : r < spacing L / 2)
    (kind : WordKind) {k : ℕ} (u : Fin k → Seq2) (i : Fin k) (v w : Seq2)
    (n : ℤ) (a b : Fin 2) :
    pathSumEntry (L := L) (r := r) (κ := κ) kind (Function.update u i (v+w)) n a b =
      pathSumEntry (L := L) (r := r) (κ := κ) kind (Function.update u i v) n a b +
      pathSumEntry (L := L) (r := r) (κ := κ) kind (Function.update u i w) n a b := by
  unfold pathSumEntry
  split_ifs
  · simp only [ContinuousMultilinearMap.map_update_add]
    exact Summable.tsum_add (pathForm_summable hL hr hs kind _ n).of_norm
      (pathForm_summable hL hr hs kind _ n).of_norm
  · simp

lemma pathSumEntry_smul (kind : WordKind) {k : ℕ} (u : Fin k → Seq2) (i : Fin k)
    (c : ℂ) (v : Seq2) (n : ℤ) (a b : Fin 2) :
    pathSumEntry (L := L) (r := r) (κ := κ) kind (Function.update u i (c • v)) n a b =
      c • pathSumEntry (L := L) (r := r) (κ := κ) kind (Function.update u i v) n a b := by
  unfold pathSumEntry
  split_ifs
  · simp only [ContinuousMultilinearMap.map_update_smul, tsum_const_smul'']
  · simp

def pathLift (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) {k : ℕ} (hk : 1 ≤ k) (kind : WordKind)
    (u : Fin k → Seq2) : Mixed := by
  let h := independent_majorant hL hκ hr hs hk kind (fun t => (u t : ℤ → ℂ))
    (fun t => seq_summable (u t))
  exact Classical.choose (solid_lift (F := pathSumEntry (L := L) (r := r) (κ := κ) kind u) h.choose_spec.1 (fun n a b => by
    rw [h.choose_spec.2.2.1]
    simpa only [apply_ite, Complex.ofReal_re, Complex.zero_re] using
      pathSumEntry_bound (κ := κ) hL hr hs kind u n a b))

lemma pathLift_spec (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) {k : ℕ} (hk : 1 ≤ k) (kind : WordKind)
    (u : Fin k → Seq2) :
    (∀ n a b, matrix (pathLift hL hκ hr hs hk kind u) n a b =
      pathSumEntry (L := L) (r := r) (κ := κ) kind u n a b) ∧
    ‖pathLift hL hκ hr hs hk kind u‖ ≤ wordConstant L r κ ^ k * ∏ t, ‖u t‖ := by
  let h := independent_majorant hL hκ hr hs hk kind (fun t => (u t : ℤ → ℂ))
    (fun t => seq_summable (u t))
  have hh : Majorizes h.choose (pathSumEntry (L := L) (r := r) (κ := κ) kind u) := by
    intro n a b
    rw [h.choose_spec.2.2.1]
    simpa only [apply_ite, Complex.ofReal_re, Complex.zero_re] using
      pathSumEntry_bound (κ := κ) hL hr hs kind u n a b
  have hl := Classical.choose_spec (solid_lift h.choose_spec.1 hh)
  refine ⟨fun n a b => congrFun (congrFun (hl.1 n) a) b, hl.2.trans ?_⟩
  simpa only [input_norm] using h.choose_spec.2.1

def positiveMultilinear (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) {k : ℕ} (hk : 1 ≤ k) (kind : WordKind) :
    ContinuousMultilinearMap ℂ (fun _ : Fin k => Seq2) Mixed :=
  (show MultilinearMap ℂ (fun _ : Fin k => Seq2) Mixed from
    { toFun := pathLift hL hκ hr hs hk kind
      map_update_add' := by
        intro inst u i v w
        cases Subsingleton.elim inst (instDecidableEqFin k)
        apply matrix_ext
        intro n a b
        simp only [matrix_add, Matrix.add_apply, (pathLift_spec hL hκ hr hs hk kind _).1]
        exact pathSumEntry_add hL hr hs kind u i v w n a b
      map_update_smul' := by
        intro inst u i c v
        cases Subsingleton.elim inst (instDecidableEqFin k)
        apply matrix_ext
        intro n a b
        simp only [matrix_smul, Matrix.smul_apply, (pathLift_spec hL hκ hr hs hk kind _).1]
        exact pathSumEntry_smul kind u i c v n a b }).mkContinuous
    (wordConstant L r κ ^ k) (fun u => (pathLift_spec hL hκ hr hs hk kind u).2)

lemma positiveMultilinear_norm (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) {k : ℕ} (hk : 1 ≤ k) (kind : WordKind) :
    ‖positiveMultilinear hL hκ hr hs hk kind‖ ≤ wordConstant L r κ ^ k := by
  apply ContinuousMultilinearMap.opNorm_le_bound (pow_nonneg (wordConstant_pos hL hr hκ).le k)
  exact fun u => (pathLift_spec hL hκ hr hs hk kind u).2

/-- Freeze the other inputs and insert one independent Fourier direction.
The resulting operator retains the absolute path coefficients. -/
def positiveSlot (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) {k : ℕ} (hk : 1 ≤ k) (kind : WordKind)
    (u : Fin k → Seq2) (i : Fin k) : Seq2 →L[ℂ] Mixed :=
  (positiveMultilinear hL hκ hr hs hk kind).toContinuousLinearMap u i

lemma positiveSlot_entry (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) {k : ℕ} (hk : 1 ≤ k) (kind : WordKind)
    (u : Fin k → Seq2) (i : Fin k) (v : Seq2) (n : ℤ) (a b : Fin 2) :
    matrix (positiveSlot hL hκ hr hs hk kind u i v) n a b =
      pathSumEntry (L := L) (r := r) (κ := κ) kind (Function.update u i v) n a b :=
  (pathLift_spec hL hκ hr hs hk kind _).1 n a b

/-- Coordinatewise Fourier moduli belong to the same full l2 space. -/
def moduli (u : Seq2) : Seq2 :=
  ⟨fun m => (‖u m‖ : ℂ), (lp.memℓp u).mono' (fun m => by simp)⟩

@[simp] lemma moduli_apply (u : Seq2) (m : ℤ) : moduli u m = (‖u m‖ : ℂ) := rfl

lemma moduli_norm (u : Seq2) : ‖moduli u‖ = ‖u‖ := by
  apply le_antisymm
  · exact lp.norm_mono (by norm_num) (fun m => by simp)
  · exact lp.norm_mono (by norm_num) (fun m => by simp)

lemma pathForm_moduli (kind : WordKind) {k : ℕ} (n : ℤ) (q : Fin (k-1) → ℤ)
    (u : Fin k → Seq2) :
    pathForm (L := L) (r := r) (κ := κ) kind n q (fun t => moduli (u t)) =
      (contourAbsTerm L r κ kind (fun t => (u t : ℤ → ℂ)) n q : ℂ) := by
  rw [pathForm_apply]
  simp only [moduli_apply, contourAbsTerm, amplitude, Complex.ofReal_mul,
    Complex.ofReal_prod, Complex.ofReal_pow]
  ring

lemma positiveMultilinear_moduli_entry (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) {k : ℕ} (hk : 1 ≤ k) (kind : WordKind)
    (u : Fin k → Seq2) (n : ℤ) (a b : Fin 2) :
    matrix (positiveMultilinear hL hκ hr hs hk kind (fun t => moduli (u t))) n a b =
      if a = componentAfter k b then
        (contourMajorant L r κ kind k (fun t => (u t : ℤ → ℂ)) n : ℂ) else 0 := by
  change matrix (pathLift hL hκ hr hs hk kind (fun t => moduli (u t))) n a b = _
  rw [(pathLift_spec hL hκ hr hs hk kind _).1]
  unfold pathSumEntry
  simp only [pathForm_moduli, contourMajorant, Complex.ofReal_tsum]

lemma positiveMultilinear_moduli_positive (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) {k : ℕ} (hk : 1 ≤ k) (kind : WordKind)
    (u : Fin k → Seq2) :
    Positive (positiveMultilinear hL hκ hr hs hk kind (fun t => moduli (u t))) := by
  intro n a b
  rw [positiveMultilinear_moduli_entry]
  split_ifs
  · exact ⟨by simp, by simpa using
      (contour_majorant_data hL hr hs κ kind (fun t => (u t : ℤ → ℂ))
        (fun t => seq_summable (u t)) n).2.1⟩
  · simp

lemma positiveSlot_norm_bound (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) {k : ℕ} (hk : 1 ≤ k) (kind : WordKind)
    (u : Fin k → Seq2) (i : Fin k) (v : Seq2) :
    ‖positiveSlot hL hκ hr hs hk kind u i v‖ ≤
      wordConstant L r κ ^ k * ∏ t, ‖Function.update u i v t‖ :=
  (pathLift_spec hL hκ hr hs hk kind _).2

variable [Fact (0 < L)]

lemma contourMajorant_physical {k : ℕ} (kind : WordKind)
    (u : Fin k → ScalarInterval L) (n : ℤ) :
    contourMajorant L r κ kind k (fun t => (intervalFourierIso L (u t) : ℤ → ℂ)) n =
      physicalMajorant L r κ kind k (extendInputs u) n := by
  unfold physicalMajorant contourMajorant contourAbsTerm amplitude
  simp only [physicalInputs, extendInputs_apply_fin, physicalSlot_norm, physicalFourier]

/-- The bounded positive multilinear map is the actual Fourier-path envelope
for the frozen physical source words, including the conjugated input slots. -/
theorem physical_domination (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) {k : ℕ} (hk : 1 ≤ k) (kind : WordKind)
    (u : Fin k → ScalarInterval L) :
    Majorizes (positiveMultilinear hL hκ hr hs hk kind
      (fun t => moduli (intervalFourierIso L (u t))))
      (matrix (QuantumNLS.Local006.IndependentSlotsJ.sourceMultilinear hL hκ hr hs hk kind u)) := by
  have h := (physical_majorant hL hκ hr hs hk kind u).choose_spec
  intro n a b
  rw [positiveMultilinear_moduli_entry, contourMajorant_physical,
    QuantumNLS.Local006.IndependentSlotsJ.sourceMultilinear_apply]
  have hc := h.2.2.2 n a b
  rw [h.2.2.1] at hc
  simpa only [apply_ite, Complex.ofReal_re, Complex.zero_re] using hc

def positiveDerivative (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) (u : Seq2) (d : ℕ) : Seq2 →L[ℂ] Mixed :=
  ∑ i : Fin (d+1), positiveSlot hL hκ hr hs (Nat.succ_pos d) kind (fun _ => moduli u) i

lemma positiveDerivative_apply (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) (u v : Seq2) (d : ℕ) :
    positiveDerivative hL hκ hr hs kind u d v =
      ∑ i : Fin (d+1), positiveMultilinear hL hκ hr hs (Nat.succ_pos d) kind
        (Function.update (fun _ => moduli u) i v) := by
  simp [positiveDerivative, positiveSlot]

lemma inserted_moduli (u v : Seq2) {k : ℕ} (i : Fin k) :
    Function.update (fun _ => moduli u) i (moduli v) =
      fun t => moduli (Function.update (fun _ => u) i v t) := by
  funext t
  by_cases ht : t = i <;> simp [Function.update_apply, ht]

lemma inserted_norm (u v : Seq2) (d : ℕ) (i : Fin (d+1)) :
    (∏ t : Fin (d+1), ‖Function.update (fun _ => moduli u) i v t‖) = ‖v‖ * ‖u‖^d := by
  have h : (fun t : Fin (d+1) => ‖Function.update (fun _ => moduli u) i v t‖) =
      Function.update (fun _ => ‖u‖) i ‖v‖ := by
    funext t
    by_cases ht : t = i <;> simp [Function.update_apply, ht, moduli_norm]
  rw [h, Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem (Finset.mem_univ i)]

lemma positiveDerivative_norm (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) (u : Seq2) (d : ℕ) :
    ‖positiveDerivative hL hκ hr hs kind u d‖ ≤
      (d+1 : ℝ) * wordConstant L r κ ^ (d+1) * ‖u‖^d := by
  have hC := (wordConstant_pos hL hr hκ).le
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [positiveDerivative_apply]
  calc
    _ ≤ ∑ i : Fin (d+1), ‖positiveMultilinear hL hκ hr hs (Nat.succ_pos d) kind
      (Function.update (fun _ => moduli u) i v)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin (d+1), wordConstant L r κ ^ (d+1) * (‖v‖ * ‖u‖^d) :=
      Finset.sum_le_sum fun i hi =>
        (pathLift_spec hL hκ hr hs (Nat.succ_pos d) kind _).2.trans_eq (by rw [inserted_norm])
    _ = _ := by simp; ring

theorem physical_derivative_domination (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) (u v : ScalarInterval L) (d : ℕ) :
    Majorizes (positiveDerivative hL hκ hr hs kind (intervalFourierIso L u) d
      (moduli (intervalFourierIso L v)))
      (matrix (QuantumNLS.Local006.SlotDerivativeJ.sourceDerivative hL hκ hr hs kind u d v)) := by
  intro n a b
  rw [positiveDerivative_apply, QuantumNLS.Local006.SlotDerivativeJ.sourceDerivative_apply,
    ← entryCLM_apply n a b, map_sum]
  have he : ∀ f : Fin (d+1) → Mixed, matrix (∑ i, f i) n a b =
      ∑ i, matrix (f i) n a b := by
    intro f
    rw [← entryCLM_apply n a b, map_sum]
    simp only [entryCLM_apply]
  rw [he, Complex.re_sum]
  simp only [entryCLM_apply]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  have hp := physical_domination hL hκ hr hs (Nat.succ_pos d) kind
    (Function.update (fun _ => u) i v) n a b
  have heq : Function.update (fun _ : Fin (d+1) => moduli (intervalFourierIso L u)) i
      (moduli (intervalFourierIso L v)) =
      fun t => moduli (intervalFourierIso L (Function.update (fun _ => u) i v t)) := by
    funext t
    by_cases ht : t = i <;> simp [Function.update_apply, ht]
  rw [heq]
  exact hp

lemma positiveDerivative_summable (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) (u : Seq2)
    (hu : wordConstant L r κ * ‖u‖ < 1) :
    Summable (fun d => ‖positiveDerivative hL hκ hr hs kind u d‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (positiveDerivative_norm hL hκ hr hs kind u)
  exact QuantumNLS.Local006.TransposeMajorantG.differentiated_geometric_summable
    (wordConstant_pos hL hr hκ).le (norm_nonneg u) hu

lemma positiveDerivative_positive (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) (u v : Seq2) (d : ℕ) :
    Positive (positiveDerivative hL hκ hr hs kind u d (moduli v)) := by
  rw [positiveDerivative_apply]
  intro n a b
  have he : matrix (∑ i : Fin (d+1), positiveMultilinear hL hκ hr hs (Nat.succ_pos d) kind
      (Function.update (fun _ => moduli u) i (moduli v))) n a b =
      ∑ i : Fin (d+1), matrix (positiveMultilinear hL hκ hr hs (Nat.succ_pos d) kind
        (Function.update (fun _ => moduli u) i (moduli v))) n a b := by
    rw [← entryCLM_apply n a b, map_sum]
    simp only [entryCLM_apply]
  rw [he]
  have hpos (i : Fin (d+1)) :
      Positive (positiveMultilinear hL hκ hr hs (Nat.succ_pos d) kind
        (Function.update (fun _ => moduli u) i (moduli v))) := by
    rw [inserted_moduli]
    exact positiveMultilinear_moduli_positive hL hκ hr hs (Nat.succ_pos d) kind _
  exact ⟨by simp only [Complex.im_sum]; exact Finset.sum_eq_zero fun i hi => (hpos i n a b).1,
    by simp only [Complex.re_sum]; exact Finset.sum_nonneg fun i hi => (hpos i n a b).2⟩

def lowerLeft : Mixed →L[ℂ] Seq2 :=
  (ContinuousLinearMap.snd ℂ Seq2 Seq2).comp
    (ContinuousLinearMap.snd ℂ (SeqInf × SeqInf) (Seq2 × Seq2))

/-- The lower-left absolute source derivative kernel acts boundedly on l2.
Its definition retains every absolute path coefficient and differentiated slot. -/
def sourceKernel (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) (u : Seq2) (d : ℕ) : Seq2 →L[ℂ] Seq2 :=
  lowerLeft.comp (positiveDerivative hL hκ hr hs kind u d)

lemma sourceKernel_norm (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) (u : Seq2) (d : ℕ) :
    ‖sourceKernel hL hκ hr hs kind u d‖ ≤
      (d+1 : ℝ) * wordConstant L r κ ^ (d+1) * ‖u‖^d := by
  have hC := (wordConstant_pos hL hr hκ).le
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  exact (component_bounds (positiveDerivative hL hκ hr hs kind u d v)).2.2.2.trans
    (((positiveDerivative hL hκ hr hs kind u d).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (positiveDerivative_norm hL hκ hr hs kind u d) (norm_nonneg v)))

lemma sourceKernel_domination (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) (u v : ScalarInterval L) (d : ℕ) (n : ℤ) :
    ‖(QuantumNLS.Local006.SlotDerivativeJ.sourceDerivative hL hκ hr hs kind u d v).2.2 n‖ ≤
      (sourceKernel hL hκ hr hs kind (intervalFourierIso L u) d
        (moduli (intervalFourierIso L v)) n).re := by
  simpa [matrix, sourceKernel, lowerLeft] using
    physical_derivative_domination hL hκ hr hs kind u v d n 1 0

lemma moduli_single (m : ℤ) : moduli (lp.single 2 m (1 : ℂ)) = lp.single 2 m (1 : ℂ) := by
  apply lp.ext
  funext n
  by_cases hn : n = m <;> simp [moduli_apply, lp.single_apply, hn]

lemma sourceKernel_entry_positive (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) (u : Seq2) (d : ℕ) (n m : ℤ) :
    (sourceKernel hL hκ hr hs kind u d (lp.single 2 m 1) n).im = 0 ∧
      0 ≤ (sourceKernel hL hκ hr hs kind u d (lp.single 2 m 1) n).re := by
  have h := positiveDerivative_positive hL hκ hr hs kind u (lp.single 2 m 1) d n 1 0
  rw [moduli_single] at h
  exact h

/-- The Hilbert adjoint of this real positive kernel has the transposed
entries, and keeps the same operator norm. -/
theorem sourceKernel_transpose (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) (u : Seq2) (d : ℕ) :
    ‖ContinuousLinearMap.adjoint (sourceKernel hL hκ hr hs kind u d)‖ =
      ‖sourceKernel hL hκ hr hs kind u d‖ ∧
      ∀ n m : ℤ,
        ContinuousLinearMap.adjoint (sourceKernel hL hκ hr hs kind u d) (lp.single 2 n 1) m =
          sourceKernel hL hκ hr hs kind u d (lp.single 2 m 1) n := by
  refine ⟨ContinuousLinearMap.adjoint.norm_map _, ?_⟩
  intro n m
  have h := (sourceKernel hL hκ hr hs kind u d).adjoint_inner_right
    (lp.single 2 m 1) (lp.single 2 n 1)
  simp only [lp.inner_single_left, lp.inner_single_right, RCLike.inner_apply,
    starRingEnd_apply, star_one, one_mul, mul_one] at h
  rw [h]
  apply Complex.ext <;> simp [(sourceKernel_entry_positive hL hκ hr hs kind u d n m).1]

theorem sourceKernel_summable (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) (u : Seq2)
    (hu : wordConstant L r κ * ‖u‖ < 1) :
    Summable (fun d => ‖sourceKernel hL hκ hr hs kind u d‖) ∧
      Summable (fun d => ‖ContinuousLinearMap.adjoint (sourceKernel hL hκ hr hs kind u d)‖) := by
  have h : Summable (fun d => ‖sourceKernel hL hκ hr hs kind u d‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (sourceKernel_norm hL hκ hr hs kind u)
      (QuantumNLS.Local006.TransposeMajorantG.differentiated_geometric_summable
        (wordConstant_pos hL hr hκ).le (norm_nonneg u) hu)
  exact ⟨h, by simpa only [ContinuousLinearMap.adjoint.norm_map] using h⟩

end QuantumNLS.Local006.PositiveSlotsJ

#print axioms QuantumNLS.Local006.PositiveSlotsJ.positiveMultilinear_norm
#print axioms QuantumNLS.Local006.PositiveSlotsJ.positiveSlot_entry
#print axioms QuantumNLS.Local006.PositiveSlotsJ.physical_derivative_domination
#print axioms QuantumNLS.Local006.PositiveSlotsJ.positiveDerivative_norm
#print axioms QuantumNLS.Local006.PositiveSlotsJ.positiveDerivative_summable
#print axioms QuantumNLS.Local006.PositiveSlotsJ.sourceKernel_domination
#print axioms QuantumNLS.Local006.PositiveSlotsJ.sourceKernel_transpose
#print axioms QuantumNLS.Local006.PositiveSlotsJ.sourceKernel_summable
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local006.PositiveSlotsJ." ||
        n.toString.startsWith "_private.QuantumNLS.Local006PositiveSlotsJ" then
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
  Lean.logInfo m!"Local006PositiveSlotsJ audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."

