import QuantumNLS.Local006G3Expansion
import QuantumNLS.Local006CubicResiduesG
import QuantumNLS.Local006VerifiedPartF

/-! LOCAL-006, gap LOCAL006-G3-IDENTIFICATION, final step: the computed
normalized source coefficient `factor · [K₃ − ½(S₂K₁ + K₁S₂)]₁₀` equals the
printed

  `g_3(u)_n = (κ/L) [ Σ_{a,b≠n} u_a u_b ū_{a+b−n} / ((p_n−p_a)(p_n−p_b))
                     − u_n Σ_{a≠n} |u_a|² / (p_n−p_a)² ]`

(source `spectral_reduction.tex`, display after the multiplication
coefficients), with `p_a = 2πa/L` and `u_a = (𝓕u)_a` the DEF-001 unitary
Fourier coefficients. The double sum is the unconditional sum over `ℤ × ℤ`;
it is absolutely convergent (proved, from the accepted LOCAL-005 path bound).

Matrix products: `S₂` is diagonal with both entries `−(κ/L) N`, `K₁` has
lower-left entry `2i√(κ/L) u_n` and zero diagonal. The cubic source path sum
(`CubicResiduesG.source_cubic_moment`, all returning paths retained) is split
into the three path classes and reindexed by `a = n + q₀`, `b = n + q₁`. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric Filter Topology Complex
open scoped ENNReal InnerProductSpace ComplexConjugate BigOperators
namespace QuantumNLS.Local006.G3Fourier
open QuantumNLS.LocalSpectral QuantumNLS.Local005 QuantumNLS.Local005.SourceC
  QuantumNLS.Local005.SourceD QuantumNLS.ResetFreeResolventLOCAL001
  QuantumNLS.ResolventWordCoefficientLOCAL005 QuantumNLS.Local006.CubicResiduesG
  QuantumNLS.Local006.G3Expansion QuantumNLS.Local006.CollectiveF QuantumNLS.PhysicalTensor
  QuantumNLS.Local002Bridge QuantumNLS.Local003Analytic

variable {L κ r : ℝ} [Fact (0 < L)]

/-! ### The printed coefficient -/

/-- Summand of the printed double sum `Σ_{a,b≠n}`. -/
def doubleTerm (L : ℝ) (u : ℤ → ℂ) (n : ℤ) (ab : ℤ × ℤ) : ℂ :=
  if ab.1 ≠ n ∧ ab.2 ≠ n then
    u ab.1 * u ab.2 * conj (u (ab.1 + ab.2 - n)) /
      (((pm L n : ℂ) - (pm L ab.1 : ℂ)) * ((pm L n : ℂ) - (pm L ab.2 : ℂ)))
  else 0

/-- Summand of the printed normalization sum `Σ_{a≠n}`. -/
def normTerm (L : ℝ) (u : ℤ → ℂ) (n : ℤ) (a : ℤ) : ℂ :=
  if a ≠ n then ((‖u a‖ ^ 2 : ℝ) : ℂ) / ((pm L n : ℂ) - (pm L a : ℂ)) ^ 2 else 0

/-- `Σ_{a,b≠n} u_a u_b ū_{a+b−n} / ((p_n−p_a)(p_n−p_b))`. -/
def printedDouble (L : ℝ) (u : ℤ → ℂ) (n : ℤ) : ℂ := ∑' ab : ℤ × ℤ, doubleTerm L u n ab

/-- `Σ_{a≠n} |u_a|² / (p_n−p_a)²`. -/
def printedNorm (L : ℝ) (u : ℤ → ℂ) (n : ℤ) : ℂ := ∑' a : ℤ, normTerm L u n a

/-- The printed cubic coefficient `g_3(u)_n`, as a function of the Fourier
coefficients `u_a`. -/
def printedG3 (L κ : ℝ) (u : ℤ → ℂ) (n : ℤ) : ℂ :=
  ((κ / L : ℝ) : ℂ) * (printedDouble L u n - u n * printedNorm L u n)

/-! ### Elementary identities -/

lemma delta_eq (L : ℝ) (n m : ℤ) :
    (pm L n : ℂ) - (pm L (sourceMode n m) : ℂ) = 2 * ((pm L n : ℂ) - (pm L (n + m) : ℂ)) := by
  simp only [pm, sourceMode]
  push_cast
  ring

lemma star_mul_self' (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [RCLike.star_def, Complex.conj_mul', Complex.ofReal_pow]

lemma vec2_zero (a b : ℂ) : vec2 a b 0 = a := rfl
lemma vec2_one (a b : ℂ) : vec2 a b 1 = b := rfl

lemma physicalFourier_toInterval (v : L2T L) (m : ℤ) :
    physicalFourier (toInterval L v : CompletionB.ScalarInterval L) m =
      QuantumNLS.Fourier.fourierL2 L v m := by
  show (QuantumNLS.Fourier.fourierL2 L ((CompletionB.intervalToCircleIso L)
    ((CompletionB.intervalToCircleIso L).symm v))) m = _
  rw [LinearIsometryEquiv.apply_symm_apply]

lemma factor_mul (hL : 0 < L) (hκ : 0 < κ) :
    factor L κ * (2 * I * (Real.sqrt (κ / L) : ℂ) ^ 3) = ((κ / L : ℝ) : ℂ) := by
  have hsq : Real.sqrt (κ / L) = Real.sqrt κ / Real.sqrt L := Real.sqrt_div hκ.le L
  have hkp : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hlp : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have ha : ((Real.sqrt κ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hkp.ne'
  have hb : ((Real.sqrt L : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlp.ne'
  have hκc : ((κ : ℝ) : ℂ) = ((Real.sqrt κ : ℝ) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hκ.le]
  have hLc : ((L : ℝ) : ℂ) = ((Real.sqrt L : ℝ) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hL.le]
  rw [factor, hsq, Complex.ofReal_div, Complex.ofReal_div, hκc, hLc]
  field_simp

/-! ### Entries of the compressed matrix products -/

/-- The lower-left entry of the normalized cubic combination, in terms of the
four relevant source entries. -/
lemma ell_combo (n : ℤ) (X3 X1 Y2 : H2 L →L[ℂ] H2 L) :
    ell (Fm L n X3 - (1 / 2 : ℂ) • (Fm L n Y2 * Fm L n X1 + Fm L n X1 * Fm L n Y2)) =
      entryFunctional n 1 0 X3 - (1 / 2 : ℂ) *
        ((entryFunctional n 0 0 X1 * entryFunctional n 1 0 Y2 +
            entryFunctional n 1 0 X1 * entryFunctional n 1 1 Y2) +
          (entryFunctional n 0 0 Y2 * entryFunctional n 1 0 X1 +
            entryFunctional n 1 0 Y2 * entryFunctional n 1 1 X1)) := by
  rw [ell_apply]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply, PiLp.sub_apply,
    PiLp.smul_apply, PiLp.add_apply, Fm_apply_apply, smul_eq_mul, vec2_zero, vec2_one]
  ring

lemma entry_word (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r) (hs : r < spacing L / 2)
    (w : CompletionB.ScalarInterval L) (n : ℤ) (kind : WordKind) {k : ℕ} (hk : 1 ≤ k)
    (i j : Fin 2) :
    entryFunctional n i j (sourceWord hL hκ hr hs kind w n k) =
      coefficientEntry L r κ kind k (physicalInputs j (fun _ : Fin k => w)) n i j := by
  rw [← orderedSourceWord_const hL hκ hr hs kind w n k]
  exact orderedSourceWord_entry_posdegree hL hκ hr hs n (fun _ => w) hk kind i j

lemma contour_moment_one (hr : 0 < r) (n : ℤ) (q : Fin (1 - 1) → ℤ) :
    contourScalar L r .moment n q = 1 := by
  have hprod (z : ℂ) : (∏ i : Fin (1 - 1), (z - (pm L (sourceMode n (q i)) : ℂ))⁻¹) = 1 :=
    Finset.prod_eq_one (fun i _ => Fin.elim0 i)
  simp only [contourScalar, endpointOrder, hprod, mul_one, pow_one]
  rw [circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_self hr), smul_eq_mul,
    inv_mul_cancel₀ Complex.two_pi_I_ne_zero]

lemma cA00 : componentAfter 0 (0 : Fin 2) = 0 := by decide
lemma cA10 : componentAfter 1 (0 : Fin 2) = 1 := by decide
lemma cA01 : componentAfter 0 (1 : Fin 2) = 1 := by decide
lemma cA11 : componentAfter 1 (1 : Fin 2) = 0 := by decide
lemma one_ne_zero' : (1 : Fin 2) ≠ 0 := by decide

/-- `K₁` lower-left entry: the linear coefficient `2i√(κ/L) u_n`. -/
lemma entry_K1 (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r) (hs : r < spacing L / 2)
    (w : CompletionB.ScalarInterval L) (n : ℤ) :
    entryFunctional n 1 0 (sourceWord hL hκ hr hs .moment w n 1) =
      2 * I * (Real.sqrt (κ / L) : ℂ) * physicalFourier w n := by
  rw [entry_word hL hκ hr hs w n .moment le_rfl, coefficientEntry, if_pos (by decide)]
  rw [tsum_eq_single (fun i => Fin.elim0 i : Fin (1 - 1) → ℤ)
    (fun q hq => absurd (funext fun i => Fin.elim0 i) hq)]
  simp [pathCoefficient, contour_moment_one hr, slotPhase, wordLabel, previousShift,
    nextShift, physicalInputs, physicalSlot, cA00]

/-- `K₁` has zero diagonal (odd degree). -/
lemma entry_K1_diag (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r) (hs : r < spacing L / 2)
    (w : CompletionB.ScalarInterval L) (n : ℤ) (j : Fin 2) :
    entryFunctional n j j (sourceWord hL hκ hr hs .moment w n 1) = 0 := by
  rw [entry_word hL hκ hr hs w n .moment le_rfl, coefficientEntry]
  exact if_neg (by fin_cases j <;> decide)

/-- `S₂` has zero off-diagonal (even degree). -/
lemma entry_S2_off (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r) (hs : r < spacing L / 2)
    (w : CompletionB.ScalarInterval L) (n : ℤ) :
    entryFunctional n 1 0 (sourceWord hL hκ hr hs .projection w n 2) = 0 := by
  rw [entry_word hL hκ hr hs w n .projection (by norm_num), coefficientEntry]
  exact if_neg (by decide)

lemma phase_pair (j : Fin 2) :
    slotPhase L κ (componentAfter 0 j) * slotPhase L κ (componentAfter 1 j) =
      4 * (Real.sqrt (κ / L) : ℂ) ^ 2 := by
  fin_cases j
  · simp only [Fin.zero_eta, cA00, cA10, slotPhase, ↓reduceIte, one_ne_zero', if_false]
    linear_combination (-4 * (Real.sqrt (κ / L) : ℂ) ^ 2) * Complex.I_sq
  · simp only [Fin.mk_one, cA01, cA11, slotPhase, ↓reduceIte, one_ne_zero', if_false]
    linear_combination (-4 * (Real.sqrt (κ / L) : ℂ) ^ 2) * Complex.I_sq

lemma slot_pair (j : Fin 2) (w : CompletionB.ScalarInterval L) (m : ℤ) :
    physicalSlot (componentAfter 0 j) w m * physicalSlot (componentAfter 1 j) w m =
      ((‖physicalFourier w m‖ ^ 2 : ℝ) : ℂ) := by
  fin_cases j
  · simp only [Fin.zero_eta, cA00, cA10, physicalSlot, ↓reduceIte, one_ne_zero', if_false]
    rw [Complex.mul_conj', Complex.ofReal_pow]
  · simp only [Fin.mk_one, cA01, cA11, physicalSlot, ↓reduceIte, one_ne_zero', if_false]
    rw [Complex.conj_mul', Complex.ofReal_pow]

/-- `S₂` diagonal entries: `−(κ/L) Σ_{a≠n} |u_a|²/(p_n−p_a)²` (negative sign). -/
lemma entry_S2_diag (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r) (hs : r < spacing L / 2)
    (w : CompletionB.ScalarInterval L) (n : ℤ) (j : Fin 2) :
    entryFunctional n j j (sourceWord hL hκ hr hs .projection w n 2) =
      -((Real.sqrt (κ / L) : ℂ) ^ 2) * printedNorm L (physicalFourier w) n := by
  rw [entry_word hL hκ hr hs w n .projection (by norm_num), coefficientEntry,
    if_pos (by fin_cases j <;> decide)]
  have hinj : Function.Injective (fun m : ℤ => (fun _ : Fin (2 - 1) => m)) :=
    fun a b h => congrFun h ⟨0, by norm_num⟩
  have hsupp : Function.support (fun q : Fin (2 - 1) → ℤ =>
      pathCoefficient L r κ .projection j (physicalInputs j (fun _ : Fin 2 => w)) n q) ⊆
      Set.range (fun m : ℤ => (fun _ : Fin (2 - 1) => m)) := by
    intro q _
    refine ⟨q ⟨0, by norm_num⟩, funext fun i => ?_⟩
    have hi := i.isLt
    exact congrArg q (Fin.ext (show 0 = i.val by omega))
  rw [← hinj.tsum_eq hsupp, printedNorm, ← tsum_mul_left]
  have hterm : ∀ m : ℤ,
      pathCoefficient L r κ .projection j (physicalInputs j (fun _ : Fin 2 => w)) n
        (fun _ : Fin (2 - 1) => m) =
      -((Real.sqrt (κ / L) : ℂ) ^ 2) * normTerm L (physicalFourier w) n (n + m) := by
    intro m
    rw [pathCoefficient, projection_two_scalar hL hr hs n, Fin.prod_univ_two, Fin.prod_univ_two]
    simp only [Fin.val_zero, Fin.val_one, physicalInputs, wordLabel, previousShift,
      nextShift, ↓reduceDIte, ↓reduceIte, dite_true, dite_false, eq_self_iff_true,
      show ¬ ((0 : ℕ) + 1 = 2) by decide, show (1 : ℕ) + 1 = 2 by decide,
      show ¬ ((1 : ℕ) = 0) by decide, add_zero]
    by_cases hm : m = 0
    · subst hm
      simp [normTerm]
    · rw [if_neg hm, normTerm, if_pos (by omega), delta_eq]
      have hp := phase_pair (L := L) (κ := κ) j
      have hq := slot_pair j w (n + m)
      generalize (pm L n : ℂ) - (pm L (n + m) : ℂ) = d
      linear_combination
        (-(d⁻¹ ^ 2) / 4 *
          physicalSlot (componentAfter 0 j) w (n + m) *
          physicalSlot (componentAfter 1 j) w (n + m)) * hp +
        (-((Real.sqrt (κ / L) : ℂ) ^ 2) * d⁻¹ ^ 2) * hq
  have hshift : ∑' m : ℤ, -((Real.sqrt (κ / L) : ℂ) ^ 2) *
      normTerm L (physicalFourier w) n (n + m) =
      ∑' a : ℤ, -((Real.sqrt (κ / L) : ℂ) ^ 2) * normTerm L (physicalFourier w) n a :=
    (Equiv.addLeft n).tsum_eq (fun a => -((Real.sqrt (κ / L) : ℂ) ^ 2) *
      normTerm L (physicalFourier w) n a)
  rw [← hshift]
  exact tsum_congr hterm

/-! ### The cubic path sum, split into its three path classes -/

/-- Exact residue of a length-three moment path (`CubicResiduesG.moment_three_scalar`). -/
def resid (L : ℝ) (n : ℤ) (q : Fin 2 → ℤ) : ℂ :=
  if q 0 = 0 then (if q 1 = 0 then 0 else
    -(((pm L n : ℂ) - (pm L (sourceMode n (q 1)) : ℂ))⁻¹ ^ 2))
  else if q 1 = 0 then -(((pm L n : ℂ) - (pm L (sourceMode n (q 0)) : ℂ))⁻¹ ^ 2)
  else ((pm L n : ℂ) - (pm L (sourceMode n (q 0)) : ℂ))⁻¹ *
    ((pm L n : ℂ) - (pm L (sourceMode n (q 1)) : ℂ))⁻¹

/-- The summand of `CubicResiduesG.source_cubic_moment`. -/
def cubicTerm (L κ : ℝ) (u : ℤ → ℂ) (n : ℤ) (q : Fin 2 → ℤ) : ℂ :=
  (8 * I * (Real.sqrt (κ / L) : ℂ) ^ 3) * u (n + q 0) * star (u (n + q 0 + q 1)) *
    u (n + q 1) * resid L n q

def pieceGen (f : (Fin 2 → ℤ) → ℂ) (q : Fin 2 → ℤ) : ℂ :=
  if q 0 ≠ 0 ∧ q 1 ≠ 0 then f q else 0
def pieceLeft (f : (Fin 2 → ℤ) → ℂ) (q : Fin 2 → ℤ) : ℂ :=
  if q 0 = 0 then f q else 0
def pieceRight (f : (Fin 2 → ℤ) → ℂ) (q : Fin 2 → ℤ) : ℂ :=
  if q 0 ≠ 0 ∧ q 1 = 0 then f q else 0

lemma piece_summable {f : (Fin 2 → ℤ) → ℂ} (hf : Summable fun q => ‖f q‖)
    (P : (Fin 2 → ℤ) → ℂ) (hP : ∀ q, P q = f q ∨ P q = 0) : Summable P := by
  refine Summable.of_norm_bounded hf (fun q => ?_)
  rcases hP q with h | h
  · rw [h]
  · rw [h, norm_zero]; exact norm_nonneg _

lemma vec_eq (q : Fin 2 → ℤ) : q = ![q 0, q 1] := by
  ext i; fin_cases i <;> rfl

theorem cubic_split (u : ℤ → ℂ) (n : ℤ)
    (hsum : Summable fun q : Fin 2 → ℤ => ‖cubicTerm L κ u n q‖) :
    ∑' q, cubicTerm L κ u n q = (8 * I * (Real.sqrt (κ / L) : ℂ) ^ 3) *
      (printedDouble L u n / 4 - u n * printedNorm L u n / 2) := by
  have hsplit : ∀ q, cubicTerm L κ u n q = pieceGen (cubicTerm L κ u n) q + pieceLeft (cubicTerm L κ u n) q + pieceRight (cubicTerm L κ u n) q := by
    intro q
    by_cases h0 : q 0 = 0 <;> by_cases h1 : q 1 = 0 <;>
      simp [pieceGen, pieceLeft, pieceRight, h0, h1]
  have hs1 := piece_summable hsum (pieceGen (cubicTerm L κ u n)) (fun q => by
    unfold pieceGen; split_ifs <;> simp)
  have hs2 := piece_summable hsum (pieceLeft (cubicTerm L κ u n)) (fun q => by
    unfold pieceLeft; split_ifs <;> simp)
  have hs3 := piece_summable hsum (pieceRight (cubicTerm L κ u n)) (fun q => by
    unfold pieceRight; split_ifs <;> simp)
  have htot : ∑' q, cubicTerm L κ u n q = ∑' q, pieceGen (cubicTerm L κ u n) q + ∑' q, pieceLeft (cubicTerm L κ u n) q + ∑' q, pieceRight (cubicTerm L κ u n) q := by
    rw [tsum_congr hsplit, Summable.tsum_add (hs1.add hs2) hs3, Summable.tsum_add hs1 hs2]
  -- generic paths: reindex by (a, b) = (n + q₀, n + q₁)
  have hg1 : Function.Injective (fun ab : ℤ × ℤ => (![ab.1 - n, ab.2 - n] : Fin 2 → ℤ)) := by
    intro x y h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h0 h1
    exact Prod.ext (by omega) (by omega)
  have hsp1 : Function.support (pieceGen (cubicTerm L κ u n)) ⊆
      Set.range (fun ab : ℤ × ℤ => (![ab.1 - n, ab.2 - n] : Fin 2 → ℤ)) := by
    intro q _
    refine ⟨(q 0 + n, q 1 + n), ?_⟩
    ext i; fin_cases i <;> simp
  have hv1 : ∀ ab : ℤ × ℤ, pieceGen (cubicTerm L κ u n) (![ab.1 - n, ab.2 - n] : Fin 2 → ℤ) =
      (8 * I * (Real.sqrt (κ / L) : ℂ) ^ 3) / 4 * doubleTerm L u n ab := by
    rintro ⟨a, b⟩
    simp only [pieceGen, doubleTerm, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, sub_ne_zero]
    by_cases hab : a ≠ n ∧ b ≠ n
    · rw [if_pos hab, if_pos hab, cubicTerm, resid]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        sub_eq_zero, if_neg hab.1, if_neg hab.2, delta_eq]
      have e1 : n + (a - n) = a := by ring
      have e2 : n + (a - n) + (b - n) = a + b - n := by ring
      have e3 : n + (b - n) = b := by ring
      have e4 : a + (b - n) = a + b - n := by ring
      try simp only [e1, e2, e3, e4]
      rw [RCLike.star_def]
      generalize (pm L n : ℂ) - (pm L a : ℂ) = da
      generalize (pm L n : ℂ) - (pm L b : ℂ) = db
      ring
    · rw [if_neg hab, if_neg hab, mul_zero]
  -- paths returning after the first step: q = (0, m)
  have hg2 : Function.Injective (fun m : ℤ => (![0, m] : Fin 2 → ℤ)) := by
    intro x y h
    have h1 := congrFun h 1
    simpa using h1
  have hsp2 : Function.support (pieceLeft (cubicTerm L κ u n)) ⊆
      Set.range (fun m : ℤ => (![0, m] : Fin 2 → ℤ)) := by
    intro q hq
    have h0 : q 0 = 0 := by
      by_contra h
      exact hq (by simp [pieceLeft, h])
    refine ⟨q 1, ?_⟩
    ext i; fin_cases i <;> simp [h0]
  have hv2 : ∀ m : ℤ, pieceLeft (cubicTerm L κ u n) (![0, m] : Fin 2 → ℤ) =
      -((8 * I * (Real.sqrt (κ / L) : ℂ) ^ 3) / 4) * (u n * normTerm L u n (n + m)) := by
    intro m
    simp only [pieceLeft, cubicTerm, resid, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, eq_self_iff_true, ↓reduceIte, add_zero]
    by_cases hm : m = 0
    · subst hm
      simp [normTerm]
    · have hnm : n + m ≠ n := by omega
      simp only [hm, hnm, normTerm, ↓reduceIte, not_false_eq_true, ne_eq]
      rw [delta_eq]
      have hq := star_mul_self' (u (n + m))
      generalize (pm L n : ℂ) - (pm L (n + m) : ℂ) = d
      linear_combination (-((8 * I * (Real.sqrt (κ / L) : ℂ) ^ 3) / 4) * u n * d⁻¹ ^ 2) * hq
  -- paths returning after the second step: q = (m, 0), m ≠ 0
  have hg3 : Function.Injective (fun m : ℤ => (![m, 0] : Fin 2 → ℤ)) := by
    intro x y h
    have h0 := congrFun h 0
    simpa using h0
  have hsp3 : Function.support (pieceRight (cubicTerm L κ u n)) ⊆
      Set.range (fun m : ℤ => (![m, 0] : Fin 2 → ℤ)) := by
    intro q hq
    have h1 : q 1 = 0 := by
      by_contra h
      exact hq (by simp [pieceRight, h])
    refine ⟨q 0, ?_⟩
    ext i; fin_cases i <;> simp [h1]
  have hv3 : ∀ m : ℤ, pieceRight (cubicTerm L κ u n) (![m, 0] : Fin 2 → ℤ) =
      -((8 * I * (Real.sqrt (κ / L) : ℂ) ^ 3) / 4) * (u n * normTerm L u n (n + m)) := by
    intro m
    simp only [pieceRight, cubicTerm, resid, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, eq_self_iff_true, and_true, ↓reduceIte, add_zero]
    by_cases hm : m = 0
    · subst hm
      simp [normTerm]
    · have hnm : n + m ≠ n := by omega
      simp only [hm, hnm, normTerm, ↓reduceIte, not_false_eq_true, ne_eq]
      rw [delta_eq]
      have hq := star_mul_self' (u (n + m))
      generalize (pm L n : ℂ) - (pm L (n + m) : ℂ) = d
      linear_combination (-((8 * I * (Real.sqrt (κ / L) : ℂ) ^ 3) / 4) * u n * d⁻¹ ^ 2) * hq
  have hshift : ∑' m : ℤ, -((8 * I * (Real.sqrt (κ / L) : ℂ) ^ 3) / 4) * (u n * normTerm L u n (n + m)) =
      -((8 * I * (Real.sqrt (κ / L) : ℂ) ^ 3) / 4) * (u n * printedNorm L u n) := by
    rw [tsum_mul_left, tsum_mul_left, printedNorm]
    congr 2
    exact (Equiv.addLeft n).tsum_eq (normTerm L u n)
  rw [htot, ← hg1.tsum_eq hsp1, ← hg2.tsum_eq hsp2, ← hg3.tsum_eq hsp3,
    tsum_congr hv1, tsum_congr hv2, tsum_congr hv3, hshift, tsum_mul_left, ← printedDouble]
  ring


/-! ### Absolute convergence of the printed sums -/

lemma gen_inj (n : ℤ) :
    Function.Injective (fun ab : ℤ × ℤ => (![ab.1 - n, ab.2 - n] : Fin 2 → ℤ)) := by
  intro x y h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h0 h1
  exact Prod.ext (by omega) (by omega)

lemma gen_value (u : ℤ → ℂ) (n : ℤ) (ab : ℤ × ℤ) :
    pieceGen (cubicTerm L κ u n) (![ab.1 - n, ab.2 - n] : Fin 2 → ℤ) =
      (8 * I * (Real.sqrt (κ / L) : ℂ) ^ 3) / 4 * doubleTerm L u n ab := by
  obtain ⟨a, b⟩ := ab
  simp only [pieceGen, doubleTerm, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, sub_ne_zero]
  by_cases hab : a ≠ n ∧ b ≠ n
  · rw [if_pos hab, if_pos hab, cubicTerm, resid]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      sub_eq_zero, if_neg hab.1, if_neg hab.2, delta_eq]
    have e1 : n + (a - n) = a := by ring
    have e2 : n + (a - n) + (b - n) = a + b - n := by ring
    have e3 : n + (b - n) = b := by ring
    have e4 : a + (b - n) = a + b - n := by ring
    try simp only [e1, e2, e3, e4]
    rw [RCLike.star_def]
    generalize (pm L n : ℂ) - (pm L a : ℂ) = da
    generalize (pm L n : ℂ) - (pm L b : ℂ) = db
    ring
  · rw [if_neg hab, if_neg hab, mul_zero]

lemma double_summable (u : ℤ → ℂ) (n : ℤ)
    (hK : (8 * I * (Real.sqrt (κ / L) : ℂ) ^ 3) / 4 ≠ 0)
    (hsum : Summable fun q : Fin 2 → ℤ => ‖cubicTerm L κ u n q‖) :
    Summable fun ab : ℤ × ℤ => ‖doubleTerm L u n ab‖ := by
  have h1 : Summable fun q : Fin 2 → ℤ => ‖pieceGen (cubicTerm L κ u n) q‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun q => by unfold pieceGen; split_ifs <;> simp) hsum
  have h2 := h1.comp_injective (gen_inj n)
  have h3 : Summable fun ab : ℤ × ℤ =>
      ‖(8 * I * (Real.sqrt (κ / L) : ℂ) ^ 3) / 4‖ * ‖doubleTerm L u n ab‖ :=
    h2.congr (fun ab => by simp only [Function.comp_apply, gen_value, norm_mul])
  exact (summable_mul_left_iff (norm_ne_zero_iff.mpr hK)).mp h3

lemma normTerm_bound (hL : 0 < L) (u : ℤ → ℂ) (n a : ℤ) :
    ‖normTerm L u n a‖ ≤ (L / (2 * Real.pi)) ^ 2 * ‖u a‖ ^ 2 := by
  unfold normTerm
  split_ifs with h
  · have hd : 2 * Real.pi / L ≤ ‖(pm L n : ℂ) - (pm L a : ℂ)‖ := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have e : pm L n - pm L a = 2 * Real.pi * ((n - a : ℤ) : ℝ) / L := by
        unfold pm; push_cast; ring
      have h1 : (1 : ℝ) ≤ |((n - a : ℤ) : ℝ)| := by
        have := Int.one_le_abs (sub_ne_zero.mpr (Ne.symm h))
        exact_mod_cast this
      rw [e, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
        abs_of_pos hL, div_le_div_iff_of_pos_right hL]
      nlinarith [Real.pi_pos]
    have hp : 0 < 2 * Real.pi / L := by positivity
    have hdpos : 0 < ‖(pm L n : ℂ) - (pm L a : ℂ)‖ := lt_of_lt_of_le hp hd
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    have hsq : (2 * Real.pi / L) ^ 2 ≤ ‖(pm L n : ℂ) - (pm L a : ℂ)‖ ^ 2 :=
      pow_le_pow_left₀ hp.le hd 2
    have hk : (L / (2 * Real.pi)) ^ 2 * (2 * Real.pi / L) ^ 2 = 1 := by
      field_simp
    calc ‖u a‖ ^ 2 = (L / (2 * Real.pi)) ^ 2 * ‖u a‖ ^ 2 * (2 * Real.pi / L) ^ 2 := by
          rw [mul_assoc, mul_comm (‖u a‖ ^ 2), ← mul_assoc, hk, one_mul]
      _ ≤ (L / (2 * Real.pi)) ^ 2 * ‖u a‖ ^ 2 * ‖(pm L n : ℂ) - (pm L a : ℂ)‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
  · simp only [norm_zero]
    positivity

lemma cubic_term_summable (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r) (hs : r < spacing L / 2)
    (w : CompletionB.ScalarInterval L) (n : ℤ) :
    Summable fun q : Fin 2 → ℤ => ‖cubicTerm L κ (physicalFourier w) n q‖ := by
  have hpt : ∀ q : Fin (3 - 1) → ℤ,
      pathCoefficient L r κ .moment 0 (physicalInputs 0 (fun _ : Fin 3 => w)) n q =
        (8 * I * (Real.sqrt (κ / L) : ℂ) ^ 3) *
          physicalFourier w (n + q 0) *
          star (physicalFourier w (n + q 0 + q 1)) *
          physicalFourier w (n + q 1) *
          (if q 0 = 0 then (if q 1 = 0 then 0 else
            -(((pm L n : ℂ) - (pm L (sourceMode n (q 1)) : ℂ))⁻¹ ^ 2))
          else if q 1 = 0 then -(((pm L n : ℂ) - (pm L (sourceMode n (q 0)) : ℂ))⁻¹ ^ 2)
          else ((pm L n : ℂ) - (pm L (sourceMode n (q 0)) : ℂ))⁻¹ *
            ((pm L n : ℂ) - (pm L (sourceMode n (q 1)) : ℂ))⁻¹) := by
    intro q
    rw [cubic_word_labels, moment_three_scalar hL hr hs]
    simp [physicalInputs, physicalSlot, componentAfter]
  have hc := (coefficient_converges hL hr hs κ .moment (physicalInputs 0 (fun _ : Fin 3 => w))
    (physicalInputs_summable 0 _) n 1 0).1
  have hsum' := Summable.congr hc (fun q => congrArg norm (hpt q))
  exact hsum'

/-- Both printed sums converge absolutely, for every `u ∈ L²(𝕋_L)`; their
`tsum` values are genuine sums. -/
theorem printed_sums_summable (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (v : L2T L) (n : ℤ) :
    Summable (fun ab : ℤ × ℤ =>
      ‖doubleTerm L (fun m => QuantumNLS.Fourier.fourierL2 L v m) n ab‖) ∧
    Summable (fun a : ℤ =>
      ‖normTerm L (fun m => QuantumNLS.Fourier.fourierL2 L v m) n a‖) := by
  have hpf : physicalFourier (toInterval L v : CompletionB.ScalarInterval L) =
      fun m => QuantumNLS.Fourier.fourierL2 L v m :=
    funext (physicalFourier_toInterval v)
  have hK : (8 * I * (Real.sqrt (κ / L) : ℂ) ^ 3) / 4 ≠ 0 := by
    have hs0 : ((Real.sqrt (κ / L) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (div_pos hκ hL)).ne'
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
      (pow_ne_zero _ hs0)) (by norm_num)
  have hc := cubic_term_summable hL hκ hr hs (toInterval L v : CompletionB.ScalarInterval L) n
  rw [hpf] at hc
  have hsq := (physicalFourier_sq (toInterval L v : CompletionB.ScalarInterval L)).1
  simp only [physicalFourier_toInterval] at hsq
  refine ⟨double_summable _ n hK hc, ?_⟩
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (normTerm_bound hL _ n)
    (hsq.mul_left _)

/-- `K₃` lower-left entry, with every returning path retained. -/
lemma entry_K3 (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r) (hs : r < spacing L / 2)
    (w : CompletionB.ScalarInterval L) (n : ℤ) :
    entryFunctional n 1 0 (sourceWord hL hκ hr hs .moment w n 3) =
      (8 * I * (Real.sqrt (κ / L) : ℂ) ^ 3) *
        (printedDouble L (physicalFourier w) n / 4 -
          physicalFourier w n * printedNorm L (physicalFourier w) n / 2) := by
  have h := source_cubic_moment hL hκ hr hs w n
  rw [orderedSourceWord_const] at h
  have h' : entryFunctional n 1 0 (sourceWord hL hκ hr hs .moment w n 3) =
      ∑' q : Fin 2 → ℤ, cubicTerm L κ (physicalFourier w) n q := h
  have hpt : ∀ q : Fin (3 - 1) → ℤ,
      pathCoefficient L r κ .moment 0 (physicalInputs 0 (fun _ : Fin 3 => w)) n q =
        (8 * I * (Real.sqrt (κ / L) : ℂ) ^ 3) *
          physicalFourier w (n + q 0) *
          star (physicalFourier w (n + q 0 + q 1)) *
          physicalFourier w (n + q 1) *
          (if q 0 = 0 then (if q 1 = 0 then 0 else
            -(((pm L n : ℂ) - (pm L (sourceMode n (q 1)) : ℂ))⁻¹ ^ 2))
          else if q 1 = 0 then -(((pm L n : ℂ) - (pm L (sourceMode n (q 0)) : ℂ))⁻¹ ^ 2)
          else ((pm L n : ℂ) - (pm L (sourceMode n (q 0)) : ℂ))⁻¹ *
            ((pm L n : ℂ) - (pm L (sourceMode n (q 1)) : ℂ))⁻¹) := by
    intro q
    rw [cubic_word_labels, moment_three_scalar hL hr hs]
    simp [physicalInputs, physicalSlot, componentAfter]
  have hc := (coefficient_converges hL hr hs κ .moment (physicalInputs 0 (fun _ : Fin 3 => w))
    (physicalInputs_summable 0 _) n 1 0).1
  have hsum' := Summable.congr hc (fun q => congrArg norm (hpt q))
  have hsum : Summable fun q : Fin 2 → ℤ => ‖cubicTerm L κ (physicalFourier w) n q‖ := hsum'
  rw [h', cubic_split _ _ hsum]

/-! ### Identification -/

/-- The computed normalized source coefficient is the printed `g_3`. -/
theorem cubicCoeff_eq_printed (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r) (hs : r < spacing L / 2)
    (v : L2T L) (n : ℤ) :
    cubicCoeff hL hκ hr hs v n =
      printedG3 L κ (fun m => QuantumNLS.Fourier.fourierL2 L v m) n := by
  have hpf : physicalFourier (toInterval L v : CompletionB.ScalarInterval L) =
      fun m => QuantumNLS.Fourier.fourierL2 L v m :=
    funext (physicalFourier_toInterval v)
  have hK3 := entry_K3 hL hκ hr hs (toInterval L v : CompletionB.ScalarInterval L) n
  have hK1 := entry_K1 hL hκ hr hs (toInterval L v : CompletionB.ScalarInterval L) n
  have hK1d := entry_K1_diag hL hκ hr hs (toInterval L v : CompletionB.ScalarInterval L) n
  have hS2o := entry_S2_off hL hκ hr hs (toInterval L v : CompletionB.ScalarInterval L) n
  have hS2d := entry_S2_diag hL hκ hr hs (toInterval L v : CompletionB.ScalarInterval L) n
  rw [hpf] at hK3 hK1 hS2d
  have hf := factor_mul hL hκ
  unfold cubicCoeff Sw Kw
  rw [ell_combo, hK3, hK1, hK1d 0, hK1d 1, hS2o, hS2d 0, hS2d 1, printedG3]
  linear_combination (printedDouble L (fun m => QuantumNLS.Fourier.fourierL2 L v m) n -
    QuantumNLS.Fourier.fourierL2 L v n *
      printedNorm L (fun m => QuantumNLS.Fourier.fourierL2 L v m) n) * hf

/-- **LOCAL006-G3-IDENTIFICATION.** For every analytic map `G` agreeing with
the actual chart `scalarG` on a ball about zero (as in
`Local006VerifiedPartF.reset_collective_spectral_verified_part`), and every
power series `p` of `G` at zero, the genuine cubic Taylor coefficient is the
printed `g_3`, coordinatewise in every Fourier mode. -/
theorem p3_eq_printed_g3 (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hr2 : r < 2 * Real.pi / L) {ρ : ℝ} (hρ : 0 < ρ) {G : L2T L → Seq}
    {p : FormalMultilinearSeries ℝ (L2T L) Seq} (hp : HasFPowerSeriesAt G p 0)
    (hGe : ∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ, G u n = scalarG L κ r u n)
    (u : L2T L) (n : ℤ) :
    p 3 (fun _ => u) n = printedG3 L κ (fun m => QuantumNLS.Fourier.fourierL2 L u m) n := by
  rw [p3_coord hL hκ hr hr2 (hsmall_of hr2) hρ hp hGe u n,
    cubicCoeff_eq_printed hL hκ hr (hsmall_of hr2) u n]

/-- The verified LOCAL-006 partial theorem, with the cubic Taylor coefficient
now identified with the printed `g_3` (the printed double Fourier sum minus its
normalization sum). The absolute-majorant clauses are not part of this
statement. -/
theorem reset_collective_spectral_verified_part_g3 (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hr2 : r < 2 * Real.pi / L) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ (G : L2T L → Seq)
      (p : FormalMultilinearSeries ℝ (L2T L) Seq)
      (e : OpenPartialHomeomorph (L2T L) Seq),
      AnalyticOnNhd ℝ G (ball 0 ρ) ∧ HasFPowerSeriesAt G p 0 ∧
      (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ, G u n = scalarG L κ r u n) ∧
      G 0 = 0 ∧ fderiv ℝ G 0 =
        (QuantumNLS.Local006.FirstJetF.fourierR L : L2T L →L[ℝ] Seq) ∧
      (e : L2T L → Seq) = G ∧ (0 : L2T L) ∈ e.source ∧ (0 : Seq) ∈ e.target ∧
      e.symm 0 = 0 ∧ AnalyticAt ℝ (e.symm : Seq → L2T L) 0 ∧
      (∀ k : ℕ, Even k → ∀ u : L2T L, p k (fun _ => u) = 0) ∧
      (∀ u ∈ ball (0 : L2T L) ρ,
        ‖G u - QuantumNLS.Local006.FirstJetF.fourierR L u - p 3 (fun _ => u)‖ ≤ C * ‖u‖ ^ 5) ∧
      (∀ u ∈ ball (0 : L2T L) ρ,
        ‖fderiv ℝ G u - (QuantumNLS.Local006.FirstJetF.fourierR L : L2T L →L[ℝ] Seq)‖ ≤
          C * ‖u‖ ^ 2) ∧
      (∀ (u : L2T L) (n : ℤ),
        p 3 (fun _ => u) n = printedG3 L κ (fun m => QuantumNLS.Fourier.fourierL2 L u m) n) ∧
      (∀ (u : L2T L) (n : ℤ),
        Summable (fun ab : ℤ × ℤ =>
          ‖doubleTerm L (fun m => QuantumNLS.Fourier.fourierL2 L u m) n ab‖) ∧
        Summable (fun a : ℤ =>
          ‖normTerm L (fun m => QuantumNLS.Fourier.fourierL2 L u m) n a‖)) := by
  obtain ⟨ρ, hρ, C, hC, G, p, e, hG, hp, hGe, hG0, hF, he, hs, ht, hi, hai, heven, h5, hder⟩ :=
    QuantumNLS.Local006.VerifiedPartF.reset_collective_spectral_verified_part hL hκ hr hr2
  exact ⟨ρ, hρ, C, hC, G, p, e, hG, hp, hGe, hG0, hF, he, hs, ht, hi, hai, heven, h5, hder,
    fun u n => p3_eq_printed_g3 hL hκ hr hr2 hρ hp hGe u n,
    fun u n => printed_sums_summable hL hκ hr (hsmall_of hr2) u n⟩

end QuantumNLS.Local006.G3Fourier

#print axioms QuantumNLS.Local006.G3Fourier.entry_S2_diag
#print axioms QuantumNLS.Local006.G3Fourier.cubic_split
#print axioms QuantumNLS.Local006.G3Fourier.entry_K3
#print axioms QuantumNLS.Local006.G3Fourier.cubicCoeff_eq_printed
#print axioms QuantumNLS.Local006.G3Fourier.printed_sums_summable
#print axioms QuantumNLS.Local006.G3Fourier.p3_eq_printed_g3
#print axioms QuantumNLS.Local006.G3Fourier.reset_collective_spectral_verified_part_g3

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local006.G3Fourier." ||
        n.toString.startsWith "_private.QuantumNLS.Local006G3Fourier" then
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
  Lean.logInfo m!"Local006G3Fourier audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
