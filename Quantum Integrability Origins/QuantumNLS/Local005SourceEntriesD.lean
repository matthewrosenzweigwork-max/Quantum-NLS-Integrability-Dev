import QuantumNLS.Local005ContourTransferD

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Metric
open scoped BigOperators InnerProductSpace
namespace QuantumNLS.Local005.SourceD
open QuantumNLS.Local005.SourceC
open QuantumNLS.LocalSpectral
open QuantumNLS.ResetFreeResolventLOCAL001
open QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
open QuantumNLS.Local002

variable {L r κ : ℝ} [Fact (0 < L)]

/-- Extend a finite input family by zero; only its first k values enter a degree k word. -/
def extendInputs {k : ℕ} (u : Fin k → ScalarInterval L) (t : ℕ) : ScalarInterval L :=
  if ht : t < k then u ⟨t, ht⟩ else 0

theorem extendInputs_apply_fin {k : ℕ} (u : Fin k → ScalarInterval L) (t : Fin k) :
    extendInputs u t.val = u t := by
  simp only [extendInputs, dif_pos t.isLt]

/-- Ordered independent inputs, retaining the source's order of operator multiplication. -/
def contourPrefix (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (n : ℤ) (u : ℕ → ScalarInterval L) : ℕ → ContourOp L r n
  | 0 => 1
  | k + 1 => potentialContour hL hκ hr hsmall n (u k) * contourPrefix hL hκ hr hsmall n u k

theorem contourPrefix_apply (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (n : ℤ) (u : ℕ → ScalarInterval L)
    (k : ℕ) (z : sphere (center L n) r) :
    contourPrefix hL hκ hr hsmall n u k z =
      operatorPrefix (fun t => Mop κ (free L κ n z) (u t)) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change potentialContour hL hκ hr hsmall n (u k) z *
      contourPrefix hL hκ hr hsmall n u k z = _
    rw [ih]
    rfl

/-- The actual contour-integrated ordered coefficient of S or K. -/
def orderedSourceWord (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (kind : WordKind) (u : ℕ → ScalarInterval L)
    (n : ℤ) (k : ℕ) : Op L :=
  freeProj L κ n r * contourJ hr n (weight kind n
    (freeContour (κ := κ) hL hr hsmall n * contourPrefix hL hκ hr hsmall n u k)) * freeProj L κ n r

/-- A degree k ordered word depends only on the k printed inputs. -/
theorem contourPrefix_congr (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (n : ℤ) (k : ℕ) (u v : ℕ → ScalarInterval L)
    (h : ∀ t < k, u t = v t) :
    contourPrefix hL hκ hr hsmall n u k = contourPrefix hL hκ hr hsmall n v k := by
  have hall : ∀ s, s ≤ k → contourPrefix hL hκ hr hsmall n u s =
      contourPrefix hL hκ hr hsmall n v s := by
    intro s
    induction s with
    | zero => intro _; rfl
    | succ s ih =>
      intro hs
      simp only [contourPrefix]
      rw [h s (by omega), ih (by omega)]
  exact hall k le_rfl

theorem orderedSourceWord_congr (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (kind : WordKind) (n : ℤ) (k : ℕ)
    (u v : ℕ → ScalarInterval L) (h : ∀ t < k, u t = v t) :
    orderedSourceWord hL hκ hr hsmall kind u n k = orderedSourceWord hL hκ hr hsmall kind v n k := by
  unfold orderedSourceWord
  rw [contourPrefix_congr hL hκ hr hsmall n k u v h]

set_option backward.isDefEq.respectTransparency false in
theorem contourPrefix_const (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (n : ℤ) (u : ScalarInterval L) (k : ℕ) :
    contourPrefix hL hκ hr hsmall n (fun _ => u) k = potentialContour hL hκ hr hsmall n u ^ k := by
  ext z : 1
  rw [contourPrefix_apply, ContinuousMap.pow_apply]
  change operatorPrefix (fun _ => Mop κ (free L κ n z) u) k =
    Mop κ (free L κ n z) u ^ k
  exact operatorPrefix_const _ k

theorem orderedSourceWord_const (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (kind : WordKind) (u : ScalarInterval L) (n : ℤ) (k : ℕ) :
    orderedSourceWord hL hκ hr hsmall kind (fun _ => u) n k = sourceWord hL hκ hr hsmall kind u n k := by
  unfold orderedSourceWord sourceWord
  rw [contourPrefix_const]

theorem orderedSourceWord_repeat (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (kind : WordKind) (u : ScalarInterval L) (n : ℤ) (k : ℕ) :
    orderedSourceWord hL hκ hr hsmall kind (extendInputs (fun _ : Fin k => u)) n k =
      sourceWord hL hκ hr hsmall kind u n k := by
  rw [orderedSourceWord_congr hL hκ hr hsmall kind n k
    (extendInputs (fun _ : Fin k => u)) (fun _ => u) (fun t ht => by simp [extendInputs, ht])]
  exact orderedSourceWord_const hL hκ hr hsmall kind u n k

theorem moment_pathIntegrand {k : ℕ} (j : Fin 2) (u : Fin k → ℤ → ℂ)
    (n : ℤ) (q : Fin (k - 1) → ℤ) {z : ℂ} (hz : z - (pm L n : ℂ) ≠ 0) :
    (z - (pm L n : ℂ)) * pathIntegrand L r κ .projection j u n q z =
      pathIntegrand L r κ .moment j u n q z := by
  unfold pathIntegrand endpointOrder
  have hc := mul_inv_cancel₀ hz
  linear_combination
    ((∏ t : Fin k, slotPhase L κ (componentAfter t.val j)) *
      (∏ t : Fin k, u t (QuantumNLS.ResolventWordCoefficientLOCAL005.wordLabel n q t)) *
      (z - (pm L n : ℂ))⁻¹ *
      (∏ t, (z - (pm L (QuantumNLS.ResetFreeResolventLOCAL001.sourceMode n (q t)) : ℂ))⁻¹)) * hc

set_option backward.isDefEq.respectTransparency false in
theorem pathContour_tsum_apply (hL : 0 < L) (hr : 0 < r) (hsmall : r < spacing L / 2)
    (kind : WordKind) {k : ℕ} (j : Fin 2) (u : Fin k → ℤ → ℂ)
    (hu : ∀ t, Summable fun m => ‖u t m‖ ^ 2) (n : ℤ) (z : sphere (center L n) r) :
    (∑' q, pathContour hL hr hsmall κ kind j u n q) z =
      ∑' q, pathIntegrand L r κ kind j u n q z := by
  calc
    _ = ∑' q, (pathContour hL hr hsmall κ kind j u n q) z := by
      simpa only [ContinuousMap.evalCLM_apply] using
        ((ContinuousMap.evalCLM ℂ z).hasSum
          (pathContour_summable hL hr hsmall κ kind j u hu n).of_norm.hasSum).tsum_eq.symm
    _ = _ := by
      apply tsum_congr
      intro q
      rfl

/-- The contour function of each actual matrix entry is exactly the frozen path sum. -/
theorem source_entryContour_eq (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (n : ℤ) (u : ℕ → ScalarInterval L) (k : ℕ)
    (kind : WordKind) (i j : Fin 2) :
    functionalContour n (entryFunctional n i j) (weight kind n
      (freeContour (κ := κ) hL hr hsmall n * contourPrefix hL hκ hr hsmall n u (k + 1))) =
      if i = componentAfter (k + 1) j then
        ∑' q, pathContour hL hr hsmall κ kind j
          (physicalInputs j (fun t : Fin (k + 1) => u t)) n q else 0 := by
  split_ifs with hi
  · ext z : 1
    rw [pathContour_tsum_apply hL hr hsmall kind j _ (physicalInputs_summable j _) n z]
    cases kind with
    | projection =>
      change ⟪chi L n i, (free L κ n z *
        contourPrefix hL hκ hr hsmall n u (k + 1) z) (chi L n j)⟫_ℂ = _
      rw [contourPrefix_apply, source_word_path_sum hL hκ hr hsmall n
        (mem_sphere_iff_norm.mp z.2) u k i j, if_pos hi]
      rfl
    | moment =>
      change ⟪chi L n i, (((z : ℂ) - center L n) • (free L κ n z *
        contourPrefix hL hκ hr hsmall n u (k + 1) z)) (chi L n j)⟫_ℂ = _
      rw [ContinuousLinearMap.smul_apply, inner_smul_right, contourPrefix_apply,
        source_word_path_sum hL hκ hr hsmall n (mem_sphere_iff_norm.mp z.2) u k i j, if_pos hi,
        ← tsum_mul_left]
      apply tsum_congr
      intro q
      apply moment_pathIntegrand
      apply norm_pos_iff.mp
      change 0 < ‖(z : ℂ) - center L n‖
      rw [mem_sphere_iff_norm.mp z.2]
      exact hr
  · ext z : 1
    cases kind with
    | projection =>
      change ⟪chi L n i, (free L κ n z *
        contourPrefix hL hκ hr hsmall n u (k + 1) z) (chi L n j)⟫_ℂ = 0
      rw [contourPrefix_apply, source_word_path_sum hL hκ hr hsmall n
        (mem_sphere_iff_norm.mp z.2) u k i j, if_neg hi]
    | moment =>
      change ⟪chi L n i, (((z : ℂ) - center L n) • (free L κ n z *
        contourPrefix hL hκ hr hsmall n u (k + 1) z)) (chi L n j)⟫_ℂ = 0
      rw [ContinuousLinearMap.smul_apply, inner_smul_right, contourPrefix_apply,
        source_word_path_sum hL hκ hr hsmall n (mem_sphere_iff_norm.mp z.2) u k i j, if_neg hi,
        mul_zero]

/-- The source coefficient equality: independently ordered physical inputs, either contour
weight, both actual free projections, every positive degree. -/
theorem orderedSourceWord_entry (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (n : ℤ) (u : ℕ → ScalarInterval L) (k : ℕ)
    (kind : WordKind) (i j : Fin 2) :
    entryFunctional n i j (orderedSourceWord hL hκ hr hsmall kind u n (k + 1)) =
      coefficientEntry L r κ kind (k + 1)
        (physicalInputs j (fun t : Fin (k + 1) => u t)) n i j := by
  unfold orderedSourceWord
  rw [compressed_contour_entry hL hr hsmall n i j, source_entryContour_eq]
  unfold coefficientEntry
  split_ifs
  · exact (path_integral_hasSum hL hr hsmall κ kind j _
      (physicalInputs_summable j _) n).tsum_eq.symm
  · exact map_zero _

#print axioms orderedSourceWord_const
#print axioms source_entryContour_eq
#print axioms orderedSourceWord_entry
end QuantumNLS.Local005.SourceD

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local005.SourceD." ||
        n.toString.startsWith "_private.QuantumNLS.Local005" then
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
  Lean.logInfo m!"Local005SourceEntriesD audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
