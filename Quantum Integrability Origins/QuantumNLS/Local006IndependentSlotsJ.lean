import QuantumNLS.Local006TaylorBindingI
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Independent-slot multilinearity of the actual contour words, lifted into
 the mixed Fourier sequence space. No derivative identity is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Metric Set
open scoped BigOperators ENNReal
namespace QuantumNLS.Local006.IndependentSlotsJ
open QuantumNLS.Local005 QuantumNLS.Local005.SourceC QuantumNLS.Local005.SourceD
  QuantumNLS.Local006.CoefficientLiftE QuantumNLS.Local006.SequenceAlgebraE
  QuantumNLS.Local006.SequenceEvaluationE QuantumNLS.Local006.PositiveMajorantG
  QuantumNLS.Local006.SourceMajorantG QuantumNLS.Local006.SolidMajorantH
  QuantumNLS.Local006.BinomialBindingH
  QuantumNLS.ResetFreeResolventLOCAL001 QuantumNLS.ResetFreeResolventLOCAL001.CompletionB

variable {L r κ : ℝ} [Fact (0 < L)]

lemma potentialContour_add (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (n : ℤ) (u v : ScalarInterval L) :
    potentialContour hL hκ hr hs n (u+v) =
      potentialContour hL hκ hr hs n u + potentialContour hL hκ hr hs n v := by
  ext z : 1
  exact QuantumNLS.Local002.Mop_add
    ⟨_, (mop_data hL hκ hr hs n (mem_sphere_iff_norm.mp z.2) u).1⟩
    ⟨_, (mop_data hL hκ hr hs n (mem_sphere_iff_norm.mp z.2) v).1⟩

lemma contour_mul_add (n : ℤ) (A B C : ContourOp L r n) : A * (B+C) = A*B + A*C := by
  ext z : 1
  exact ContinuousLinearMap.comp_add (A z) (B z) (C z)

lemma contour_add_mul (n : ℤ) (A B C : ContourOp L r n) : (A+B) * C = A*C + B*C := by
  ext z : 1
  exact ContinuousLinearMap.add_comp (A z) (B z) (C z)

lemma prefix_update_ignored (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (n : ℤ) (u : ℕ → ScalarInterval L)
    (s i : ℕ) (hi : s ≤ i) (v : ScalarInterval L) :
    contourPrefix hL hκ hr hs n (Function.update u i v) s =
      contourPrefix hL hκ hr hs n u s := by
  apply contourPrefix_congr
  intro t ht
  exact Function.update_of_ne (show t ≠ i by omega) v u

lemma prefix_update_add (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (n : ℤ) (u : ℕ → ScalarInterval L)
    (s i : ℕ) (hi : i < s) (v w : ScalarInterval L) :
    contourPrefix hL hκ hr hs n (Function.update u i (v+w)) s =
      contourPrefix hL hκ hr hs n (Function.update u i v) s +
      contourPrefix hL hκ hr hs n (Function.update u i w) s := by
  induction s with
  | zero => omega
  | succ s ih =>
    by_cases he : i = s
    · subst i
      simp only [contourPrefix, Function.update_self, potentialContour_add,
        prefix_update_ignored hL hκ hr hs n u s s le_rfl]
      exact contour_add_mul n _ _ _
    · have his : i < s := by omega
      simp only [contourPrefix, Function.update_of_ne (Ne.symm he), ih his]
      exact contour_mul_add n _ _ _

lemma prefix_update_smul (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (n : ℤ) (u : ℕ → ScalarInterval L)
    (s i : ℕ) (hi : i < s) (c : ℝ) (v : ScalarInterval L) :
    contourPrefix hL hκ hr hs n (Function.update u i (c • v)) s =
      c • contourPrefix hL hκ hr hs n (Function.update u i v) s := by
  induction s with
  | zero => omega
  | succ s ih =>
    by_cases he : i = s
    · subst i
      simp only [contourPrefix, Function.update_self, potentialContour_real_smul,
        prefix_update_ignored hL hκ hr hs n u s s le_rfl]
      rw [smul_mul_assoc]
      exact algebraMap_smul ℂ c
        (potentialContour hL hκ hr hs n v * contourPrefix hL hκ hr hs n u s)
    · have his : i < s := by omega
      simp only [contourPrefix, Function.update_of_ne (Ne.symm he), ih his, mul_smul_comm]

lemma extend_update {k : ℕ} (u : Fin k → ScalarInterval L) (i : Fin k) (v : ScalarInterval L) :
    extendInputs (Function.update u i v) = Function.update (extendInputs u) i.val v := by
  classical
  funext t
  by_cases ht : t < k
  · by_cases he : t = i.val
    · subst t; simp [extendInputs]
    · have hfi : (⟨t, ht⟩ : Fin k) ≠ i := by intro h; exact he (congrArg Fin.val h)
      simp [extendInputs, ht, he, hfi]
  · have he : t ≠ i.val := by intro h; subst t; exact ht i.isLt
    simp [extendInputs, ht, he]

lemma coefficient_update_add (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) {k : ℕ} (kind : WordKind)
    (u : Fin k → ScalarInterval L) (i : Fin k) (v w : ScalarInterval L)
    (n : ℤ) (a b : Fin 2) :
    coefficient hL hκ hr hs k kind (Function.update u i (v+w)) a b n =
      coefficient hL hκ hr hs k kind (Function.update u i v) a b n +
      coefficient hL hκ hr hs k kind (Function.update u i w) a b n := by
  unfold coefficient orderedSourceWord
  rw [extend_update, extend_update, extend_update, prefix_update_add hL hκ hr hs n _ k i.val i.isLt]
  rw [contour_mul_add, map_add, map_add, _root_.mul_add, _root_.add_mul, map_add]

lemma coefficient_update_smul (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) {k : ℕ} (kind : WordKind)
    (u : Fin k → ScalarInterval L) (i : Fin k) (c : ℝ) (v : ScalarInterval L)
    (n : ℤ) (a b : Fin 2) :
    coefficient hL hκ hr hs k kind (Function.update u i (c • v)) a b n =
      c • coefficient hL hκ hr hs k kind (Function.update u i v) a b n := by
  unfold coefficient orderedSourceWord
  rw [extend_update, extend_update, prefix_update_smul hL hκ hr hs n _ k i.val i.isLt]
  rw [mul_smul_comm, (weight kind n).map_smul_of_tower,
    (contourJ hr n).map_smul_of_tower, mul_smul_comm]
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.smul_comp,
    (entryFunctional n a b).map_smul_of_tower]

/-- Independent actual coefficients in the same mixed sequence target as the
frozen diagonal coefficients. -/
def independentCoeff (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) {k : ℕ} (hk : 1 ≤ k) (kind : WordKind)
    (u : Fin k → ScalarInterval L) : Mixed :=
  Classical.choose (solid_lift (physical_majorant hL hκ hr hs hk kind u).choose_spec.1
    (physical_majorant hL hκ hr hs hk kind u).choose_spec.2.2.2)

lemma independentCoeff_spec (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) {k : ℕ} (hk : 1 ≤ k) (kind : WordKind)
    (u : Fin k → ScalarInterval L) :
    (∀ n a b, matrix (independentCoeff hL hκ hr hs hk kind u) n a b =
      coefficient hL hκ hr hs k kind u a b n) ∧
    ‖independentCoeff hL hκ hr hs hk kind u‖ ≤ wordConstant L r κ ^ k * ∏ t, ‖u t‖ := by
  have hm := (physical_majorant hL hκ hr hs hk kind u).choose_spec
  have hl := Classical.choose_spec (solid_lift hm.1 hm.2.2.2)
  exact ⟨fun n a b => congrFun (congrFun (hl.1 n) a) b, hl.2.trans hm.2.1⟩

def sourceMultilinear (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) {k : ℕ} (hk : 1 ≤ k) (kind : WordKind) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k => ScalarInterval L) Mixed :=
  (show MultilinearMap ℝ (fun _ : Fin k => ScalarInterval L) Mixed from
    { toFun := independentCoeff hL hκ hr hs hk kind
      map_update_add' := by
        intro inst u i v w
        cases Subsingleton.elim inst (instDecidableEqFin k)
        apply matrix_ext
        intro n a b
        simp only [matrix_add, Matrix.add_apply, (independentCoeff_spec hL hκ hr hs hk kind _).1]
        exact coefficient_update_add hL hκ hr hs kind u i v w n a b
      map_update_smul' := by
        intro inst u i c v
        cases Subsingleton.elim inst (instDecidableEqFin k)
        apply matrix_ext
        intro n a b
        have hm (x : Mixed) : matrix (c • x) n = c • matrix x n :=
          (evalMatrix n).map_smul_of_tower c x
        rw [hm, Matrix.smul_apply]
        simp only [(independentCoeff_spec hL hκ hr hs hk kind _).1]
        exact coefficient_update_smul hL hκ hr hs kind u i c v n a b }).mkContinuous
    (wordConstant L r κ ^ k) (fun u => (independentCoeff_spec hL hκ hr hs hk kind u).2)

lemma sourceMultilinear_apply (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) {k : ℕ} (hk : 1 ≤ k) (kind : WordKind)
    (u : Fin k → ScalarInterval L) (n : ℤ) (a b : Fin 2) :
    matrix (sourceMultilinear hL hκ hr hs hk kind u) n a b =
      coefficient hL hκ hr hs k kind u a b n :=
  (independentCoeff_spec hL hκ hr hs hk kind u).1 n a b

lemma sourceMultilinear_diagonal (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) (d : ℕ) (u : ScalarInterval L) :
    sourceMultilinear hL hκ hr hs (Nat.succ_pos d) kind (fun _ => u) =
      actualCoeff hL hκ hr hs kind u d := by
  apply matrix_ext
  intro n a b
  rw [sourceMultilinear_apply, (actualCoeff_spec hL hκ hr hs kind u d).1]

lemma sourceMultilinear_norm (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) {k : ℕ} (hk : 1 ≤ k) (kind : WordKind) :
    ‖sourceMultilinear hL hκ hr hs hk kind‖ ≤ wordConstant L r κ ^ k := by
  apply ContinuousMultilinearMap.opNorm_le_bound (pow_nonneg (wordConstant_pos hL hr hκ).le k)
  intro u
  exact (independentCoeff_spec hL hκ hr hs hk kind u).2

end QuantumNLS.Local006.IndependentSlotsJ

#print axioms QuantumNLS.Local006.IndependentSlotsJ.sourceMultilinear
#print axioms QuantumNLS.Local006.IndependentSlotsJ.sourceMultilinear_diagonal
#print axioms QuantumNLS.Local006.IndependentSlotsJ.sourceMultilinear_norm
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local006.IndependentSlotsJ." ||
        n.toString.startsWith "_private.QuantumNLS.Local006IndependentSlotsJ" then
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
  Lean.logInfo m!"Local006IndependentSlotsJ audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."

