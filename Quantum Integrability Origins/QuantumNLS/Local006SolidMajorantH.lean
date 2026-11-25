import QuantumNLS.Local006NormalizedMajorantG

/-! Solidness of the mixed Fourier sequence space and actual source coefficient
lifts. Every coefficient is the frozen source contour word, with its original
independent physical slots. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open scoped BigOperators ENNReal
namespace QuantumNLS.Local006.SolidMajorantH
open QuantumNLS.Local005 QuantumNLS.Local005.SourceD
  QuantumNLS.Local006.CoefficientLiftE QuantumNLS.Local006.SequenceAlgebraE
  QuantumNLS.Local006.SequenceEvaluationE QuantumNLS.Local006.PositiveMajorantG
  QuantumNLS.Local006.SourceMajorantG QuantumNLS.Local006.NormalizedMajorantG
  QuantumNLS.ResetFreeResolventLOCAL001 QuantumNLS.ResetFreeResolventLOCAL001.CompletionB

lemma matrix_ext {a b : Mixed} (h : ∀ n i j, matrix a n i j = matrix b n i j) : a = b := by
  apply Prod.ext <;> apply Prod.ext
  · apply lp.ext; funext n; exact h n 0 0
  · apply lp.ext; funext n; exact h n 1 1
  · apply lp.ext; funext n; exact h n 0 1
  · apply lp.ext; funext n; exact h n 1 0

lemma positive_entry_norm {a : Mixed} (ha : Positive a) (n : ℤ) (i j : Fin 2) :
    ‖matrix a n i j‖ = (matrix a n i j).re := by
  have he : matrix a n i j = ((matrix a n i j).re : ℂ) :=
    Complex.ext (by simp) (by simpa using (ha n i j).1)
  calc
    ‖matrix a n i j‖ = ‖((matrix a n i j).re : ℂ)‖ := congrArg norm he
    _ = (matrix a n i j).re := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha n i j).2]

/-- Coordinate domination retains both the mixed norm and membership. -/
theorem solid_lift {a : Mixed} {F : ℤ → Mat} (ha : Positive a) (hF : Majorizes a F) :
    ∃ b : Mixed, (∀ n, matrix b n = F n) ∧ ‖b‖ ≤ ‖a‖ := by
  have h (n : ℤ) (i j : Fin 2) : ‖F n i j‖ ≤ ‖matrix a n i j‖ := by
    rw [positive_entry_norm ha]; exact hF n i j
  let b00 : SeqInf := ⟨fun n => F n 0 0, (lp.memℓp a.1.1).mono' (fun n => h n 0 0)⟩
  let b11 : SeqInf := ⟨fun n => F n 1 1, (lp.memℓp a.1.2).mono' (fun n => h n 1 1)⟩
  let b01 : Seq2 := ⟨fun n => F n 0 1, (lp.memℓp a.2.1).mono' (fun n => h n 0 1)⟩
  let b10 : Seq2 := ⟨fun n => F n 1 0, (lp.memℓp a.2.2).mono' (fun n => h n 1 0)⟩
  refine ⟨((b00, b11), (b01, b10)), ?_, ?_⟩
  · intro n; ext i j; fin_cases i <;> fin_cases j <;> rfl
  · change max (max ‖b00‖ ‖b11‖) (max ‖b01‖ ‖b10‖) ≤ ‖a‖
    obtain ⟨h00, h11, h01, h10⟩ := component_bounds a
    exact max_le (max_le ((lp.norm_mono (by simp) (fun n => h n 0 0)).trans h00)
      ((lp.norm_mono (by simp) (fun n => h n 1 1)).trans h11))
      (max_le ((lp.norm_mono (by norm_num) (fun n => h n 0 1)).trans h01)
        ((lp.norm_mono (by norm_num) (fun n => h n 1 0)).trans h10))

lemma entry_norm_le (a : Mixed) (n : ℤ) (i j : Fin 2) : ‖matrix a n i j‖ ≤ ‖a‖ := by
  obtain ⟨h00, h11, h01, h10⟩ := component_bounds a
  fin_cases i <;> fin_cases j
  · exact (lp.norm_apply_le_norm (by simp) _ n).trans h00
  · exact (lp.norm_apply_le_norm (by norm_num) _ n).trans h01
  · exact (lp.norm_apply_le_norm (by norm_num) _ n).trans h10
  · exact (lp.norm_apply_le_norm (by simp) _ n).trans h11

lemma majorizes_tsum {ι : Type*} {a b : ι → Mixed}
    (ha : Summable (fun t => ‖a t‖)) (hb : Summable (fun t => ‖b t‖))
    (hm : ∀ t, Majorizes (a t) (matrix (b t))) :
    Majorizes (∑' t, a t) (matrix (∑' t, b t)) := by
  intro n i j
  have hsa := (entryCLM n i j).hasSum ha.of_norm.hasSum
  have hsb := (entryCLM n i j).hasSum hb.of_norm.hasSum
  simp only [entryCLM_apply] at hsa hsb
  have hnorm : Summable (fun t => ‖matrix (b t) n i j‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun t => ?_) hb
    exact entry_norm_le (b t) n i j
  calc
    ‖matrix (∑' t, b t) n i j‖ ≤ ∑' t, ‖matrix (b t) n i j‖ :=
      hsb.tsum_eq ▸ norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' t, (matrix (a t) n i j).re :=
      hnorm.tsum_le_tsum (fun t => hm t n i j) (Complex.hasSum_re hsa).summable
    _ = (matrix (∑' t, a t) n i j).re := (Complex.hasSum_re hsa).tsum_eq

variable {L r κ : ℝ} [Fact (0 < L)]

def actualCoeff (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r) (hs : r < spacing L / 2)
    (kind : WordKind) (u : ScalarInterval L) (d : ℕ) : Mixed :=
  Classical.choose (solid_lift (sourceAbs_spec hL hκ hr hs kind u d).1
    (sourceAbs_spec hL hκ hr hs kind u d).2.2.2)

lemma actualCoeff_spec (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r) (hs : r < spacing L / 2)
    (kind : WordKind) (u : ScalarInterval L) (d : ℕ) :
    (∀ n i j, matrix (actualCoeff hL hκ hr hs kind u d) n i j =
      coefficient hL hκ hr hs (d + 1) kind (fun _ => u) i j n) ∧
      ‖actualCoeff hL hκ hr hs kind u d‖ ≤ ‖sourceAbs hL hκ hr hs kind u d‖ := by
  have h := Classical.choose_spec (solid_lift (sourceAbs_spec hL hκ hr hs kind u d).1
    (sourceAbs_spec hL hκ hr hs kind u d).2.2.2)
  exact ⟨fun n i j => congrFun (congrFun (h.1 n) i) j, h.2⟩

lemma actualCoeff_summable (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) (u : ScalarInterval L)
    (hu : wordConstant L r κ * ‖u‖ < 1 / 8) :
    Summable (fun d => ‖actualCoeff hL hκ hr hs kind u d‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun d => (actualCoeff_spec hL hκ hr hs kind u d).2)
    (sourceAbs_summable hL hκ hr hs kind u hu).1

end QuantumNLS.Local006.SolidMajorantH

#print axioms QuantumNLS.Local006.SolidMajorantH.solid_lift
#print axioms QuantumNLS.Local006.SolidMajorantH.majorizes_tsum
#print axioms QuantumNLS.Local006.SolidMajorantH.actualCoeff_spec
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local006.SolidMajorantH." ||
        n.toString.startsWith "_private.QuantumNLS.Local006SolidMajorantH" then
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
  Lean.logInfo m!"Local006SolidMajorantH audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
