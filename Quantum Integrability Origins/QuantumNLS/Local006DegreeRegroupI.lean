import QuantumNLS.Local006WordExpansionI

/-! Regroup the expanded ordered source words by their total physical degree.
The rearrangements are justified in Banach norm, before evaluating coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open scoped BigOperators ENNReal
namespace QuantumNLS.Local006.DegreeRegroupI
open QuantumNLS.Local006.CoefficientLiftE QuantumNLS.Local006.SequenceAlgebraE
  QuantumNLS.Local006.SequenceEvaluationE QuantumNLS.Local006.PositiveMajorantG
  QuantumNLS.Local006.SolidMajorantH QuantumNLS.Local006.BinomialBindingH
  QuantumNLS.Local006.WordExpansionI

def degreeEnvelope (a b : ℕ → Mixed) (d : ℕ) : Mixed :=
  ∑' w : {w : AllWords // totalDegree w = d}, rawTerm a b w.1.1 w.1.2

def degreeCoefficient (a b : ℕ → Mixed) (d : ℕ) : Mixed :=
  ∑' w : {w : AllWords // totalDegree w = d}, weightedTerm a b w.1

lemma norm_fiber_summable {ι : Type*} (f : ι → Mixed) (degree : ι → ℕ)
    (hf : Summable (fun i => ‖f i‖)) :
    Summable (fun d => ‖∑' i : {i // degree i = d}, f i.1‖) := by
  have hs := hf.hasSum.tsum_fiberwise degree
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun d => ?_) hs.summable
  exact norm_tsum_le_tsum_norm (hf.subtype _)

lemma powerTerm_positive (a : ℕ → Mixed) (ha : ∀ d, Positive (a d)) (j : ℕ) :
    ∀ z, Positive (powerTerm a j z) := by
  induction j with
  | zero => intro z; exact positive_unit
  | succ j ih => intro z; exact positive_mul (ha z.1) (ih z.2)

lemma raw_positive (a b : ℕ → Mixed) (ha : ∀ d, Positive (a d))
    (hb : ∀ d, Positive (b d)) (w : AllWords) : Positive (rawTerm a b w.1 w.2) :=
  positive_mul (positive_mul (powerTerm_positive a ha _ _) (hb _)) (powerTerm_positive a ha _ _)

lemma powerTerm_majorizes (a s : ℕ → Mixed) (ha : ∀ d, Positive (a d))
    (hs : ∀ d, Majorizes (a d) (matrix (s d))) (j : ℕ) :
    ∀ z, Majorizes (powerTerm a j z) (matrix (powerTerm s j z)) := by
  induction j with
  | zero =>
    intro z n i k
    rw [show powerTerm s 0 z = unit from rfl, show powerTerm a 0 z = unit from rfl]
    exact le_of_eq (positive_entry_norm positive_unit n i k)
  | succ j ih =>
    intro z n i k
    simpa only [powerTerm, matrix_mul] using
      majorizes_mul (ha z.1) (powerTerm_positive a ha j z.2) (hs z.1) (ih z.2) n i k

lemma raw_majorizes (a b s k : ℕ → Mixed) (ha : ∀ d, Positive (a d))
    (hb : ∀ d, Positive (b d)) (hs : ∀ d, Majorizes (a d) (matrix (s d)))
    (hk : ∀ d, Majorizes (b d) (matrix (k d))) (w : AllWords) :
    Majorizes (rawTerm a b w.1 w.2) (matrix (weightedTerm s k w)) := by
  have hl := powerTerm_positive a ha w.1.1 w.2.1.1
  have hr := powerTerm_positive a ha w.1.2 w.2.2
  have hsl := powerTerm_majorizes a s ha hs w.1.1 w.2.1.1
  have hsr := powerTerm_majorizes a s ha hs w.1.2 w.2.2
  have h := majorizes_mul (positive_mul hl (hb w.2.1.2)) hr
    (majorizes_mul hl (hb w.2.1.2) hsl (hk w.2.1.2)) hsr
  intro n i j
  change ‖matrix (weight w.1 • rawTerm s k w.1 w.2) n i j‖ ≤ _
  rw [matrix_smul, Matrix.smul_apply, norm_smul]
  apply (mul_le_of_le_one_left (norm_nonneg _) (weight_norm _)).trans
  simpa only [rawTerm, matrix_mul] using h n i j

/-- The complete normalization series is regrouped by total source degree,
with a positive coefficient envelope in every degree and absolute convergence
of both grouped series in the mixed sequence norm. -/
theorem regroup_majorized (a b s k : ℕ → Mixed)
    (ha : Summable (fun d => ‖a d‖)) (hb : Summable (fun d => ‖b d‖))
    (hpa : ∀ d, Positive (a d)) (hpb : ∀ d, Positive (b d))
    (hs : ∀ d, Majorizes (a d) (matrix (s d)))
    (hk : ∀ d, Majorizes (b d) (matrix (k d)))
    (hsmall : 2 * (∑' d, ‖a d‖) < 1) :
    Summable (fun d => ‖degreeEnvelope a b d‖) ∧
      Summable (fun d => ‖degreeCoefficient s k d‖) ∧
      HasSum (degreeEnvelope a b) (∑' jl, envelopeWord (∑' d, a d) (∑' d, b d) jl) ∧
      HasSum (degreeCoefficient s k) (mul (mul (inverseSqrt (∑' d, s d)) (∑' d, k d))
        (inverseSqrt (∑' d, s d))) ∧
      ∀ d, Positive (degreeEnvelope a b d) ∧
        Majorizes (degreeEnvelope a b d) (matrix (degreeCoefficient s k d)) := by
  have hsn (d : ℕ) : ‖s d‖ ≤ ‖a d‖ := solid_norm (hpa d) (hs d)
  have hkn (d : ℕ) : ‖k d‖ ≤ ‖b d‖ := solid_norm (hpb d) (hk d)
  have hss := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hsn ha
  have hks := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hkn hb
  have hsm : 2 * (∑' d, ‖s d‖) < 1 :=
    (mul_le_mul_of_nonneg_left (hss.tsum_le_tsum hsn ha) (by norm_num)).trans_lt hsmall
  have hr := raw_all_summable a b ha hb hsmall
  have hw := weighted_expansion s k hss hks hsm
  have hraw := hr.of_norm.hasSum.sigma (fun jl => (raw_expansion a b ha hb jl).2.1)
  have hrawsum : (∑' w : AllWords, rawTerm a b w.1 w.2) =
      ∑' jl, envelopeWord (∑' d, a d) (∑' d, b d) jl := hraw.tsum_eq.symm
  refine ⟨norm_fiber_summable (fun w : AllWords => rawTerm a b w.1 w.2) totalDegree hr, norm_fiber_summable (weightedTerm s k) totalDegree hw.1,
    ?_, hw.2.tsum_fiberwise totalDegree, ?_⟩
  · rw [← hrawsum]
    exact hr.of_norm.hasSum.tsum_fiberwise totalDegree
  · intro d
    let f := fun w : {w : AllWords // totalDegree w = d} => rawTerm a b w.1.1 w.1.2
    let g := fun w : {w : AllWords // totalDegree w = d} => weightedTerm s k w.1
    have hf : Summable (fun w => ‖f w‖) := hr.subtype _
    have hg : Summable (fun w => ‖g w‖) := hw.1.subtype _
    exact ⟨positive_tsum (f := f) hf.of_norm (fun w => raw_positive a b hpa hpb w.1),
      majorizes_tsum (a := f) (b := g) hf hg
        (fun w => raw_majorizes a b s k hpa hpb hs hk w.1)⟩

end QuantumNLS.Local006.DegreeRegroupI
#print axioms QuantumNLS.Local006.DegreeRegroupI.regroup_majorized

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local006.DegreeRegroupI." ||
        n.toString.startsWith "_private.QuantumNLS.Local006DegreeRegroupI" then
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
  Lean.logInfo m!"Local006DegreeRegroupI audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
