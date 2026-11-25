import QuantumNLS.Local006SourceBindingH

/-! The full positive normalization word sum dominates the actual normalized
mixed sequence. Both binomial factors and the double sum are identified. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open scoped BigOperators ENNReal
namespace QuantumNLS.Local006.BinomialBindingH
open QuantumNLS.LocalSpectral QuantumNLS.Local006.CoefficientLiftE
  QuantumNLS.Local006.SequenceAlgebraE QuantumNLS.Local006.SequenceEvaluationE
  QuantumNLS.Local006.PositiveMajorantG QuantumNLS.Local006.SolidMajorantH

lemma matrix_add (a b : Mixed) (n : ℤ) : matrix (a + b) n = matrix a n + matrix b n :=
  (evalMatrix n).map_add a b

lemma matrix_smul (c : ℂ) (a : Mixed) (n : ℤ) : matrix (c • a) n = c • matrix a n :=
  (evalMatrix n).map_smul c a

def mulLeft (x : Mixed) : Mixed →L[ℂ] Mixed :=
  LinearMap.mkContinuous
    { toFun := mul x
      map_add' := fun y z => by
        apply matrix_ext
        intro n i j
        simp only [matrix_mul, matrix_add, Matrix.mul_add]
      map_smul' := fun c y => by
        apply matrix_ext
        intro n i j
        simp only [matrix_mul, matrix_smul, Matrix.mul_smul, RingHom.id_apply] }
    (2 * ‖x‖) (fun y => mul_norm x y)

def mulRight (y : Mixed) : Mixed →L[ℂ] Mixed :=
  LinearMap.mkContinuous
    { toFun := fun x => mul x y
      map_add' := fun x z => by
        apply matrix_ext
        intro n i j
        simp only [matrix_mul, matrix_add, Matrix.add_mul]
      map_smul' := fun c x => by
        apply matrix_ext
        intro n i j
        simp only [matrix_mul, matrix_smul, Matrix.smul_mul, RingHom.id_apply] }
    (2 * ‖y‖) (fun x => (mul_norm x y).trans_eq (by ring))

@[simp] lemma mulLeft_apply (x y : Mixed) : mulLeft x y = mul x y := rfl
@[simp] lemma mulRight_apply (x y : Mixed) : mulRight y x = mul x y := rfl

lemma solid_norm {a b : Mixed} (ha : Positive a) (hb : Majorizes a (matrix b)) : ‖b‖ ≤ ‖a‖ := by
  obtain ⟨c, he, hc⟩ := solid_lift ha hb
  have heq : c = b := matrix_ext (fun n i j => congrFun (congrFun (he n) i) j)
  exact heq ▸ hc

def normalizedWord (s k : Mixed) (jl : ℕ × ℕ) : Mixed :=
  mul (mul ((invSqrtCoeff jl.1 : ℂ) • power s jl.1) k)
    ((invSqrtCoeff jl.2 : ℂ) • power s jl.2)

def envelopeWord (a b : Mixed) (jl : ℕ × ℕ) : Mixed :=
  mul (mul (power a jl.1) b) (power a jl.2)

lemma normalizedWord_majorizes {a b s k : Mixed} (ha : Positive a) (hb : Positive b)
    (hs : Majorizes a (matrix s)) (hk : Majorizes b (matrix k)) (jl : ℕ × ℕ) :
    Majorizes (envelopeWord a b jl) (matrix (normalizedWord s k jl)) := by
  intro n i j
  have h := normalized_word_majorizes ha hb hs hk jl.1 jl.2 n i j
  change ‖matrix (normalizedWord s k jl) n i j‖ ≤ _
  simp only [normalizedWord, matrix_mul, matrix_smul, matrix_power]
  exact h

lemma normalizedWord_summable {a b s k : Mixed} (ha : Positive a) (hb : Positive b)
    (hs : Majorizes a (matrix s)) (hk : Majorizes b (matrix k)) (hsmall : 2 * ‖a‖ < 1) :
    Summable (fun jl => ‖normalizedWord s k jl‖) := by
  have hn (jl : ℕ × ℕ) : ‖normalizedWord s k jl‖ ≤ ‖envelopeWord a b jl‖ := by
    have hp : Positive (envelopeWord a b jl) :=
      positive_mul (positive_mul (positive_power ha jl.1) hb) (positive_power ha jl.2)
    exact solid_norm (a := envelopeWord a b jl) (b := normalizedWord s k jl) hp
      (normalizedWord_majorizes ha hb hs hk jl)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hn
    (normalization_words_summable a b hsmall)

lemma normalizedWord_hasSum (s k : Mixed) (hs : 2 * ‖s‖ < 1)
    (hw : Summable (fun jl => ‖normalizedWord s k jl‖)) :
    HasSum (normalizedWord s k) (mul (mul (inverseSqrt s) k) (inverseSqrt s)) := by
  have h := inverse_sqrt_hasSum s hs
  have houter := ((mulRight (inverseSqrt s)).comp (mulRight k)).hasSum h
  have hinner (j : ℕ) := (mulLeft (mul ((invSqrtCoeff j : ℂ) • power s j) k)).hasSum h
  have htotal := hw.of_norm.hasSum.prod_fiberwise hinner
  have he := htotal.unique houter
  have he' : (∑' jl, normalizedWord s k jl) = mul (mul (inverseSqrt s) k) (inverseSqrt s) := by
    simpa only [ContinuousLinearMap.comp_apply, mulRight_apply] using he
  rw [← he']
  exact hw.of_norm.hasSum

/-- The summed envelope dominates the actual, fully normalized sequence;
there is no assumed identity of normalized kernels or chart coefficients. -/
theorem normalization_majorant {a b s k : Mixed} (ha : Positive a) (hb : Positive b)
    (hs : Majorizes a (matrix s)) (hk : Majorizes b (matrix k)) (hsmall : 2 * ‖a‖ < 1) :
    Summable (fun jl => ‖normalizedWord s k jl‖) ∧
      HasSum (normalizedWord s k) (mul (mul (inverseSqrt s) k) (inverseSqrt s)) ∧
      Positive (∑' jl, envelopeWord a b jl) ∧
      Majorizes (∑' jl, envelopeWord a b jl)
        (matrix (mul (mul (inverseSqrt s) k) (inverseSqrt s))) := by
  have hw := normalizedWord_summable ha hb hs hk hsmall
  have hs0 : 2 * ‖s‖ < 1 := (mul_le_mul_of_nonneg_left (solid_norm ha hs) (by norm_num)).trans_lt hsmall
  have hsum := normalizedWord_hasSum s k hs0 hw
  have hp : ∀ jl, Positive (envelopeWord a b jl) := fun jl =>
    positive_mul (positive_mul (positive_power ha jl.1) hb) (positive_power ha jl.2)
  have henv := normalization_words_summable a b hsmall
  refine ⟨hw, hsum, positive_tsum henv.of_norm hp, ?_⟩
  have hm := majorizes_tsum henv hw (normalizedWord_majorizes ha hb hs hk)
  rwa [hsum.tsum_eq] at hm

end QuantumNLS.Local006.BinomialBindingH
#print axioms QuantumNLS.Local006.BinomialBindingH.normalization_majorant

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local006.BinomialBindingH." ||
        n.toString.startsWith "_private.QuantumNLS.Local006BinomialBindingH" then
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
  Lean.logInfo m!"Local006BinomialBindingH audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
