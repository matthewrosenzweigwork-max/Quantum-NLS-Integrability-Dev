import QuantumNLS.Local006ChartMajorantH

/-! Absolutely convergent expansion of every normalization word into ordered
source degrees. The index records every source degree, before any regrouping. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 150000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open scoped BigOperators ENNReal
namespace QuantumNLS.Local006.WordExpansionI
open QuantumNLS.Local006.CoefficientLiftE QuantumNLS.Local006.SequenceAlgebraE
  QuantumNLS.Local006.SequenceEvaluationE QuantumNLS.Local006.PositiveMajorantG
  QuantumNLS.Local006.SolidMajorantH QuantumNLS.Local006.BinomialBindingH

lemma mul_expansion {α β : Type*} (a : α → Mixed) (b : β → Mixed)
    (ha : Summable (fun i => ‖a i‖)) (hb : Summable (fun j => ‖b j‖)) :
    Summable (fun z : α × β => ‖mul (a z.1) (b z.2)‖) ∧
      HasSum (fun z : α × β => mul (a z.1) (b z.2)) (mul (∑' i, a i) (∑' j, b j)) ∧
      (∑' z : α × β, ‖mul (a z.1) (b z.2)‖) ≤
        2 * (∑' i, ‖a i‖) * (∑' j, ‖b j‖) := by
  have hp := (ha.mul_of_nonneg hb (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mul_left 2
  have hn : Summable (fun z : α × β => ‖mul (a z.1) (b z.2)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun z => by simpa [mul_assoc] using mul_norm (a z.1) (b z.2)) hp
  have ht := hn.of_norm.hasSum.prod_fiberwise (fun i => (mulLeft (a i)).hasSum hb.of_norm.hasSum)
  have ho := (mulRight (∑' j, b j)).hasSum ha.of_norm.hasSum
  have he : (∑' z : α × β, mul (a z.1) (b z.2)) = mul (∑' i, a i) (∑' j, b j) :=
    ht.unique ho
  refine ⟨hn, he ▸ hn.of_norm.hasSum, ?_⟩
  calc
    _ ≤ ∑' z : α × β, 2 * (‖a z.1‖ * ‖b z.2‖) :=
      hn.tsum_le_tsum (fun z => by simpa [mul_assoc] using mul_norm (a z.1) (b z.2)) hp
    _ = 2 * (∑' i, ‖a i‖) * (∑' j, ‖b j‖) := by
      rw [tsum_mul_left, ← ha.tsum_mul_tsum hb
        (ha.mul_of_nonneg hb (fun _ => norm_nonneg _) (fun _ => norm_nonneg _))]
      ring

def PowerIndex : ℕ → Type
  | 0 => PUnit
  | j + 1 => ℕ × PowerIndex j

def powerTerm (a : ℕ → Mixed) : (j : ℕ) → PowerIndex j → Mixed
  | 0, _ => unit
  | j + 1, z => mul (a z.1) (powerTerm a j z.2)

def powerDegree : (j : ℕ) → PowerIndex j → ℕ
  | 0, _ => 0
  | j + 1, z => (z.1 + 1) + powerDegree j z.2

lemma power_expansion (a : ℕ → Mixed) (ha : Summable (fun d => ‖a d‖)) (j : ℕ) :
    Summable (fun z => ‖powerTerm a j z‖) ∧
      HasSum (powerTerm a j) (power (∑' d, a d) j) ∧
      (∑' z, ‖powerTerm a j z‖) ≤ (2 * ∑' d, ‖a d‖) ^ j := by
  induction j with
  | zero =>
    change Summable (fun _ : PUnit => ‖unit‖) ∧ HasSum (fun _ : PUnit => unit) unit ∧ _
    exact ⟨(hasSum_fintype _).summable, by simpa using hasSum_fintype (fun _ : PUnit => unit),
      by change (∑' _ : PUnit, ‖unit‖) ≤ 1; simpa using unit_norm⟩
  | succ j ih =>
    obtain ⟨hn, hs, hb⟩ := mul_expansion a (powerTerm a j) ha ih.1
    refine ⟨hn, ?_, ?_⟩
    · simpa only [PowerIndex, powerTerm, ih.2.1.tsum_eq, power] using hs
    · change (∑' z : ℕ × PowerIndex j, ‖mul (a z.1) (powerTerm a j z.2)‖) ≤ _
      calc
        _ ≤ 2 * (∑' d, ‖a d‖) * (∑' z, ‖powerTerm a j z‖) := hb
        _ ≤ (2 * ∑' d, ‖a d‖) * (2 * ∑' d, ‖a d‖) ^ j :=
          mul_le_mul_of_nonneg_left ih.2.2 (by positivity)
        _ = _ := by rw [pow_succ']

abbrev WordIndex (jl : ℕ × ℕ) := (PowerIndex jl.1 × ℕ) × PowerIndex jl.2
abbrev AllWords := Σ jl : ℕ × ℕ, WordIndex jl

def rawTerm (a b : ℕ → Mixed) (jl : ℕ × ℕ) (z : WordIndex jl) : Mixed :=
  mul (mul (powerTerm a jl.1 z.1.1) (b z.1.2)) (powerTerm a jl.2 z.2)

def weight (jl : ℕ × ℕ) : ℂ :=
  (QuantumNLS.LocalSpectral.invSqrtCoeff jl.1 : ℂ) *
    (QuantumNLS.LocalSpectral.invSqrtCoeff jl.2 : ℂ)

def weightedTerm (a b : ℕ → Mixed) (w : AllWords) : Mixed :=
  weight w.1 • rawTerm a b w.1 w.2

def totalDegree (w : AllWords) : ℕ :=
  powerDegree w.1.1 w.2.1.1 + (w.2.1.2 + 1) + powerDegree w.1.2 w.2.2

lemma weight_norm (jl : ℕ × ℕ) : ‖weight jl‖ ≤ 1 := by
  unfold weight
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right (QuantumNLS.LocalSpectral.abs_invSqrtCoeff_le _)
    (abs_nonneg _)).trans (by simpa using QuantumNLS.LocalSpectral.abs_invSqrtCoeff_le jl.2)

lemma raw_expansion (a b : ℕ → Mixed)
    (ha : Summable (fun d => ‖a d‖)) (hb : Summable (fun d => ‖b d‖)) (jl : ℕ × ℕ) :
    Summable (fun z => ‖rawTerm a b jl z‖) ∧
      HasSum (rawTerm a b jl) (envelopeWord (∑' d, a d) (∑' d, b d) jl) ∧
      (∑' z, ‖rawTerm a b jl z‖) ≤
        4 * (∑' d, ‖b d‖) * ((2 * ∑' d, ‖a d‖)^jl.1 * (2 * ∑' d, ‖a d‖)^jl.2) := by
  have h1 := power_expansion a ha jl.1
  have h2 := power_expansion a ha jl.2
  have h3 := mul_expansion (powerTerm a jl.1) b h1.1 hb
  obtain ⟨hn, hs, hbound⟩ := mul_expansion
    (fun z : PowerIndex jl.1 × ℕ => mul (powerTerm a jl.1 z.1) (b z.2))
    (powerTerm a jl.2) h3.1 h2.1
  refine ⟨hn, ?_, ?_⟩
  · change HasSum (fun z : (PowerIndex jl.1 × ℕ) × PowerIndex jl.2 =>
        mul (mul (powerTerm a jl.1 z.1.1) (b z.1.2)) (powerTerm a jl.2 z.2)) _
    simpa only [h3.2.1.tsum_eq, h1.2.1.tsum_eq, h2.2.1.tsum_eq, envelopeWord] using hs
  · change (∑' z : WordIndex jl, ‖mul (mul (powerTerm a jl.1 z.1.1) (b z.1.2)) (powerTerm a jl.2 z.2)‖) ≤ _
    calc
      _ ≤ 2 * (∑' z : PowerIndex jl.1 × ℕ, ‖mul (powerTerm a jl.1 z.1) (b z.2)‖) *
          (∑' z, ‖powerTerm a jl.2 z‖) := hbound
      _ ≤ 2 * (2 * (2 * ∑' d, ‖a d‖)^jl.1 * (∑' d, ‖b d‖)) *
          (2 * ∑' d, ‖a d‖)^jl.2 := by
        gcongr
        · exact h3.2.2.trans (by gcongr; exact h1.2.2)
        · exact h2.2.2
      _ = _ := by ring

lemma raw_all_summable (a b : ℕ → Mixed)
    (ha : Summable (fun d => ‖a d‖)) (hb : Summable (fun d => ‖b d‖))
    (hsmall : 2 * (∑' d, ‖a d‖) < 1) :
    Summable (fun w : AllWords => ‖rawTerm a b w.1 w.2‖) := by
  have hg := summable_geometric_of_lt_one (by positivity : 0 ≤ 2 * ∑' d, ‖a d‖) hsmall
  have hp := (hg.mul_of_nonneg hg (fun _ => by positivity) (fun _ => by positivity)).mul_left
    (4 * ∑' d, ‖b d‖)
  apply (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨fun jl => (raw_expansion a b ha hb jl).1, ?_⟩
  exact Summable.of_nonneg_of_le (fun _ => tsum_nonneg (fun _ => norm_nonneg _))
    (fun jl => (raw_expansion a b ha hb jl).2.2) hp

/-- Every source degree in both binomial factors and the central moment is
expanded, with absolute convergence in the mixed Banach sequence space. -/
theorem weighted_expansion (a b : ℕ → Mixed)
    (ha : Summable (fun d => ‖a d‖)) (hb : Summable (fun d => ‖b d‖))
    (hsmall : 2 * (∑' d, ‖a d‖) < 1) :
    Summable (fun w : AllWords => ‖weightedTerm a b w‖) ∧
      HasSum (weightedTerm a b) (mul (mul (inverseSqrt (∑' d, a d)) (∑' d, b d))
        (inverseSqrt (∑' d, a d))) := by
  have hr := raw_all_summable a b ha hb hsmall
  have hn : Summable (fun w => ‖weightedTerm a b w‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun w => by rw [weightedTerm, norm_smul]; exact mul_le_of_le_one_left (norm_nonneg _) (weight_norm _)) hr
  have hfixed (jl : ℕ × ℕ) :
      HasSum (fun z => weightedTerm a b ⟨jl, z⟩) (normalizedWord (∑' d, a d) (∑' d, b d) jl) := by
    have hs := ((raw_expansion a b ha hb jl).2.1).const_smul (weight jl)
    have heq : weight jl • envelopeWord (∑' d, a d) (∑' d, b d) jl =
        normalizedWord (∑' d, a d) (∑' d, b d) jl := by
      apply matrix_ext
      intro n i j
      simp only [normalizedWord, envelopeWord, matrix_mul, matrix_smul, weight,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm]
    rw [← heq]
    exact hs
  have hnorm : Summable (fun jl => ‖normalizedWord (∑' d, a d) (∑' d, b d) jl‖) := by
    have ht := (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mp hn
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun jl => (hfixed jl).tsum_eq ▸ norm_tsum_le_tsum_norm (ht.1 jl)) ht.2
  have hs := hn.of_norm.hasSum.sigma hfixed
  have hsm : 2 * ‖∑' d, a d‖ < 1 :=
    (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm ha) (by norm_num)).trans_lt hsmall
  have ho := normalizedWord_hasSum (∑' d, a d) (∑' d, b d) hsm hnorm
  exact ⟨hn, (hs.unique ho) ▸ hn.of_norm.hasSum⟩

end QuantumNLS.Local006.WordExpansionI
#print axioms QuantumNLS.Local006.WordExpansionI.weighted_expansion

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local006.WordExpansionI." ||
        n.toString.startsWith "_private.QuantumNLS.Local006WordExpansionI" then
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
  Lean.logInfo m!"Local006WordExpansionI audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
