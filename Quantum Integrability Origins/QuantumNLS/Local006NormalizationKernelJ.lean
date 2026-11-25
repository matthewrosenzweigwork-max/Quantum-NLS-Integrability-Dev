import QuantumNLS.Local006SourceSumJ
import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-! Product rules for differentiated normalization words, retaining positive
 Fourier kernels and uniform summable bounds for both binomial factors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open scoped BigOperators ENNReal
namespace QuantumNLS.Local006.NormalizationKernelJ
open QuantumNLS.Local006.CoefficientLiftE QuantumNLS.Local006.SequenceAlgebraE
  QuantumNLS.Local006.SequenceEvaluationE QuantumNLS.Local006.PositiveMajorantG
  QuantumNLS.Local006.SolidMajorantH QuantumNLS.Local006.BinomialBindingH
  QuantumNLS.Local006.PositiveSlotsJ

lemma positive_add {a b : Mixed} (ha : Positive a) (hb : Positive b) : Positive (a+b) := by
  intro n i j
  rw [matrix_add, Matrix.add_apply]
  exact ⟨by simp [(ha n i j).1, (hb n i j).1], by simpa using add_nonneg (ha n i j).2 (hb n i j).2⟩

lemma majorizes_add {a b x y : Mixed} (hx : Majorizes a (matrix x))
    (hy : Majorizes b (matrix y)) : Majorizes (a+b) (matrix (x+y)) := by
  intro n i j
  rw [matrix_add, Matrix.add_apply, matrix_add, Matrix.add_apply, Complex.add_re]
  exact (norm_add_le _ _).trans (add_le_add (hx n i j) (hy n i j))

lemma mulLeft_norm (a : Mixed) : ‖mulLeft a‖ ≤ 2*‖a‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun b => mul_norm a b)

lemma mulRight_norm (b : Mixed) : ‖mulRight b‖ ≤ 2*‖b‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun a => (mul_norm a b).trans_eq (by ring))

def mulBilinearR : Mixed →L[ℝ] Mixed →L[ℝ] Mixed :=
  LinearMap.mkContinuous
    { toFun := fun a => (mulLeft a).restrictScalars ℝ
      map_add' := fun a b => by
        apply ContinuousLinearMap.ext
        intro x
        apply matrix_ext
        intro n i j
        change matrix (mul (a+b) x) n i j = matrix (mul a x + mul b x) n i j
        simp only [matrix_mul, matrix_add, Matrix.add_mul]
      map_smul' := fun c a => by
        apply ContinuousLinearMap.ext
        intro x
        apply matrix_ext
        intro n i j
        change matrix (mul (c • a) x) n i j = matrix (c • mul a x) n i j
        have h (y : Mixed) : matrix (c • y) n = c • matrix y n := (evalMatrix n).map_smul_of_tower c y
        rw [matrix_mul, h, h, Matrix.smul_mul, matrix_mul] }
    2 (fun a => by
      change ‖(mulLeft a).restrictScalars ℝ‖ ≤ 2*‖a‖
      rw [ContinuousLinearMap.norm_restrictScalars]
      exact mulLeft_norm a)

@[simp] lemma mulBilinearR_apply (a b : Mixed) : mulBilinearR a b = mul a b := rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def productDerivative (x y : Mixed) (D H : E →L[ℝ] Mixed) : E →L[ℝ] Mixed :=
  ((mulRight y).restrictScalars ℝ).comp D + ((mulLeft x).restrictScalars ℝ).comp H

lemma product_hasFDerivAt {f g : E → Mixed} {D H : E →L[ℝ] Mixed} {u : E}
    (hf : HasFDerivAt f D u) (hg : HasFDerivAt g H u) :
    HasFDerivAt (fun v => mul (f v) (g v)) (productDerivative (f u) (g u) D H) u := by
  have h := mulBilinearR.hasFDerivAt_of_bilinear hf hg
  simp only [mulBilinearR_apply] at h
  convert! h using 1
  apply ContinuousLinearMap.ext
  intro v
  change mul (D v) (g u) + mul (f u) (H v) = mul (f u) (H v) + mul (D v) (g u)
  exact add_comm _ _

def productKernel (a b : Mixed) (K H : Seq2 →L[ℂ] Mixed) : Seq2 →L[ℂ] Mixed :=
  (mulRight b).comp K + (mulLeft a).comp H

lemma productKernel_norm (a b : Mixed) (K H : Seq2 →L[ℂ] Mixed) :
    ‖productKernel a b K H‖ ≤ 2*‖b‖*‖K‖ + 2*‖a‖*‖H‖ := by
  exact (norm_add_le _ _).trans (add_le_add
    ((ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right (mulRight_norm b) (norm_nonneg K)))
    ((ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right (mulLeft_norm a) (norm_nonneg H))))

lemma productKernel_positive {a b : Mixed} {K H : Seq2 →L[ℂ] Mixed}
    (ha : Positive a) (hb : Positive b) (hK : ∀ v, Positive (K (moduli v)))
    (hH : ∀ v, Positive (H (moduli v))) (v : Seq2) :
    Positive (productKernel a b K H (moduli v)) :=
  positive_add (positive_mul (hK v) hb) (positive_mul ha (hH v))

lemma productKernel_majorizes {a b x y : Mixed} {K H : Seq2 →L[ℂ] Mixed}
    {D J : E →L[ℝ] Mixed} (F : E → Seq2)
    (ha : Positive a) (hb : Positive b) (hx : Majorizes a (matrix x)) (hy : Majorizes b (matrix y))
    (hKp : ∀ v, Positive (K (moduli v))) (hHp : ∀ v, Positive (H (moduli v)))
    (hK : ∀ v, Majorizes (K (moduli (F v))) (matrix (D v)))
    (hH : ∀ v, Majorizes (H (moduli (F v))) (matrix (J v))) (v : E) :
    Majorizes (productKernel a b K H (moduli (F v))) (matrix (productDerivative x y D J v)) := by
  apply majorizes_add
  · intro n i j
    change ‖matrix (mul (D v) y) n i j‖ ≤ (matrix (mul (K (moduli (F v))) b) n i j).re
    rw [matrix_mul]
    exact majorizes_mul (hKp (F v)) hb (hK v) hy n i j
  · intro n i j
    change ‖matrix (mul x (J v)) n i j‖ ≤ (matrix (mul a (H (moduli (F v)))) n i j).re
    rw [matrix_mul]
    exact majorizes_mul ha (hHp (F v)) hx (hH v) n i j

def powerKernel (a : Mixed) (K : Seq2 →L[ℂ] Mixed) : ℕ → Seq2 →L[ℂ] Mixed
  | 0 => 0
  | j+1 => productKernel a (power a j) K (powerKernel a K j)

lemma powerKernel_positive {a : Mixed} {K : Seq2 →L[ℂ] Mixed}
    (ha : Positive a) (hK : ∀ v, Positive (K (moduli v))) (j : ℕ) (v : Seq2) :
    Positive (powerKernel a K j (moduli v)) := by
  induction j generalizing v with
  | zero => intro n i j; simp [powerKernel, matrix]
  | succ j ih => exact productKernel_positive ha (positive_power ha j) hK ih v

lemma powerKernel_norm {a : Mixed} {K : Seq2 →L[ℂ] Mixed} {M : ℝ}
    (ha : ‖a‖ ≤ 1/4) (hM : 0 ≤ M) (hK : ‖K‖ ≤ M) (j : ℕ) :
    ‖powerKernel a K j‖ ≤ 4 * j * M * (1/2 : ℝ)^j := by
  have hp (j : ℕ) : ‖power a j‖ ≤ (1/2 : ℝ)^j :=
    (power_norm a j).trans (pow_le_pow_left₀ (by positivity) (by linarith) j)
  induction j with
  | zero => simp [powerKernel]
  | succ j ih =>
    calc
      _ ≤ 2 * ‖power a j‖ * ‖K‖ + 2 * ‖a‖ * ‖powerKernel a K j‖ := productKernel_norm _ _ _ _
      _ ≤ 2 * (1/2 : ℝ)^j * M + 2 * (1/4 : ℝ) * (4*j*M*(1/2 : ℝ)^j) := by
        gcongr
        exact hp j
      _ = _ := by push_cast; rw [pow_succ]; ring

def wordKernel (a b : Mixed) (K H : Seq2 →L[ℂ] Mixed) (jl : ℕ × ℕ) : Seq2 →L[ℂ] Mixed :=
  productKernel (mul (power a jl.1) b) (power a jl.2)
    (productKernel (power a jl.1) b (powerKernel a K jl.1) H) (powerKernel a K jl.2)

lemma wordKernel_positive {a b : Mixed} {K H : Seq2 →L[ℂ] Mixed}
    (ha : Positive a) (hb : Positive b) (hK : ∀ v, Positive (K (moduli v)))
    (hH : ∀ v, Positive (H (moduli v))) (jl : ℕ × ℕ) (v : Seq2) :
    Positive (wordKernel a b K H jl (moduli v)) :=
  productKernel_positive (positive_mul (positive_power ha _) hb) (positive_power ha _)
    (fun v => productKernel_positive (positive_power ha _) hb (powerKernel_positive ha hK _) hH v)
    (powerKernel_positive ha hK _) v

lemma wordKernel_norm {a b : Mixed} {K H : Seq2 →L[ℂ] Mixed} {M : ℝ}
    (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4) (hM : 0 ≤ M) (hK : ‖K‖ ≤ M) (hH : ‖H‖ ≤ M)
    (jl : ℕ × ℕ) :
    ‖wordKernel a b K H jl‖ ≤ 4 * (jl.1+jl.2+1 : ℝ) * M *
      ((1/2 : ℝ)^jl.1 * (1/2 : ℝ)^jl.2) := by
  have hp (j : ℕ) : ‖power a j‖ ≤ (1/2 : ℝ)^j :=
    (power_norm a j).trans (pow_le_pow_left₀ (by positivity) (by linarith) j)
  have hi : ‖productKernel (power a jl.1) b (powerKernel a K jl.1) H‖ ≤
      2 * (jl.1+1 : ℝ) * M * (1/2 : ℝ)^jl.1 := by
    calc
      _ ≤ 2*‖b‖*‖powerKernel a K jl.1‖ + 2*‖power a jl.1‖*‖H‖ := productKernel_norm _ _ _ _
      _ ≤ 2*(1/4 : ℝ)*(4*jl.1*M*(1/2 : ℝ)^jl.1) + 2*(1/2 : ℝ)^jl.1*M := by
        gcongr
        · exact powerKernel_norm ha hM hK _
        · exact hp _
      _ = _ := by push_cast; ring
  have hm : ‖mul (power a jl.1) b‖ ≤ (1/2 : ℝ) * (1/2 : ℝ)^jl.1 := by
    calc
      _ ≤ 2*‖power a jl.1‖*‖b‖ := mul_norm _ _
      _ ≤ 2*(1/2 : ℝ)^jl.1*(1/4 : ℝ) := by gcongr; exact hp _
      _ = _ := by ring
  calc
    _ ≤ 2*‖power a jl.2‖*‖productKernel (power a jl.1) b (powerKernel a K jl.1) H‖ +
        2*‖mul (power a jl.1) b‖*‖powerKernel a K jl.2‖ := productKernel_norm _ _ _ _
    _ ≤ 2*(1/2 : ℝ)^jl.2*(2*(jl.1+1 : ℝ)*M*(1/2 : ℝ)^jl.1) +
        2*((1/2 : ℝ)*(1/2 : ℝ)^jl.1)*(4*jl.2*M*(1/2 : ℝ)^jl.2) := by
      gcongr
      · exact hp _
      · exact powerKernel_norm ha hM hK _
    _ = _ := by push_cast; ring

lemma wordKernel_summable {a b : Mixed} {K H : Seq2 →L[ℂ] Mixed}
    (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4) :
    Summable (fun jl : ℕ × ℕ => ‖wordKernel a b K H jl‖) := by
  let M := max ‖K‖ ‖H‖
  have hM : 0 ≤ M := (norm_nonneg K).trans (le_max_left _ _)
  have hq : ‖(1/2 : ℝ)‖ < 1 := by norm_num
  have hg := summable_geometric_of_norm_lt_one hq
  have hj := summable_pow_mul_geometric_of_norm_lt_one 1 hq
  simp only [pow_one] at hj
  have h1 := hj.mul_of_nonneg hg (fun n => by positivity) (fun n => by positivity)
  have h2 := hg.mul_of_nonneg hj (fun n => by positivity) (fun n => by positivity)
  have h3 := hg.mul_of_nonneg hg (fun n => by positivity) (fun n => by positivity)
  have hm := ((h1.add h2).add h3).mul_left (4*M)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun jl =>
    (wordKernel_norm ha hb hM (le_max_left _ _) (le_max_right _ _) jl).trans_eq ?_) hm
  ring

def powerDerivative (x : Mixed) (D : E →L[ℝ] Mixed) : ℕ → E →L[ℝ] Mixed
  | 0 => 0
  | j+1 => productDerivative x (power x j) D (powerDerivative x D j)

lemma power_hasFDerivAt {f : E → Mixed} {D : E →L[ℝ] Mixed} {u : E}
    (hf : HasFDerivAt f D u) (j : ℕ) :
    HasFDerivAt (fun v => power (f v) j) (powerDerivative (f u) D j) u := by
  induction j with
  | zero => exact hasFDerivAt_const (𝕜 := ℝ) unit u
  | succ j ih => exact product_hasFDerivAt hf ih

lemma powerKernel_majorizes {a x : Mixed} {K : Seq2 →L[ℂ] Mixed} {D : E →L[ℝ] Mixed}
    (F : E → Seq2) (ha : Positive a) (hx : Majorizes a (matrix x))
    (hKp : ∀ v, Positive (K (moduli v)))
    (hK : ∀ v, Majorizes (K (moduli (F v))) (matrix (D v))) (j : ℕ) (v : E) :
    Majorizes (powerKernel a K j (moduli (F v))) (matrix (powerDerivative x D j v)) := by
  induction j generalizing v with
  | zero => intro n i j; simp [powerKernel, powerDerivative, matrix]
  | succ j ih =>
    exact productKernel_majorizes F ha (positive_power ha j) hx
      (by intro n i k; rw [matrix_power]; exact majorizes_power ha hx j n i k) hKp (powerKernel_positive ha hKp j)
      hK ih v

def rawWordDerivative (x y : Mixed) (D H : E →L[ℝ] Mixed) (jl : ℕ × ℕ) : E →L[ℝ] Mixed :=
  productDerivative (mul (power x jl.1) y) (power x jl.2)
    (productDerivative (power x jl.1) y (powerDerivative x D jl.1) H) (powerDerivative x D jl.2)

def wordDerivative (x y : Mixed) (D H : E →L[ℝ] Mixed) (jl : ℕ × ℕ) : E →L[ℝ] Mixed :=
  QuantumNLS.Local006.WordExpansionI.weight jl • rawWordDerivative x y D H jl

lemma normalizedWord_weight (x y : Mixed) (jl : ℕ × ℕ) :
    normalizedWord x y jl = QuantumNLS.Local006.WordExpansionI.weight jl • envelopeWord x y jl := by
  apply matrix_ext
  intro n i j
  simp only [normalizedWord, envelopeWord, matrix_mul, matrix_smul,
    QuantumNLS.Local006.WordExpansionI.weight, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm]

lemma normalizedWord_hasFDerivAt {f g : E → Mixed} {D H : E →L[ℝ] Mixed} {u : E}
    (hf : HasFDerivAt f D u) (hg : HasFDerivAt g H u) (jl : ℕ × ℕ) :
    HasFDerivAt (fun v => normalizedWord (f v) (g v) jl)
      (wordDerivative (f u) (g u) D H jl) u := by
  have h := (product_hasFDerivAt (product_hasFDerivAt (power_hasFDerivAt hf jl.1) hg)
    (power_hasFDerivAt hf jl.2)).const_smul (QuantumNLS.Local006.WordExpansionI.weight jl)
  simp only [normalizedWord_weight]
  convert! h using 1

lemma wordKernel_majorizes {a b x y : Mixed} {K H : Seq2 →L[ℂ] Mixed}
    {D J : E →L[ℝ] Mixed} (F : E → Seq2)
    (ha : Positive a) (hb : Positive b) (hx : Majorizes a (matrix x)) (hy : Majorizes b (matrix y))
    (hKp : ∀ v, Positive (K (moduli v))) (hHp : ∀ v, Positive (H (moduli v)))
    (hK : ∀ v, Majorizes (K (moduli (F v))) (matrix (D v)))
    (hH : ∀ v, Majorizes (H (moduli (F v))) (matrix (J v))) (jl : ℕ × ℕ) (v : E) :
    Majorizes (wordKernel a b K H jl (moduli (F v))) (matrix (wordDerivative x y D J jl v)) := by
  have hpow (j : ℕ) : Majorizes (power a j) (matrix (power x j)) := by
    intro n i k
    rw [matrix_power]
    exact majorizes_power ha hx j n i k
  have hmul : Majorizes (mul (power a jl.1) b) (matrix (mul (power x jl.1) y)) := by
    intro n i k
    rw [matrix_mul]
    exact majorizes_mul (positive_power ha jl.1) hb (hpow jl.1) hy n i k
  have h := productKernel_majorizes F (positive_mul (positive_power ha jl.1) hb)
    (positive_power ha jl.2) hmul (hpow jl.2)
    (fun v => productKernel_positive (positive_power ha jl.1) hb (powerKernel_positive ha hKp jl.1) hHp v)
    (powerKernel_positive ha hKp jl.2)
    (fun v => productKernel_majorizes F (positive_power ha jl.1) hb (hpow jl.1) hy
      (powerKernel_positive ha hKp jl.1) hHp (powerKernel_majorizes F ha hx hKp hK jl.1) hH v)
    (powerKernel_majorizes F ha hx hKp hK jl.2) v
  intro n i j
  change ‖matrix (QuantumNLS.Local006.WordExpansionI.weight jl • rawWordDerivative x y D J jl v) n i j‖ ≤ _
  rw [matrix_smul, Matrix.smul_apply, norm_smul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (QuantumNLS.Local006.WordExpansionI.weight_norm jl)).trans (h n i j)

lemma wordDerivative_norm_le {a b x y : Mixed} {K H : Seq2 →L[ℂ] Mixed}
    {D J : E →L[ℝ] Mixed} (F : E → Seq2) (hF : ∀ v, ‖F v‖ = ‖v‖)
    (ha : Positive a) (hb : Positive b) (hx : Majorizes a (matrix x)) (hy : Majorizes b (matrix y))
    (hKp : ∀ v, Positive (K (moduli v))) (hHp : ∀ v, Positive (H (moduli v)))
    (hK : ∀ v, Majorizes (K (moduli (F v))) (matrix (D v)))
    (hH : ∀ v, Majorizes (H (moduli (F v))) (matrix (J v))) (jl : ℕ × ℕ) :
    ‖wordDerivative x y D J jl‖ ≤ ‖wordKernel a b K H jl‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  exact (solid_norm (wordKernel_positive ha hb hKp hHp jl (F v))
    (wordKernel_majorizes F ha hb hx hy hKp hHp hK hH jl v)).trans
    (by simpa only [moduli_norm, hF] using (wordKernel a b K H jl).le_opNorm (moduli (F v)))

lemma wordBound_summable (M : ℝ) : Summable (fun jl : ℕ × ℕ =>
    4 * (jl.1+jl.2+1 : ℝ) * M * ((1/2 : ℝ)^jl.1 * (1/2 : ℝ)^jl.2)) := by
  have hq : ‖(1/2 : ℝ)‖ < 1 := by norm_num
  have hg := summable_geometric_of_norm_lt_one hq
  have hj := summable_pow_mul_geometric_of_norm_lt_one 1 hq
  simp only [pow_one] at hj
  have h1 := hj.mul_of_nonneg hg (fun n => by positivity) (fun n => by positivity)
  have h2 := hg.mul_of_nonneg hj (fun n => by positivity) (fun n => by positivity)
  have h3 := hg.mul_of_nonneg hg (fun n => by positivity) (fun n => by positivity)
  apply (((h1.add h2).add h3).mul_left (4*M)).congr
  intro jl
  ring

end QuantumNLS.Local006.NormalizationKernelJ

#print axioms QuantumNLS.Local006.NormalizationKernelJ.product_hasFDerivAt
#print axioms QuantumNLS.Local006.NormalizationKernelJ.wordKernel_summable
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local006.NormalizationKernelJ." ||
        n.toString.startsWith "_private.QuantumNLS.Local006NormalizationKernelJ" then
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
  Lean.logInfo m!"Local006NormalizationKernelJ audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."

