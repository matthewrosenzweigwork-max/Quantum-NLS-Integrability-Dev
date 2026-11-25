import QuantumNLS.Local006PositiveMajorantG
import QuantumNLS.Local006FirstCoefficientE

/-! Actual positive Fourier path majorants lifted to the mixed sequence space.
All hypotheses are the standing source geometry. Every Fourier slot is allowed
independent data. The degree-one projection majorant is exactly zero. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open scoped BigOperators ENNReal
namespace QuantumNLS.Local006.SourceMajorantG
open QuantumNLS.Local005 QuantumNLS.Local005.SourceC QuantumNLS.Local005.SourceD
  QuantumNLS.Local006.CoefficientLiftE QuantumNLS.Local006.SequenceAlgebraE
  QuantumNLS.Local006.SequenceEvaluationE QuantumNLS.Local006.PositiveMajorantG
  QuantumNLS.Local006.FirstCoefficientE QuantumNLS.LocalSpectral
  QuantumNLS.ResetFreeResolventLOCAL001 QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
  QuantumNLS.ResolventWordEstimateStage2LOCAL005

/-- A nonnegative scalar Fourier envelope is placed in its actual parity
components, rather than used merely as a bound on the whole matrix norm. -/
lemma lift_parity {k : ℕ} {M : ℤ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hM : ∀ n, 0 ≤ M n)
    (ho : Odd k → Summable (fun n => M n ^ 2) ∧ ∑' n, M n ^ 2 ≤ B ^ 2)
    (he : ¬ Odd k → ∀ n, M n ≤ B) :
    ∃ a : Mixed, Positive a ∧ ‖a‖ ≤ B ∧
      ∀ n i j, matrix a n i j = if i = componentAfter k j then (M n : ℂ) else 0 := by
  classical
  by_cases hk : Odd k
  · obtain ⟨v, hv, hn⟩ := lift_l2 (fun n => (M n : ℂ)) M hB (ho hk).1 (ho hk).2
      (fun n => by simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hM n)])
    let a : Mixed := ((0, 0), (v, v))
    have hm : ∀ n i j, matrix a n i j = if i = componentAfter k j then (M n : ℂ) else 0 := by
      intro n i j
      have h0 : componentAfter k 0 = 1 := by
        apply Fin.ext
        have hmod := Nat.odd_iff.mp hk
        change (0 + k) % 2 = 1
        omega
      have h1 : componentAfter k 1 = 0 := by
        apply Fin.ext
        have hmod := Nat.odd_iff.mp hk
        change (1 + k) % 2 = 0
        omega
      fin_cases i <;> fin_cases j <;> simp [a, matrix, h0, h1, hv]
    refine ⟨a, ?_, ?_, hm⟩
    · intro n i j
      rw [hm]
      split_ifs <;> simp [hM n]
    · simpa only [a, Prod.norm_def, norm_zero, max_self, max_eq_right (norm_nonneg v)] using hn
  · obtain ⟨v, hv, hn⟩ := lift_linf (fun n => (M n : ℂ)) hB
      (fun n => by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hM n)] using he hk n)
    let a : Mixed := ((v, v), (0, 0))
    have hm : ∀ n i j, matrix a n i j = if i = componentAfter k j then (M n : ℂ) else 0 := by
      intro n i j
      rw [componentAfter_even (Nat.not_odd_iff_even.mp hk)]
      fin_cases i <;> fin_cases j <;> simp [a, matrix, hv]
    refine ⟨a, ?_, ?_, hm⟩
    · intro n i j
      rw [hm]
      split_ifs <;> simp [hM n]
    · simpa only [a, Prod.norm_def, norm_zero, max_self, max_eq_left (norm_nonneg v)] using hn

/-- Independent-slot LOCAL-005 bounds give positive sequence-space majorants,
with the exact absolute path sum in every supported matrix entry. -/
theorem independent_majorant {L r κ : ℝ} (hL : 0 < L) (hκ : 0 < κ)
    (hr : 0 < r) (hsmall : r < spacing L / 2) {k : ℕ} (hk : 1 ≤ k)
    (kind : WordKind) (u : Fin k → ℤ → ℂ)
    (hu : ∀ t, Summable fun m => ‖u t m‖ ^ 2) :
    ∃ a : Mixed, Positive a ∧ ‖a‖ ≤ wordConstant L r κ ^ k * ∏ t, inputL2Norm u t ∧
      (∀ n i j, matrix a n i j =
        if i = componentAfter k j then (contourMajorant L r κ kind k u n : ℂ) else 0) ∧
      Majorizes a (fun n i j => coefficientEntry L r κ kind k u n i j) := by
  obtain ⟨a, ha, hn, hm⟩ := lift_parity
    (k := k) (M := contourMajorant L r κ kind k u) (by
      exact mul_nonneg (pow_nonneg (wordConstant_pos hL hr hκ).le _) (Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _))
    (fun n => (contour_majorant_data hL hr hsmall κ kind u hu n).2.1)
    (fun hodd => contour_odd_bound hL hr hsmall κ hκ hk hodd kind u hu)
    (fun _ n => contour_even_bound hL hr hsmall κ hκ hk kind u hu n)
  refine ⟨a, ha, hn, hm, ?_⟩
  intro n i j
  rw [hm]
  by_cases hij : i = componentAfter k j
  · rw [if_pos hij, Complex.ofReal_re]
    exact (coefficient_converges hL hr hsmall κ kind u hu n i j).2
  · simp [coefficientEntry, hij]

variable {L r κ : ℝ} [Fact (0 < L)]

/-- Source-word instantiation: no norm or coefficient-identity hypotheses on
physical inputs. The binomial majorants are fed the actual source words. -/
theorem physical_majorant (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) {k : ℕ} (hk : 1 ≤ k)
    (kind : WordKind) (u : Fin k → ScalarInterval L) :
    ∃ a : Mixed, Positive a ∧ ‖a‖ ≤ wordConstant L r κ ^ k * ∏ t, ‖u t‖ ∧
      (∀ n i j, matrix a n i j =
        if i = componentAfter k j then
          (physicalMajorant L r κ kind k (extendInputs u) n : ℂ) else 0) ∧
      Majorizes a (fun n i j => coefficient hL hκ hr hsmall k kind u i j n) := by
  obtain ⟨a, ha, hn, hm, hmaj⟩ := independent_majorant hL hκ hr hsmall hk kind
    (physicalInputs 0 u) (physicalInputs_summable 0 u)
  simp only [physicalInputs_norm, physicalMajorant_finite] at hn hm
  refine ⟨a, ha, hn, hm, ?_⟩
  intro n i j
  rw [hm]
  by_cases hij : i = componentAfter k j
  · rw [if_pos hij, Complex.ofReal_re]
    change ‖entryFunctional n i j
      (orderedSourceWord hL hκ hr hsmall kind (extendInputs u) n k)‖ ≤ _
    rw [orderedSourceWord_entry_posdegree hL hκ hr hsmall n (extendInputs u) hk kind i j]
    have hc := (coefficient_converges hL hr hsmall κ kind
      (physicalInputs j (fun t : Fin k => extendInputs u t))
      (physicalInputs_summable j _) n i j).2
    simpa only [physicalMajorant_component] using hc
  · rw [if_neg hij]
    change ‖entryFunctional n i j
      (orderedSourceWord hL hκ hr hsmall kind (extendInputs u) n k)‖ ≤ _
    rw [orderedSourceWord_entry_posdegree hL hκ hr hsmall n (extendInputs u) hk kind i j]
    simp [coefficientEntry, hij]

/-- Vanishing survives passage to coefficientwise absolute Fourier values. -/
theorem first_projection_majorant_zero (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (u : Fin 1 → ScalarInterval L)
    (a : Mixed) (hm : ∀ n i j, matrix a n i j =
      if i = componentAfter 1 j then
        (physicalMajorant L r κ .projection 1 (extendInputs u) n : ℂ) else 0) : a = 0 := by
  have hz : ∀ n i j, matrix a n i j = 0 := by
    intro n i j
    rw [hm, (first_projection_coefficient_zero hL hκ hr hsmall u n i j).2]
    split_ifs <;> rfl
  apply Prod.ext
  · apply Prod.ext
    · apply lp.ext; funext n; simpa [matrix] using hz n 0 0
    · apply lp.ext; funext n; simpa [matrix] using hz n 1 1
  · apply Prod.ext
    · apply lp.ext; funext n; simpa [matrix] using hz n 0 1
    · apply lp.ext; funext n; simpa [matrix] using hz n 1 0

end QuantumNLS.Local006.SourceMajorantG
#print axioms QuantumNLS.Local006.SourceMajorantG.independent_majorant
#print axioms QuantumNLS.Local006.SourceMajorantG.physical_majorant
#print axioms QuantumNLS.Local006.SourceMajorantG.first_projection_majorant_zero

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local006.SourceMajorantG." ||
        n.toString.startsWith "_private.QuantumNLS.Local006SourceMajorantG" then
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
  Lean.logInfo m!"Local006SourceMajorantG audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
