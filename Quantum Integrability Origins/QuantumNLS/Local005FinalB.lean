import QuantumNLS.Local005BoundsB
import QuantumNLS.Local005CoefficientsB

/-!
LOCAL-005: exact contour-integrated Fourier word estimates in every positive degree.
The source's k inputs are independent complex Fourier sequences; all conjugated
slots are allowed independent inputs. The path formula keeps S's two endpoint
poles and K's extra factor. There is no supplied LOCAL-001 bound hypothesis.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators ENNReal
namespace QuantumNLS.Local005
open QuantumNLS.ResetFreeResolventLOCAL001
open QuantumNLS.ResolventWordEstimateStage2LOCAL005

def wordConstant (L r κ : ℝ) : ℝ :=
  2 * Real.sqrt (κ / L) * (1 + L * resolventConstant L r ^ 2) * (1 + r⁻¹)

/-- The uniform denominator sum is exactly the LOCAL-001 source constant.
This uses the completed r12 theorem directly, with a genuine contour point. -/
theorem gapSum_eq_local001 {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (κ : ℝ) (hκ : 0 < κ) :
    gapSum L r = L * resolventConstant L r ^ 2 := by
  let : Fact (0 < L) := ⟨hL⟩
  have hz : OnGamma L r 0 (r : ℂ) := by
    simp [OnGamma, QuantumNLS.LocalSpectral.pm, abs_of_pos hr]
  have hc := (reset_free_resolvent_estimates κ hL hκ 0 hr hsmall hz
    (0 : CompletionB.ScalarInterval L)).2.2.1
  rw [gapSum, denominatorMajorant_tsum_eq_source hL hr hsmall, hc]
  field_simp [ne_of_gt hL]

theorem wordConstant_eq {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (κ : ℝ) (hκ : 0 < κ) :
    wordConstant L r κ = baseConstant L r κ * (1 + r⁻¹) := by
  rw [wordConstant, baseConstant, gapSum_eq_local001 hL hr hsmall κ hκ]

theorem wordConstant_pos {L r κ : ℝ} (hL : 0 < L) (hr : 0 < r) (hκ : 0 < κ) :
    0 < wordConstant L r κ := by unfold wordConstant; positivity

theorem endpoint_absorbed {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (κ : ℝ) (hκ : 0 < κ)
    {k : ℕ} (hk : 1 ≤ k) (kind : WordKind) (N : ℝ) (hN : 0 ≤ N) :
    endpointBound r kind * (baseConstant L r κ ^ k * N) ≤
      wordConstant L r κ ^ k * N := by
  have hE : 1 ≤ 1 + r⁻¹ := by linarith [inv_pos.mpr hr]
  have hEP : 1 + r⁻¹ ≤ (1 + r⁻¹) ^ k := by
    simpa using pow_le_pow_right₀ hE hk
  have hkind : endpointBound r kind ≤ 1 + r⁻¹ := by
    cases kind with
    | projection => change r⁻¹ ≤ 1 + r⁻¹; linarith
    | moment => exact hE
  have hbase := pow_nonneg (baseConstant_nonneg L r κ) k
  rw [wordConstant_eq hL hr hsmall κ hκ, mul_pow]
  calc
    _ ≤ (1 + r⁻¹) ^ k * (baseConstant L r κ ^ k * N) :=
      mul_le_mul_of_nonneg_right (hkind.trans hEP) (mul_nonneg hbase hN)
    _ = _ := by ring

/-- Uniform bound for either integrated majorant, without a parity restriction. -/
theorem contour_even_bound {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (κ : ℝ) (hκ : 0 < κ)
    {k : ℕ} (hk : 1 ≤ k) (kind : WordKind)
    (u : Fin k → ℤ → ℂ) (hu : ∀ j, Summable fun m => ‖u j m‖ ^ 2) (n : ℤ) :
    contourMajorant L r κ kind k u n ≤
      wordConstant L r κ ^ k * ∏ j, inputL2Norm u j := by
  have hd := contour_majorant_data hL hr hsmall κ kind u hu n
  have hE : 0 ≤ endpointBound r kind := by cases kind <;> simp [endpointBound]; positivity
  calc
    _ ≤ endpointBound r kind * envelope L r κ k u n := hd.2.2
    _ ≤ endpointBound r kind * (baseConstant L r κ ^ k * ∏ j, inputL2Norm u j) :=
      mul_le_mul_of_nonneg_left (envelope_even_bound hL hr hsmall κ hk u hu n) hE
    _ ≤ _ := endpoint_absorbed hL hr hsmall κ hκ hk kind _
      (Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _)

/-- Summing the squared integrated majorants in odd degree is legitimate and bounded. -/
theorem contour_odd_bound {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (κ : ℝ) (hκ : 0 < κ)
    {k : ℕ} (hk : 1 ≤ k) (hodd : Odd k) (kind : WordKind)
    (u : Fin k → ℤ → ℂ) (hu : ∀ j, Summable fun m => ‖u j m‖ ^ 2) :
    Summable (fun n : ℤ => contourMajorant L r κ kind k u n ^ 2) ∧
      ∑' n : ℤ, contourMajorant L r κ kind k u n ^ 2 ≤
        (wordConstant L r κ ^ k * ∏ j, inputL2Norm u j) ^ 2 := by
  obtain ⟨hs, hb⟩ := envelope_odd_bound hL hr hsmall κ hk hodd u hu
  have hE : 0 ≤ endpointBound r kind := by cases kind <;> simp [endpointBound]; positivity
  have hpoint : ∀ n : ℤ, contourMajorant L r κ kind k u n ^ 2 ≤
      endpointBound r kind ^ 2 * envelope L r κ k u n ^ 2 := by
    intro n
    have hd := contour_majorant_data hL hr hsmall κ kind u hu n
    simpa only [mul_pow] using (sq_le_sq₀ hd.2.1
      (mul_nonneg hE (envelope_nonneg L r κ k u n))).2 hd.2.2
  have hsum : Summable (fun n : ℤ => contourMajorant L r κ kind k u n ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hpoint (hs.mul_left _)
  have hN : 0 ≤ ∏ j, inputL2Norm u j := Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _
  refine ⟨hsum, ?_⟩
  calc
    _ ≤ ∑' n : ℤ, endpointBound r kind ^ 2 * envelope L r κ k u n ^ 2 :=
      hsum.tsum_le_tsum hpoint (hs.mul_left _)
    _ = endpointBound r kind ^ 2 * ∑' n : ℤ, envelope L r κ k u n ^ 2 := tsum_mul_left
    _ ≤ endpointBound r kind ^ 2 *
        (baseConstant L r κ ^ k * ∏ j, inputL2Norm u j) ^ 2 :=
      mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = (endpointBound r kind *
        (baseConstant L r κ ^ k * ∏ j, inputL2Norm u j)) ^ 2 := (mul_pow _ _ _).symm
    _ ≤ _ := (sq_le_sq₀
      (mul_nonneg hE (mul_nonneg (pow_nonneg (baseConstant_nonneg L r κ) k) hN))
      (mul_nonneg (pow_nonneg (wordConstant_pos hL hr hκ).le k) hN)).2
        (endpoint_absorbed hL hr hsmall κ hκ hk kind _
          (Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _))

end QuantumNLS.Local005
namespace QuantumNLS.ResetResolventWordLOCAL005
open QuantumNLS.Local005
open QuantumNLS.ResetFreeResolventLOCAL001
open QuantumNLS.ResolventWordEstimateStage2LOCAL005

/-- **LOCAL-005: Resolvent word estimate.** In every positive degree and for
all independent square-summable Fourier inputs, the exact integrated S and K
Fourier path series converge absolutely. Odd words are off-diagonal with the
printed collective l2 bound; even words are diagonal with the printed uniform
bound. All scientific hypotheses are the printed geometric ones. -/
theorem reset_resolvent_word (L r κ : ℝ) (hL : 0 < L) (hκ : 0 < κ)
    (hr : 0 < r) (hsmall : r < spacing L / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k : ℕ), 1 ≤ k → ∀ (u : Fin k → ℤ → ℂ),
        (∀ j, Summable fun m => ‖u j m‖ ^ 2) → ∀ kind : WordKind,
          (∀ (n : ℤ) (i j : Fin 2),
            Summable (fun q : Fin (k - 1) → ℤ => ‖pathCoefficient L r κ kind j u n q‖) ∧
              ‖coefficientEntry L r κ kind k u n i j‖ ≤ contourMajorant L r κ kind k u n ∧
              ENNReal.ofReal (contourMajorant L r κ kind k u n) =
                ⨆ N, ∑ t ∈ Finset.range N,
                  codedTerm (fun q : Fin (k - 1) → ℤ =>
                    ENNReal.ofReal (contourAbsTerm L r κ kind u n q)) t) ∧
          if Odd k then
            (∀ (n : ℤ) (j : Fin 2), coefficientEntry L r κ kind k u n j j = 0) ∧
              Summable (fun n : ℤ => contourMajorant L r κ kind k u n ^ 2) ∧
                ∑' n : ℤ, contourMajorant L r κ kind k u n ^ 2 ≤
                  (C ^ k * ∏ j, inputL2Norm u j) ^ 2
          else
            (∀ (n : ℤ) (i j : Fin 2), i ≠ j → coefficientEntry L r κ kind k u n i j = 0) ∧
              ∀ n : ℤ, contourMajorant L r κ kind k u n ≤ C ^ k * ∏ j, inputL2Norm u j := by
  refine ⟨wordConstant L r κ, wordConstant_pos hL hr hκ, ?_⟩
  intro k hk u hu kind
  refine ⟨?_, ?_⟩
  · intro n i j
    have hd := coefficient_converges hL hr hsmall κ kind u hu n i j
    exact ⟨hd.1, hd.2, contour_monotone_convergence hL hr hsmall κ kind u hu n⟩
  · split_ifs with hodd
    · refine ⟨fun n j => coefficient_odd hodd L r κ kind u n j, ?_⟩
      exact contour_odd_bound hL hr hsmall κ hκ hk hodd kind u hu
    · refine ⟨fun n i j hij => coefficient_even (Nat.not_odd_iff_even.mp hodd)
          L r κ kind u n i j hij, ?_⟩
      exact fun n => contour_even_bound hL hr hsmall κ hκ hk kind u hu n

set_option pp.proofs false in
#print reset_resolvent_word
#print axioms reset_resolvent_word
end QuantumNLS.ResetResolventWordLOCAL005

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local005." ||
        n.toString.startsWith "QuantumNLS.ResetResolventWordLOCAL005." ||
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
  Lean.logInfo m!"Local005FinalB audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
