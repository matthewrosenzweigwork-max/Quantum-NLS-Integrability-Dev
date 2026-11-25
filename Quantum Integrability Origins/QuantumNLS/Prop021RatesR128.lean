import QuantumNLS.Prop021CoefficientR128

/-! PROP-021: the polynomial number parameter and the exact N^(-1/4) rate
arithmetic after the operator estimates. Constants are explicit and independent
of dimension, N, M, P and u_0. This is scalar bookkeeping, not an assertion
that the physical error or beta block has already been identified. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace QuantumNLS.Prop021RatesR128

/-- Literal Q from Q7B:eq:Q. -/
def numberParameter (C T M P : ℝ) : ℝ := 1+C^2*T^2*M^2*P^2

lemma one_le_numberParameter (C T M P : ℝ) : 1 ≤ numberParameter C T M P := by
  have h : 0 ≤ C^2*T^2*M^2*P^2 := by positivity
  unfold numberParameter
  linarith

/-- The printed beta bound gives the printed depletion scale, including
negative times. The beta bound is a predecessor estimate, not proved here. -/
theorem beta_square_le {C T M P t b : ℝ} (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hM : 0 ≤ M) (hP : 0 ≤ P) (hb : 0 ≤ b) (ht : |t| ≤ T)
    (hβ : b ≤ |t| * C*M*P) : b^2 ≤ numberParameter C T M P-1 := by
  have hm : |t| * C*M*P ≤ T*C*M*P := by gcongr
  have hn : 0 ≤ T*C*M*P := by positivity
  have hs : (T*C*M*P)^2 = numberParameter C T M P-1 := by
    unfold numberParameter
    ring
  rw [← hs]
  nlinarith [hβ.trans hm]

/-- Square-root ratio expressed at exactly the source power of N. -/
theorem sqrt_ratio {N Q : ℝ} (hN : 0 < N) (hQ : 0 ≤ Q) :
    Real.sqrt (Q/N) = Real.sqrt Q * N^(-(1/2):ℝ) := by
  rw [Real.sqrt_div hQ,Real.sqrt_eq_rpow N,Real.rpow_neg hN.le]
  norm_num
  ring

/-- The N^(1/4) projection loss changes both terms from N^(-1/2) to N^(-1/4). -/
theorem extraction_rate_identity {N Q : ℝ} (hN : 0 < N) (hQ : 0 ≤ Q) (D M : ℝ) :
    N^(1/4:ℝ) *
      (D*M*N^(-(1/2):ℝ)*Q^(3/2:ℝ)+Real.sqrt (Q/N)) =
    N^(-(1/4):ℝ) * (D*M*Q^(3/2:ℝ)+Real.sqrt Q) := by
  have hp : N^(1/4:ℝ)*N^(-(1/2):ℝ) =
      N^(-(1/4):ℝ) := by
    rw [← Real.rpow_add hN]
    norm_num
  rw [sqrt_ratio hN hQ]
  calc
    _ = (N^(1/4:ℝ)*N^(-(1/2):ℝ))*
        (D*M*Q^(3/2:ℝ)+Real.sqrt Q) := by ring
    _ = _ := by rw [hp]

/-- Absorb the remainder constant into a single parameter-independent constant. -/
theorem source_marginal_rate {N Q M : ℝ} (hN : 0 < N) (hQ : 0 ≤ Q)
    (hM : 0 ≤ M) (D k : ℝ) :
    2*Real.sqrt k*(Real.sqrt (Real.exp 1)*N^(1/4:ℝ)*
      (D*M*N^(-(1/2):ℝ)*Q^(3/2:ℝ)+Real.sqrt (Q/N))) ≤
    (2*Real.sqrt (Real.exp 1)*max D 1)*Real.sqrt k*N^(-(1/4):ℝ)*
      (M*Q^(3/2:ℝ)+Real.sqrt Q) := by
  have ha : 0 ≤ M*Q^(3/2:ℝ) := mul_nonneg hM (Real.rpow_nonneg hQ _)
  have hb : 0 ≤ Real.sqrt Q := Real.sqrt_nonneg _
  have hab : D*(M*Q^(3/2:ℝ))+Real.sqrt Q ≤
      max D 1*(M*Q^(3/2:ℝ)+Real.sqrt Q) := by
    nlinarith [le_max_left D 1,le_max_right D 1]
  have hf : 0 ≤ 2*Real.sqrt k*Real.sqrt (Real.exp 1)*N^(-(1/4):ℝ) := by positivity
  calc
    _ = (2*Real.sqrt k*Real.sqrt (Real.exp 1)) *
        (N^(1/4:ℝ)*
          (D*M*N^(-(1/2):ℝ)*Q^(3/2:ℝ)+Real.sqrt (Q/N))) := by ring
    _ = (2*Real.sqrt k*Real.sqrt (Real.exp 1)*N^(-(1/4):ℝ))*
        (D*(M*Q^(3/2:ℝ))+Real.sqrt Q) := by
      rw [extraction_rate_identity hN hQ]
      ring
    _ ≤ (2*Real.sqrt k*Real.sqrt (Real.exp 1)*N^(-(1/4):ℝ))*
        (max D 1*(M*Q^(3/2:ℝ)+Real.sqrt Q)) := mul_le_mul_of_nonneg_left hab hf
    _ = _ := by ring
end QuantumNLS.Prop021RatesR128
#print axioms QuantumNLS.Prop021RatesR128.beta_square_le
#print axioms QuantumNLS.Prop021RatesR128.source_marginal_rate

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if ["Prop021RatesR128"].any
        (fun m => n.toString.startsWith ("QuantumNLS." ++ m ++ ".") ||
          n.toString.startsWith ("_private.QuantumNLS." ++ m ++ ".")) then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").contains "HeldGP14Tonelli" ||
          (n.toString.splitOn ".").contains "RegularCut" then
        throwError "Forbidden held dependency: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"R128 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
