import QuantumNLS.Prop001RseventeenDuhamel

/-! Exponential rank estimates for the actual collision series.
These estimates retain the printed C_a, and supply no propagation conclusion. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
open Filter Topology
open scoped BigOperators ENNReal
namespace QuantumNLS.Prop001RseventeenWeights
open TraceClass TraceIdeal TensorCarrier Prop001 Prop001RthirteenSeries Ext025A12Collision
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A useful squared-polynomial majorant with the exact constant four. -/
theorem square_le_exp (x : ℝ) (hx : 0 ≤ x) : x^2 ≤ Real.exp x := by
  have h := Real.add_one_le_exp (x/2-1)
  have htwo := Real.add_one_le_exp (1 : ℝ)
  have he : x ≤ Real.exp (x/2) := by
    calc
      x ≤ 2*Real.exp (x/2-1) := by linarith
      _ ≤ Real.exp 1*Real.exp (x/2-1) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = Real.exp (x/2) := by rw [← Real.exp_add];congr 1;ring
  calc
    x^2 ≤ (Real.exp (x/2))^2 := pow_le_pow_left₀ hx he 2
    _ = Real.exp x := by rw [← Real.exp_nat_mul];congr 1;ring

/-- The source forcing polynomial fits in half the exponential margin. -/
theorem square_half_exp_bound {a : ℝ} (ha : 0 < a) (k : ℕ) :
    (k : ℝ)^2 ≤ (4/a^2)*Real.exp (a/2*k) := by
  have h := square_le_exp (a/2*k) (by positivity)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
  nlinarith

/-- The printed rank moment controls every smaller exponential weight. -/
theorem rank_moment (D : ClassicalData H) (q : ℝ) (hq : q ≤ D.a) :
    Summable (fun n => (2*((n+1 : ℕ) : ℝ)*‖D.A n‖)*Real.exp (q*n)) ∧
      (∑' n,(2*((n+1 : ℕ) : ℝ)*‖D.A n‖)*Real.exp (q*n)) ≤ collisionSum D.A D.a := by
  let f := fun n : ℕ => (2*((n+1 : ℕ) : ℝ)*‖D.A n‖)*Real.exp (q*n)
  let g := fun n : ℕ => 2*(((n+1 : ℕ) : ℝ)*‖D.A n‖*Real.exp (D.a*n))
  have hg : Summable g := D.exponential.mul_left 2
  have hp : ∀ n,0 ≤ f n := fun _ => by dsimp [f];positivity
  have hle (n : ℕ) : f n ≤ g n := by
    dsimp [f,g]
    calc
      _ ≤ (2*((n+1 : ℕ) : ℝ)*‖D.A n‖)*Real.exp (D.a*n) := by
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg n))) (by positivity)
      _ = _ := by ring
  have hf := Summable.of_nonneg_of_le hp hle hg
  refine ⟨hf,?_⟩
  have hh := hf.tsum_le_tsum hle hg
  simpa only [g,tsum_mul_left,collisionSum] using hh

/-- The scalar collision of an exponential rank weight, with exact C_a. -/
theorem collision_exp_weight (D : ClassicalData H) (q : ℝ) (hq : q ≤ D.a) (k : ℕ) :
    Summable (fun n => (2*((n+1 : ℕ) : ℝ)*((k+1 : ℕ) : ℝ)*‖D.A n‖)*
      Real.exp (q*(((k+1)+n : ℕ) : ℝ))) ∧
    (∑' n,(2*((n+1 : ℕ) : ℝ)*((k+1 : ℕ) : ℝ)*‖D.A n‖)*Real.exp (q*(((k+1)+n : ℕ) : ℝ))) ≤
      ((k+1 : ℕ) : ℝ)*Real.exp (q*((k+1 : ℕ) : ℝ))*collisionSum D.A D.a := by
  have he (n : ℕ) :
      (2*((n+1 : ℕ) : ℝ)*((k+1 : ℕ) : ℝ)*‖D.A n‖)*Real.exp (q*(((k+1)+n : ℕ) : ℝ)) =
      (((k+1 : ℕ) : ℝ)*Real.exp (q*((k+1 : ℕ) : ℝ)))*
        ((2*((n+1 : ℕ) : ℝ)*‖D.A n‖)*Real.exp (q*n)) := by
    have hex : Real.exp (q*(((k+1)+n : ℕ) : ℝ)) =
        Real.exp (q*((k+1 : ℕ) : ℝ))*Real.exp (q*n) := by
      rw [Nat.cast_add,mul_add,Real.exp_add]
    rw [hex]
    ring
  simp_rw [he]
  refine ⟨(rank_moment D q hq).1.mul_left _,?_⟩
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (rank_moment D q hq).2 (by positivity)

/-- The actual collision series maps exponential rank bounds with the printed
moment C_a. Summability is proved from that same majorant. -/
theorem collisionSeries_exp_bound (D : ClassicalData H) (q : ℝ) (hq : q ≤ D.a)
    (Γ : Hierarchy H) (hΓ : ∀ j,IsTraceClass (Γ j)) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j,traceNorm (Γ j) ≤ ENNReal.ofReal (M*Real.exp (q*j))) (k : ℕ) :
    traceNorm (collisionSeries D.A Γ hΓ k) ≤
      ENNReal.ofReal (M*(((k+1 : ℕ) : ℝ)*Real.exp (q*((k+1 : ℕ) : ℝ))*collisionSum D.A D.a)) := by
  let b := fun n : ℕ => M*((2*((n+1 : ℕ) : ℝ)*((k+1 : ℕ) : ℝ)*‖D.A n‖)*
    Real.exp (q*(((k+1)+n : ℕ) : ℝ)))
  have hb : Summable b := (collision_exp_weight D q hq k).1.mul_left M
  have hp : ∀ n,0 ≤ b n := fun n => by dsimp [b];positivity
  have ht : traceNorm (collisionSeries D.A Γ hΓ k) ≤ ENNReal.ofReal (∑' n,b n) := by
    apply traceNorm_tsum_le _ b hb hp
    intro n
    refine (sourceRankCollision_bound k n (D.A n) _ (hΓ _)).trans ?_
    calc
      _ ≤ ENNReal.ofReal (2*((n+1 : ℕ) : ℝ)*((k+1 : ℕ) : ℝ)*‖D.A n‖)*
          ENNReal.ofReal (M*Real.exp (q*(((k+1)+n : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left (hbound _) (by positivity)
      _ = ENNReal.ofReal (b n) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        dsimp [b]
        ring
  apply ht.trans
  apply ENNReal.ofReal_le_ofReal
  rw [show (∑' n,b n)=M*∑' n,(2*((n+1 : ℕ) : ℝ)*((k+1 : ℕ) : ℝ)*‖D.A n‖)*
    Real.exp (q*(((k+1)+n : ℕ) : ℝ)) from tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (collision_exp_weight D q hq k).2 hM

end QuantumNLS.Prop001RseventeenWeights

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001RseventeenWeights" then
      pending := pending.push n
      roots := roots + 1
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
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Prop001RseventeenWeights audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."





#print axioms QuantumNLS.Prop001RseventeenWeights.square_le_exp
#print axioms QuantumNLS.Prop001RseventeenWeights.square_half_exp_bound
#print axioms QuantumNLS.Prop001RseventeenWeights.rank_moment
#print axioms QuantumNLS.Prop001RseventeenWeights.collision_exp_weight

#print axioms QuantumNLS.Prop001RseventeenWeights.collisionSeries_exp_bound
