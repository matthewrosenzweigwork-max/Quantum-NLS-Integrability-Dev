import QuantumNLS.Prop001RtwentyIteration
import QuantumNLS.Prop001RseventeenWeights
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import QuantumNLS.Prop001RelevenClassical
import QuantumNLS.Prop001RseventeenZero

/-! Consolidated round20 propagation proof. Each namespace fragment is enclosed
in its own section, reproducing the source module scope. -/

-- Namespace fragment: Prop001RtwentyRemainder
/-! A direct analytic-scale estimate for the ACTUAL finite-depth remainder.
The radius is the printed a/C_a, including the printed step a/(4*C_a).
This does not yet estimate the initial/forcing partial substitutions. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
open Filter Topology MeasureTheory
open scoped BigOperators ENNReal
namespace QuantumNLS.Prop001RtwentyRemainder
open TraceClass TensorCarrier Prop001 Prop001RtwentyIteration
  Prop001RseventeenContinuity Prop001RseventeenWeights
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exp_rank_loss (q δ x : ℝ) (hδ : 0 < δ) :
    x*Real.exp (q*x) ≤ Real.exp ((q+δ)*x)/(δ*Real.exp 1) := by
  have h : δ*x ≤ Real.exp (δ*x-1) := by linarith [Real.add_one_le_exp (δ*x-1)]
  apply (le_div_iff₀ (mul_pos hδ (Real.exp_pos 1))).mpr
  calc
    _ = (δ*x)*(Real.exp (q*x)*Real.exp 1) := by ring
    _ ≤ Real.exp (δ*x-1)*(Real.exp (q*x)*Real.exp 1) :=
      mul_le_mul_of_nonneg_right h (by positivity)
    _ = _ := by rw [← Real.exp_add,← Real.exp_add];congr 1;ring

/-- An actual rank sum with its summability discharged by the printed moment. -/
theorem rank_sum_bound (D : ClassicalData H) (q M : ℝ) (hq : q ≤ D.a)
    (hM : 0 ≤ M) (k : ℕ) :
    (∑' n,rankWeights D n*((k+1 : ℕ) : ℝ≥0∞)*
      ENNReal.ofReal (M*Real.exp (q*((k+n+1 : ℕ) : ℝ)))) ≤
      ENNReal.ofReal (M*(((k+1 : ℕ) : ℝ)*Real.exp (q*((k+1 : ℕ) : ℝ))*collisionSum D.A D.a)) := by
  let f := fun n : ℕ =>
    (2*((n+1 : ℕ) : ℝ)*((k+1 : ℕ) : ℝ)*‖D.A n‖)*Real.exp (q*(((k+1)+n : ℕ) : ℝ))
  have hs : Summable f := (collision_exp_weight D q hq k).1
  have he (n : ℕ) : rankWeights D n*((k+1 : ℕ) : ℝ≥0∞)*
      ENNReal.ofReal (M*Real.exp (q*((k+n+1 : ℕ) : ℝ))) = ENNReal.ofReal (M*f n) := by
    have hn : k+n+1=(k+1)+n := by omega
    rw [rankWeights,← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity),hn]
    congr 1
    dsimp [f]
    ring
  simp_rw [he]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by dsimp [f];positivity) (hs.mul_left M),tsum_mul_left]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (collision_exp_weight D q hq k).2 hM)

/-- Integrate a polynomial/exponential majorant against the actual scalar
Volterra operator. The estimate retains its factorial time gain. -/
theorem volterra_monomial_bound (D : ClassicalData H) (q δ M : ℝ)
    (hq : q ≤ D.a) (hδ : 0 < δ) (hM : 0 ≤ M) (p : ℕ)
    (f : ℕ → ℝ → ℝ≥0∞)
    (hf : ∀ j s,0 ≤ s → f j s ≤ ENNReal.ofReal (M*s^p*Real.exp (q*((j+1 : ℕ) : ℝ))))
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    volterra (rankWeights D) f k t ≤
      ENNReal.ofReal (M*(collisionSum D.A D.a/(δ*Real.exp 1))*
        (t^(p+1)/((p+1 : ℕ) : ℝ))*Real.exp ((q+δ)*((k+1 : ℕ) : ℝ))) := by
  let c := ((k+1 : ℕ) : ℝ)*Real.exp (q*((k+1 : ℕ) : ℝ))*collisionSum D.A D.a
  have hc : 0 ≤ c := by dsimp [c];exact mul_nonneg (by positivity) (collisionSum_nonneg _ _)
  have hpoint (s : ℝ) (hs : 0 ≤ s) :
      (∑' n,rankWeights D n*((k+1 : ℕ) : ℝ≥0∞)*f (k+n) s) ≤
        ENNReal.ofReal (M*s^p*c) := by
    exact (ENNReal.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (hf (k+n) s hs)
      (by positivity))).trans (rank_sum_bound D q (M*s^p) hq (by positivity) k)
  have hi : IntervalIntegrable (fun s : ℝ => M*s^p*c) volume 0 t :=
    ((continuous_const.mul (continuous_id.pow p)).mul continuous_const).intervalIntegrable 0 t
  have he : (∫⁻ s in Set.Ioc 0 t,ENNReal.ofReal (M*s^p*c)) =
      ENNReal.ofReal (M*c*(t^(p+1)/((p+1 : ℕ) : ℝ))) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi.1]
    · rw [← intervalIntegral.integral_of_le ht]
      congr 1
      simp_rw [mul_right_comm M _ c]
      rw [intervalIntegral.integral_const_mul,integral_pow]
      simp only [zero_pow (Nat.succ_ne_zero p),sub_zero,Nat.cast_add,Nat.cast_one]
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact mul_nonneg (mul_nonneg hM (pow_nonneg hs.1.le _)) hc
  calc
    _ ≤ ∫⁻ s in Set.Ioc 0 t,ENNReal.ofReal (M*s^p*c) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact hpoint s hs.1.le
    _ = _ := he
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have h := mul_le_mul_of_nonneg_right
        (exp_rank_loss q δ ((k+1 : ℕ) : ℝ) hδ) (collisionSum_nonneg D.A D.a)
      have h' := mul_le_mul_of_nonneg_left h
        (show 0 ≤ M*(t^(p+1)/((p+1 : ℕ) : ℝ)) by positivity)
      convert h' using 1 <;> (try dsimp [c]) <;> ring

/-- Polynomial/exponential data under any finite number of actual scalar
substitutions. The factorial ratio includes the original time power. -/
theorem iterate_monomial_bound (D : ClassicalData H) (q δ M : ℝ)
    (hδ : 0 < δ) (hM : 0 ≤ M) (p : ℕ) (f : ℕ → ℝ → ℝ≥0∞)
    (hf : ∀ j s,0 ≤ s → f j s ≤ ENNReal.ofReal (M*s^p*Real.exp (q*((j+1 : ℕ) : ℝ)))) :
    ∀ n : ℕ, q+(n : ℝ)*δ ≤ D.a → ∀ (k : ℕ) (t : ℝ),0 ≤ t →
      iterate (rankWeights D) f n k t ≤
        ENNReal.ofReal (M*(collisionSum D.A D.a/(δ*Real.exp 1))^n*
          ((p.factorial : ℝ)/((p+n).factorial : ℝ))*t^(p+n)*
          Real.exp ((q+(n : ℝ)*δ)*((k+1 : ℕ) : ℝ))) := by
  have hc := collisionSum_nonneg D.A D.a
  intro n
  induction n with
  | zero =>
    intro _ k t ht
    simpa only [iterate,Nat.add_zero,Nat.cast_zero,zero_mul,add_zero,pow_zero,mul_one,
      div_self (show (p.factorial : ℝ) ≠ 0 by positivity)] using hf k t ht
  | succ n ih =>
    intro hn k t ht
    have hn' : q+(n : ℝ)*δ ≤ D.a := by push_cast at hn;linarith
    have h := volterra_monomial_bound D (q+(n : ℝ)*δ) δ
      (M*(collisionSum D.A D.a/(δ*Real.exp 1))^n*((p.factorial : ℝ)/((p+n).factorial : ℝ)))
      hn' hδ (by positivity) (p+n) (iterate (rankWeights D) f n) (ih hn') k t ht
    change volterra (rankWeights D) (iterate (rankWeights D) f n) k t ≤ _
    apply h.trans (le_of_eq ?_)
    apply congrArg ENNReal.ofReal
    have hqeq : q+((n+1 : ℕ) : ℝ)*δ=q+(n : ℝ)*δ+δ := by push_cast;ring
    rw [hqeq]
    simp only [Nat.add_succ,Nat.factorial_succ,Nat.cast_mul,pow_succ,div_eq_mul_inv,mul_inv_rev]
    push_cast
    ring

/-- Bound n actual substitutions in an exponential scale of step δ.
No bound on the iterate, hierarchy equation or rate is an input. -/
theorem actual_iterate_scale (D : ClassicalData H) (N : ℕ) (ψ : SymSector ℂ H N)
    (hψ : ‖ψ‖=1) (u : Sphere H) (δ : ℝ) (hδ : 0 < δ) :
    ∀ n : ℕ, (n : ℝ)*δ ≤ D.a → ∀ (k : ℕ) (t : ℝ),0 ≤ t →
      iterate (rankWeights D) (errorKernel D N ψ u) n k t ≤
        ENNReal.ofReal (2*(collisionSum D.A D.a/(δ*Real.exp 1))^n/(n.factorial : ℝ)*t^n*
          Real.exp (((n : ℝ)*δ)*((k+1 : ℕ) : ℝ))) := by
  have hh (j : ℕ) (s : ℝ) (_hs : 0 ≤ s) : errorKernel D N ψ u j s ≤
      ENNReal.ofReal (2*s^0*Real.exp ((0 : ℝ)*((j+1 : ℕ) : ℝ))) := by
    simp only [pow_zero,mul_one,zero_mul,Real.exp_zero,errorKernel]
    exact ENNReal.ofReal_le_ofReal (error_le_two D N ψ hψ u _ s)
  intro n hn k t ht
  have h := iterate_monomial_bound D 0 δ 2 hδ (by norm_num) 0
    (errorKernel D N ψ u) hh n (by simpa only [zero_add] using hn) k t ht
  simpa only [Nat.zero_add,Nat.factorial_zero,Nat.cast_one,zero_add,div_eq_mul_inv,mul_assoc,one_mul] using h

/-- The actual remainder satisfies the exact printed geometric majorant. -/
theorem actual_iterate_bound (D : ClassicalData H) (N : ℕ) (ψ : SymSector ℂ H N)
    (hψ : ‖ψ‖=1) (u : Sphere H) (n k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    iterate (rankWeights D) (errorKernel D N ψ u) n k t ≤
      ENNReal.ofReal (2*Real.exp (D.a*((k+1 : ℕ) : ℝ))*
        (t*collisionSum D.A D.a/D.a)^n) := by
  have ha := D.a_pos
  have hc := collisionSum_nonneg D.A D.a
  by_cases hn : n=0
  · subst n
    simp only [iterate,errorKernel,pow_zero,mul_one]
    apply ENNReal.ofReal_le_ofReal
    apply (error_le_two D N ψ hψ u _ t).trans
    have he : 1 ≤ Real.exp (D.a*((k+1 : ℕ) : ℝ)) :=
      Real.one_le_exp (by positivity)
    linarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hδ : 0 < D.a/(n : ℝ) := div_pos D.a_pos hnpos
  have hδeq : (n : ℝ)*(D.a/(n : ℝ))=D.a := by field_simp
  apply (actual_iterate_scale D N ψ hψ u (D.a/n) hδ n (by rw [hδeq]) k t ht).trans
  apply ENNReal.ofReal_le_ofReal
  have hp := Real.pow_div_factorial_le_exp (n : ℝ) hnpos.le n
  have hex : Real.exp (n : ℝ)=(Real.exp 1)^n := by
    simpa only [mul_one] using Real.exp_nat_mul (1 : ℝ) n
  rw [hex] at hp
  calc
    _ = (2*Real.exp (D.a*((k+1 : ℕ) : ℝ))*(t*collisionSum D.A D.a/(D.a*Real.exp 1))^n)*
        ((n : ℝ)^n/(n.factorial : ℝ)) := by
      rw [hδeq]
      simp only [div_eq_mul_inv,mul_inv_rev,inv_inv,mul_pow]
      ring
    _ ≤ (2*Real.exp (D.a*((k+1 : ℕ) : ℝ))*(t*collisionSum D.A D.a/(D.a*Real.exp 1))^n)*
        (Real.exp 1)^n := mul_le_mul_of_nonneg_left hp (by
          exact mul_nonneg (by positivity) (pow_nonneg
            (div_nonneg (mul_nonneg ht (collisionSum_nonneg _ _)) (by positivity)) n))
    _ = _ := by
      rw [mul_assoc,← mul_pow]
      congr 2
      field_simp

/-- Vanishing of the actual unsubstituted remainder, at a proved radius. -/
theorem actual_remainder_tends_to_zero (D : ClassicalData H) (N : ℕ)
    (ψ : SymSector ℂ H N) (hψ : ‖ψ‖=1) (u : Sphere H) (k : ℕ)
    (t : ℝ) (ht : 0 ≤ t) (hsmall : t*collisionSum D.A D.a < D.a) :
    Tendsto (fun n => iterate (rankWeights D) (errorKernel D N ψ u) n k t) atTop (𝓝 0) := by
  have hr0 : 0 ≤ t*collisionSum D.A D.a/D.a :=
    div_nonneg (mul_nonneg ht (collisionSum_nonneg _ _)) D.a_pos.le
  have hr1 : t*collisionSum D.A D.a/D.a < 1 := (div_lt_one D.a_pos).mpr hsmall
  have hh := ENNReal.tendsto_ofReal
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul
      (2*Real.exp (D.a*((k+1 : ℕ) : ℝ))))
  simp only [mul_zero,ENNReal.ofReal_zero] at hh
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh
    (fun _ => bot_le) (fun n => actual_iterate_bound D N ψ hψ u n k t ht)

/-- In particular the actual remainder vanishes throughout the printed
first interval, including its endpoint. -/
theorem actual_remainder_on_step (D : ClassicalData H) (hCa : collisionSum D.A D.a ≠ 0)
    (N : ℕ) (ψ : SymSector ℂ H N) (hψ : ‖ψ‖=1) (u : Sphere H) (k : ℕ)
    (t : ℝ) (ht : 0 ≤ t) (hstep : t ≤ stepTime D.a (collisionSum D.A D.a)) :
    Tendsto (fun n => iterate (rankWeights D) (errorKernel D N ψ u) n k t) atTop (𝓝 0) := by
  apply actual_remainder_tends_to_zero D N ψ hψ u k t ht
  have hc : 0 < collisionSum D.A D.a :=
    lt_of_le_of_ne (collisionSum_nonneg _ _) hCa.symm
  have h : t*collisionSum D.A D.a ≤ D.a/4 := by
    unfold stepTime at hstep
    have := (le_div_iff₀ (show 0 < 4*collisionSum D.A D.a by positivity)).mp hstep
    linarith
  linarith [D.a_pos]

/-- Remove the actual remainder by its proved limit. Only the substituted
initial/forcing partial sums remain to be estimated. -/
theorem actual_error_le_partial_sup (D : ClassicalData H) (hCa : collisionSum D.A D.a ≠ 0)
    (N : ℕ) (ψ : SymSector ℂ H N) (hψ : ‖ψ‖=1) (u : Sphere H) (k : ℕ)
    (t : ℝ) (ht : 0 ≤ t) (hstep : t ≤ stepTime D.a (collisionSum D.A D.a)) :
    traceNorm (extendedMarginal D.A N (k+1) t ψ-coherentProjector (k+1) (trajectory D u t)) ≤
      ⨆ n : ℕ,partialSum (rankWeights D) (freeKernel D N ψ u) n k t := by
  have hr := actual_remainder_on_step D hCa N ψ hψ u k t ht hstep
  have hl := (tendsto_const_nhds (x := (⨆ m : ℕ,partialSum (rankWeights D) (freeKernel D N ψ u) m k t))).add hr
  have hb : ∀ n : ℕ,
      traceNorm (extendedMarginal D.A N (k+1) t ψ-coherentProjector (k+1) (trajectory D u t)) ≤
        (⨆ m : ℕ,partialSum (rankWeights D) (freeKernel D N ψ u) m k t)+
          iterate (rankWeights D) (errorKernel D N ψ u) n k t := by
    intro n
    exact (actual_finite_depth D N ψ hψ u n k t ht).trans
      (add_le_add (le_iSup (fun m => partialSum (rankWeights D) (freeKernel D N ψ u) m k t) n) le_rfl)
  have hh := ge_of_tendsto hl (Filter.Eventually.of_forall hb)
  simpa only [add_zero] using hh

end QuantumNLS.Prop001RtwentyRemainder

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001RtwentyRemainder" then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      if n.toString == ("QuantumNLS.Prop001.HeldGP" ++ "14Tonelli") then
        throwError "Rejected GP14 wrapper dependency"
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
  Lean.logInfo m!"Prop001RtwentyRemainder audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."






#print axioms QuantumNLS.Prop001RtwentyRemainder.rank_sum_bound
#print axioms QuantumNLS.Prop001RtwentyRemainder.volterra_monomial_bound
#print axioms QuantumNLS.Prop001RtwentyRemainder.actual_iterate_scale
#print axioms QuantumNLS.Prop001RtwentyRemainder.actual_iterate_bound
#print axioms QuantumNLS.Prop001RtwentyRemainder.actual_remainder_tends_to_zero
#print axioms QuantumNLS.Prop001RtwentyRemainder.actual_remainder_on_step
#print axioms QuantumNLS.Prop001RtwentyRemainder.actual_error_le_partial_sup

end

-- Namespace fragment: Prop001RtwentyAssembly
/-! PROP-001 statement and assembly from a proved rate. GP-14 is discharged by actual measurable product integration. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
open Filter Topology MeasureTheory
open scoped BigOperators ENNReal
namespace QuantumNLS.Prop001RtwentyAssembly
open TraceClass TensorCarrier PhysicalTensor Prop001 Prop001RthirteenSeries
  Prop001RtwentyIteration Prop001RseventeenVolterra Prop001RseventeenContinuity
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A common sequence of norm bounds, with exactly the printed assumptions. -/
structure NormBudget where
  a : ℝ
  a_pos : 0 < a
  b : ℕ → ℝ
  nonneg : ∀ n, 0 ≤ b n
  cubic : Summable (fun n => ((n+1 : ℕ) : ℝ)^3*b n)
  exponential : Summable (fun n => ((n+1 : ℕ) : ℝ)*b n*Real.exp (a*n))

def NormBudget.Ca (B : NormBudget) : ℝ :=
  2*∑' n,((n+1 : ℕ) : ℝ)*B.b n*Real.exp (B.a*n)
def NormBudget.C0 (B : NormBudget) : ℝ := 6*∑' n,((n+1 : ℕ) : ℝ)^3*B.b n
def NormBudget.tau (B : NormBudget) : ℝ := stepTime B.a B.Ca
def NormBudget.E (B : NormBudget) : ℝ := forcingConstant B.a B.C0 B.tau
def NormBudget.D (B : NormBudget) : ℝ := rateConstant B.a B.C0 B.tau
def NormBudget.rate (B : NormBudget) (k N : ℕ) (T : ℝ) : ℝ :=
  B.D*Real.exp (B.a*k)*(N : ℝ)^(-rateExponent B.tau T)

def ownBudget (D : ClassicalData H) : NormBudget :=
  ⟨D.a,D.a_pos,fun n => ‖D.A n‖,fun n => ContinuousLinearMap.opNorm_nonneg (D.A n),D.cubic,D.exponential⟩

def Dominates (B : NormBudget) (L : List (ClassicalData H × ℝ)) : Prop :=
  ∀ p ∈ L, ∀ n, ‖p.1.A n‖ ≤ B.b n

/-- Total elapsed length, admitting either sign on every segment. -/
def elapsed (L : List (ClassicalData H × ℝ)) : ℝ := (L.map (fun p => |p.2|)).sum

def scheduleMarginal (N k : ℕ) (hk : k ≤ N) (L : List (ClassicalData H × ℝ))
    (ψ : SymSector ℂ H N) : RankOperator H k :=
  reducedDensityN N k hk (quantumSegments N L ψ : HilbertTensorPower ℂ H N)

def scheduleProjector (L : List (ClassicalData H × ℝ)) (u : Sphere H) (k : ℕ) :
    RankOperator H k := coherentProjector k (classicalSegments L u).val

/-- Nonzero-Ca rate predicate used by the constructive assembly.
The finite-list quantifier covers every finite piecewise constant schedule
and each prefix, with constants from one common norm sequence. -/
def NonzeroCaRate (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : Prop :=
  ∀ (B : NormBudget), B.Ca ≠ 0 → ∀ (L : List (ClassicalData H × ℝ)), Dominates B L →
    ∀ (u : Sphere H) (N k : ℕ) (hk : k ≤ N) (T : ℝ), 0 ≤ T → elapsed L ≤ T →
      traceNorm (scheduleMarginal N k hk L (productVector N u.val)-scheduleProjector L u k) ≤
        ENNReal.ofReal (B.rate k N T)

theorem budget_nonneg (B : NormBudget) : 0 ≤ B.Ca := by
  apply mul_nonneg (by norm_num)
  exact tsum_nonneg (fun n => mul_nonneg (mul_nonneg (by positivity) (B.nonneg n))
    (Real.exp_pos _).le)

/-- A zero common exponential moment forces every dominated kernel to vanish. -/
theorem dominated_kernels_zero (B : NormBudget) (hz : B.Ca=0)
    (D : ClassicalData H) (hD : ∀ n, ‖D.A n‖ ≤ B.b n) : ∀ n,D.A n=0 := by
  have hs : (∑' n,((n+1 : ℕ) : ℝ)*B.b n*Real.exp (B.a*n))=0 := by
    have := hz
    unfold NormBudget.Ca at this
    linarith
  intro n
  have hn := B.exponential.le_tsum n (fun _ _ =>
    mul_nonneg (mul_nonneg (by positivity) (B.nonneg _)) (Real.exp_pos _).le)
  rw [hs] at hn
  have hw : 0 < ((n+1 : ℕ) : ℝ)*Real.exp (B.a*n) := by positivity
  have hb : B.b n=0 := by nlinarith [B.nonneg n]
  apply (norm_eq_zero (a := D.A n)).mp
  exact le_antisymm (by simpa only [hb] using hD n) (ContinuousLinearMap.opNorm_nonneg _)

theorem zero_quantum (D : ClassicalData H) (hz : ∀ n,D.A n=0) (N : ℕ) (t : ℝ) :
    quantumEvolution D.A N t=1 := by
  unfold quantumEvolution LinearTailPhysicalEvolution.evolution
  rw [generator_zero D.A hz]
  simp only [smul_zero,NormedSpace.exp_zero]

theorem zero_flow (D : ClassicalData H) (hz : ∀ n,D.A n=0) (u : Sphere H) (t : ℝ) :
    flow D t u=u := by
  have hc : collisionSum D.A D.a=0 := by simp only [collisionSum,hz,ContinuousLinearMap.opNorm_zero,mul_zero,zero_mul,tsum_zero]
  apply Subtype.ext
  exact congrFun (zero_collision_trajectory D hc u) t

/-- The entire zero-Ca schedule branch is proved, including arbitrary signs. -/
theorem zero_schedule (B : NormBudget) (hz : B.Ca=0)
    (L : List (ClassicalData H × ℝ)) (hL : Dominates B L) (u : Sphere H) :
    classicalSegments L u=u ∧ ∀ N,quantumSegments N L=1 := by
  induction L generalizing u with
  | nil => exact ⟨rfl,fun _ => rfl⟩
  | cons p L ih =>
    have hp : ∀ n,p.1.A n=0 := dominated_kernels_zero B hz p.1
      (hL p (List.mem_cons_self ..))
    have ht : Dominates B L := fun q hq => hL q (List.mem_cons_of_mem _ hq)
    refine ⟨?_,?_⟩
    · rw [classicalSegments,(ih ht (flow p.1 p.2 u)).1,zero_flow p.1 hp]
    · intro N
      rw [quantumSegments,(ih ht u).2 N,zero_quantum p.1 hp]
      ext x
      rfl

theorem schedule_zero_error (B : NormBudget) (hz : B.Ca=0)
    (L : List (ClassicalData H × ℝ)) (hL : Dominates B L) (u : Sphere H)
    (N k : ℕ) (hk : k ≤ N) :
    traceNorm (scheduleMarginal N k hk L (productVector N u.val)-scheduleProjector L u k)=0 := by
  obtain ⟨hc,hq⟩ := zero_schedule B hz L hL u
  simp only [scheduleMarginal,scheduleProjector,hq,hc,one_apply_eq_self]
  change traceNorm (reducedDensityN N k hk (htpow N u.val)-coherentProjector k u.val)=0
  rw [reducedDensityN_htpow,u.property]
  simp [coherentProjector,Fidelity.traceNorm_zero]

theorem rate_nonneg (B : NormBudget) (k N : ℕ) (T : ℝ) : 0 ≤ B.rate k N T := by
  unfold NormBudget.rate
  exact mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 1).trans
    (rateConstant_ge_one _ _ _)) (Real.exp_pos _).le) (Real.rpow_nonneg (by positivity) _)

/-- Full schedule rate, with the zero branch discharged independently. -/
theorem schedule_rate (rate : NonzeroCaRate H) (B : NormBudget)
    (L : List (ClassicalData H × ℝ)) (hL : Dominates B L) (u : Sphere H)
    (N k : ℕ) (hk : k ≤ N) (T : ℝ) (hT : 0 ≤ T) (ht : elapsed L ≤ T) :
    traceNorm (scheduleMarginal N k hk L (productVector N u.val)-scheduleProjector L u k) ≤
      ENNReal.ofReal (B.rate k N T) := by
  by_cases hz : B.Ca=0
  · rw [schedule_zero_error B hz L hL u N k hk]
    exact bot_le
  · exact rate B hz L hL u N k hk T hT ht

/-- Packet extension is proved from actual unitary schedule evolution. -/
theorem schedule_packet (rate : NonzeroCaRate H) (B : NormBudget)
    (L : List (ClassicalData H × ℝ)) (hL : Dominates B L) (u : Sphere H)
    (N k : ℕ) (hk : k ≤ N) (T : ℝ) (hT : 0 ≤ T) (ht : elapsed L ≤ T)
    (ψ : SymSector ℂ H N) (hψ : ‖ψ‖=1) :
    traceNorm (scheduleMarginal N k hk L ψ-scheduleProjector L u k) ≤
      ENNReal.ofReal (B.rate k N T+2*‖ψ-productVector N u.val‖) := by
  have hp : ‖productVector N u.val‖=1 := by rw [productVector_norm,u.property,one_pow]
  have h := traceNorm_add_le
    (scheduleMarginal N k hk L ψ-scheduleMarginal N k hk L (productVector N u.val))
    (scheduleMarginal N k hk L (productVector N u.val)-scheduleProjector L u k)
  rw [sub_add_sub_cancel] at h
  apply h.trans
  rw [ENNReal.ofReal_add (rate_nonneg B k N T) (by positivity),add_comm]
  exact add_le_add (schedule_rate rate B L hL u N k hk T hT ht)
    (quantumSegments_packet_stability N k hk L ψ (productVector N u.val) hψ hp)

theorem autonomous_rate (rate : NonzeroCaRate H) (D : ClassicalData H) (u : Sphere H)
    (N k : ℕ) (hk : k ≤ N) (T : ℝ) (hT : 0 ≤ T) (t : ℝ) (ht : |t| ≤ T) :
    traceNorm (marginal D.A N k hk t (productVector N u.val)-
      coherentProjector k (trajectory D u t)) ≤ ENNReal.ofReal ((ownBudget D).rate k N T) := by
  have hL : Dominates (ownBudget D) [(D,t)] := by
    intro p hp n
    have he : p=(D,t) := by simpa using hp
    subst p
    exact (le_refl ‖D.A n‖)
  simpa only [scheduleMarginal,scheduleProjector,quantumSegments,classicalSegments,
    ContinuousLinearMap.comp_apply,one_apply_eq_self,flow,marginal,
    elapsed,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
      schedule_rate rate (ownBudget D) [(D,t)] hL u N k hk T hT
        (by simpa only [elapsed,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using ht)

theorem autonomous_packet (rate : NonzeroCaRate H) (D : ClassicalData H) (u : Sphere H)
    (N k : ℕ) (hk : k ≤ N) (T : ℝ) (hT : 0 ≤ T) (t : ℝ) (ht : |t| ≤ T)
    (ψ : SymSector ℂ H N) (hψ : ‖ψ‖=1) :
    traceNorm (marginal D.A N k hk t ψ-coherentProjector k (trajectory D u t)) ≤
      ENNReal.ofReal ((ownBudget D).rate k N T+2*‖ψ-productVector N u.val‖) := by
  apply (perturbed_comparison D.A D.selfAdjoint N k hk t ψ hψ u.val u.property _).trans
  rw [ENNReal.ofReal_add (rate_nonneg _ _ _ _) (by positivity)]
  exact add_le_add (autonomous_rate rate D u N k hk T hT t ht) le_rfl

/-- The complete printed PROP-001 statement, including the actual Tonelli exchange. -/
structure BoundedPropagation (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : Prop where
  classical : ∀ (D : ClassicalData H) (u : Sphere H), ∃! v : ℝ → H,
    v 0=u.val ∧ ContDiff ℝ 1 v ∧ ∀ t, ‖v t‖=1 ∧
      HasDerivAt v (Ext025A8.sourceHartreeField D.A (v t)) t
  zero : ∀ (D : ClassicalData H), collisionSum D.A D.a=0 →
    ∀ (u : Sphere H) (N k : ℕ) (hk : k ≤ N) (t : ℝ),
      traceNorm (marginal D.A N k hk t (productVector N u.val)-
        coherentProjector k (trajectory D u t))=0
  autonomous : ∀ (D : ClassicalData H) (u : Sphere H) (N k : ℕ) (hk : k ≤ N)
    (T : ℝ), 0 ≤ T → ∀ t : ℝ, |t| ≤ T →
      traceNorm (marginal D.A N k hk t (productVector N u.val)-
        coherentProjector k (trajectory D u t)) ≤ ENNReal.ofReal ((ownBudget D).rate k N T)
  packet : ∀ (D : ClassicalData H) (u : Sphere H) (N k : ℕ) (hk : k ≤ N)
    (T : ℝ), 0 ≤ T → ∀ t : ℝ, |t| ≤ T →
    ∀ (ψ : SymSector ℂ H N), ‖ψ‖=1 →
      traceNorm (marginal D.A N k hk t ψ-coherentProjector k (trajectory D u t)) ≤
        ENNReal.ofReal ((ownBudget D).rate k N T+2*‖ψ-productVector N u.val‖)
  piecewiseZero : ∀ (B : NormBudget), B.Ca=0 →
    ∀ (L : List (ClassicalData H × ℝ)), Dominates B L →
    ∀ (u : Sphere H) (N k : ℕ) (hk : k ≤ N),
      traceNorm (scheduleMarginal N k hk L (productVector N u.val)-scheduleProjector L u k)=0
  piecewise : ∀ (B : NormBudget) (L : List (ClassicalData H × ℝ)), Dominates B L →
    ∀ (u : Sphere H) (N k : ℕ) (hk : k ≤ N) (T : ℝ), 0 ≤ T → elapsed L ≤ T →
    ∀ (ψ : SymSector ℂ H N), ‖ψ‖=1 →
      traceNorm (scheduleMarginal N k hk L ψ-scheduleProjector L u k) ≤
        ENNReal.ofReal (B.rate k N T+2*‖ψ-productVector N u.val‖)
  exchange : ∀ (D : ClassicalData H) (N : ℕ) (ψ : SymSector ℂ H N), ‖ψ‖=1 →
    ∀ (u : Sphere H) (k : ℕ) (a b : ℝ),
      (∫⁻ t in Set.Ioc a b,ENNReal.ofReal (collisionMajorant D N ψ u k t)) =
        ∑' n,∫⁻ t in Set.Ioc a b,
          ENNReal.ofReal ((2*((n+1 : ℕ) : ℝ)*((k+1 : ℕ) : ℝ)*‖D.A n‖)*
            error D N ψ u ((k+1)+n) t)

/-- Assemble the printed clauses from a rate proof and the proved actual Tonelli exchange. -/
theorem assemble_from_rate (rate : NonzeroCaRate H) : BoundedPropagation H := by
  refine ⟨?_,?_,autonomous_rate rate,autonomous_packet rate,schedule_zero_error,
    schedule_packet rate,actual_rank_time_exchange⟩
  · intro D u
    refine ⟨trajectory D u,⟨(trajectory_spec D u).1,(trajectory_spec D u).2.1,
      (trajectory_spec D u).2.2.1⟩,?_⟩
    intro v hv
    exact (trajectory_spec D u).2.2.2 v hv.1 hv.2.2
  · intro D hz u N k hk t
    exact zero_collision_full D hz u N k hk t

theorem propagation_from_rate
    (rate : NonzeroCaRate H) : BoundedPropagation H :=
  assemble_from_rate rate

end QuantumNLS.Prop001RtwentyAssembly

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001RtwentyAssembly" then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      if n.toString == ("QuantumNLS.Prop001.HeldGP" ++ "14Tonelli") then
        throwError "Rejected GP14 wrapper dependency"
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
  Lean.logInfo m!"Prop001RtwentyAssembly audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."






#print axioms QuantumNLS.Prop001RtwentyAssembly.dominated_kernels_zero
#print axioms QuantumNLS.Prop001RtwentyAssembly.zero_schedule
#print axioms QuantumNLS.Prop001RtwentyAssembly.schedule_zero_error
#print axioms QuantumNLS.Prop001RtwentyAssembly.schedule_rate
#print axioms QuantumNLS.Prop001RtwentyAssembly.schedule_packet
#print axioms QuantumNLS.Prop001RtwentyAssembly.autonomous_rate
#print axioms QuantumNLS.Prop001RtwentyAssembly.autonomous_packet
#print axioms QuantumNLS.Prop001RtwentyAssembly.assemble_from_rate
#print axioms QuantumNLS.Prop001RtwentyAssembly.propagation_from_rate

end

-- Namespace fragment: Prop001RtwentyExpansion
/-! The actual scalar Duhamel expansion after removing the proved remainder.
Its substituted initial/forcing series remains explicit, without a rate
assumption. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
open Filter Topology MeasureTheory
open scoped BigOperators ENNReal
namespace QuantumNLS.Prop001RtwentyExpansion
open TraceClass TensorCarrier Prop001 Prop001RthirteenSeries
  Prop001RtwentyIteration Prop001RtwentyRemainder Prop001RtwentyAssembly
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem volterra_finset_sum (b : ℕ → ℝ≥0∞) (s : Finset ℕ)
    (f : ℕ → ℕ → ℝ → ℝ≥0∞) (hf : ∀ j k,Measurable (f j k)) (k : ℕ) (t : ℝ) :
    volterra b (fun k t => ∑ j ∈ s,f j k t) k t = ∑ j ∈ s,volterra b (f j) k t := by
  induction s using Finset.induction with
  | empty => simp [volterra]
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    rw [volterra_add b _ _ (hf j),ih]

/-- The recursively substituted data are exactly the finite sum of the
literal Volterra iterates. Every additivity premise is proved measurable. -/
theorem partialSum_eq_sum (b : ℕ → ℝ≥0∞) (g : ℕ → ℝ → ℝ≥0∞)
    (hg : ∀ k,Measurable (g k)) (n k : ℕ) (t : ℝ) :
    partialSum b g n k t=∑ j ∈ Finset.range n,iterate b g j k t := by
  induction n generalizing k t with
  | zero => simp [partialSum]
  | succ n ih =>
    change g k t+volterra b (partialSum b g n) k t=_
    have he : partialSum b g n=(fun j s => ∑ i ∈ Finset.range n,iterate b g i j s) := by
      funext j s
      exact ih j s
    rw [he]
    rw [volterra_finset_sum b _ _ (fun j => iterate_measurable b g hg j)]
    rw [Finset.sum_range_succ']
    simp only [iterate]
    exact add_comm _ _

/-- Full actual positive-rank scalar expansion on the printed step.
The substituted data series is bounded in the downstream constructive proof. -/
theorem actual_error_le_series (D : ClassicalData H) (hCa : collisionSum D.A D.a ≠ 0)
    (N : ℕ) (ψ : SymSector ℂ H N) (hψ : ‖ψ‖=1) (u : Sphere H) (k : ℕ)
    (t : ℝ) (ht : 0 ≤ t) (hstep : t ≤ stepTime D.a (collisionSum D.A D.a)) :
    traceNorm (extendedMarginal D.A N (k+1) t ψ-coherentProjector (k+1) (trajectory D u t)) ≤
      ∑' n,iterate (rankWeights D) (freeKernel D N ψ u) n k t := by
  apply (actual_error_le_partial_sup D hCa N ψ hψ u k t ht hstep).trans
  apply iSup_le
  intro n
  rw [partialSum_eq_sum (rankWeights D) (freeKernel D N ψ u)
    (fun j => ENNReal.continuous_ofReal.measurable.comp
      (continuous_const.add (continuous_id.mul continuous_const)).measurable)]
  exact ENNReal.sum_le_tsum _


end QuantumNLS.Prop001RtwentyExpansion

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001RtwentyExpansion" then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      if n.toString == ("QuantumNLS.Prop001.HeldGP" ++ "14Tonelli") then
        throwError "Rejected GP14 wrapper dependency"
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
  Lean.logInfo m!"Prop001RtwentyExpansion audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."






#print axioms QuantumNLS.Prop001RtwentyExpansion.volterra_finset_sum
#print axioms QuantumNLS.Prop001RtwentyExpansion.partialSum_eq_sum
#print axioms QuantumNLS.Prop001RtwentyExpansion.actual_error_le_series

end

-- Namespace fragment: Prop001RtwentyData
/-! Exact initial/forcing summand estimates for the actual substitutions. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
open Filter Topology MeasureTheory
open scoped BigOperators ENNReal
namespace QuantumNLS.Prop001RtwentyData
open TraceClass TensorCarrier Prop001 Prop001RthirteenSeries Prop001RseventeenContinuity
  Prop001RtwentyIteration Prop001RtwentyRemainder Prop001RtwentyExpansion
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def polynomialKernel (B : ℝ) (p k : ℕ) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (B*((k+1 : ℕ) : ℝ)^(p+1)*t^p)

theorem polynomial_measurable (B : ℝ) (p k : ℕ) : Measurable (polynomialKernel B p k) :=
  ENNReal.continuous_ofReal.measurable.comp
    (continuous_const.mul (continuous_id.pow p)).measurable

/-- Exact scalar optimization of the analytic scale; this retains the
source's n+1 and n+2 factors when p=0 and p=1. -/
theorem optimize_scale (a C B t X : ℝ) (ha : 0 < a) (hC : 0 ≤ C)
    (hB : 0 ≤ B) (ht : 0 ≤ t) (hX : 0 ≤ X) (p n : ℕ) :
    (B/((a/((p+n+1 : ℕ) : ℝ))*Real.exp 1)^(p+1))*
      (C/((a/((p+n+1 : ℕ) : ℝ))*Real.exp 1))^n*
      ((p.factorial : ℝ)/((p+n).factorial : ℝ))*t^(p+n)*X ≤
    B*X*(p.factorial : ℝ)*((p+n+1 : ℕ) : ℝ)/a^(p+1)*t^p*(t*C/a)^n := by
  let m : ℝ := ((p+n+1 : ℕ) : ℝ)
  have hm : 0 < m := by dsimp [m];positivity
  have hp := initial_factorial_majorant (a := (1 : ℝ)) (x := m) (by norm_num) hm.le (p+n)
  simp only [one_mul,one_pow,div_one] at hp
  have hex : Real.exp m=(Real.exp 1)^(p+n+1) := by
    simpa only [m,mul_one] using Real.exp_nat_mul (1 : ℝ) (p+n+1)
  rw [hex] at hp
  have hr : m^(p+n+1)/((Real.exp 1)^(p+n+1)*((p+n).factorial : ℝ)) ≤ m := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hh := (div_le_iff₀ (show (0 : ℝ) < (p+n).factorial by positivity)).mp hp
    convert hh using 1
    dsimp [m]
    ring
  let K := B*X*(p.factorial : ℝ)/a^(p+1)*t^p*(t*C/a)^n
  have hK : 0 ≤ K := by dsimp [K];positivity
  have hh := mul_le_mul_of_nonneg_left hr hK
  convert hh using 1 <;> dsimp [K,m] <;>
    simp only [div_eq_mul_inv,mul_inv_rev,inv_pow,inv_inv,mul_pow,pow_add,pow_succ] <;> ring

/-- The actual iterate of polynomial rank/time data has the printed scalar
summand bound. No hierarchy or scalar rate is an input. -/
theorem iterate_polynomial_bound (D : ClassicalData H) (B : ℝ) (hB : 0 ≤ B)
    (p n k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    iterate (rankWeights D) (polynomialKernel B p) n k t ≤
      ENNReal.ofReal (B*Real.exp (D.a*((k+1 : ℕ) : ℝ))*(p.factorial : ℝ)*
        ((p+n+1 : ℕ) : ℝ)/D.a^(p+1)*t^p*(t*collisionSum D.A D.a/D.a)^n) := by
  let δ := D.a/((p+n+1 : ℕ) : ℝ)
  have ha := D.a_pos
  have hδ : 0 < δ := by dsimp [δ];positivity
  let q := ((p+1 : ℕ) : ℝ)*δ
  have hq : q+(n : ℝ)*δ=D.a := by
    dsimp [q,δ]
    push_cast
    field_simp
    ring
  have hf (j : ℕ) (s : ℝ) (hs : 0 ≤ s) : polynomialKernel B p j s ≤
      ENNReal.ofReal ((B/(δ*Real.exp 1)^(p+1))*s^p*Real.exp (q*((j+1 : ℕ) : ℝ))) := by
    have hx := exp_rank_loss 0 δ ((j+1 : ℕ) : ℝ) hδ
    simp only [zero_mul,Real.exp_zero,mul_one,zero_add] at hx
    have hp := pow_le_pow_left₀ (show (0 : ℝ) ≤ (j+1 : ℕ) by positivity) hx (p+1)
    rw [div_pow,← Real.exp_nat_mul] at hp
    have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ B*s^p by positivity)
    apply ENNReal.ofReal_le_ofReal
    have he : ((p+1 : ℕ) : ℝ)*(δ*((j+1 : ℕ) : ℝ))=q*((j+1 : ℕ) : ℝ) := by dsimp [q];ring
    rw [he] at hh
    convert hh using 1 <;> ring
  have hh := iterate_monomial_bound D q δ (B/(δ*Real.exp 1)^(p+1)) hδ
    (by positivity) p (polynomialKernel B p) hf n (by rw [hq]) k t ht
  rw [hq] at hh
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  exact optimize_scale D.a (collisionSum D.A D.a) B t
    (Real.exp (D.a*((k+1 : ℕ) : ℝ))) ha (collisionSum_nonneg _ _) hB ht (by positivity) p n

theorem iterate_mono_nonneg (b : ℕ → ℝ≥0∞) (f g : ℕ → ℝ → ℝ≥0∞)
    (h : ∀ k t,0 ≤ t → f k t ≤ g k t) :
    ∀ n k t,0 ≤ t → iterate b f n k t ≤ iterate b g n k t := by
  intro n
  induction n with
  | zero => exact h
  | succ n ih => intro k t _;exact volterra_mono_nonneg b ih k t

theorem iterate_add (b : ℕ → ℝ≥0∞) (f g : ℕ → ℝ → ℝ≥0∞)
    (hf : ∀ k,Measurable (f k)) (n k : ℕ) (t : ℝ) :
    iterate b (fun j s => f j s+g j s) n k t=iterate b f n k t+iterate b g n k t := by
  induction n generalizing k t with
  | zero => rfl
  | succ n ih =>
    change volterra b (iterate b (fun j s => f j s+g j s) n) k t=_
    have he : iterate b (fun j s => f j s+g j s) n=
        (fun j s => iterate b f n j s+iterate b g n j s) := by
      funext j s
      exact ih j s
    rw [he]
    exact volterra_add b _ _ (iterate_measurable b f hf n) k t

theorem product_free_bound (D : ClassicalData H) (N : ℕ) (hN : 0 < N) (u : Sphere H)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    freeKernel D N (productVector N u.val) u k t ≤
      polynomialKernel (1/(N : ℝ)) 0 k t+polynomialKernel (errorSum D.A/N) 1 k t := by
  have hi := actual_product_initial D N hN u k
  have hzero : error D N (productVector N u.val) u (k+1) 0 ≤ ((k+1 : ℕ) : ℝ)/N := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hi
    simpa only [errorKernel,ENNReal.toReal_ofReal (error_nonneg D N _ u _ 0),
      ENNReal.toReal_ofReal (show (0 : ℝ) ≤ ((k+1 : ℕ) : ℝ)/N by positivity)] using hh
  have hC := errorSum_nonneg D.A
  unfold freeKernel polynomialKernel
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  simp only [Nat.zero_add,Nat.reduceAdd,pow_zero,pow_one,mul_one]
  convert add_le_add_right hzero (t*(errorSum D.A*((k+1 : ℕ) : ℝ)^2/N)) using 1 <;> ring

def initialTerm (D : ClassicalData H) (N k : ℕ) (t : ℝ) (n : ℕ) : ℝ :=
  Real.exp (D.a*((k+1 : ℕ) : ℝ))/(D.a*N)*
    (((n+1 : ℕ) : ℝ)*(t*collisionSum D.A D.a/D.a)^n)
def forcingTerm (D : ClassicalData H) (N k : ℕ) (t : ℝ) (n : ℕ) : ℝ :=
  errorSum D.A*t*Real.exp (D.a*((k+1 : ℕ) : ℝ))/(D.a^2*N)*
    (((n+2 : ℕ) : ℝ)*(t*collisionSum D.A D.a/D.a)^n)

/-- The actual free-data iterate is bounded by the two literal printed
summands, rather than an unrelated scalar series. -/
theorem actual_free_iterate_bound (D : ClassicalData H) (N : ℕ) (hN : 0 < N)
    (u : Sphere H) (n k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    iterate (rankWeights D) (freeKernel D N (productVector N u.val) u) n k t ≤
      ENNReal.ofReal (initialTerm D N k t n)+ENNReal.ofReal (forcingTerm D N k t n) := by
  have h := iterate_mono_nonneg (rankWeights D) _ _ (product_free_bound D N hN u) n k t ht
  rw [iterate_add _ _ _ (polynomial_measurable (1/(N : ℝ)) 0)] at h
  apply h.trans
  apply add_le_add
  · apply (iterate_polynomial_bound D (1/(N : ℝ)) (by positivity) 0 n k t ht).trans
    apply le_of_eq
    apply congrArg ENNReal.ofReal
    simp only [initialTerm,Nat.factorial_zero,Nat.cast_one,Nat.zero_add,pow_one,pow_zero,mul_one]
    ring
  · apply (iterate_polynomial_bound D (errorSum D.A/N) (div_nonneg (errorSum_nonneg _) (by positivity)) 1 n k t ht).trans
    apply le_of_eq
    apply congrArg ENNReal.ofReal
    simp only [forcingTerm,Nat.factorial_one,Nat.cast_one,pow_one,mul_one]
    have he : 1+n+1=n+2 := by omega
    rw [he]
    ring

/-- Actual exponent-one product-state estimate on the first printed step,
with exactly the printed first-interval scalar coefficient. -/
theorem actual_first_interval_bound (D : ClassicalData H) (hCa : collisionSum D.A D.a ≠ 0)
    (N : ℕ) (hN : 0 < N) (u : Sphere H) (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (hstep : t ≤ stepTime D.a (collisionSum D.A D.a)) :
    traceNorm (extendedMarginal D.A N (k+1) t (productVector N u.val)-
      coherentProjector (k+1) (trajectory D u t)) ≤
      ENNReal.ofReal ((4/D.a+8*errorSum D.A*t/D.a^2)*
        Real.exp (D.a*((k+1 : ℕ) : ℝ))/N) := by
  let rho := t*collisionSum D.A D.a/D.a
  have ha := D.a_pos
  have hC := errorSum_nonneg D.A
  have hc : 0 < collisionSum D.A D.a := lt_of_le_of_ne (collisionSum_nonneg _ _) hCa.symm
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hr0 : 0 ≤ rho := by dsimp [rho];positivity
  have hr : rho ≤ 1/4 := by
    unfold stepTime at hstep
    have hh := (le_div_iff₀ (show 0 < 4*collisionSum D.A D.a by positivity)).mp hstep
    dsimp [rho]
    apply (div_le_iff₀ ha).mpr
    nlinarith
  have hr1 : rho < 1 := by linarith
  have hI : HasSum (initialTerm D N k t)
      (Real.exp (D.a*((k+1 : ℕ) : ℝ))/(D.a*N*(1-rho)^2)) :=
    initial_series_value (a := D.a) (N := (N : ℝ)) (k+1) hr0 hr1
  have hF : HasSum (forcingTerm D N k t)
      (errorSum D.A*t*Real.exp (D.a*((k+1 : ℕ) : ℝ))*(2-rho)/(D.a^2*N*(1-rho)^2)) :=
    forcing_series_value (a := D.a) (C0 := errorSum D.A) (t := t) (N := (N : ℝ)) (k+1) hr0 hr1
  have hIP (n : ℕ) : 0 ≤ initialTerm D N k t n := by dsimp [initialTerm];positivity
  have hFP (n : ℕ) : 0 ≤ forcingTerm D N k t n := by dsimp [forcingTerm];positivity
  have hIv : 0 ≤ ∑' n,initialTerm D N k t n := tsum_nonneg hIP
  have hFv : 0 ≤ ∑' n,forcingTerm D N k t n := tsum_nonneg hFP
  rw [hI.tsum_eq] at hIv
  rw [hF.tsum_eq] at hFv
  have hψ : ‖productVector N u.val‖=1 := by rw [productVector_norm,u.property,one_pow]
  apply (actual_error_le_series D hCa N _ hψ u k t ht hstep).trans
  apply (ENNReal.tsum_le_tsum (fun n => actual_free_iterate_bound D N hN u n k t ht)).trans
  rw [ENNReal.tsum_add,← ENNReal.ofReal_tsum_of_nonneg hIP hI.summable,
    ← ENNReal.ofReal_tsum_of_nonneg hFP hF.summable,hI.tsum_eq,hF.tsum_eq,
    ← ENNReal.ofReal_add hIv hFv]
  apply ENNReal.ofReal_le_ofReal
  have hh := mul_le_mul_of_nonneg_left
    (first_interval_scalar_bound ha hC ht hNp hr0 hr)
    (Real.exp_pos (D.a*((k+1 : ℕ) : ℝ))).le
  convert hh using 1 <;> ring

/-- The printed D controls the actual exponent-one estimate on the entire
first interval. Restart to later intervals is not a premise or conclusion. -/
theorem actual_first_interval_printed (D : ClassicalData H) (hCa : collisionSum D.A D.a ≠ 0)
    (N : ℕ) (hN : 0 < N) (u : Sphere H) (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (hstep : t ≤ stepTime D.a (collisionSum D.A D.a)) :
    traceNorm (extendedMarginal D.A N (k+1) t (productVector N u.val)-
      coherentProjector (k+1) (trajectory D u t)) ≤
      ENNReal.ofReal (rateConstant D.a (errorSum D.A) (stepTime D.a (collisionSum D.A D.a))*
        Real.exp (D.a*((k+1 : ℕ) : ℝ))/N) := by
  apply (actual_first_interval_bound D hCa N hN u k t ht hstep).trans
  apply ENNReal.ofReal_le_ofReal
  have hC := errorSum_nonneg D.A
  have hh := add_le_add (le_refl (4/D.a)) (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hstep (show 0 ≤ 8*errorSum D.A by positivity)) (sq_nonneg D.a))
  have hd : 4/D.a+8*errorSum D.A*stepTime D.a (collisionSum D.A D.a)/D.a^2 ≤
      rateConstant D.a (errorSum D.A) (stepTime D.a (collisionSum D.A D.a)) :=
    (le_max_left _ _).trans (le_max_right _ _)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hh.trans hd) (by positivity)) (by positivity)


end QuantumNLS.Prop001RtwentyData

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001RtwentyData" then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      if n.toString == ("QuantumNLS.Prop001.HeldGP" ++ "14Tonelli") then
        throwError "Rejected GP14 wrapper dependency"
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
  Lean.logInfo m!"Prop001RtwentyData audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."






#print axioms QuantumNLS.Prop001RtwentyData.optimize_scale
#print axioms QuantumNLS.Prop001RtwentyData.iterate_polynomial_bound
#print axioms QuantumNLS.Prop001RtwentyData.product_free_bound
#print axioms QuantumNLS.Prop001RtwentyData.actual_free_iterate_bound
#print axioms QuantumNLS.Prop001RtwentyData.actual_first_interval_bound

#print axioms QuantumNLS.Prop001RtwentyData.actual_first_interval_printed

end

-- Namespace fragment: Prop001RtwentyComparison
/-! Comparison with an explicit supersolution for the actual scalar errors. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
open Filter Topology MeasureTheory
open scoped BigOperators ENNReal
namespace QuantumNLS.Prop001RtwentyComparison
open TraceClass TensorCarrier Prop001 Prop001RthirteenSeries Prop001RseventeenContinuity
  Prop001RtwentyIteration Prop001RtwentyRemainder Prop001RtwentyExpansion
  Prop001RtwentyData
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Local comparison needs no estimates beyond the interval being used. -/
theorem partial_le_supersolution (b : ℕ → ℝ≥0∞) (g F : ℕ → ℝ → ℝ≥0∞)
    (T : ℝ) (hF : ∀ k t,0 ≤ t → t ≤ T → g k t+volterra b F k t ≤ F k t) :
    ∀ n k t,0 ≤ t → t ≤ T → partialSum b g n k t ≤ F k t := by
  intro n
  induction n with
  | zero => intro k t _ _;exact bot_le
  | succ n ih =>
    intro k t ht htT
    change g k t+volterra b (partialSum b g n) k t ≤ F k t
    apply (add_le_add le_rfl (show volterra b (partialSum b g n) k t ≤ volterra b F k t from ?_)).trans (hF k t ht htT)
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    apply ENNReal.tsum_le_tsum
    intro j
    exact mul_le_mul_of_nonneg_left (ih (k+j) s hs.1.le (hs.2.trans htT)) (by positivity)

/-- Comparison is discharged by the proved actual remainder limit, including
when the actual interaction vanishes. No rate or hierarchy is assumed. -/
theorem actual_comparison (D : ClassicalData H) (N : ℕ) (ψ : SymSector ℂ H N)
    (hψ : ‖ψ‖=1) (u : Sphere H) (F : ℕ → ℝ → ℝ≥0∞) (T : ℝ)
    (hF : ∀ k t,0 ≤ t → t ≤ T →
      freeKernel D N ψ u k t+volterra (rankWeights D) F k t ≤ F k t)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T)
    (hsmall : t*collisionSum D.A D.a < D.a) :
    traceNorm (extendedMarginal D.A N (k+1) t ψ-coherentProjector (k+1) (trajectory D u t)) ≤ F k t := by
  have hr := actual_remainder_tends_to_zero D N ψ hψ u k t ht hsmall
  have hl := (tendsto_const_nhds (x := F k t)).add hr
  have hb : ∀ n : ℕ,
      traceNorm (extendedMarginal D.A N (k+1) t ψ-coherentProjector (k+1) (trajectory D u t)) ≤
        F k t+iterate (rankWeights D) (errorKernel D N ψ u) n k t := by
    intro n
    exact (actual_finite_depth D N ψ hψ u n k t ht).trans
      (add_le_add (partial_le_supersolution (rankWeights D) _ F T hF n k t ht htT) le_rfl)
  simpa only [add_zero] using ge_of_tendsto hl (Filter.Eventually.of_forall hb)

/-- Printed forcing budget in the half analytic scale. -/
theorem rank_square_half (a x : ℝ) (ha : 0 < a) (hx : 0 ≤ x) :
    x^2 ≤ 4/a^2*Real.exp (a/2*x) := by
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hh := exp_rank_loss 0 (a/4) x (by positivity)
  simp only [zero_mul,Real.exp_zero,mul_one,zero_add] at hh
  have hp := pow_le_pow_left₀ hx hh 2
  rw [div_pow,← Real.exp_nat_mul] at hp
  norm_num only [Nat.cast_ofNat] at hp
  have hex : 2*(a/4*x)=a/2*x := by ring
  rw [hex] at hp
  have hden : a^2/4 ≤ (a/4*Real.exp 1)^2 := by nlinarith [sq_nonneg (Real.exp 1-2)]
  have hbound : Real.exp (a/2*x)/(a/4*Real.exp 1)^2 ≤
      Real.exp (a/2*x)/(a^2/4) :=
    div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) hden
  apply hp.trans (hbound.trans (le_of_eq ?_))
  ring

def barrier (M L q C : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  (M+L*t)*Real.exp ((q+C*t)*((k+1 : ℕ) : ℝ))

def barrierDerivative (M L q C : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  (L+C*((k+1 : ℕ) : ℝ)*(M+L*t))*Real.exp ((q+C*t)*((k+1 : ℕ) : ℝ))

theorem barrier_hasDerivAt (M L q C : ℝ) (k : ℕ) (t : ℝ) :
    HasDerivAt (barrier M L q C k) (barrierDerivative M L q C k t) t := by
  have hm := (hasDerivAt_const t M).add ((hasDerivAt_id t).const_mul L)
  have hq := ((hasDerivAt_const t q).add ((hasDerivAt_id t).const_mul C)).mul_const (((k+1 : ℕ) : ℝ))
  convert! hm.mul hq.exp using 1
  dsimp [barrier,barrierDerivative]
  ring

theorem barrierDerivative_continuous (M L q C : ℝ) (k : ℕ) :
    Continuous (barrierDerivative M L q C k) := by
  unfold barrierDerivative
  fun_prop

/-- A single actual segment preserves a moving analytic envelope. This
form retains the elapsed-time budget across switches of interaction. -/
theorem barrier_supersolution (D : ClassicalData H) (N : ℕ) (hN : 0 < N)
    (ψ : SymSector ℂ H N) (u : Sphere H) (M L q C T : ℝ)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hC : collisionSum D.A D.a ≤ C)
    (hq : D.a/2 ≤ q) (_hT : 0 ≤ T) (hscale : q+C*T ≤ D.a)
    (hforce : 4*errorSum D.A/D.a^2/N ≤ L)
    (hi : ∀ j,error D N ψ u (j+1) 0 ≤ barrier M L q C j 0) :
    ∀ k t,0 ≤ t → t ≤ T →
      freeKernel D N ψ u k t+
        volterra (rankWeights D) (fun j s => ENNReal.ofReal (barrier M L q C j s)) k t ≤
      ENNReal.ofReal (barrier M L q C k t) := by
  have ha := D.a_pos
  have hc : 0 ≤ C := (collisionSum_nonneg _ _).trans hC
  have hC0 := errorSum_nonneg D.A
  intro k t ht htT
  let j : ℝ := ((k+1 : ℕ) : ℝ)
  let f := fun s : ℝ => errorSum D.A*j^2/N+
    (M+L*s)*(j*Real.exp ((q+C*s)*j)*collisionSum D.A D.a)
  have hp (s : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
      f s ≤ barrierDerivative M L q C k s := by
    have hq' : D.a/2 ≤ q+C*s := by nlinarith
    have hj : 0 ≤ j := by dsimp [j];positivity
    have hsq := rank_square_half D.a j ha hj
    have hExp : Real.exp (D.a/2*j) ≤ Real.exp ((q+C*s)*j) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hq' hj)
    have hforcing := mul_le_mul_of_nonneg_left (hsq.trans
      (mul_le_mul_of_nonneg_left hExp (by positivity : 0 ≤ 4/D.a^2)))
      (show 0 ≤ errorSum D.A/(N : ℝ) by positivity)
    have hforcing' : errorSum D.A*j^2/N ≤ L*Real.exp ((q+C*s)*j) := by
      have hh := mul_le_mul_of_nonneg_right hforce (Real.exp_pos ((q+C*s)*j)).le
      have hforcingEq : errorSum D.A*j^2/N ≤
          4*errorSum D.A/D.a^2/N*Real.exp ((q+C*s)*j) := by
        convert hforcing using 1 <;> simp only [div_eq_mul_inv] <;> ring
      exact hforcingEq.trans hh
    have hcoll := mul_le_mul_of_nonneg_left hC
      (show 0 ≤ (M+L*s)*(j*Real.exp ((q+C*s)*j)) by positivity)
    dsimp [f,barrierDerivative]
    dsimp [j] at *
    nlinarith [hcoll]
  have hV : volterra (rankWeights D) (fun j s => ENNReal.ofReal (barrier M L q C j s)) k t ≤
      ∫⁻ s in Set.Ioc 0 t,ENNReal.ofReal ((M+L*s)*(j*Real.exp ((q+C*s)*j)*collisionSum D.A D.a)) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact rank_sum_bound D (q+C*s) (M+L*s)
      (by have hh := mul_le_mul_of_nonneg_left (hs.2.trans htT) hc;nlinarith)
      (by exact add_nonneg hM (mul_nonneg hL hs.1.le)) k
  have hInt : IntervalIntegrable (barrierDerivative M L q C k) volume 0 t :=
    (barrierDerivative_continuous M L q C k).intervalIntegrable 0 t
  have hDeriv := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => barrier_hasDerivAt M L q C k s) hInt
  have he : (∫⁻ s in Set.Ioc 0 t,ENNReal.ofReal (barrierDerivative M L q C k s))=
      ENNReal.ofReal (barrier M L q C k t-barrier M L q C k 0) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hInt.1]
    · rw [← intervalIntegral.integral_of_le ht,hDeriv]
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      dsimp [barrierDerivative]
      have hs0 := hs.1.le
      positivity
  have hfree : freeKernel D N ψ u k t ≤ ENNReal.ofReal (barrier M L q C k 0)+
      ∫⁻ s in Set.Ioc 0 t,ENNReal.ofReal (errorSum D.A*j^2/N) := by
    rw [MeasureTheory.lintegral_const]
    simp only [Measure.restrict_apply_univ,Real.volume_Ioc,sub_zero]
    rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_add (by dsimp [barrier];positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    convert add_le_add (hi k) (le_refl (t*(errorSum D.A*j^2/N))) using 1
    ring
  have hsum : freeKernel D N ψ u k t+
      volterra (rankWeights D) (fun j s => ENNReal.ofReal (barrier M L q C j s)) k t ≤
      ENNReal.ofReal (barrier M L q C k 0)+
        ∫⁻ s in Set.Ioc 0 t,ENNReal.ofReal (barrierDerivative M L q C k s) := by
    apply (add_le_add hfree hV).trans
    rw [add_assoc,← lintegral_add_left measurable_const]
    apply add_le_add le_rfl
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hs0 := hs.1.le
    have hca := collisionSum_nonneg D.A D.a
    have hj : 0 ≤ j := by dsimp [j];positivity
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (hp s hs.1.le hs.2)
  rw [he,← ENNReal.ofReal_add (by dsimp [barrier];positivity) (by
    exact sub_nonneg.mpr (by
      dsimp [barrier]
      apply mul_le_mul (by nlinarith) (Real.exp_le_exp.mpr (by
        have hk : (0 : ℝ) ≤ (k+1 : ℕ) := by positivity
        have hh := mul_nonneg (mul_nonneg hc ht) hk
        nlinarith)) (by positivity) (by positivity)))] at hsum
  simpa only [add_sub_cancel] using hsum

end QuantumNLS.Prop001RtwentyComparison

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001RtwentyComparison" then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      if n.toString == ("QuantumNLS.Prop001.HeldGP" ++ "14Tonelli") then
        throwError "Rejected GP14 wrapper dependency"
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
  Lean.logInfo m!"Prop001RtwentyComparison audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."






#print axioms QuantumNLS.Prop001RtwentyComparison.partial_le_supersolution
#print axioms QuantumNLS.Prop001RtwentyComparison.actual_comparison
#print axioms QuantumNLS.Prop001RtwentyComparison.rank_square_half
#print axioms QuantumNLS.Prop001RtwentyComparison.barrier_hasDerivAt
#print axioms QuantumNLS.Prop001RtwentyComparison.barrier_supersolution

end

-- Namespace fragment: Prop001RtwentyFlow
/-! Literal quantum and classical restart identities. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
open Filter Topology MeasureTheory
open scoped BigOperators ENNReal
namespace QuantumNLS.Prop001RtwentyFlow
open TraceClass TensorCarrier Prop001 Prop001RthirteenSeries Prop001RseventeenContinuity
  Prop001RtwentyIteration
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem quantum_add (A : Interactions H) (N : ℕ) (t s : ℝ) :
    quantumEvolution A N (t+s)=quantumEvolution A N t*quantumEvolution A N s := by
  let +nondep : NormedAlgebra ℚ (SymSector ℂ H N →L[ℂ] SymSector ℂ H N) :=
    .restrictScalars ℚ ℂ _
  unfold quantumEvolution LinearTailPhysicalEvolution.evolution
  rw [Complex.ofReal_add,add_smul]
  have hc : Commute ((t : ℂ) • ((-Complex.I) • generator A N))
      ((s : ℂ) • ((-Complex.I) • generator A N)) :=
    by
      change _ * _ = _ * _
      ext x
      simp only [mul_apply_eq_comp,smul_apply,map_smul,smul_smul]
      congr 1
      ring
  rw [NormedSpace.exp_add_of_commute hc]

theorem extended_shift (A : Interactions H) (N j : ℕ) (ψ : SymSector ℂ H N) (s t : ℝ) :
    extendedMarginal A N j t (quantumEvolution A N s ψ)=extendedMarginal A N j (t+s) ψ := by
  by_cases hj : j ≤ N
  · simp only [extendedMarginal_of_le A N j hj,marginal,quantum_add,
      mul_apply_eq_comp]
  · simp only [extendedMarginal,dite_eq_right hj]

theorem error_shift (D : ClassicalData H) (N : ℕ) (ψ : SymSector ℂ H N)
    (u : Sphere H) (s t : ℝ) (j : ℕ) :
    error D N (quantumEvolution D.A N s ψ) (flow D s u) j t=error D N ψ u j (t+s) := by
  unfold error
  rw [extended_shift,← congrFun (trajectory_shift D u s) t]

end QuantumNLS.Prop001RtwentyFlow

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001RtwentyFlow" then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      if n.toString == ("QuantumNLS.Prop001.HeldGP" ++ "14Tonelli") then
        throwError "Rejected GP14 wrapper dependency"
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
  Lean.logInfo m!"Prop001RtwentyFlow audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."






#print axioms QuantumNLS.Prop001RtwentyFlow.quantum_add
#print axioms QuantumNLS.Prop001RtwentyFlow.extended_shift
#print axioms QuantumNLS.Prop001RtwentyFlow.error_shift

end

-- Namespace fragment: Prop001RtwentyBudget
/-! Common norm budgets and exact schedule composition. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
open Filter Topology MeasureTheory
open scoped BigOperators ENNReal
namespace QuantumNLS.Prop001RtwentyBudget
open TraceClass TensorCarrier Prop001 Prop001RthirteenSeries Prop001RseventeenContinuity
  Prop001RtwentyIteration Prop001RtwentyAssembly Prop001RtwentyFlow
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Retain the same kernels while putting every segment in the common
analytic scale; the trajectory will be identified by uniqueness below. -/
def aligned (B : NormBudget) (D : ClassicalData H) (hD : ∀ n, ‖D.A n‖ ≤ B.b n) :
    ClassicalData H where
  A := D.A
  selfAdjoint := D.selfAdjoint
  a := B.a
  a_pos := B.a_pos
  cubic := D.cubic
  exponential := Summable.of_nonneg_of_le (fun _ => by positivity)
    (fun n => mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hD n) (by positivity)) (Real.exp_pos _).le) B.exponential

theorem aligned_trajectory (B : NormBudget) (D : ClassicalData H)
    (hD : ∀ n, ‖D.A n‖ ≤ B.b n) (u : Sphere H) :
    trajectory (aligned B D hD) u=trajectory D u := by
  apply (trajectory_spec D u).2.2.2
  · exact (trajectory_spec (aligned B D hD) u).1
  · exact (trajectory_spec (aligned B D hD) u).2.2.1

theorem aligned_moments (B : NormBudget) (D : ClassicalData H)
    (hD : ∀ n, ‖D.A n‖ ≤ B.b n) :
    collisionSum D.A B.a ≤ B.Ca ∧ errorSum D.A ≤ B.C0 := by
  have hE := (aligned B D hD).exponential
  constructor
  · apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
    exact Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hD n) (by positivity)) (Real.exp_pos _).le) hE B.exponential
  · apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 6)
    exact Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (hD n) (by positivity)) D.cubic B.cubic

theorem quantum_append (N : ℕ) (L K : List (ClassicalData H × ℝ)) :
    quantumSegments N (L++K)=(quantumSegments N K).comp (quantumSegments N L) := by
  induction L with
  | nil => ext x;rfl
  | cons p L ih =>
    simp only [List.cons_append,quantumSegments,ih,ContinuousLinearMap.comp_assoc]

theorem classical_append (L K : List (ClassicalData H × ℝ)) (u : Sphere H) :
    classicalSegments (L++K) u=classicalSegments K (classicalSegments L u) := by
  induction L generalizing u with
  | nil => rfl
  | cons p L ih => exact ih (flow p.1 p.2 u)

theorem elapsed_append (L K : List (ClassicalData H × ℝ)) :
    elapsed (L++K)=elapsed L+elapsed K := by simp [elapsed]

theorem split_quantum (N : ℕ) (D : ClassicalData H) (s t : ℝ)
    (L : List (ClassicalData H × ℝ)) :
    quantumSegments N ((D,t+s)::L)=quantumSegments N ((D,s)::(D,t)::L) := by
  simp only [quantumSegments,quantum_add]
  ext x
  rfl

theorem split_classical (D : ClassicalData H) (s t : ℝ)
    (L : List (ClassicalData H × ℝ)) (u : Sphere H) :
    classicalSegments ((D,t+s)::L) u=classicalSegments ((D,s)::(D,t)::L) u := by
  simp only [classicalSegments,flow_add]

theorem elapsed_nonneg (L : List (ClassicalData H × ℝ)) : 0 ≤ elapsed L := by
  unfold elapsed
  exact List.sum_nonneg (fun x hx => by obtain ⟨p,_,rfl⟩ := List.mem_map.mp hx;exact abs_nonneg _)

end QuantumNLS.Prop001RtwentyBudget

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001RtwentyBudget" then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      if n.toString == ("QuantumNLS.Prop001.HeldGP" ++ "14Tonelli") then
        throwError "Rejected GP14 wrapper dependency"
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
  Lean.logInfo m!"Prop001RtwentyBudget audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."






#print axioms QuantumNLS.Prop001RtwentyBudget.aligned
#print axioms QuantumNLS.Prop001RtwentyBudget.aligned_trajectory
#print axioms QuantumNLS.Prop001RtwentyBudget.aligned_moments
#print axioms QuantumNLS.Prop001RtwentyBudget.quantum_append
#print axioms QuantumNLS.Prop001RtwentyBudget.classical_append
#print axioms QuantumNLS.Prop001RtwentyBudget.elapsed_append
#print axioms QuantumNLS.Prop001RtwentyBudget.split_quantum
#print axioms QuantumNLS.Prop001RtwentyBudget.split_classical
#print axioms QuantumNLS.Prop001RtwentyBudget.elapsed_nonneg

end

-- Namespace fragment: Prop001RtwentySigns
/-! Reverse-time data with the identical sequence of kernel norms. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
open Filter Topology MeasureTheory
open scoped BigOperators ENNReal
namespace QuantumNLS.Prop001RtwentySigns
open TraceClass TensorCarrier Prop001 Prop001RthirteenSeries Prop001RseventeenContinuity
  Prop001RtwentyIteration TensorPlacements KernelDefinition PhysicalTensor
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def reverseData (D : ClassicalData H) : ClassicalData H where
  A n := -(D.A n)
  selfAdjoint n := by
    change (-(D.A n)).adjoint= -(D.A n)
    rw [map_neg]
    exact congrArg Neg.neg (D.selfAdjoint n).star_eq
  a := D.a
  a_pos := D.a_pos
  cubic := by simpa only [ContinuousLinearMap.opNorm_neg] using D.cubic
  exponential := by simpa only [ContinuousLinearMap.opNorm_neg] using D.exponential

theorem reverse_moments (D : ClassicalData H) :
    collisionSum (reverseData D).A D.a=collisionSum D.A D.a ∧
      errorSum (reverseData D).A=errorSum D.A := by
  constructor <;> simp only [collisionSum,errorSum,reverseData,ContinuousLinearMap.opNorm_neg]

theorem field_neg (A : Interactions H) (u : H) :
    Ext025A8.sourceHartreeField (fun n => -(A n)) u= -Ext025A8.sourceHartreeField A u := by
  have he (n : ℕ) : extendSymKernel (-(A n))= -(extendSymKernel (A n)) := by
    ext x
    simp [extendSymKernel]
  simp only [Ext025A8.sourceHartreeField,Ext025A8.hartreeField,he]
  have ht (n : ℕ) : Ext025A8.hartreeTerm (fun n => -(extendSymKernel (A n))) n u=
      -Ext025A8.hartreeTerm (fun n => extendSymKernel (A n)) n u := by
    simp [Ext025A8.hartreeTerm,Ext025A8.hartreeContraction]
  simp only [ht,tsum_neg,smul_neg]

theorem reverse_trajectory (D : ClassicalData H) (u : Sphere H) :
    trajectory (reverseData D) u=(fun t => trajectory D u (-t)) := by
  symm
  apply (trajectory_spec (reverseData D) u).2.2.2
  · simpa only [neg_zero] using (trajectory_spec D u).1
  · intro t
    refine ⟨((trajectory_spec D u).2.2.1 (-t)).1,?_⟩
    rw [show (reverseData D).A=(fun n => -(D.A n)) from rfl,field_neg]
    simpa only [neg_one_smul,Function.comp_def] using
      (((trajectory_spec D u).2.2.1 (-t)).2.scomp t (hasDerivAt_id t).neg)

theorem generator_neg (A : Interactions H) (N : ℕ) :
    generator (fun n => -(A n)) N= -generator A N := by
  have hg (n : Fin N) :
      genericU_N_r N (n.val+1) (Nat.succ_le_of_lt n.isLt) (-(A n.val))=
        -genericU_N_r N (n.val+1) (Nat.succ_le_of_lt n.isLt) (A n.val) := by
    have hh := RootOverlapLimit.genericU_smul N (n.val+1) (Nat.succ_le_of_lt n.isLt) (-1 : ℂ) (A n.val)
    have he : (-1 : ℂ) • A n.val= -(A n.val) := by ext x;simp
    rw [he] at hh
    convert hh using 1
  simp only [generator,hg,smul_neg,Finset.sum_neg_distrib]

theorem reverse_quantum (D : ClassicalData H) (N : ℕ) (t : ℝ) :
    quantumEvolution (reverseData D).A N t=quantumEvolution D.A N (-t) := by
  unfold quantumEvolution LinearTailPhysicalEvolution.evolution
  rw [show (reverseData D).A=(fun n => -(D.A n)) from rfl,generator_neg]
  simp only [smul_neg,Complex.ofReal_neg,neg_smul]

theorem reverse_error (D : ClassicalData H) (N : ℕ) (ψ : SymSector ℂ H N)
    (u : Sphere H) (j : ℕ) (t : ℝ) :
    error (reverseData D) N ψ u j t=error D N ψ u j (-t) := by
  unfold error
  rw [reverse_trajectory]
  by_cases hj : j ≤ N
  · simp only [extendedMarginal_of_le _ N j hj,marginal,reverse_quantum]
  · simp only [extendedMarginal,dite_eq_right hj]

end QuantumNLS.Prop001RtwentySigns

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001RtwentySigns" then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      if n.toString == ("QuantumNLS.Prop001.HeldGP" ++ "14Tonelli") then
        throwError "Rejected GP14 wrapper dependency"
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
  Lean.logInfo m!"Prop001RtwentySigns audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."






#print axioms QuantumNLS.Prop001RtwentySigns.reverse_moments
#print axioms QuantumNLS.Prop001RtwentySigns.field_neg
#print axioms QuantumNLS.Prop001RtwentySigns.reverse_trajectory
#print axioms QuantumNLS.Prop001RtwentySigns.generator_neg
#print axioms QuantumNLS.Prop001RtwentySigns.reverse_quantum
#print axioms QuantumNLS.Prop001RtwentySigns.reverse_error

end

-- Namespace fragment: Prop001RtwentySchedule
/-! A common moving analytic envelope across actual schedule boundaries. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
open Filter Topology MeasureTheory
open scoped BigOperators ENNReal
namespace QuantumNLS.Prop001RtwentySchedule
open TraceClass TensorCarrier PhysicalTensor Prop001 Prop001RthirteenSeries Prop001RseventeenContinuity
  Prop001RtwentyIteration Prop001RtwentyAssembly Prop001RtwentyFlow
  Prop001RtwentyBudget Prop001RtwentySigns Prop001RtwentyComparison
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def pureMarginal (N j : ℕ) (ψ : SymSector ℂ H N) : RankOperator H j :=
  if h : j ≤ N then reducedDensityN N j h (ψ : HilbertTensorPower ℂ H N) else 0

def pureError (N : ℕ) (ψ : SymSector ℂ H N) (u : Sphere H) (j : ℕ) : ℝ :=
  (traceNorm (pureMarginal N j ψ-coherentProjector j u.val)).toReal

theorem error_pure (D : ClassicalData H) (N : ℕ) (ψ : SymSector ℂ H N)
    (u : Sphere H) (j : ℕ) (t : ℝ) :
    error D N ψ u j t=pureError N (quantumEvolution D.A N t ψ) (flow D t u) j := by
  rfl

theorem error_initial_pure (D : ClassicalData H) (N : ℕ) (ψ : SymSector ℂ H N)
    (u : Sphere H) (j : ℕ) : error D N ψ u j 0=pureError N ψ u j := by
  rw [error_pure,flow_zero]
  simp only [quantumEvolution,LinearTailPhysicalEvolution.evolution_zero,one_apply_eq_self]

/-- A positive segment preserves the moving envelope at the common scale. -/
theorem segment_barrier (B : NormBudget) (D : ClassicalData H)
    (hD : ∀ n, ‖D.A n‖ ≤ B.b n) (N : ℕ) (hN : 0 < N)
    (ψ : SymSector ℂ H N) (hψ : ‖ψ‖=1) (u : Sphere H) (M q t : ℝ)
    (hM : 0 ≤ M) (hq : B.a/2 ≤ q) (ht : 0 ≤ t) (hscale : q+B.Ca*t ≤ B.a)
    (hsmall : t*B.Ca < B.a)
    (hi : ∀ j,pureError N ψ u (j+1) ≤ M*Real.exp (q*((j+1 : ℕ) : ℝ))) :
    ∀ j,pureError N (quantumEvolution D.A N t ψ) (flow D t u) (j+1) ≤
      (M+(4*B.C0/B.a^2/N)*t)*Real.exp ((q+B.Ca*t)*((j+1 : ℕ) : ℝ)) := by
  let E := aligned B D hD
  let L := 4*B.C0/B.a^2/N
  have hC0 : 0 ≤ B.C0 := mul_nonneg (by norm_num) (tsum_nonneg (fun n => mul_nonneg (by positivity) (B.nonneg n)))
  have hL : 0 ≤ L := by dsimp [L];positivity
  have hforce : 4*errorSum E.A/E.a^2/N ≤ L := by
    exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (aligned_moments B D hD).2 (by norm_num)) (sq_nonneg _)) (by positivity)
  have hi' : ∀ j,error E N ψ u (j+1) 0 ≤ barrier M L q B.Ca j 0 := by
    simpa only [error_initial_pure,barrier,mul_zero,add_zero] using hi
  have hs := barrier_supersolution E N hN ψ u M L q B.Ca t hM hL
    (aligned_moments B D hD).1 hq ht hscale hforce hi'
  intro j
  have hh := actual_comparison E N ψ hψ u
    (fun j s => ENNReal.ofReal (barrier M L q B.Ca j s)) t hs j t ht le_rfl
    ((mul_le_mul_of_nonneg_left (aligned_moments B D hD).1 ht).trans_lt hsmall)
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  have hpos : 0 ≤ barrier M L q B.Ca j t := by dsimp [barrier];positivity
  rw [ENNReal.toReal_ofReal hpos] at hr
  change error E N ψ u (j+1) t ≤ _ at hr
  have he : error E N ψ u (j+1) t=error D N ψ u (j+1) t := by
    unfold error
    rw [aligned_trajectory]
    rfl
  rw [he,error_pure] at hr
  exact hr

/-- Actual boundary induction on a positive schedule, retaining one common
analytic scale and one elapsed-time forcing budget. -/
theorem positive_schedule_barrier (B : NormBudget) (S : List (ClassicalData H × ℝ))
    (hS : Dominates B S) (hpos : ∀ p ∈ S,0 ≤ p.2)
    (N : ℕ) (hN : 0 < N) (ψ : SymSector ℂ H N) (hψ : ‖ψ‖=1)
    (u : Sphere H) (M q : ℝ) (hM : 0 ≤ M) (hq : B.a/2 ≤ q)
    (hscale : q+B.Ca*elapsed S ≤ B.a) (hsmall : elapsed S*B.Ca < B.a)
    (hi : ∀ j,pureError N ψ u (j+1) ≤ M*Real.exp (q*((j+1 : ℕ) : ℝ))) :
    ∀ j,pureError N (quantumSegments N S ψ) (classicalSegments S u) (j+1) ≤
      (M+(4*B.C0/B.a^2/N)*elapsed S)*
        Real.exp ((q+B.Ca*elapsed S)*((j+1 : ℕ) : ℝ)) := by
  have hc := budget_nonneg B
  induction S generalizing ψ u M q with
  | nil => simpa only [quantumSegments,classicalSegments,elapsed,List.map_nil,List.sum_nil,mul_zero,add_zero,one_apply_eq_self] using hi
  | cons p S ih =>
    have ht := hpos p (List.mem_cons_self ..)
    have hel : elapsed (p::S)=p.2+elapsed S := by simp [elapsed,abs_of_nonneg ht]
    have hrest := elapsed_nonneg S
    have hp : ∀ n,‖p.1.A n‖ ≤ B.b n := hS p (List.mem_cons_self ..)
    have hdom : Dominates B S := fun x hx => hS x (List.mem_cons_of_mem _ hx)
    have hpos' : ∀ x ∈ S,0 ≤ x.2 := fun x hx => hpos x (List.mem_cons_of_mem _ hx)
    have hscale' : q+B.Ca*p.2 ≤ B.a := by rw [hel] at hscale;nlinarith [mul_nonneg hc hrest]
    have hsmall' : p.2*B.Ca < B.a := by rw [hel] at hsmall;nlinarith [mul_nonneg hc hrest]
    have hfirst := segment_barrier B p.1 hp N hN ψ hψ u M q p.2 hM hq ht hscale' hsmall' hi
    have hψ' : ‖quantumEvolution p.1.A N p.2 ψ‖=1 :=
      (quantumEvolution_norm p.1.A p.1.selfAdjoint N p.2 ψ).trans hψ
    have hC0 : 0 ≤ B.C0 := mul_nonneg (by norm_num) (tsum_nonneg (fun n => mul_nonneg (by positivity) (B.nonneg n)))
    have hM' : 0 ≤ M+(4*B.C0/B.a^2/N)*p.2 := by positivity
    have hq' : B.a/2 ≤ q+B.Ca*p.2 := by nlinarith
    have hs' : (q+B.Ca*p.2)+B.Ca*elapsed S ≤ B.a := by rw [hel] at hscale;nlinarith
    have hsm' : elapsed S*B.Ca < B.a := by rw [hel] at hsmall;nlinarith [mul_nonneg hc ht]
    have hh := ih hdom hpos' (quantumEvolution p.1.A N p.2 ψ) hψ'
      (flow p.1 p.2 u) (M+(4*B.C0/B.a^2/N)*p.2) (q+B.Ca*p.2) hM' hq' hs' hsm' hfirst
    intro j
    simpa only [quantumSegments,classicalSegments,ContinuousLinearMap.comp_apply,hel,
      mul_add,add_assoc] using hh j

end QuantumNLS.Prop001RtwentySchedule

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001RtwentySchedule" then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      if n.toString == ("QuantumNLS.Prop001.HeldGP" ++ "14Tonelli") then
        throwError "Rejected GP14 wrapper dependency"
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
  Lean.logInfo m!"Prop001RtwentySchedule audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."






#print axioms QuantumNLS.Prop001RtwentySchedule.error_pure
#print axioms QuantumNLS.Prop001RtwentySchedule.error_initial_pure
#print axioms QuantumNLS.Prop001RtwentySchedule.segment_barrier
#print axioms QuantumNLS.Prop001RtwentySchedule.positive_schedule_barrier

end

-- Namespace fragment: Prop001RtwentySplit
/-! A cut at any elapsed time preserves the literal scheduled flows. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
open scoped BigOperators ENNReal
namespace QuantumNLS.Prop001RtwentySplit
open TraceClass TensorCarrier Prop001 Prop001RtwentyAssembly Prop001RtwentyBudget
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def Positive (S : List (ClassicalData H × ℝ)) : Prop := ∀ p ∈ S,0 ≤ p.2

/-- The cut may lie inside a segment. Its two pieces retain the same
kernels and total evolution; no restart estimate is part of this lemma. -/
theorem split_positive (B : NormBudget) (S : List (ClassicalData H × ℝ))
    (hS : Dominates B S) (hpos : Positive S) (t : ℝ) (ht : 0 ≤ t) (htS : t ≤ elapsed S) :
    ∃ L K : List (ClassicalData H × ℝ),
      Dominates B L ∧ Dominates B K ∧ Positive L ∧ Positive K ∧
      elapsed L=t ∧ elapsed K=elapsed S-t ∧
      (∀ N,quantumSegments N S=quantumSegments N (L++K)) ∧
      (∀ u,classicalSegments S u=classicalSegments (L++K) u) := by
  induction S generalizing t with
  | nil =>
    have hz : t=0 := by simpa only [elapsed,List.map_nil,List.sum_nil] using le_antisymm htS ht
    subst t
    refine ⟨[],[],hS,hS,hpos,hpos,rfl,?_,fun _ => rfl,fun _ => rfl⟩
    simp [elapsed]
  | cons p S ih =>
    have hp : ∀ n,‖p.1.A n‖ ≤ B.b n := hS p (List.mem_cons_self ..)
    have htail : Dominates B S := fun q hq => hS q (List.mem_cons_of_mem _ hq)
    have hp0 := hpos p (List.mem_cons_self ..)
    have htail0 : Positive S := fun q hq => hpos q (List.mem_cons_of_mem _ hq)
    have hel : elapsed (p::S)=p.2+elapsed S := by simp [elapsed,abs_of_nonneg hp0]
    by_cases hcut : t ≤ p.2
    · let L := [(p.1,t)]
      let K := (p.1,p.2-t)::S
      have hrem : 0 ≤ p.2-t := sub_nonneg.mpr hcut
      have hL : Dominates B L := by
        intro q hq n
        have he : q=(p.1,t) := by simpa only [L,List.mem_singleton] using hq
        subst q
        exact hp n
      have hK : Dominates B K := by
        intro q hq n
        rcases List.mem_cons.mp hq with he|he
        · subst q;exact hp n
        · exact htail q he n
      have hL0 : Positive L := by
        intro q hq
        have he : q=(p.1,t) := by simpa only [L,List.mem_singleton] using hq
        subst q
        exact ht
      have hK0 : Positive K := by
        intro q hq
        rcases List.mem_cons.mp hq with he|he
        · subst q;exact hrem
        · exact htail0 q he
      refine ⟨L,K,hL,hK,hL0,hK0,?_,?_,?_,?_⟩
      · simp only [L,elapsed,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,abs_of_nonneg ht]
      · rw [hel]
        simp only [K,elapsed,List.map_cons,List.sum_cons,abs_of_nonneg hrem]
        ring
      · intro N
        have hh := split_quantum N p.1 t (p.2-t) S
        have he : p.2-t+t=p.2 := by ring
        rw [he] at hh
        exact hh
      · intro u
        have hh := split_classical p.1 t (p.2-t) S u
        have he : p.2-t+t=p.2 := by ring
        rw [he] at hh
        exact hh
    · have hgt : p.2 < t := lt_of_not_ge hcut
      obtain ⟨L,K,hL,hK,hL0,hK0,hLt,hKt,hQ,hC⟩ := ih htail htail0 (t-p.2)
        (by linarith) (by rw [hel] at htS;linarith)
      refine ⟨p::L,K,?_,hK,?_,hK0,?_,?_,?_,?_⟩
      · intro q hq n
        rcases List.mem_cons.mp hq with he|he
        · subst q;exact hp n
        · exact hL q he n
      · intro q hq
        rcases List.mem_cons.mp hq with he|he
        · subst q;exact hp0
        · exact hL0 q he
      · simp only [elapsed,List.map_cons,List.sum_cons,abs_of_nonneg hp0]
        change p.2+elapsed L=t
        rw [hLt]
        ring
      · rw [hKt,hel]
        ring
      · intro N
        simpa only [List.cons_append,quantumSegments] using
          congrArg (fun A => A.comp (quantumEvolution p.1.A N p.2)) (hQ N)
      · intro u
        exact hC (flow p.1 p.2 u)

end QuantumNLS.Prop001RtwentySplit

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001RtwentySplit" then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      if n.toString == ("QuantumNLS.Prop001.HeldGP" ++ "14Tonelli") then
        throwError "Rejected GP14 wrapper dependency"
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
  Lean.logInfo m!"Prop001RtwentySplit audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."






#print axioms QuantumNLS.Prop001RtwentySplit.split_positive

end

-- Namespace fragment: Prop001RtwentyRestart
/-! Actual restart from arbitrary normalized initial data, at the printed step. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
open Filter Topology MeasureTheory
open scoped BigOperators ENNReal
namespace QuantumNLS.Prop001RtwentyRestart
open TraceClass TensorCarrier Prop001 Prop001RthirteenSeries Prop001RseventeenContinuity
  Prop001RtwentyIteration Prop001RtwentyRemainder Prop001RtwentyExpansion
  Prop001RtwentyData
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Exponential initial data spend exactly half the available analytic scale. -/
theorem iterate_exponential_bound (D : ClassicalData H) (M : ℝ) (hM : 0 ≤ M)
    (f : ℕ → ℝ → ℝ≥0∞)
    (hf : ∀ j s, 0 ≤ s → f j s ≤
      ENNReal.ofReal (M*Real.exp (D.a/2*((j+1 : ℕ) : ℝ))))
    (n k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    iterate (rankWeights D) f n k t ≤
      ENNReal.ofReal (M*Real.exp (D.a*((k+1 : ℕ) : ℝ))*
        (2*t*collisionSum D.A D.a/D.a)^n) := by
  have ha := D.a_pos
  have hc := collisionSum_nonneg D.A D.a
  by_cases hn : n=0
  · subst n
    simp only [iterate,pow_zero,mul_one]
    apply (hf k t ht).trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hM
    apply Real.exp_le_exp.mpr
    have ha := D.a_pos
    have hk : (0 : ℝ) ≤ (k+1 : ℕ) := by positivity
    nlinarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  let δ := D.a/(2*(n : ℝ))
  have hδ : 0 < δ := by dsimp [δ];positivity
  have hq : D.a/2+(n : ℝ)*δ=D.a := by dsimp [δ];field_simp;ring
  have hf' : ∀ j s,0 ≤ s → f j s ≤
      ENNReal.ofReal (M*s^0*Real.exp (D.a/2*((j+1 : ℕ) : ℝ))) := by
    simpa only [pow_zero,mul_one] using hf
  have hh := iterate_monomial_bound D (D.a/2) δ M hδ hM 0 f hf' n
    (by rw [hq]) k t ht
  rw [hq] at hh
  simp only [Nat.zero_add,Nat.factorial_zero,Nat.cast_one,one_div] at hh
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  have hp := Real.pow_div_factorial_le_exp (n : ℝ) hnpos.le n
  have hex : Real.exp (n : ℝ)=(Real.exp 1)^n := by
    simpa only [mul_one] using Real.exp_nat_mul (1 : ℝ) n
  rw [hex] at hp
  calc
    _ = (M*Real.exp (D.a*((k+1 : ℕ) : ℝ))*(2*t*collisionSum D.A D.a/(D.a*Real.exp 1))^n)*
        ((n : ℝ)^n/(n.factorial : ℝ)) := by
      dsimp [δ]
      simp only [div_eq_mul_inv,mul_inv_rev,inv_inv,mul_pow]
      ring
    _ ≤ (M*Real.exp (D.a*((k+1 : ℕ) : ℝ))*(2*t*collisionSum D.A D.a/(D.a*Real.exp 1))^n)*
        (Real.exp 1)^n := mul_le_mul_of_nonneg_left hp (by
          exact mul_nonneg (mul_nonneg hM (Real.exp_pos _).le)
            (pow_nonneg (div_nonneg (by positivity) (by positivity)) n))
    _ = _ := by
      rw [mul_assoc,← mul_pow]
      congr 2
      field_simp

/-- Actual restarted free data split into their initial part and forcing. -/
theorem restarted_free_bound (D : ClassicalData H) (N : ℕ)
    (ψ : SymSector ℂ H N) (u : Sphere H) (M : ℝ) (_hM : 0 ≤ M)
    (hi : ∀ j,error D N ψ u (j+1) 0 ≤ M*Real.exp (D.a/2*((j+1 : ℕ) : ℝ)))
    (n k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    iterate (rankWeights D) (freeKernel D N ψ u) n k t ≤
      ENNReal.ofReal (M*Real.exp (D.a*((k+1 : ℕ) : ℝ))*
        (2*t*collisionSum D.A D.a/D.a)^n)+ENNReal.ofReal (forcingTerm D N k t n) := by
  have ha := D.a_pos
  have hC := errorSum_nonneg D.A
  let f := fun j (_s : ℝ) => ENNReal.ofReal (error D N ψ u (j+1) 0)
  have hf : ∀ j,Measurable (f j) := fun _ => measurable_const
  have hb : ∀ j s,0 ≤ s → freeKernel D N ψ u j s ≤
      f j s+polynomialKernel (errorSum D.A/N) 1 j s := by
    intro j s hs
    unfold freeKernel polynomialKernel f
    rw [← ENNReal.ofReal_add (error_nonneg D N ψ u _ 0) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    simp only [Nat.reduceAdd,pow_one]
    apply le_of_eq
    ring
  have hh := iterate_mono_nonneg (rankWeights D) _ _ hb n k t ht
  rw [iterate_add _ _ _ hf] at hh
  apply hh.trans
  apply add_le_add
  · exact iterate_exponential_bound D M _hM f (fun j _ _ => ENNReal.ofReal_le_ofReal (hi j)) n k t ht
  · apply (iterate_polynomial_bound D (errorSum D.A/N)
      (div_nonneg (errorSum_nonneg _) (by positivity)) 1 n k t ht).trans
    apply le_of_eq
    apply congrArg ENNReal.ofReal
    simp only [forcingTerm,Nat.factorial_one,Nat.cast_one,pow_one,mul_one]
    have he : 1+n+1=n+2 := by omega
    rw [he]
    ring

/-- The exact initial and forcing sums at restart. In particular the forcing
coefficient is E, rather than the weaker first-interval coefficient 2E. -/
theorem actual_restart_envelope (D : ClassicalData H) (hCa : collisionSum D.A D.a ≠ 0)
    (N : ℕ) (hN : 0 < N) (ψ : SymSector ℂ H N) (hψ : ‖ψ‖=1)
    (u : Sphere H) (M : ℝ) (hM : 0 ≤ M)
    (hi : ∀ j,error D N ψ u (j+1) 0 ≤ M*Real.exp (D.a/2*((j+1 : ℕ) : ℝ)))
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (hstep : t ≤ stepTime D.a (collisionSum D.A D.a)) :
    traceNorm (extendedMarginal D.A N (k+1) t ψ-coherentProjector (k+1) (trajectory D u t)) ≤
      ENNReal.ofReal ((2*M+forcingConstant D.a (errorSum D.A)
        (stepTime D.a (collisionSum D.A D.a))/N)*Real.exp (D.a*((k+1 : ℕ) : ℝ))) := by
  have hC := errorSum_nonneg D.A
  let rho := t*collisionSum D.A D.a/D.a
  have ha := D.a_pos
  have hc : 0 < collisionSum D.A D.a := lt_of_le_of_ne (collisionSum_nonneg _ _) hCa.symm
  have hr0 : 0 ≤ rho := by dsimp [rho];positivity
  have hr : rho ≤ 1/4 := by
    unfold stepTime at hstep
    have hh := (le_div_iff₀ (show 0 < 4*collisionSum D.A D.a by positivity)).mp hstep
    dsimp [rho]
    apply (div_le_iff₀ ha).mpr
    nlinarith
  have hr1 : rho < 1 := by linarith
  have htwo : |2*rho| < 1 := by rw [abs_of_nonneg (by positivity)];linarith
  have hI : HasSum (fun n : ℕ => M*Real.exp (D.a*((k+1 : ℕ) : ℝ))*(2*rho)^n)
      (M*Real.exp (D.a*((k+1 : ℕ) : ℝ))*(1-2*rho)⁻¹) :=
    (hasSum_geometric_of_abs_lt_one htwo).mul_left _
  have hF : HasSum (forcingTerm D N k t)
      (errorSum D.A*t*Real.exp (D.a*((k+1 : ℕ) : ℝ))*(2-rho)/(D.a^2*N*(1-rho)^2)) :=
    forcing_series_value (a := D.a) (C0 := errorSum D.A) (t := t) (N := (N : ℝ)) (k+1) hr0 hr1
  have hIP (n : ℕ) : 0 ≤ M*Real.exp (D.a*((k+1 : ℕ) : ℝ))*(2*rho)^n := by positivity
  have hFP (n : ℕ) : 0 ≤ forcingTerm D N k t n := by dsimp [forcingTerm];positivity
  apply (actual_error_le_series D hCa N ψ hψ u k t ht hstep).trans
  apply (ENNReal.tsum_le_tsum (fun n => restarted_free_bound D N ψ u M hM hi n k t ht)).trans
  have he : 2*t*collisionSum D.A D.a/D.a=2*rho := by dsimp [rho];ring
  simp_rw [he]
  rw [ENNReal.tsum_add,← ENNReal.ofReal_tsum_of_nonneg hIP hI.summable,
    ← ENNReal.ofReal_tsum_of_nonneg hFP hF.summable,hI.tsum_eq,hF.tsum_eq,
    ← ENNReal.ofReal_add
      (mul_nonneg (by positivity) (inv_nonneg.mpr (by linarith)))
      (div_nonneg (mul_nonneg (by positivity) (by linarith)) (by positivity))]
  apply ENNReal.ofReal_le_ofReal
  have hInv : (1-2*rho)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by linarith : 0 < 1-2*rho)).mpr
    linarith
  have hForce : (2-rho)/(1-rho)^2 ≤ 4 := by
    apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < 1-rho))).mpr
    nlinarith [sq_nonneg rho]
  have hA := mul_le_mul_of_nonneg_left hInv
    (show 0 ≤ M*Real.exp (D.a*((k+1 : ℕ) : ℝ)) by positivity)
  have hB := mul_le_mul_of_nonneg_left hForce
    (show 0 ≤ errorSum D.A*t*Real.exp (D.a*((k+1 : ℕ) : ℝ))/(D.a^2*N) by
      exact div_nonneg (mul_nonneg (mul_nonneg (errorSum_nonneg _) ht) (by positivity)) (by positivity))
  have hB' : errorSum D.A*t*Real.exp (D.a*((k+1 : ℕ) : ℝ))*(2-rho)/(D.a^2*N*(1-rho)^2) ≤
      4*errorSum D.A*t/D.a^2/N*Real.exp (D.a*((k+1 : ℕ) : ℝ)) := by
    convert hB using 1 <;> simp only [div_eq_mul_inv,mul_inv_rev] <;> ring
  have hC := mul_le_mul_of_nonneg_right hstep
    (show 0 ≤ 4*errorSum D.A/D.a^2/N*Real.exp (D.a*((k+1 : ℕ) : ℝ)) by positivity)
  have hC' : 4*errorSum D.A*t/D.a^2/N*Real.exp (D.a*((k+1 : ℕ) : ℝ)) ≤
      forcingConstant D.a (errorSum D.A) (stepTime D.a (collisionSum D.A D.a))/N*
        Real.exp (D.a*((k+1 : ℕ) : ℝ)) := by
    simp only [forcingConstant]
    convert hC using 1 <;> ring
  have hh := add_le_add hA (hB'.trans hC')
  convert hh using 1
  ring

/-- Interpolation uses the actual universal error bound by two. -/
theorem initial_interpolation (D : ClassicalData H) (N : ℕ) (ψ : SymSector ℂ H N)
    (hψ : ‖ψ‖=1) (u : Sphere H) (K x : ℝ) (hK : 0 ≤ K) (hx : 0 ≤ x)
    (hi : ∀ j,error D N ψ u (j+1) 0 ≤ K*Real.exp (D.a*((j+1 : ℕ) : ℝ))*x^2) :
    ∀ j,error D N ψ u (j+1) 0 ≤
      (Real.sqrt (2*K)*x)*Real.exp (D.a/2*((j+1 : ℕ) : ℝ)) := by
  intro j
  let d := error D N ψ u (j+1) 0
  let v := (Real.sqrt (2*K)*x)*Real.exp (D.a/2*((j+1 : ℕ) : ℝ))
  have hd : 0 ≤ d := error_nonneg D N ψ u _ 0
  have hv : 0 ≤ v := by dsimp [v];positivity
  have hs : d^2 ≤ 2*(K*Real.exp (D.a*((j+1 : ℕ) : ℝ))*x^2) := by
    have hh := mul_le_mul (error_le_two D N ψ hψ u (j+1) 0) (hi j) hd (by norm_num : (0:ℝ) ≤ 2)
    simpa only [pow_two] using hh
  have hv2 : v^2=2*(K*Real.exp (D.a*((j+1 : ℕ) : ℝ))*x^2) := by
    dsimp [v]
    rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity),← Real.exp_nat_mul]
    have he : (2 : ℝ)*(D.a/2*((j+1 : ℕ) : ℝ))=D.a*((j+1 : ℕ) : ℝ) := by ring
    norm_num only [Nat.cast_ofNat] at *
    rw [he]
    ring
  change d ≤ v
  nlinarith

/-- Actual restart closure with unchanged D, tau and E. The hypothesis is
ordinary initial data. -/
theorem actual_restart_printed (D : ClassicalData H) (hCa : collisionSum D.A D.a ≠ 0)
    (N : ℕ) (hN : 0 < N) (ψ : SymSector ℂ H N) (hψ : ‖ψ‖=1)
    (u : Sphere H) (x : ℝ) (hx : 0 ≤ x) (hNx : 1/(N : ℝ) ≤ x)
    (hi : ∀ j,error D N ψ u (j+1) 0 ≤
      rateConstant D.a (errorSum D.A) (stepTime D.a (collisionSum D.A D.a))*
        Real.exp (D.a*((j+1 : ℕ) : ℝ))*x^2)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (hstep : t ≤ stepTime D.a (collisionSum D.A D.a)) :
    traceNorm (extendedMarginal D.A N (k+1) t ψ-coherentProjector (k+1) (trajectory D u t)) ≤
      ENNReal.ofReal (rateConstant D.a (errorSum D.A) (stepTime D.a (collisionSum D.A D.a))*
        Real.exp (D.a*((k+1 : ℕ) : ℝ))*x) := by
  let K := rateConstant D.a (errorSum D.A) (stepTime D.a (collisionSum D.A D.a))
  let E := forcingConstant D.a (errorSum D.A) (stepTime D.a (collisionSum D.A D.a))
  have hK : 0 ≤ K := (by norm_num : (0:ℝ) ≤ 1).trans (rateConstant_ge_one _ _ _)
  have hE : 0 ≤ E := by dsimp [E,forcingConstant];exact div_nonneg (by
    exact mul_nonneg (mul_nonneg (by norm_num) (errorSum_nonneg _))
      (source_stepTime_pos D hCa).le) (sq_nonneg _)
  have hi' := initial_interpolation D N ψ hψ u K x hK hx hi
  apply (actual_restart_envelope D hCa N hN ψ hψ u (Real.sqrt (2*K)*x) (by positivity) hi' k t ht hstep).trans
  apply ENNReal.ofReal_le_ofReal
  have hforce : E/(N : ℝ) ≤ E*x := by
    simpa only [div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_left hNx hE
  have hclose := rateConstant_restart (a := D.a) (errorSum_nonneg D.A) (source_stepTime_pos D hCa).le
  change 2*Real.sqrt (2*K)+E ≤ K at hclose
  have hh := mul_le_mul_of_nonneg_right hclose hx
  have hs : 2*(Real.sqrt (2*K)*x)+E/N ≤ K*x := by nlinarith
  have hv := mul_le_mul_of_nonneg_right hs (Real.exp_pos (D.a*((k+1 : ℕ) : ℝ))).le
  dsimp [K,E] at hv
  convert hv using 1
  ring

end QuantumNLS.Prop001RtwentyRestart

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001RtwentyRestart" then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      if n.toString == ("QuantumNLS.Prop001.HeldGP" ++ "14Tonelli") then
        throwError "Rejected GP14 wrapper dependency"
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
  Lean.logInfo m!"Prop001RtwentyRestart audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."






#print axioms QuantumNLS.Prop001RtwentyRestart.iterate_exponential_bound
#print axioms QuantumNLS.Prop001RtwentyRestart.restarted_free_bound
#print axioms QuantumNLS.Prop001RtwentyRestart.actual_restart_envelope
#print axioms QuantumNLS.Prop001RtwentyRestart.initial_interpolation
#print axioms QuantumNLS.Prop001RtwentyRestart.actual_restart_printed

end

-- Namespace fragment: Prop001RtwentyGlobal
/-! Actual autonomous propagation to every nonnegative time by restart. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
open Filter Topology MeasureTheory
open scoped BigOperators ENNReal
namespace QuantumNLS.Prop001RtwentyGlobal
open TraceClass TensorCarrier Prop001 Prop001RthirteenSeries Prop001RseventeenContinuity
  Prop001RtwentyIteration Prop001RtwentyRemainder Prop001RtwentyExpansion
  Prop001RtwentyData Prop001RtwentyRestart Prop001RtwentyFlow
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def exponent (n : ℕ) : ℝ := (2 : ℝ)^(-(n : ℝ))

theorem exponent_zero : exponent 0=1 := by simp [exponent]

theorem exponent_pos (n : ℕ) : 0 < exponent n := by unfold exponent;positivity

theorem exponent_le_one (n : ℕ) : exponent n ≤ 1 := by
  apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
  exact neg_nonpos.mpr (Nat.cast_nonneg _)

theorem exponent_half (n : ℕ) : exponent (n+1)*2=exponent n := by
  unfold exponent
  push_cast
  rw [neg_add,Real.rpow_add (by norm_num : (0:ℝ) < 2),Real.rpow_neg_one]
  ring

theorem factor_square (N n : ℕ) :
    ((N : ℝ)^(-exponent (n+1)))^2=(N : ℝ)^(-exponent n) := by
  rw [← Real.rpow_mul_natCast (by positivity)]
  congr 1
  have hh := exponent_half n
  push_cast
  linarith

theorem factor_ge_inverse (N n : ℕ) (hN : 0 < N) :
    1/(N : ℝ) ≤ (N : ℝ)^(-exponent n) := by
  have hb : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hh := Real.rpow_le_rpow_of_exponent_le hb (neg_le_neg (exponent_le_one n))
  simpa only [Real.rpow_neg_one,one_div] using hh

/-- The initial estimate at the restart is transferred through the literal
evolution identities, rather than supplied as an induction assumption about
an unrelated hierarchy. -/
theorem actual_grid (D : ClassicalData H) (hCa : collisionSum D.A D.a ≠ 0)
    (N : ℕ) (hN : 0 < N) (u : Sphere H) (δ : ℝ) (hδ : 0 ≤ δ)
    (hs : δ ≤ stepTime D.a (collisionSum D.A D.a)) :
    ∀ n k,error D N (productVector N u.val) u (k+1) (((n+1 : ℕ) : ℝ)*δ) ≤
      rateConstant D.a (errorSum D.A) (stepTime D.a (collisionSum D.A D.a))*
        Real.exp (D.a*((k+1 : ℕ) : ℝ))*(N : ℝ)^(-exponent n) := by
  have hp : ‖productVector N u.val‖=1 := by rw [productVector_norm,u.property,one_pow]
  intro n
  induction n with
  | zero =>
    intro k
    have hh := actual_first_interval_printed D hCa N hN u k δ hδ hs
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
    have hR : 0 ≤ rateConstant D.a (errorSum D.A) (stepTime D.a (collisionSum D.A D.a))*
        Real.exp (D.a*((k+1 : ℕ) : ℝ))/N := by
      have hK := rateConstant_ge_one D.a (errorSum D.A) (stepTime D.a (collisionSum D.A D.a))
      positivity
    rw [ENNReal.toReal_ofReal hR] at hr
    simpa only [Nat.zero_add,Nat.cast_one,one_mul,exponent_zero,Real.rpow_neg_one,
      div_eq_mul_inv,error] using hr
  | succ n ih =>
    let s := ((n+1 : ℕ) : ℝ)*δ
    let ψ := quantumEvolution D.A N s (productVector N u.val)
    have hψ : ‖ψ‖=1 := (quantumEvolution_norm D.A D.selfAdjoint N s (productVector N u.val)).trans hp
    have hi : ∀ j,error D N ψ (flow D s u) (j+1) 0 ≤
        rateConstant D.a (errorSum D.A) (stepTime D.a (collisionSum D.A D.a))*
          Real.exp (D.a*((j+1 : ℕ) : ℝ))*((N : ℝ)^(-exponent (n+1)))^2 := by
      intro j
      rw [factor_square]
      simpa only [ψ,error_shift,zero_add,s] using ih j
    intro k
    have hh := actual_restart_printed D hCa N hN ψ hψ (flow D s u)
      ((N : ℝ)^(-exponent (n+1))) (Real.rpow_nonneg (by positivity) _)
      (factor_ge_inverse N (n+1) hN) hi k δ hδ hs
    have hK := rateConstant_ge_one D.a (errorSum D.A) (stepTime D.a (collisionSum D.A D.a))
    have hR : 0 ≤ rateConstant D.a (errorSum D.A) (stepTime D.a (collisionSum D.A D.a))*
        Real.exp (D.a*((k+1 : ℕ) : ℝ))*(N : ℝ)^(-exponent (n+1)) := by positivity
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
    rw [ENNReal.toReal_ofReal hR] at hr
    change error D N ψ (flow D s u) (k+1) δ ≤ _ at hr
    dsimp only [ψ] at hr
    rw [error_shift] at hr
    have he : δ+s=((n+1+1 : ℕ) : ℝ)*δ := by dsimp [s];push_cast;ring
    rw [he] at hr
    exact hr

/-- Every finite nonnegative time has the printed exponent beta(T), with
exactly ceil(T/tau) restarts. -/
theorem actual_positive_time (D : ClassicalData H) (hCa : collisionSum D.A D.a ≠ 0)
    (N : ℕ) (hN : 0 < N) (u : Sphere H) (k : ℕ)
    (T t : ℝ) (hT : 0 ≤ T) (ht : 0 ≤ t) (htT : t ≤ T) :
    traceNorm (extendedMarginal D.A N (k+1) t (productVector N u.val)-
      coherentProjector (k+1) (trajectory D u t)) ≤
      ENNReal.ofReal (rateConstant D.a (errorSum D.A) (stepTime D.a (collisionSum D.A D.a))*
        Real.exp (D.a*((k+1 : ℕ) : ℝ))*
        (N : ℝ)^(-rateExponent (stepTime D.a (collisionSum D.A D.a)) T)) := by
  let τ := stepTime D.a (collisionSum D.A D.a)
  let m := max 1 (⌈T/τ⌉₊)
  have hm : 1 ≤ m := le_max_left _ _
  have hmp : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hδ : 0 ≤ t/(m : ℝ) := div_nonneg ht hmp.le
  have hstep : t/(m : ℝ) ≤ τ :=
    (div_le_div_of_nonneg_right htT hmp.le).trans
      (ceiling_subdivision (source_stepTime_pos D hCa) hT).2.2
  have he : m-1+1=m := Nat.sub_add_cancel hm
  have hh := actual_grid D hCa N hN u (t/(m : ℝ)) hδ hstep (m-1) k
  rw [he,mul_div_cancel₀ t (ne_of_gt hmp)] at hh
  have hex : exponent (m-1)=rateExponent τ T := by
    unfold exponent rateExponent
    congr 1
    have hcast : ((m-1 : ℕ) : ℝ)=(m : ℝ)-1 := by rw [Nat.cast_sub hm,Nat.cast_one]
    rw [hcast]
    dsimp [m]
    push_cast
    ring
  rw [hex] at hh
  have hfin := extendedMarginal_error_le_two D.A D.selfAdjoint N (k+1) t
    (productVector N u.val) (by rw [productVector_norm,u.property,one_pow])
    (trajectory D u t) ((trajectory_spec D u).2.2.1 t).1
  rw [← ENNReal.ofReal_toReal (ne_top_of_le_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hfin)]
  exact ENNReal.ofReal_le_ofReal hh

end QuantumNLS.Prop001RtwentyGlobal

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001RtwentyGlobal" then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      if n.toString == ("QuantumNLS.Prop001.HeldGP" ++ "14Tonelli") then
        throwError "Rejected GP14 wrapper dependency"
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
  Lean.logInfo m!"Prop001RtwentyGlobal audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."






#print axioms QuantumNLS.Prop001RtwentyGlobal.exponent_zero
#print axioms QuantumNLS.Prop001RtwentyGlobal.exponent_pos
#print axioms QuantumNLS.Prop001RtwentyGlobal.exponent_le_one
#print axioms QuantumNLS.Prop001RtwentyGlobal.exponent_half
#print axioms QuantumNLS.Prop001RtwentyGlobal.factor_square
#print axioms QuantumNLS.Prop001RtwentyGlobal.factor_ge_inverse
#print axioms QuantumNLS.Prop001RtwentyGlobal.actual_grid
#print axioms QuantumNLS.Prop001RtwentyGlobal.actual_positive_time

end

-- Namespace fragment: Prop001RtwentyScheduleRate
/-! Printed-constant estimates for actual positive schedules. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
open Filter Topology MeasureTheory
open scoped BigOperators ENNReal
namespace QuantumNLS.Prop001RtwentyScheduleRate
open TraceClass TensorCarrier Prop001 Prop001RthirteenSeries Prop001RseventeenContinuity
  Prop001RtwentyIteration Prop001RtwentyAssembly Prop001RtwentyFlow
  Prop001RtwentyBudget Prop001RtwentySigns Prop001RtwentyComparison
  Prop001RtwentySchedule Prop001RtwentySplit Prop001RtwentyRestart Prop001RtwentyGlobal
  Prop001RtwentyRemainder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def zeroData (B : NormBudget) : ClassicalData H where
  A _ := 0
  selfAdjoint n := by
    change (0 : SymSector ℂ H (n+1) →L[ℂ] SymSector ℂ H (n+1)).adjoint=0
    exact map_zero _
  a := B.a
  a_pos := B.a_pos
  cubic := by simp only [ContinuousLinearMap.opNorm_zero,mul_zero];exact summable_zero
  exponential := by simp only [ContinuousLinearMap.opNorm_zero,mul_zero,zero_mul];exact summable_zero

theorem budget_C0_nonneg (B : NormBudget) : 0 ≤ B.C0 :=
  mul_nonneg (by norm_num) (tsum_nonneg (fun n => mul_nonneg (by positivity) (B.nonneg n)))

theorem budget_step (B : NormBudget) (hCa : B.Ca ≠ 0) :
    0 < B.tau ∧ B.Ca*B.tau=B.a/4 := by
  have hc : 0 < B.Ca := lt_of_le_of_ne (budget_nonneg B) hCa.symm
  refine ⟨stepTime_pos B.a_pos hc,?_⟩
  unfold NormBudget.tau stepTime
  field_simp

theorem short_scale (B : NormBudget) (hCa : B.Ca ≠ 0) (s : ℝ) (_hs : 0 ≤ s) (hst : s ≤ B.tau) :
    B.a/2+B.Ca*s ≤ B.a ∧ s*B.Ca < B.a := by
  have hh := mul_le_mul_of_nonneg_left hst (budget_nonneg B)
  rw [(budget_step B hCa).2] at hh
  have ha := B.a_pos
  constructor <;> nlinarith

/-- Exact all-rank product initial estimate in a half analytic scale. -/
theorem product_initial_half (B : NormBudget) (N : ℕ) (hN : 0 < N) (u : Sphere H) :
    ∀ j,pureError N (productVector N u.val) u (j+1) ≤
      (2/(B.a*N))*Real.exp (B.a/2*((j+1 : ℕ) : ℝ)) := by
  intro j
  have hh := actual_product_initial (zeroData B) N hN u j
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  have hj : (0 : ℝ) ≤ ((j+1 : ℕ) : ℝ)/N := by positivity
  dsimp only [errorKernel] at hr
  rw [ENNReal.toReal_ofReal (error_nonneg (zeroData B) N (productVector N u.val) u (j+1) 0),
    ENNReal.toReal_ofReal hj,error_initial_pure] at hr
  have he := exp_rank_loss 0 (B.a/2) ((j+1 : ℕ) : ℝ) (by have ha := B.a_pos;positivity)
  simp only [zero_mul,Real.exp_zero,mul_one,zero_add] at he
  have hex : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hden : B.a/2 ≤ B.a/2*Real.exp 1 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hex (half_pos B.a_pos).le
  have he' := div_le_div_of_nonneg_left (Real.exp_pos (B.a/2*((j+1 : ℕ) : ℝ))).le (by have ha := B.a_pos;positivity) hden
  have hJ := div_le_div_of_nonneg_right (he.trans he') (show (0:ℝ) ≤ N by positivity)
  apply hr.trans
  convert hJ using 1
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- Every short positive schedule has the original exponent one; switches
spend elapsed time, rather than a restart at each list entry. -/
theorem first_schedule (B : NormBudget) (hCa : B.Ca ≠ 0)
    (S : List (ClassicalData H × ℝ)) (hS : Dominates B S) (hpos : Positive S)
    (N : ℕ) (hN : 0 < N) (u : Sphere H) (hstep : elapsed S ≤ B.tau) :
    ∀ j,pureError N (quantumSegments N S (productVector N u.val)) (classicalSegments S u) (j+1) ≤
      B.D*Real.exp (B.a*((j+1 : ℕ) : ℝ))/N := by
  have ha := B.a_pos
  have hC0 := budget_C0_nonneg B
  have hD := rateConstant_ge_one B.a B.C0 B.tau
  change 1 ≤ B.D at hD
  have htime := elapsed_nonneg S
  obtain ⟨hscale,hsmall⟩ := short_scale B hCa (elapsed S) htime hstep
  have hh := positive_schedule_barrier B S hS hpos N hN (productVector N u.val)
    (by rw [productVector_norm,u.property,one_pow]) u (2/(B.a*N)) (B.a/2)
    (by positivity) le_rfl hscale hsmall (product_initial_half B N hN u)
  have hCoeff : 2/(B.a*N)+(4*B.C0/B.a^2/N)*elapsed S ≤ B.D/N := by
    have hA := mul_le_mul_of_nonneg_left hstep
      (show 0 ≤ 4*B.C0/B.a^2/N by positivity)
    have hD : 4/B.a+8*B.C0*B.tau/B.a^2 ≤ B.D :=
      (le_max_left _ _).trans (le_max_right _ _)
    have hD' := div_le_div_of_nonneg_right hD (show (0:ℝ) ≤ N by positivity)
    have htau := (budget_step B hCa).1.le
    have hbudget : 0 ≤ B.C0*B.tau/B.a^2/N := by positivity
    have hposA : 0 ≤ 2/(B.a*N) := by positivity
    simp only [div_eq_mul_inv,mul_inv_rev] at hA hD' hbudget hposA ⊢
    nlinarith [hA]
  intro j
  apply (hh j).trans
  have hq : B.a/2+B.Ca*elapsed S ≤ B.a := hscale
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hq (show (0:ℝ) ≤ (j+1 : ℕ) by positivity))
  have hv := mul_le_mul hCoeff he (Real.exp_pos _).le (by positivity : 0 ≤ B.D/N)
  convert hv using 1
  ring

/-- Restart an arbitrary normalized actual schedule state with the unchanged
printed D, tau and E. -/
theorem restart_schedule (B : NormBudget) (hCa : B.Ca ≠ 0)
    (S : List (ClassicalData H × ℝ)) (hS : Dominates B S) (hpos : Positive S)
    (N : ℕ) (hN : 0 < N) (ψ : SymSector ℂ H N) (hψ : ‖ψ‖=1)
    (u : Sphere H) (x : ℝ) (hx : 0 ≤ x) (hNx : 1/(N : ℝ) ≤ x)
    (hstep : elapsed S ≤ B.tau)
    (hi : ∀ j,pureError N ψ u (j+1) ≤ B.D*Real.exp (B.a*((j+1 : ℕ) : ℝ))*x^2) :
    ∀ j,pureError N (quantumSegments N S ψ) (classicalSegments S u) (j+1) ≤
      B.D*Real.exp (B.a*((j+1 : ℕ) : ℝ))*x := by
  have ha := B.a_pos
  have hC0 := budget_C0_nonneg B
  have hD : 1 ≤ B.D := rateConstant_ge_one _ _ _
  have hD0 : 0 ≤ B.D := by linarith
  have htime := elapsed_nonneg S
  obtain ⟨hscale,hsmall⟩ := short_scale B hCa (elapsed S) htime hstep
  have hi0 : ∀ j,error (zeroData B) N ψ u (j+1) 0 ≤
      B.D*Real.exp (B.a*((j+1 : ℕ) : ℝ))*x^2 := by
    simpa only [error_initial_pure] using hi
  have hi' := initial_interpolation (zeroData B) N ψ hψ u B.D x hD0 hx hi0
  simp only [error_initial_pure] at hi'
  have hh := positive_schedule_barrier B S hS hpos N hN ψ hψ u (Real.sqrt (2*B.D)*x) (B.a/2)
    (by positivity) le_rfl hscale hsmall hi'
  have htau := (budget_step B hCa).1.le
  have hE : 0 ≤ B.E := by unfold NormBudget.E forcingConstant;positivity
  have hCoeff : Real.sqrt (2*B.D)*x+(4*B.C0/B.a^2/N)*elapsed S ≤ B.D*x := by
    have hA := mul_le_mul_of_nonneg_left hstep
      (show 0 ≤ 4*B.C0/B.a^2/N by positivity)
    have hE0 : (4*B.C0/B.a^2/N)*B.tau=B.E/N := by unfold NormBudget.E forcingConstant;ring
    rw [hE0] at hA
    have hB := mul_le_mul_of_nonneg_left hNx hE
    have hB' : B.E/N ≤ B.E*x := by simpa only [div_eq_mul_inv,one_mul] using hB
    have hclosed := rateConstant_restart (a := B.a) hC0 (budget_step B hCa).1.le
    change 2*Real.sqrt (2*B.D)+B.E ≤ B.D at hclosed
    have hC := mul_le_mul_of_nonneg_right hclosed hx
    nlinarith [mul_nonneg (Real.sqrt_nonneg (2*B.D)) hx]
  intro j
  apply (hh j).trans
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hscale (show (0:ℝ) ≤ (j+1 : ℕ) by positivity))
  have hv := mul_le_mul hCoeff he (Real.exp_pos _).le (by positivity : 0 ≤ B.D*x)
  convert hv using 1
  ring

end QuantumNLS.Prop001RtwentyScheduleRate

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001RtwentyScheduleRate" then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      if n.toString == ("QuantumNLS.Prop001.HeldGP" ++ "14Tonelli") then
        throwError "Rejected GP14 wrapper dependency"
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
  Lean.logInfo m!"Prop001RtwentyScheduleRate audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."






#print axioms QuantumNLS.Prop001RtwentyScheduleRate.budget_step
#print axioms QuantumNLS.Prop001RtwentyScheduleRate.short_scale
#print axioms QuantumNLS.Prop001RtwentyScheduleRate.product_initial_half
#print axioms QuantumNLS.Prop001RtwentyScheduleRate.first_schedule
#print axioms QuantumNLS.Prop001RtwentyScheduleRate.restart_schedule

end

-- Namespace fragment: Prop001RtwentyForward
/-! Replace signed schedule segments by equal forward evolutions. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
open scoped BigOperators ENNReal
namespace QuantumNLS.Prop001RtwentyForward
open TraceClass TensorCarrier Prop001 Prop001RtwentyAssembly Prop001RtwentySigns
  Prop001RtwentySplit
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def forwardData (D : ClassicalData H) (t : ℝ) : ClassicalData H :=
  if 0 ≤ t then D else reverseData D

def forwardSchedule (S : List (ClassicalData H × ℝ)) : List (ClassicalData H × ℝ) :=
  S.map (fun p => (forwardData p.1 p.2,|p.2|))

theorem forward_quantum (D : ClassicalData H) (N : ℕ) (t : ℝ) :
    quantumEvolution (forwardData D t).A N |t|=quantumEvolution D.A N t := by
  by_cases ht : 0 ≤ t
  · simp only [forwardData,ite_eq_left ht,abs_of_nonneg ht]
  · simp only [forwardData,ite_eq_right ht,abs_of_neg (lt_of_not_ge ht),reverse_quantum,neg_neg]

theorem forward_flow (D : ClassicalData H) (t : ℝ) (u : Sphere H) :
    flow (forwardData D t) |t| u=flow D t u := by
  by_cases ht : 0 ≤ t
  · simp only [forwardData,ite_eq_left ht,abs_of_nonneg ht]
  · apply Subtype.ext
    simp only [forwardData,ite_eq_right ht,abs_of_neg (lt_of_not_ge ht),flow,reverse_trajectory,neg_neg]

theorem forward_dominates (B : NormBudget) (S : List (ClassicalData H × ℝ))
    (hS : Dominates B S) : Dominates B (forwardSchedule S) := by
  intro p hp n
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  have hh := hS q hq n
  by_cases ht : 0 ≤ q.2
  · simpa only [forwardData,ite_eq_left ht] using hh
  · simpa only [forwardData,ite_eq_right ht,reverseData,ContinuousLinearMap.opNorm_neg] using hh

theorem forward_positive (S : List (ClassicalData H × ℝ)) : Positive (forwardSchedule S) := by
  intro p hp
  obtain ⟨q,_,rfl⟩ := List.mem_map.mp hp
  exact abs_nonneg _

theorem forward_elapsed (S : List (ClassicalData H × ℝ)) : elapsed (forwardSchedule S)=elapsed S := by
  simp only [elapsed,forwardSchedule,List.map_map,Function.comp_def,abs_abs]

theorem forward_quantumSegments (N : ℕ) (S : List (ClassicalData H × ℝ)) :
    quantumSegments N (forwardSchedule S)=quantumSegments N S := by
  induction S with
  | nil => rfl
  | cons p S ih =>
    change quantumSegments N ((forwardData p.1 p.2,|p.2|)::forwardSchedule S)=quantumSegments N (p::S)
    simp only [quantumSegments,forward_quantum,ih]

theorem forward_classicalSegments (S : List (ClassicalData H × ℝ)) (u : Sphere H) :
    classicalSegments (forwardSchedule S) u=classicalSegments S u := by
  induction S generalizing u with
  | nil => rfl
  | cons p S ih =>
    simp only [forwardSchedule,List.map_cons,classicalSegments,forward_flow]
    exact ih (flow p.1 p.2 u)

end QuantumNLS.Prop001RtwentyForward

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001RtwentyForward" then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      if n.toString == ("QuantumNLS.Prop001.HeldGP" ++ "14Tonelli") then
        throwError "Rejected GP14 wrapper dependency"
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
  Lean.logInfo m!"Prop001RtwentyForward audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."






#print axioms QuantumNLS.Prop001RtwentyForward.forward_quantum
#print axioms QuantumNLS.Prop001RtwentyForward.forward_flow
#print axioms QuantumNLS.Prop001RtwentyForward.forward_dominates
#print axioms QuantumNLS.Prop001RtwentyForward.forward_positive
#print axioms QuantumNLS.Prop001RtwentyForward.forward_elapsed
#print axioms QuantumNLS.Prop001RtwentyForward.forward_quantumSegments
#print axioms QuantumNLS.Prop001RtwentyForward.forward_classicalSegments

end

-- Namespace fragment: Prop001RtwentyTheorem
/-! Global propagation on arbitrary finite signed schedules, with one common
norm sequence and the exact printed constants. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
open Filter Topology MeasureTheory
open scoped BigOperators ENNReal
namespace QuantumNLS.Prop001RtwentyTheorem
open TraceClass TensorCarrier Prop001 Prop001RthirteenSeries Prop001RseventeenContinuity
  Prop001RtwentyIteration Prop001RseventeenVolterra Prop001RtwentyAssembly Prop001RtwentyFlow
  Prop001RtwentyBudget Prop001RtwentySchedule Prop001RtwentySplit
  Prop001RtwentyScheduleRate Prop001RtwentyGlobal Prop001RtwentyForward
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Induction on elapsed-time blocks, allowing cuts inside actual segments. -/
theorem positive_schedule_grid (B : NormBudget) (hCa : B.Ca ≠ 0)
    (N : ℕ) (hN : 0 < N) (u : Sphere H) :
    ∀ n (S : List (ClassicalData H × ℝ)),Dominates B S → Positive S →
      elapsed S ≤ ((n+1 : ℕ) : ℝ)*B.tau →
      ∀ j,pureError N (quantumSegments N S (productVector N u.val)) (classicalSegments S u) (j+1) ≤
        B.D*Real.exp (B.a*((j+1 : ℕ) : ℝ))*(N : ℝ)^(-exponent n) := by
  intro n
  induction n with
  | zero =>
    intro S hS hpos hstep j
    simpa only [exponent_zero,Real.rpow_neg_one,div_eq_mul_inv] using
      first_schedule B hCa S hS hpos N hN u (by simpa only [Nat.zero_add,Nat.cast_one,one_mul] using hstep) j
  | succ n ih =>
    intro S hS hpos hstep
    let t := min (elapsed S) (((n+1 : ℕ) : ℝ)*B.tau)
    have ht : 0 ≤ t := le_min (elapsed_nonneg S) (by have htau := (budget_step B hCa).1;positivity)
    have htS : t ≤ elapsed S := min_le_left _ _
    obtain ⟨L,K,hL,hK,hL0,hK0,hLt,hKt,hQ,hC⟩ := split_positive B S hS hpos t ht htS
    have hLt' : elapsed L ≤ ((n+1 : ℕ) : ℝ)*B.tau := by rw [hLt];exact min_le_right _ _
    have hKt' : elapsed K ≤ B.tau := by
      rw [hKt]
      dsimp [t]
      by_cases hcut : elapsed S ≤ ((n+1 : ℕ) : ℝ)*B.tau
      · rw [min_eq_left hcut,sub_self]
        exact (budget_step B hCa).1.le
      · rw [min_eq_right (le_of_not_ge hcut)]
        push_cast at hstep ⊢
        nlinarith
    let ψ := quantumSegments N L (productVector N u.val)
    let v := classicalSegments L u
    have hψ : ‖ψ‖=1 := (quantumSegments_norm N L (productVector N u.val)).trans
      (by rw [productVector_norm,u.property,one_pow])
    have hi : ∀ j,pureError N ψ v (j+1) ≤
        B.D*Real.exp (B.a*((j+1 : ℕ) : ℝ))*((N : ℝ)^(-exponent (n+1)))^2 := by
      intro j
      rw [factor_square]
      exact ih L hL hL0 hLt' j
    have hh := restart_schedule B hCa K hK hK0 N hN ψ hψ v ((N : ℝ)^(-exponent (n+1)))
      (Real.rpow_nonneg (by positivity) _) (factor_ge_inverse N (n+1) hN) hKt' hi
    intro j
    rw [hQ N,hC u,quantumSegments_append,classicalSegments_append]
    exact hh j

/-- The printed ceiling controls arbitrary positive schedules and every prefix. -/
theorem positive_schedule_rate (B : NormBudget) (hCa : B.Ca ≠ 0)
    (S : List (ClassicalData H × ℝ)) (hS : Dominates B S) (hpos : Positive S)
    (N : ℕ) (hN : 0 < N) (u : Sphere H) (T : ℝ) (_hT : 0 ≤ T) (ht : elapsed S ≤ T) :
    ∀ j,pureError N (quantumSegments N S (productVector N u.val)) (classicalSegments S u) (j+1) ≤
      B.rate (j+1) N T := by
  let m := max 1 (⌈T/B.tau⌉₊)
  have hm : 1 ≤ m := le_max_left _ _
  have he : m-1+1=m := Nat.sub_add_cancel hm
  have hceil : T ≤ (m : ℝ)*B.tau := by
    have hh := Nat.le_ceil (T/B.tau)
    have hc : (⌈T/B.tau⌉₊ : ℝ) ≤ m := by exact_mod_cast le_max_right 1 (⌈T/B.tau⌉₊)
    have hmult := (div_le_iff₀ (budget_step B hCa).1).mp (hh.trans hc)
    nlinarith
  have hex : exponent (m-1)=rateExponent B.tau T := by
    unfold exponent rateExponent
    congr 1
    rw [Nat.cast_sub hm,Nat.cast_one]
    dsimp [m]
    push_cast
    ring
  intro j
  have hh := positive_schedule_grid B hCa N hN u (m-1) S hS hpos
    (by rw [he];exact ht.trans hceil) j
  simpa only [NormBudget.rate,hex] using hh

/-- The former second hypothesis is proved for actual finite schedules,
including either sign on every segment. -/
theorem nonzeroCaRate : NonzeroCaRate H := by
  intro B hCa S hS u N k hk T hT ht
  let ψ := quantumSegments N S (productVector N u.val)
  let v := classicalSegments S u
  have hψ : ‖ψ‖=1 := (quantumSegments_norm N S (productVector N u.val)).trans
    (by rw [productVector_norm,u.property,one_pow])
  have hpure : pureMarginal N k ψ=scheduleMarginal N k hk S (productVector N u.val) := by
    simp only [pureMarginal,dite_eq_left hk,ψ,scheduleMarginal]
  have hinit : extendedMarginal (zeroData B).A N k 0 ψ=pureMarginal N k ψ := by
    by_cases h : k ≤ N
    · simp only [extendedMarginal_of_le _ N k h,marginal,pureMarginal,dite_eq_left h,
        quantumEvolution,LinearTailPhysicalEvolution.evolution_zero,one_apply_eq_self]
    · simp only [extendedMarginal,pureMarginal,dite_eq_right h]
  cases k with
  | zero =>
    have hz := Prop001RseventeenZero.marginal_zero (zeroData B) N ψ hψ v.val 0
    rw [hinit] at hz
    change traceNorm (scheduleMarginal N 0 hk S (productVector N u.val)-coherentProjector 0 v.val) ≤ _
    rw [← hpure,hz,sub_self,Fidelity.traceNorm_zero]
    exact bot_le
  | succ j =>
    have hN : 0 < N := lt_of_lt_of_le (Nat.succ_pos _) hk
    have hf := positive_schedule_rate B hCa (forwardSchedule S) (forward_dominates B S hS)
      (forward_positive S) N hN u T hT (by rw [forward_elapsed];exact ht) j
    rw [forward_quantumSegments,forward_classicalSegments] at hf
    have he := traceNorm_error_eq (zeroData B) N ψ hψ v (j+1) 0
    rw [hinit,(trajectory_spec (zeroData B) v).1,error_initial_pure] at he
    change traceNorm (scheduleMarginal N (j+1) hk S (productVector N u.val)-coherentProjector (j+1) v.val) ≤ _
    rw [← hpure,he]
    exact ENNReal.ofReal_le_ofReal hf

/-- PROP-001 with exactly the printed Hilbert-space and kernel assumptions.
The actual nonnegative Tonelli exchange is proved, with no analytic hypothesis. -/
theorem PROP001 : BoundedPropagation H :=
  Prop001RtwentyAssembly.assemble_from_rate nonzeroCaRate


end QuantumNLS.Prop001RtwentyTheorem

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001RtwentyTheorem" then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      if n.toString == ("QuantumNLS.Prop001.HeldGP" ++ "14Tonelli") then
        throwError "Rejected GP14 wrapper dependency"
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
  unless seen.contains ``MeasureTheory.lintegral_prod &&
      seen.contains ``MeasureTheory.lintegral_prod_symm do
    throwError "Actual Tonelli proof must use both proved product integral theorems"
  Lean.logInfo m!"PROP001 closure: rejected wrapper absent; lintegral_prod and lintegral_prod_symm present."
  Lean.logInfo m!"Prop001RtwentyTheorem audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."






#print axioms QuantumNLS.Prop001RtwentyTheorem.positive_schedule_grid
#print axioms QuantumNLS.Prop001RtwentyTheorem.positive_schedule_rate
#print axioms QuantumNLS.Prop001RtwentyTheorem.nonzeroCaRate
#print axioms QuantumNLS.Prop001RtwentyTheorem.PROP001

#check @QuantumNLS.Prop001RtwentyTheorem.PROP001

end
