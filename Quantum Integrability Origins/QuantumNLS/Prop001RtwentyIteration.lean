import QuantumNLS.Prop001RseventeenVolterra
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! Actual measurable scalar kernels and Tonelli iteration from proved Mathlib product integrals. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1400000
open Filter Topology MeasureTheory
open scoped BigOperators ENNReal
namespace QuantumNLS.Prop001RtwentyIteration
open TraceClass TraceIdeal TensorCarrier Prop001 Prop001RthirteenSeries
  Prop001RseventeenContinuity Prop001RseventeenVolterra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Corrected GP-14 applied directly to the literal measurable error kernel. -/
theorem actual_rank_time_exchange (D : ClassicalData H)
    (N : ℕ) (ψ : SymSector ℂ H N) (hψ : ‖ψ‖=1) (u : Sphere H)
    (k : ℕ) (a b : ℝ) :
    (∫⁻ t in Set.Ioc a b,ENNReal.ofReal (collisionMajorant D N ψ u k t)) =
      ∑' n,∫⁻ t in Set.Ioc a b,
        ENNReal.ofReal ((2*((n+1 : ℕ) : ℝ)*((k+1 : ℕ) : ℝ)*‖D.A n‖)*
          error D N ψ u ((k+1)+n) t) := by
  have he (t : ℝ) : ENNReal.ofReal (collisionMajorant D N ψ u k t) =
      ∑' n, ENNReal.ofReal ((2*((n+1 : ℕ) : ℝ)*((k+1 : ℕ) : ℝ)*‖D.A n‖)*
        error D N ψ u ((k+1)+n) t) :=
    ENNReal.ofReal_tsum_of_nonneg
      (fun n => mul_nonneg (by positivity) (error_nonneg D N ψ u _ t))
      (Summable.of_norm_bounded (scalarBound_summable D k)
        (fun n => collision_scalar_term_bound D N ψ hψ u k n t))
  simp_rw [he]
  let f : ℕ × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal ((2*((p.1+1 : ℕ) : ℝ)*((k+1 : ℕ) : ℝ)*‖D.A p.1‖)*
      error D N ψ u ((k+1)+p.1) p.2)
  have hf : Measurable f := by
    apply measurable_from_prod_countable_right
    intro n
    change Measurable (fun t : ℝ => ENNReal.ofReal
      ((2*((n+1 : ℕ) : ℝ)*((k+1 : ℕ) : ℝ)*‖D.A n‖)*error D N ψ u ((k+1)+n) t))
    exact ENNReal.continuous_ofReal.measurable.comp
      (continuous_const.mul (error_continuous D N ψ hψ u ((k+1)+n))).measurable
  have hp := MeasureTheory.lintegral_prod
    (μ := (Measure.count : Measure ℕ)) (ν := volume.restrict (Set.Ioc a b)) f hf.aemeasurable
  have hs := MeasureTheory.lintegral_prod_symm
    (μ := (Measure.count : Measure ℕ)) (ν := volume.restrict (Set.Ioc a b)) f hf.aemeasurable
  rw [lintegral_count] at hp
  simp_rw [lintegral_count] at hs
  exact hs.symm.trans hp

/-- Positive scalar Duhamel operator, before taking any iteration limit. -/
def volterra (b : ℕ → ℝ≥0∞) (f : ℕ → ℝ → ℝ≥0∞) (k : ℕ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Set.Ioc 0 t,∑' n,b n*((k+1 : ℕ) : ℝ≥0∞)*f (k+n) s

theorem volterra_mono (b : ℕ → ℝ≥0∞) {f g : ℕ → ℝ → ℝ≥0∞}
    (h : ∀ k t,f k t ≤ g k t) : ∀ k t,volterra b f k t ≤ volterra b g k t := by
  intro k t
  apply lintegral_mono
  intro s
  exact ENNReal.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (h (k+n) s) (by positivity))

/-- Every finite substitution remains a measurable nonnegative scalar kernel. -/
theorem volterra_measurable (b : ℕ → ℝ≥0∞) (f : ℕ → ℝ → ℝ≥0∞)
    (hf : ∀ k,Measurable (f k)) (k : ℕ) : Measurable (volterra b f k) := by
  let g : ℝ × ℝ → ℝ≥0∞ := fun p => ∑' n,b n*((k+1 : ℕ) : ℝ≥0∞)*f (k+n) p.2
  have hg : Measurable g := Measurable.tsum (fun n =>
    measurable_const.mul ((hf (k+n)).comp measurable_snd))
  have hs : MeasurableSet {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ p.1} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst)
  have hi := (hg.indicator hs).lintegral_prod_right' (ν := (volume : Measure ℝ))
  convert hi using 1
  funext t
  rw [volterra,← lintegral_indicator measurableSet_Ioc]
  rfl

/-- Additivity needed for finite-depth substitutions, with measurability explicit. -/
theorem volterra_add (b : ℕ → ℝ≥0∞) (f g : ℕ → ℝ → ℝ≥0∞)
    (hf : ∀ k,Measurable (f k)) (k : ℕ) (t : ℝ) :
    volterra b (fun j s => f j s+g j s) k t = volterra b f k t+volterra b g k t := by
  unfold volterra
  simp_rw [mul_add,ENNReal.tsum_add]
  exact lintegral_add_left (Measurable.tsum (fun n => measurable_const.mul (hf (k+n)))) _

theorem volterra_mono_nonneg (b : ℕ → ℝ≥0∞) {f g : ℕ → ℝ → ℝ≥0∞}
    (h : ∀ k t,0 ≤ t → f k t ≤ g k t) : ∀ k t,volterra b f k t ≤ volterra b g k t := by
  intro k t
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact ENNReal.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (h (k+n) s hs.1.le) (by positivity))

/-- Literal finite number of Duhamel substitutions. -/
def iterate (b : ℕ → ℝ≥0∞) (f : ℕ → ℝ → ℝ≥0∞) : ℕ → ℕ → ℝ → ℝ≥0∞
  | 0 => f
  | n+1 => volterra b (iterate b f n)

def partialSum (b : ℕ → ℝ≥0∞) (g : ℕ → ℝ → ℝ≥0∞) : ℕ → ℕ → ℝ → ℝ≥0∞
  | 0 => fun _ _ => 0
  | n+1 => fun k t => g k t+volterra b (partialSum b g n) k t

theorem iterate_measurable (b : ℕ → ℝ≥0∞) (f : ℕ → ℝ → ℝ≥0∞)
    (hf : ∀ k,Measurable (f k)) : ∀ n k,Measurable (iterate b f n k) := by
  intro n
  induction n with
  | zero => exact hf
  | succ n ih => exact volterra_measurable b _ ih

theorem partial_measurable (b : ℕ → ℝ≥0∞) (g : ℕ → ℝ → ℝ≥0∞)
    (hg : ∀ k,Measurable (g k)) : ∀ n k,Measurable (partialSum b g n k) := by
  intro n
  induction n with
  | zero => exact fun _ => measurable_const
  | succ n ih => exact fun k => (hg k).add (volterra_measurable b _ ih k)

/-- Finite-depth scalar iteration with the actual unsubstituted remainder.
It does not assume a convergence estimate or a rate for that remainder. -/
theorem finite_depth (b : ℕ → ℝ≥0∞) (d g : ℕ → ℝ → ℝ≥0∞)
    (hg : ∀ k,Measurable (g k))
    (h : ∀ k t,0 ≤ t → d k t ≤ g k t+volterra b d k t) :
    ∀ n k t,0 ≤ t → d k t ≤ partialSum b g n k t+iterate b d n k t := by
  intro n
  induction n with
  | zero => intro k t _;simp only [partialSum,iterate,zero_add,le_refl]
  | succ n ih =>
    intro k t ht
    calc
      d k t ≤ g k t+volterra b d k t := h k t ht
      _ ≤ g k t+volterra b (fun j s => partialSum b g n j s+iterate b d n j s) k t :=
        add_le_add (le_refl (g k t)) (volterra_mono_nonneg b ih k t)
      _ = partialSum b g (n+1) k t+iterate b d (n+1) k t := by
        rw [volterra_add b _ _ (partial_measurable b g hg n)]
        simp only [partialSum,iterate,add_assoc]

/-- Source b_r, indexed by r-1. -/
def rankWeights (D : ClassicalData H) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (2*((n+1 : ℕ) : ℝ)*‖D.A n‖)

def errorKernel (D : ClassicalData H) (N : ℕ) (ψ : SymSector ℂ H N)
    (u : Sphere H) (k : ℕ) (t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (error D N ψ u (k+1) t)

def freeKernel (D : ClassicalData H) (N : ℕ) (ψ : SymSector ℂ H N)
    (u : Sphere H) (k : ℕ) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (error D N ψ u (k+1) 0+t*(errorSum D.A*((k+1 : ℕ) : ℝ)^2/N))

theorem volterra_error_eq (D : ClassicalData H) (N : ℕ) (ψ : SymSector ℂ H N)
    (hψ : ‖ψ‖=1) (u : Sphere H) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    volterra (rankWeights D) (errorKernel D N ψ u) k t =
      ENNReal.ofReal (∫ s in 0..t,collisionMajorant D N ψ u k s) := by
  have hi := (collisionMajorant_integrable D N ψ hψ u k 0 t).1
  rw [intervalIntegral.integral_of_le ht,ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun s => tsum_nonneg (fun n =>
      mul_nonneg (by positivity) (error_nonneg D N ψ u _ s))))]
  apply lintegral_congr
  intro r
  rw [collisionMajorant,ENNReal.ofReal_tsum_of_nonneg
    (fun n => mul_nonneg (by positivity) (error_nonneg D N ψ u _ r))
    (Summable.of_norm_bounded (scalarBound_summable D k)
      (fun n => collision_scalar_term_bound D N ψ hψ u k n r))]
  apply tsum_congr
  intro n
  have he : (k+n)+1=(k+1)+n := by omega
  simp only [rankWeights,errorKernel,he]
  rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

theorem actual_one_step (D : ClassicalData H) (N : ℕ) (ψ : SymSector ℂ H N)
    (hψ : ‖ψ‖=1) (u : Sphere H) (k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    errorKernel D N ψ u k t ≤ freeKernel D N ψ u k t+
      volterra (rankWeights D) (errorKernel D N ψ u) k t := by
  have h := error_Volterra_all D N k ψ hψ u ht
  rw [intervalIntegral.integral_add (collisionMajorant_integrable D N ψ hψ u k 0 t)
    intervalIntegrable_const,intervalIntegral.integral_const,sub_zero,smul_eq_mul] at h
  have hp : 0 ≤ ∫ s in 0..t,collisionMajorant D N ψ u k s :=
    intervalIntegral.integral_nonneg ht (fun s _ => tsum_nonneg (fun n =>
      mul_nonneg (by positivity) (error_nonneg D N ψ u _ s)))
  rw [volterra_error_eq D N ψ hψ u k ht]
  unfold errorKernel freeKernel
  rw [← ENNReal.ofReal_add (add_nonneg (error_nonneg D N ψ u _ 0)
    (mul_nonneg ht (div_nonneg (mul_nonneg (errorSum_nonneg D.A) (sq_nonneg _))
      (by positivity)))) hp]
  apply ENNReal.ofReal_le_ofReal
  convert h using 1;ring

/-- Actual finite-depth Duhamel inequality, with every scalar integrand
measurable and the unsubstituted error retained explicitly. -/
theorem actual_finite_depth (D : ClassicalData H) (N : ℕ) (ψ : SymSector ℂ H N)
    (hψ : ‖ψ‖=1) (u : Sphere H) (n k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    traceNorm (extendedMarginal D.A N (k+1) t ψ-coherentProjector (k+1) (trajectory D u t)) ≤
      partialSum (rankWeights D) (freeKernel D N ψ u) n k t+
        iterate (rankWeights D) (errorKernel D N ψ u) n k t := by
  rw [traceNorm_error_eq D N ψ hψ u _ t]
  apply finite_depth (rankWeights D) (errorKernel D N ψ u) (freeKernel D N ψ u)
    (fun j => ENNReal.continuous_ofReal.measurable.comp
      (continuous_const.add (continuous_id.mul continuous_const)).measurable)
    (actual_one_step D N ψ hψ u) n k t ht

/-- The source's all-rank initial-data bound on the literal product state. -/
theorem actual_product_initial (D : ClassicalData H) (N : ℕ) (hN : 0 < N)
    (u : Sphere H) (k : ℕ) :
    errorKernel D N (productVector N u.val) u k 0 ≤ ENNReal.ofReal (((k+1 : ℕ) : ℝ)/N) := by
  have hp : ‖productVector N u.val‖=1 := by rw [productVector_norm,u.property,one_pow]
  rw [errorKernel,← traceNorm_error_eq D N (productVector N u.val) hp u (k+1) 0,
    (trajectory_spec D u).1]
  exact extendedMarginal_initial_error_le D.A N (k+1) hN u.val u.property

end QuantumNLS.Prop001RtwentyIteration

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001RtwentyIteration" then
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
  Lean.logInfo m!"Prop001RtwentyIteration audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."






#print axioms QuantumNLS.Prop001RtwentyIteration.actual_rank_time_exchange
#print axioms QuantumNLS.Prop001RtwentyIteration.volterra
#print axioms QuantumNLS.Prop001RtwentyIteration.volterra_mono
#print axioms QuantumNLS.Prop001RtwentyIteration.volterra_measurable
#print axioms QuantumNLS.Prop001RtwentyIteration.volterra_add
#print axioms QuantumNLS.Prop001RtwentyIteration.volterra_mono_nonneg
#print axioms QuantumNLS.Prop001RtwentyIteration.iterate
#print axioms QuantumNLS.Prop001RtwentyIteration.partialSum
#print axioms QuantumNLS.Prop001RtwentyIteration.iterate_measurable
#print axioms QuantumNLS.Prop001RtwentyIteration.partial_measurable
#print axioms QuantumNLS.Prop001RtwentyIteration.finite_depth

#print axioms QuantumNLS.Prop001RtwentyIteration.rankWeights

#print axioms QuantumNLS.Prop001RtwentyIteration.errorKernel

#print axioms QuantumNLS.Prop001RtwentyIteration.freeKernel

#print axioms QuantumNLS.Prop001RtwentyIteration.volterra_error_eq

#print axioms QuantumNLS.Prop001RtwentyIteration.actual_one_step

#print axioms QuantumNLS.Prop001RtwentyIteration.actual_finite_depth

#print axioms QuantumNLS.Prop001RtwentyIteration.actual_product_initial
