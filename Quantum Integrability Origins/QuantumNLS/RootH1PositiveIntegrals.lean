import QuantumNLS.RootH1PositiveAlgebra
import QuantumNLS.RootH1PositiveChain

/-! Integrated positive identity: the cross terms are proved to vanish. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory Set Filter Topology ComplexConjugate
open QuantumNLS.RootH1PositiveAlgebra QuantumNLS.RootH1PositiveChain
namespace QuantumNLS.RootH1PositiveIntegrals

def w1 (κ : ℝ) (g : ℝ → ℂ) (t : ℝ) : ℝ := ‖g t‖^2/(1-κ*‖g t‖^2)
def w2 (κ : ℝ) (g : ℝ → ℂ) (t : ℝ) : ℝ := ‖g t‖^2/(1-κ*‖g t‖^2)^2
def w4 (κ : ℝ) (g : ℝ → ℂ) (t : ℝ) : ℝ := ‖g t‖^4/(1-κ*‖g t‖^2)^2

lemma den_bounds {κ : ℝ} (hκ : 0 ≤ κ) {r : ℂ} (hb : κ*‖r‖^2 ≤ 1/4) :
    3/4 ≤ 1-κ*‖r‖^2 ∧ 15/16 ≤ 1-κ^2*‖r‖^4 := by
  have hn : 0 ≤ κ*‖r‖^2 := mul_nonneg hκ (sq_nonneg _)
  have hsq := pow_le_pow_left₀ hn hb 2
  constructor
  · linarith
  · nlinarith

lemma den_ne {κ : ℝ} (hκ : 0 ≤ κ) {r : ℂ} (hb : κ*‖r‖^2 ≤ 1/4) :
    1-κ*‖r‖^2 ≠ 0 ∧ 1-κ^2*‖r‖^4 ≠ 0 := by
  have hh := den_bounds hκ hb
  constructor <;> linarith [hh.1,hh.2]

lemma continuous_weights {L κ : ℝ} (hκ : 0 ≤ κ) {g : ℝ → ℂ}
    (hc : ContinuousOn g (Icc 0 L))
    (hb : ∀ t ∈ Icc (0:ℝ) L, κ*‖g t‖^2 ≤ 1/4) :
    ContinuousOn (w1 κ g) (Icc 0 L) ∧ ContinuousOn (w2 κ g) (Icc 0 L) ∧
    ContinuousOn (w4 κ g) (Icc 0 L) := by
  have hd : ContinuousOn (fun t => (1-κ*‖g t‖^2)⁻¹) (Icc 0 L) := by
    apply (continuousOn_const.sub (continuousOn_const.mul (hc.norm.pow 2))).inv₀
    intro t ht
    change 1-κ*‖g t‖^2 ≠ 0
    exact (den_ne hκ (hb t ht)).1
  refine ⟨?_,?_,?_⟩
  · unfold w1
    simpa only [div_eq_mul_inv,Pi.mul_def,Pi.pow_def] using (hc.norm.pow 2).mul hd
  · unfold w2
    simpa only [div_eq_mul_inv,inv_pow,Pi.mul_def,Pi.pow_def] using (hc.norm.pow 2).mul (hd.pow 2)
  · unfold w4
    simpa only [div_eq_mul_inv,inv_pow,Pi.mul_def,Pi.pow_def] using (hc.norm.pow 4).mul (hd.pow 2)

lemma continuous_memLp {L : ℝ} {f : ℝ → ℂ} (hf : ContinuousOn f (Icc 0 L)) :
    MemLp f 2 (volume.restrict (Icc 0 L)) := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine MemLp.of_bound (hf.aestronglyMeasurable measurableSet_Icc) C ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht using hC t ht

lemma aux_memLp {L κ Y : ℝ} (hκ : 0 ≤ κ) {g d f : ℝ → ℂ}
    (hc : ContinuousOn g (Icc 0 L)) (hf : MemLp f 2 (volume.restrict (Icc 0 L)))
    (hb : ∀ t ∈ Icc (0:ℝ) L, κ*‖g t‖^2 ≤ 1/4)
    (he : ∀ᵐ t ∂volume.restrict (Icc 0 L),
      d t = f t-(Y:ℂ)*g t-(κ:ℂ)*conj (f t)*(g t)^2) :
    MemLp (fun t => aux κ (g t) (d t)) 2 (volume.restrict (Icc 0 L)) := by
  let B : ℝ → ℂ := fun t => (Y:ℂ)*g t/((1-κ*‖g t‖^2:ℝ):ℂ)
  have hcB : ContinuousOn B (Icc 0 L) := by
    apply (continuousOn_const.mul hc).div₀
      (Complex.continuous_ofReal.comp_continuousOn
        (continuousOn_const.sub (continuousOn_const.mul (hc.norm.pow 2))))
    intro t ht
    change ((1-κ*‖g t‖^2:ℝ):ℂ) ≠ 0
    exact_mod_cast (den_ne hκ (hb t ht)).1
  refine MemLp.ae_eq ?_ (hf.sub (continuous_memLp hcB))
  filter_upwards [he,ae_restrict_mem measurableSet_Icc] with t ht hti
  have hh := split (den_ne hκ (hb t hti)).1 (den_ne hκ (hb t hti)).2 ht
  change f t-B t = _
  dsimp [B]
  linear_combination hh

/-- The printed pairing and mass splits, including all integrability facts. -/
theorem splits {L κ Y : ℝ} (hL : 0 ≤ L) (hκ : 0 < κ) {g d f : ℝ → ℂ}
    (hg : AbsolutelyContinuousOnInterval g 0 L) (hper : g L = g 0)
    (hf : MemLp f 2 (volume.restrict (Icc 0 L)))
    (hd : MemLp d 2 (volume.restrict (Icc 0 L)))
    (hder : ∀ᵐ t ∂volume.restrict (Icc 0 L), HasDerivAt g (d t) t)
    (he : ∀ᵐ t ∂volume.restrict (Icc 0 L),
      d t = f t-(Y:ℂ)*g t-(κ:ℂ)*conj (f t)*(g t)^2)
    (hb : ∀ t ∈ Icc (0:ℝ) L, κ*‖g t‖^2 ≤ 1/4) :
    (∫ t in (0:ℝ)..L, (conj (f t)*g t).re) = Y*(∫ t in (0:ℝ)..L, w1 κ g t) ∧
    (∫ t in (0:ℝ)..L, ‖f t‖^2) =
      Y^2*(∫ t in (0:ℝ)..L, w2 κ g t)+(∫ t in (0:ℝ)..L, ‖aux κ (g t) (d t)‖^2) ∧
    IntervalIntegrable (fun t => ‖aux κ (g t) (d t)‖^2) volume 0 L := by
  have hc : ContinuousOn g (Icc 0 L) := by simpa [uIcc_of_le hL] using hg.continuousOn
  have hiD : IntervalIntegrable d volume 0 L :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hL).mpr (hd.integrable (by norm_num))
  have hw := continuous_weights hκ.le hc hb
  have hw1 : IntervalIntegrable (w1 κ g) volume 0 L := hw.1.intervalIntegrable_of_Icc hL
  have hw2 : IntervalIntegrable (w2 κ g) volume 0 L := hw.2.1.intervalIntegrable_of_Icc hL
  have hA : IntervalIntegrable (fun t => ‖aux κ (g t) (d t)‖^2) volume 0 L :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hL).mpr
      ((aux_memLp hκ.le hc hf hb he).integrable_norm_pow (by decide))
  have hq := chain_integrable hL hg hiD hb
  have hz := cancellations hL hκ hg hper hiD hder hb
  have he1 : (∫ t in (0:ℝ)..L, (conj (f t)*g t).re) =
      ∫ t in (0:ℝ)..L, Y*w1 κ g t+(conj (g t)*d t).re/(1-κ*‖g t‖^2) := by
    apply intervalIntegral.integral_congr_ae
    have hh := (ae_restrict_iff' measurableSet_Icc).mp he
    filter_upwards [hh] with t ht hti
    have htI : t ∈ Icc (0:ℝ) L := by simpa [uIcc_of_le hL] using uIoc_subset_uIcc hti
    simpa only [w1,mul_div_assoc] using pairing_split (den_ne hκ.le (hb t htI)).1 (den_ne hκ.le (hb t htI)).2 (ht htI)
  have he2 : (∫ t in (0:ℝ)..L, ‖f t‖^2) =
      ∫ t in (0:ℝ)..L, (Y^2*w2 κ g t+‖aux κ (g t) (d t)‖^2)+
        (2*Y)*((conj (g t)*d t).re/(1-κ*‖g t‖^2)^2) := by
    apply intervalIntegral.integral_congr_ae
    have hh := (ae_restrict_iff' measurableSet_Icc).mp he
    filter_upwards [hh] with t ht hti
    have htI : t ∈ Icc (0:ℝ) L := by simpa [uIcc_of_le hL] using uIoc_subset_uIcc hti
    have hx := norm_split (den_ne hκ.le (hb t htI)).1 (den_ne hκ.le (hb t htI)).2 (ht htI)
    dsimp [w2]
    convert hx using 1
    ring
  rw [intervalIntegral.integral_add (hw1.const_mul Y) hq.1,
    intervalIntegral.integral_const_mul,hz.1,add_zero] at he1
  rw [intervalIntegral.integral_add ((hw2.const_mul (Y^2)).add hA) (hq.2.const_mul (2*Y)),
    intervalIntegral.integral_add (hw2.const_mul (Y^2)) hA,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,hz.2,mul_zero,add_zero] at he2
  exact ⟨he1,he2,hA⟩

lemma weight_difference (κ : ℝ) (r : ℂ) :
    ‖r‖^2/(1-κ*‖r‖^2)^2-‖r‖^2/(1-κ*‖r‖^2) = κ*‖r‖^4/(1-κ*‖r‖^2)^2 := by
  field_simp
  ring

#print axioms den_bounds
#print axioms den_ne
#print axioms continuous_weights
#print axioms continuous_memLp
#print axioms aux_memLp
#print axioms splits
#print axioms weight_difference
end QuantumNLS.RootH1PositiveIntegrals

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootH1PositiveIntegrals." ||
        n.toString.startsWith "_private.QuantumNLS.RootH1PositiveIntegrals." then
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
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
