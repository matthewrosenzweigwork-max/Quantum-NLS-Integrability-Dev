import QuantumNLS.Ext005PhysicalResolventR35b
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.Units

/-! Transfer the literal nonreal-resolvent strong-commutation convention to
real resolvents. Nearby nonreal resolvents are constructed by a Neumann
perturbation and converge in operator norm. No commuting real resolvents
or spectral identification are assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate LinearPMap Ring
open ContinuousLinearMap InnerProductSpace Set Filter
namespace QuantumNLS.Ext005ResolventPerturbR35b
open Ext005SourceHypothesesR114 Ext005GramConvergenceR112
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def nearby (R : H →L[ℂ] H) (d : ℂ) : H →L[ℂ] H := R * (1 - d • R)⁻¹ʳ

omit [CompleteSpace H] in
lemma nearby_resolves (T : H →ₗ.[ℂ] H) (z d : ℂ) (R : H →L[ℂ] H)
    (hR : Resolves T z R) (hu : IsUnit (1-d • R)) :
    Resolves T (z+d) (nearby R d) := by
  let U : H →L[ℂ] H := 1-d • R
  let V := U⁻¹ʳ
  have hUV : U * V = 1 := Ring.mul_inverse_cancel U hu
  have hVU : V * U = 1 := Ring.inverse_mul_cancel U hu
  have hRU : Commute R U := by
    change R * (1-d • R) = (1-d • R)*R
    simp only [mul_sub, sub_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc]
  have hRV : Commute R V := by
    rcases hu with ⟨u, hu⟩
    change Commute R (1-d • R)⁻¹ʳ
    rw [← hu, Ring.inverse_unit]
    apply Commute.units_inv_right
    simpa only [hu] using hRU
  constructor
  · intro x
    obtain ⟨hx, heq⟩ := hR.1 (V x)
    refine ⟨hx, ?_⟩
    have hux := congrArg (fun f : H →L[ℂ] H => f x) hUV
    change V x - d • R (V x) = x at hux
    change T ⟨R (V x), hx⟩ - (z+d) • R (V x) = x
    calc
      _ = (T ⟨R (V x), hx⟩ - z • R (V x)) - d • R (V x) := by module
      _ = _ := by rw [heq, hux]
  · intro u
    have hrv := congrArg (fun f : H →L[ℂ] H => f (T u - (z+d) • (u : H))) hRV.eq
    change R (V (T u - (z+d) • (u : H))) = V (R (T u - (z+d) • (u : H))) at hrv
    change R (V (T u - (z+d) • (u : H))) = (u : H)
    rw [hrv]
    have heq : R (T u - (z+d) • (u : H)) = U (u : H) := by
      have he : T u - (z+d) • (u : H) = (T u - z • (u : H)) - d • (u : H) := by module
      rw [he, map_sub, map_smul, hR.2 u]
      rfl
    rw [heq]
    exact congrArg (fun f : H →L[ℂ] H => f (u : H)) hVU

lemma nearby_tendsto (R : H →L[ℂ] H) :
    Tendsto (nearby R) (𝓝 0) (𝓝 R) := by
  have ht : Tendsto (fun d : ℂ => (1 : H →L[ℂ] H) - d • R) (𝓝 0) (𝓝 1) := by
    simpa only [id_eq, zero_smul, sub_zero] using tendsto_const_nhds.sub ((tendsto_id : Tendsto (fun d : ℂ => d) (𝓝 0) (𝓝 0)).smul_const R)
  have hi := (NormedRing.inverse_continuousAt (1 : (H →L[ℂ] H)ˣ)).tendsto.comp ht
  unfold nearby
  convert hi.const_mul R using 1 <;> simp only [Function.comp_def, Units.val_one, Ring.inverse_one, mul_one]

/-- Nonreal resolvent strong commutation implies commutation for any
existing real resolvents, via constructed nearby nonreal resolvents. -/
theorem stronglyCommute_real_resolvents (A B : H →ₗ.[ℂ] H)
    (hc : StronglyCommute A B) (z w : ℂ) (hz : z.im = 0) (hw : w.im = 0)
    (R S : H →L[ℂ] H) (hR : Resolves A z R) (hS : Resolves B w S) :
    R.comp S = S.comp R := by
  let d : ℕ → ℂ := fun n => (epsilon n : ℂ) * Complex.I
  have hd : Tendsto d atTop (𝓝 0) := by
    simpa only [Function.comp_def, d, Complex.ofReal_zero, zero_mul] using
      (Complex.continuous_ofReal.tendsto 0 |>.comp epsilon_tendsto).mul_const Complex.I
  have hn (T : H →L[ℂ] H) : ∀ᶠ n in atTop, ‖d n • T‖ < 1 := by
    have h : Tendsto (fun n => ‖d n • T‖) atTop (𝓝 0) := by
      simpa only [zero_smul, norm_zero] using (hd.smul_const T).norm
    exact h.eventually (gt_mem_nhds zero_lt_one)
  have he : ∀ᶠ n in atTop, (nearby R (d n)).comp (nearby S (d n)) =
      (nearby S (d n)).comp (nearby R (d n)) := by
    filter_upwards [hn R, hn S] with n hnr hns
    apply hc (z+d n) (w+d n)
    · simp only [Complex.add_im, hz, zero_add, d, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, Complex.I_re,
        mul_one, zero_mul, add_zero]
      exact (epsilon_pos n).ne'
    · simp only [Complex.add_im, hw, zero_add, d, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, Complex.I_re,
        mul_one, zero_mul, add_zero]
      exact (epsilon_pos n).ne'
    · exact nearby_resolves A z (d n) R hR (isUnit_one_sub_of_norm_lt_one hnr)
    · exact nearby_resolves B w (d n) S hS (isUnit_one_sub_of_norm_lt_one hns)
  have hr := (nearby_tendsto R).comp hd
  have hs := (nearby_tendsto S).comp hd
  have hleft := hr.mul hs
  have hright := hs.mul hr
  change R*S = S*R
  exact tendsto_nhds_unique_of_eventuallyEq hleft hright he

omit [CompleteSpace H] in
/-- Shift covariance for the actual partial-operator resolvent. -/
lemma resolves_unshift (T : H →ₗ.[ℂ] H) (c : ℝ) (z : ℂ) (R : H →L[ℂ] H)
    (h : Resolves (Ext005ShiftR114.shift T c) z R) : Resolves T (z-(c:ℂ)) R := by
  constructor
  · intro x
    obtain ⟨hx, heq⟩ := h.1 x
    refine ⟨hx, ?_⟩
    change T ⟨R x, hx⟩ + (c:ℂ) • R x - z • R x = x at heq
    calc
      _ = T ⟨R x, hx⟩ + (c:ℂ) • R x - z • R x := by module
      _ = x := heq
  · intro u
    have heq := h.2 u
    change R (T u + (c:ℂ) • (u:H) - z • (u:H)) = (u:H) at heq
    have he : T u - (z-(c:ℂ)) • (u:H) = T u + (c:ℂ) • (u:H) - z • (u:H) := by module
    rw [he]
    exact heq

/-- A direct consequence of the literal source strong-commutation
hypothesis: the actual A and B+1 physical cutoffs commute. No bounded
comparison-form commutation or invariant-core density is a premise. -/
theorem source_physical_cutoffs_commute (A : Ext005OperatorFormR113.PositiveOperator H)
    (B : Ext005ShiftR114.NonnegativeOperator H) (hc : StronglyCommute A.op B.op)
    (e f : ℝ) (he : 0 < e) (hf : 0 < f) :
    (Ext005PhysicalResolventR35b.physicalCutoffC A e he).comp
        (Ext005PhysicalResolventR35b.physicalCutoffC (Ext005ShiftR114.plusOne B) f hf) =
      (Ext005PhysicalResolventR35b.physicalCutoffC (Ext005ShiftR114.plusOne B) f hf).comp
        (Ext005PhysicalResolventR35b.physicalCutoffC A e he) := by
  have hA := Ext005PhysicalResolventR35b.resolves_negative A e he
  have hB := resolves_unshift B.op 1 (-(f⁻¹:ℝ):ℂ)
    ((f:ℂ) • Ext005PhysicalResolventR35b.physicalCutoffC (Ext005ShiftR114.plusOne B) f hf)
    (Ext005PhysicalResolventR35b.resolves_negative (Ext005ShiftR114.plusOne B) f hf)
  have h := stronglyCommute_real_resolvents A.op B.op hc (-(e⁻¹:ℝ):ℂ)
    ((-(f⁻¹:ℝ):ℂ)-(1:ℝ)) (by simp) (by simp) _ _ hA hB
  have heC : (e:ℂ) ≠ 0 := by exact_mod_cast he.ne'
  have hfC : (f:ℂ) ≠ 0 := by exact_mod_cast hf.ne'
  ext x
  have hx := congrArg (fun R : H →L[ℂ] H => R x) h
  change (e:ℂ) • (Ext005PhysicalResolventR35b.physicalCutoffC A e he)
      ((f:ℂ) • (Ext005PhysicalResolventR35b.physicalCutoffC (Ext005ShiftR114.plusOne B) f hf) x) =
    (f:ℂ) • (Ext005PhysicalResolventR35b.physicalCutoffC (Ext005ShiftR114.plusOne B) f hf)
      ((e:ℂ) • (Ext005PhysicalResolventR35b.physicalCutoffC A e he) x) at hx
  rw [map_smul, map_smul, smul_smul, smul_smul, mul_comm (f:ℂ) (e:ℂ)] at hx
  exact smul_right_injective (M := H) (mul_ne_zero heC hfC) hx

end QuantumNLS.Ext005ResolventPerturbR35b
#print axioms QuantumNLS.Ext005ResolventPerturbR35b.stronglyCommute_real_resolvents
#print axioms QuantumNLS.Ext005ResolventPerturbR35b.source_physical_cutoffs_commute

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005ResolventPerturbR35b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005ResolventPerturbR35b." then
      pending := pending.push n
  let roots := pending.size
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
  Lean.logInfo m!"R35b aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
