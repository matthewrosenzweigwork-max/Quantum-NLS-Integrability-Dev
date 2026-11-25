import QuantumNLS.Ext025B7PVMForms
import Mathlib.MeasureTheory.Function.SimpleFunc

/-! GP-08: spectral integration built from the laws of an arbitrary PVM.
No spectral representation or compact-resolvent premise is supplied. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
open MeasureTheory Filter Topology Function
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.Ext025B8SimpleCalculus
open BetheChargeResolution Ext025B6PVM
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (P : ProjectionMeasure E)

/-- The canonical finite Borel spectral integral, including its zero fiber. -/
def simple (f : SimpleFunc ℝ ℂ) : E →L[ℂ] E :=
  ∑ z ∈ f.range, z • P.toFun (f ⁻¹' {z})

theorem fiber_disjoint {A : Type*} (f : SimpleFunc ℝ A) :
    (f.range : Set A).Pairwise (Disjoint on (fun z => f ⁻¹' {z})) := by
  intro a ha b hb hab
  exact Set.disjoint_left.mpr fun x hxa hxb => hab (hxa.symm.trans hxb)

theorem simple_square (f : SimpleFunc ℝ ℂ) (x : E) :
    ENNReal.ofReal (‖simple P f x‖^2) =
      ∫⁻ t, ENNReal.ofReal (‖f t‖^2) ∂scalarMeasure P x := by
  have hn := step_norm_sq P f.range (fun z => f ⁻¹' {z}) id
    (fun z _ => f.measurableSet_fiber z) (fiber_disjoint f) x
  change ‖simple P f x‖^2 = _ at hn
  rw [hn,ENNReal.ofReal_sum_of_nonneg (fun z _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  have hi := (f.map (fun z => ENNReal.ofReal (‖z‖^2))).lintegral_eq_lintegral (scalarMeasure P x)
  rw [SimpleFunc.map_lintegral] at hi
  apply Eq.trans (b := ∑ z ∈ f.range, ENNReal.ofReal (‖z‖^2) * scalarMeasure P x (f ⁻¹' {z})) _ hi.symm
  apply Finset.sum_congr rfl
  intro z hz
  rw [scalarMeasure_apply P x _ (f.measurableSet_fiber z),ENNReal.ofReal_mul (sq_nonneg _)]
  rfl

/-- Finite spectral partitions resolve the identity, derived from the scalar
measure and orthogonality rather than an extra additivity assumption. -/
theorem partition_identity {A : Type*} (f : SimpleFunc ℝ A) :
    (∑ z ∈ f.range, P.toFun (f ⁻¹' {z})) = 1 := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  let T : E →L[ℂ] E := ∑ z ∈ f.range, P.toFun (f ⁻¹' {z})
  have hs : ∑ z ∈ f.range, ‖P.toFun (f ⁻¹' {z}) x‖^2 = ‖x‖^2 := by
    have h := f.sum_range_measure_preimage_singleton (scalarMeasure P x)
    simp only [scalarMeasure_apply P x _ (f.measurableSet_fiber _),scalarMeasure_univ] at h
    have hr := congrArg ENNReal.toReal h
    simpa only [ENNReal.toReal_sum (fun z _ => ENNReal.ofReal_ne_top),
      ENNReal.toReal_ofReal (sq_nonneg _)] using hr
  have hn : ‖T x‖^2 = ‖x‖^2 := by
    have h := step_norm_sq P f.range (fun z => f ⁻¹' {z}) (fun _ => 1)
      (fun z _ => f.measurableSet_fiber z) (fiber_disjoint f) x
    simpa only [step,norm_one,one_pow,one_mul,one_smul,hs] using h
  have hi : ⟪x,T x⟫_ℂ = (‖x‖^2 : ℝ) := by
    simp only [T,sum_apply,inner_sum,inner_self_project P _ (f.measurableSet_fiber _)]
    exact_mod_cast hs
  have hz : ‖x-T x‖^2 = 0 := by
    rw [norm_sub_sq (𝕜 := ℂ),hi,hn]
    change ‖x‖^2-2*(‖x‖^2)+‖x‖^2 = 0
    ring
  have he : T x = x := (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))).symm
  exact he

/-- A simple integral acts by its scalar value on any finer measurable fiber. -/
theorem simple_local (f : SimpleFunc ℝ ℂ) (s : Set ℝ) (hs : MeasurableSet s)
    (c : ℂ) (hc : ∀ t ∈ s, f t = c) :
    simple P f * P.toFun s = c • P.toFun s := by
  classical
  by_cases he : s = ∅
  · simp [he,P.empty]
  have hne : s.Nonempty := Set.nonempty_iff_ne_empty.mpr he
  have hcr : c ∈ f.range := by
    obtain ⟨t,ht⟩ := hne
    rw [← hc t ht]
    exact f.mem_range_self t
  simp only [simple,Finset.sum_mul,smul_mul_assoc]
  rw [Finset.sum_eq_single c]
  · rw [P.inter _ _ (f.measurableSet_fiber c) hs]
    have hinter : (f ⁻¹' {c}) ∩ s = s := Set.inter_eq_right.mpr (fun t ht => hc t ht)
    rw [hinter]
  · intro z hz hzc
    rw [P.inter _ _ (f.measurableSet_fiber z) hs]
    have hzempty : (f ⁻¹' {z}) ∩ s = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro t ht
      exact hzc (ht.1.symm.trans (hc t ht.2))
    rw [hzempty,P.empty,smul_zero]
  · exact fun h => False.elim (h hcr)

/-- Equality of operators may be checked on the finitely many spectral fibers. -/
theorem eq_of_local {A : Type*} (f : SimpleFunc ℝ A) (S T : E →L[ℂ] E)
    (h : ∀ z ∈ f.range, S*P.toFun (f ⁻¹' {z}) = T*P.toFun (f ⁻¹' {z})) : S = T := by
  calc
    S = S*1 := (mul_one S).symm
    _ = ∑ z ∈ f.range, S*P.toFun (f ⁻¹' {z}) := by
      rw [← partition_identity P f,Finset.mul_sum]
    _ = ∑ z ∈ f.range, T*P.toFun (f ⁻¹' {z}) := Finset.sum_congr rfl h
    _ = T := by rw [← Finset.mul_sum,partition_identity P f,mul_one]

theorem simple_add (f g : SimpleFunc ℝ ℂ) : simple P (f+g) = simple P f+simple P g := by
  classical
  apply eq_of_local P (f.pair g)
  intro z hz
  have hf : ∀ t ∈ (f.pair g) ⁻¹' {z}, f t = z.1 := by
    intro t ht
    exact congrArg Prod.fst ht
  have hg : ∀ t ∈ (f.pair g) ⁻¹' {z}, g t = z.2 := by
    intro t ht
    exact congrArg Prod.snd ht
  rw [simple_local P (f+g) _ ((f.pair g).measurableSet_fiber z) (z.1+z.2)
    (fun t ht => by simp only [SimpleFunc.add_apply,hf t ht,hg t ht]),add_mul,
    simple_local P f _ ((f.pair g).measurableSet_fiber z) z.1 hf,
    simple_local P g _ ((f.pair g).measurableSet_fiber z) z.2 hg,add_smul]

theorem simple_smul (c : ℂ) (f : SimpleFunc ℝ ℂ) : simple P (c • f) = c • simple P f := by
  classical
  apply eq_of_local P f
  intro z hz
  rw [simple_local P (c • f) _ (f.measurableSet_fiber z) (c*z)
    (fun t ht => by change c * f t = c*z; rw [show f t = z from ht]),
    smul_mul_assoc,simple_local P f _ (f.measurableSet_fiber z) z (fun t ht => ht),
    smul_smul]

theorem simple_mul (f g : SimpleFunc ℝ ℂ) : simple P (f*g) = simple P f*simple P g := by
  classical
  apply eq_of_local P (f.pair g)
  intro z hz
  have hf : ∀ t ∈ (f.pair g) ⁻¹' {z}, f t = z.1 := fun t ht => congrArg Prod.fst ht
  have hg : ∀ t ∈ (f.pair g) ⁻¹' {z}, g t = z.2 := fun t ht => congrArg Prod.snd ht
  rw [simple_local P (f*g) _ ((f.pair g).measurableSet_fiber z) (z.1*z.2)
    (fun t ht => by simp only [SimpleFunc.mul_apply,hf t ht,hg t ht]),mul_assoc,
    simple_local P g _ ((f.pair g).measurableSet_fiber z) z.2 hg,mul_smul_comm,
    simple_local P f _ ((f.pair g).measurableSet_fiber z) z.1 hf,smul_smul,mul_comm z.2 z.1]

theorem simple_const (c : ℂ) : simple P (SimpleFunc.const ℝ c) = c • 1 := by
  classical
  have he : ((SimpleFunc.const ℝ c) ⁻¹' {c}) = Set.univ := by
    ext t
    simp only [Set.mem_preimage,Set.mem_singleton_iff,SimpleFunc.const_apply,Set.mem_univ]
  simp only [simple,SimpleFunc.range_const,Finset.sum_singleton,he,P.univ]

theorem simple_zero : simple P 0 = 0 := by
  have hz : (0 : SimpleFunc ℝ ℂ) = SimpleFunc.const ℝ 0 := SimpleFunc.ext fun _ => rfl
  rw [hz,simple_const,zero_smul]

theorem simple_sub (f g : SimpleFunc ℝ ℂ) : simple P (f-g) = simple P f-simple P g := by
  have hn : simple P (-g) = -simple P g := by
    simpa only [neg_one_smul] using simple_smul P (-1) g
  rw [sub_eq_add_neg,simple_add,hn,← sub_eq_add_neg]

theorem simple_bound (f : SimpleFunc ℝ ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ t, ‖f t‖ ≤ C) : ‖simple P f‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  have hi := simple_square P f x
  have hb : (∫⁻ t, ENNReal.ofReal (‖f t‖^2) ∂scalarMeasure P x) ≤
      ENNReal.ofReal (C^2*‖x‖^2) := by
    calc
      _ ≤ ∫⁻ _ : ℝ, ENNReal.ofReal (C^2) ∂scalarMeasure P x :=
        lintegral_mono fun t => ENNReal.ofReal_le_ofReal
          (pow_le_pow_left₀ (norm_nonneg _) (hf t) 2)
      _ = _ := by rw [lintegral_const,scalarMeasure_univ,← ENNReal.ofReal_mul (sq_nonneg _)]
  rw [← hi] at hb
  have hr := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg _) (sq_nonneg _))).mp hb
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp (by nlinarith)


/-- Every finite spectral integral commutes with every measurable projection. -/
theorem simple_commutes (f : SimpleFunc ℝ ℂ) : Ext025B7PVMForms.Commutes P (simple P f) := by
  intro s hs
  change simple P f*P.toFun s = P.toFun s*simple P f
  simp only [simple,Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm]
  apply Finset.sum_congr rfl
  intro z hz
  rw [P.inter _ _ (f.measurableSet_fiber z) hs,P.inter _ _ hs (f.measurableSet_fiber z),Set.inter_comm]

theorem simple_star (f : SimpleFunc ℝ ℂ) :
    (simple P f).adjoint = simple P (f.map star) := by
  apply eq_of_local P f
  intro z hz
  rw [simple_local P (f.map star) _ (f.measurableSet_fiber z) (star z)
    (fun t ht => by change star (f t) = star z; rw [show f t = z from ht])]
  have he : P.toFun (f ⁻¹' {z})*simple P f = z • P.toFun (f ⁻¹' {z}) :=
    ((simple_commutes P f _ (f.measurableSet_fiber z)).eq.symm).trans
      (simple_local P f _ (f.measurableSet_fiber z) z (fun t ht => ht))
  have h := congrArg star he
  have hp : star (P.toFun (f ⁻¹' {z})) = P.toFun (f ⁻¹' {z}) := P.selfAdjoint _ (f.measurableSet_fiber z)
  simpa only [star_mul,star_smul,hp,ContinuousLinearMap.star_eq_adjoint] using h

/-- The finite Borel integral of a literal characteristic function is the
original projection, so the constructed calculus has the prescribed PVM. -/
theorem simple_indicator (s : Set ℝ) (hs : MeasurableSet s) :
    simple P (SimpleFunc.piecewise s hs (SimpleFunc.const ℝ 1) (SimpleFunc.const ℝ 0)) = P.toFun s := by
  classical
  let f : SimpleFunc ℝ ℂ := SimpleFunc.piecewise s hs (SimpleFunc.const ℝ 1) (SimpleFunc.const ℝ 0)
  have hf : f.range ⊆ {0,1} := by
    intro z hz
    obtain ⟨t,rfl⟩ := SimpleFunc.mem_range.mp hz
    by_cases ht : t ∈ s <;> simp [f,ht]
  have hi : (f ⁻¹' {1}) = s := by
    ext t
    by_cases ht : t ∈ s <;> simp [f,ht]
  have he : simple P f = ∑ z ∈ ({0,1} : Finset ℂ), z • P.toFun (f ⁻¹' {z}) := by
    apply Finset.sum_subset hf
    intro z hz hnot
    rw [(f.preimage_eq_empty_iff z).mpr hnot,P.empty,smul_zero]
  change simple P f = _
  rw [he]
  simp only [Finset.sum_insert (by norm_num : (0 : ℂ) ∉ ({1} : Finset ℂ)),
    Finset.sum_singleton,zero_smul,zero_add,one_smul,hi]

end QuantumNLS.Ext025B8SimpleCalculus

#print axioms QuantumNLS.Ext025B8SimpleCalculus.simple
#print axioms QuantumNLS.Ext025B8SimpleCalculus.fiber_disjoint
#print axioms QuantumNLS.Ext025B8SimpleCalculus.simple_square
#print axioms QuantumNLS.Ext025B8SimpleCalculus.partition_identity
#print axioms QuantumNLS.Ext025B8SimpleCalculus.simple_local
#print axioms QuantumNLS.Ext025B8SimpleCalculus.eq_of_local
#print axioms QuantumNLS.Ext025B8SimpleCalculus.simple_add
#print axioms QuantumNLS.Ext025B8SimpleCalculus.simple_smul
#print axioms QuantumNLS.Ext025B8SimpleCalculus.simple_mul
#print axioms QuantumNLS.Ext025B8SimpleCalculus.simple_const
#print axioms QuantumNLS.Ext025B8SimpleCalculus.simple_zero
#print axioms QuantumNLS.Ext025B8SimpleCalculus.simple_sub
#print axioms QuantumNLS.Ext025B8SimpleCalculus.simple_bound
#print axioms QuantumNLS.Ext025B8SimpleCalculus.simple_commutes
#print axioms QuantumNLS.Ext025B8SimpleCalculus.simple_star
#print axioms QuantumNLS.Ext025B8SimpleCalculus.simple_indicator

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025B8SimpleCalculus." then
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
  Lean.logInfo m!"Ext025B8SimpleCalculus audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
