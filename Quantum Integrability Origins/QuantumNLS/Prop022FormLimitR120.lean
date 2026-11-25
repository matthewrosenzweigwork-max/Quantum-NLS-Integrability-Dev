import QuantumNLS.Prop022CutoffLimitR120
import QuantumNLS.Ext005PhysicalFormR110

/-! Strong form-coordinate closure from the proved third-moment bound,
and the exact antidual compression of the physical cutoff Hamiltonian. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open scoped InnerProductSpace Topology ComplexConjugate
open Set Filter ContinuousLinearMap
namespace QuantumNLS.Prop022FormLimitR120
open BetheCoefficientTransform Ext025B3PhysicalSectors Ext005Moments Ext005MomentEnergyR108
open Ext005MomentLimitR109 Ext005FormCutoffR109 Ext005FormScaleR109
open Prop022MomentTailR120 Prop022MixedCutoffR120 Prop022CutoffLimitR120
open Ext005PhysicalNumberFormR114 Ext005ComplexRieszR113 Ext005AntidualR113
open Prop022CutoffHamiltonianR115
variable {L : ℝ} [Fact (0 < L)]

lemma rootLift_error (N : ℕ) (x : momentDomain (L := L) 3) :
    ‖rootLift 1 x.val-rootCutoff 1 N x.val‖ ≤ ((N : ℝ)+1)⁻¹*‖momentRoot 3 x‖ := by
  rw [rootLift_eq 1 x.val (domain_mono (by decide : 1 ≤ 3) x.property)]
  exact root_truncation_error 1 N x

/-- Norm convergence plus a PROVED common third-moment bound implies
strong first-form convergence. The limit domain and bound are derived. -/
theorem rootLift_tendsto (u : ℕ → Fock L) (x : Fock L) (R : ℝ) (hR : 0 ≤ R)
    (hd : ∀ n, u n ∈ momentDomain (L := L) 3)
    (hb : ∀ n, ‖momentRoot 3 ⟨u n, hd n⟩‖ ≤ R)
    (hx : Tendsto u atTop (𝓝 x)) :
    Tendsto (fun n => rootLift 1 (u n)) atTop (𝓝 (rootLift 1 x)) := by
  have he (n : ℕ) : energy 3 (u n) ≤ R^2 := by
    rw [energy_eq_root 3 ⟨u n, hd n⟩]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb n) 2
  have hlim := normLimit_bound 3 u x (R^2) (fun n => ⟨hd n, he n⟩) hx
  have hxR : ‖momentRoot 3 ⟨x, hlim.1⟩‖ ≤ R := by
    have hsq : ‖momentRoot 3 ⟨x, hlim.1⟩‖^2 ≤ R^2 :=
      (energy_eq_root 3 ⟨x, hlim.1⟩).symm.le.trans hlim.2
    nlinarith [norm_nonneg (momentRoot 3 ⟨x, hlim.1⟩)]
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have ht : Tendsto (fun K : ℕ => 2*R*((K : ℝ)+1)⁻¹) atTop (𝓝 0) := by
    simpa only [mul_zero] using inverse_cutoff_tendsto.const_mul (2*R)
  obtain ⟨K, hK⟩ := (ht.eventually (gt_mem_nhds (half_pos hε))).exists
  have hlow := ((rootCutoff 1 K).continuous.tendsto x).comp hx
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlow (ε/2) (half_pos hε)
  refine ⟨N, ?_⟩
  intro n hn
  have h1 := (rootLift_error K ⟨u n, hd n⟩).trans
    (mul_le_mul_of_nonneg_left (hb n) (by positivity))
  have h2 := (rootLift_error K ⟨x, hlim.1⟩).trans
    (mul_le_mul_of_nonneg_left hxR (by positivity))
  have h3 := dist_triangle (rootLift 1 (u n)) (rootCutoff 1 K (u n)) (rootLift 1 x)
  have h4 := dist_triangle (rootCutoff 1 K (u n)) (rootCutoff 1 K x) (rootLift 1 x)
  simp only [dist_eq_norm] at h3 h4
  have hlow' := hN n hn
  rw [dist_eq_norm] at hlow' ⊢
  rw [norm_sub_rev (rootLift 1 x) (rootCutoff 1 K x)] at h2
  change ‖rootLift 1 (u n)-rootCutoff 1 K (u n)‖ ≤ ((K : ℝ)+1)⁻¹*R at h1
  simp only [Function.comp_def] at hlow'
  nlinarith

lemma cutoff_dynamic_tendsto (u : ℕ → Fock L) (x : Fock L)
    (hu : Tendsto u atTop (𝓝 x)) : Tendsto (fun N => cutoff N (u N)) atTop (𝓝 x) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := ((tendsto_iff_norm_sub_tendsto_zero.mp hu).add
    (tendsto_iff_norm_sub_tendsto_zero.mp (cutoff_tendsto x)))
  apply squeeze_zero (fun _ => norm_nonneg _) _ (by simpa only [zero_add] using ht)
  intro N
  have he : ‖cutoff N (u N)-cutoff N x‖ ≤ ‖u N-x‖ := by
    rw [← map_sub]
    exact cutoff_norm_le N (u N-x)
  have ht := dist_triangle (cutoff N (u N)) (cutoff N x) x
  simp only [dist_eq_norm] at ht
  exact ht.trans (add_le_add he le_rfl)

lemma embedding_rootCutoff (j N : ℕ) (x : Fock L) :
    embedding j (rootCutoff j N x) = cutoff N x := by
  apply Subtype.ext
  funext n
  change (((Real.sqrt (momentWeight j n))⁻¹ : ℝ) : ℂ) • (rootCutoff j N x n) = cutoff N x n
  rw [Prop022MomentTailR120.rootCutoff_apply, cutoff_apply]
  split_ifs
  · rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ (by linarith [rootWeight_one_le j n]),
      Complex.ofReal_one, one_smul]
  · exact smul_zero _

lemma rootCutoff_adjoint (j N : ℕ) :
    (rootCutoff (L := L) j N).adjoint = rootCutoff j N := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [adjoint_inner_right]
  exact Ext005PhysicalFormR110.rootCutoff_symmetric j N y x

/-- Exact antidual equation, retaining the outer cutoff. -/
lemma embedding_cutoffHamiltonian (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2)
    (N : ℕ) (x : Fock L) :
    embedding 1 (cutoffHamiltonian a b N x) =
      cutoff N (formOperator (quadraticContinuous a b) (rootCutoff 1 N x)) := by
  change embedding 1 ((rootCutoff 1 N).adjoint
    (formOperator (quadraticContinuous a b) (rootCutoff 1 N x))) = _
  rw [rootCutoff_adjoint, embedding_rootCutoff]

lemma physical_force_bound (a : HN L 1 →L[ℂ] HN L 1) (ha : a.adjoint = a)
    (b : HN L 2) (x : Fock L) :
    ‖formOperator (quadraticContinuous a b) x‖ ≤ (3*(‖a‖+‖b‖))*‖x‖ := by
  change ‖coordinates (quadraticContinuous a b x)‖ ≤ _
  rw [coordinates_norm]
  apply ContinuousLinearMap.opNorm_le_bound (quadraticContinuous a b x) (by positivity)
  intro v
  exact quadratic_bound a ha b x v

end QuantumNLS.Prop022FormLimitR120
#print axioms QuantumNLS.Prop022FormLimitR120.rootLift_tendsto
#print axioms QuantumNLS.Prop022FormLimitR120.embedding_cutoffHamiltonian
#print axioms QuantumNLS.Prop022FormLimitR120.physical_force_bound

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022FormLimitR120." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022FormLimitR120." then
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
  Lean.logInfo m!"R120 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
