import QuantumNLS.Prop022MixedCutoffR120
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Cauchy

/-! Mixed-cutoff overlap derivatives and quantitative Cauchy control for
the actual PROP-022 cutoff solutions. No solution estimate is an input. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 350000
open scoped InnerProductSpace Topology ComplexConjugate
open ContinuousLinearMap Set Filter
namespace QuantumNLS.Prop022CutoffCauchyR120
open BetheCoefficientTransform Ext025B3PhysicalSectors Ext005Moments
open Ext005MomentEnergyR108 Ext005FormCutoffR109 Ext005FormScaleR109
open Prop022CutoffEvolutionR119 Prop022FactorialCoefficientsR115 Prop022ActualProfileR117
open Prop022FactorialMajorantR115 Ext005PairCommutatorR108 Prop022MixedCutoffR120

section General
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
local instance : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H

lemma two_overlap_derivative (Q P : ℝ → H →L[ℂ] H) (hs : ∀ t, (Q t).IsSymmetric)
    (x y : ℝ → H)
    (hx : ∀ t, HasDerivAt x ((-Complex.I) • Q t (x t)) t)
    (hy : ∀ t, HasDerivAt y ((-Complex.I) • P t (y t)) t) (t : ℝ) :
    HasDerivAt (fun r => ⟪x r, y r⟫_ℂ)
      (Complex.I * ⟪x t, Q t (y t)-P t (y t)⟫_ℂ) t := by
  apply ((hx t).inner ℂ (hy t)).congr_deriv
  have hh := hs t (x t) (y t)
  change ⟪Q t (x t), y t⟫_ℂ = ⟪x t, Q t (y t)⟫_ℂ at hh
  simp only [inner_smul_left, inner_smul_right, map_neg, Complex.conj_I, neg_neg,
    inner_sub_right, hh]
  ring

lemma derivative_segment_bound (f g : ℝ → ℂ) (hd : ∀ r, HasDerivAt f (g r) r)
    (s T C : ℝ) (hb : ∀ r ∈ Icc (s-T) (s+T), ‖g r‖ ≤ C)
    (t : ℝ) (ht : t ∈ Icc (s-T) (s+T)) : ‖f t-f s‖ ≤ C*|t-s| := by
  have hT : 0 ≤ T := by linarith [ht.1, ht.2]
  by_cases hst : s ≤ t
  · have hf := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun r (_ : r ∈ Icc s t) => (hd r).hasDerivWithinAt)
      (fun r hr => hb r ⟨by linarith [hr.1], by linarith [ht.2, hr.2]⟩) t ⟨hst, le_rfl⟩
    simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using hf
  · have hts : t ≤ s := (le_of_not_ge hst)
    have hf := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun r (_ : r ∈ Icc t s) => (hd r).hasDerivWithinAt)
      (fun r hr => hb r ⟨by linarith [ht.1, hr.1], by linarith [hr.2]⟩) s ⟨hts, le_rfl⟩
    rw [norm_sub_rev] at hf
    simpa only [abs_of_neg (sub_neg.mpr (lt_of_not_ge hst)), neg_sub] using hf

lemma square_distance_control (x y : ℝ → H) (s t C : ℝ)
    (hx : ‖x t‖ = ‖x s‖) (hy : ‖y t‖ = ‖y s‖)
    (hb : ‖⟪x t,y t⟫_ℂ-⟪x s,y s⟫_ℂ‖ ≤ C) :
    ‖x t-y t‖^2 ≤ ‖x s-y s‖^2+2*C := by
  have h := (Complex.abs_re_le_norm (⟪x t,y t⟫_ℂ-⟪x s,y s⟫_ℂ)).trans hb
  rw [norm_sub_sq (𝕜 := ℂ), norm_sub_sq (𝕜 := ℂ), hx, hy]
  simp only [Complex.sub_re] at h
  change ‖x s‖^2-2*(⟪x t,y t⟫_ℂ).re+‖y s‖^2 ≤
    (‖x s‖^2-2*(⟪x s,y s⟫_ℂ).re+‖y s‖^2)+2*C
  linarith [(abs_le.mp h).1]
end General

variable {L : ℝ} [Fact (0 < L)]
local instance : NormedSpace ℝ (Fock L) := NormedSpace.restrictScalars ℝ ℂ (Fock L)

/-- One common squared third-moment radius for every cutoff on a centered interval. -/
def radiusSq (M A T : ℝ) (x : momentDomain (L := L) 3) : ℝ :=
  energy 3 x.val * Real.exp (differenceConstant 3 * (M*pairMajorant A)*T)

lemma radiusSq_nonneg (M A T : ℝ) (x : momentDomain (L := L) 3) :
    0 ≤ radiusSq M A T x := mul_nonneg (energy_nonneg 3 x.val) (Real.exp_pos _).le

lemma actual_root_bound (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : FactorialBound B M A)
    (hs : ∀ m, (B m).adjoint = B m) (u₀ : Prop001.Sphere (PhysicalTensor.L2T L))
    (N : ℕ) (s T : ℝ) (x : momentDomain (L := L) 3) (t : ℝ)
    (ht : t ∈ Icc (s-T) (s+T)) :
    ‖momentRoot 3 ⟨solution B M A hA hB hs u₀ N s x.val t,
      solution_momentDomain B M A hA hB hs u₀ N 3 s x.val t⟩‖ ≤
      Real.sqrt (radiusSq M A T x) := by
  have hst : |t-s| ≤ T := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hc : 0 ≤ differenceConstant 3 * (M*pairMajorant A) :=
    mul_nonneg (differenceConstant_nonneg 3) (mul_nonneg hM (pairMajorant_nonneg A hA))
  have he := solution_energy_envelope B M A hA hB hs u₀ N 3 (by decide) s x t
  have hb : energy 3 (solution B M A hA hB hs u₀ N s x.val t) ≤ radiusSq M A T x := by
    exact he.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hst hc)) (energy_nonneg 3 x.val))
  apply Real.le_sqrt_of_sq_le
  exact (energy_eq_root 3 ⟨_, solution_momentDomain B M A hA hB hs u₀ N 3 s x.val t⟩).symm.le.trans hb

lemma actual_overlap_derivative (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
    (u₀ : Prop001.Sphere (PhysicalTensor.L2T L)) (N K : ℕ) (s : ℝ) (x : Fock L) (t : ℝ) :
    HasDerivAt (fun r => ⟪solution B M A hA hB hs u₀ N s x r,
      solution B M A hA hB hs u₀ K s x r⟫_ℂ)
      (Complex.I * ⟪solution B M A hA hB hs u₀ N s x t,
        generator B M A hA hB hs u₀ N t (solution B M A hA hB hs u₀ K s x t)-
          generator B M A hA hB hs u₀ K t (solution B M A hA hB hs u₀ K s x t)⟫_ℂ) t := by
  exact two_overlap_derivative _ _ (generator_symmetric B M A hA hB hs u₀ N)
    _ _ (fun r => propagator_derivative B M A hA hB hs u₀ N s (cutoff N x) r)
    (fun r => propagator_derivative B M A hA hB hs u₀ K s (cutoff K x) r) t

/-- The cutoff-uniform coefficient in the mixed-overlap derivative estimate. -/
def overlapConstant (M A T : ℝ) (x : momentDomain (L := L) 3) : ℝ :=
  3*(M*(numberMajorant A+pairMajorant A))*radiusSq M A T x

lemma actual_overlap_bound (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : FactorialBound B M A)
    (hs : ∀ m, (B m).adjoint = B m) (u₀ : Prop001.Sphere (PhysicalTensor.L2T L))
    (N K : ℕ) (s T : ℝ) (x : momentDomain (L := L) 3) (t : ℝ)
    (ht : t ∈ Icc (s-T) (s+T)) :
    ‖Complex.I * ⟪solution B M A hA hB hs u₀ N s x.val t,
      generator B M A hA hB hs u₀ N t (solution B M A hA hB hs u₀ K s x.val t)-
        generator B M A hA hB hs u₀ K t (solution B M A hA hB hs u₀ K s x.val t)⟫_ℂ‖ ≤
      overlapConstant M A T x * (((N : ℝ)+1)⁻¹+((K : ℝ)+1)⁻¹) := by
  rw [norm_mul, Complex.norm_I, one_mul]
  have hm := mixed_pair_bound
    (numberCoefficient B (profile B M A hA hB hs u₀ t)) (numberCoefficient_adjoint B hs _)
    (pairCoefficient B (profile B M A hA hB hs u₀ t)) N K
    ⟨_, solution_momentDomain B M A hA hB hs u₀ N 3 s x.val t⟩
    ⟨_, solution_momentDomain B M A hA hB hs u₀ K 3 s x.val t⟩
    (solution_cutoff B M A hA hB hs u₀ N s x.val t)
    (solution_cutoff B M A hA hB hs u₀ K s x.val t)
    (Real.sqrt (radiusSq M A T x)) (Real.sqrt_nonneg _)
    (actual_root_bound B M A hM hA hB hs u₀ N s T x t ht)
    (actual_root_bound B M A hM hA hB hs u₀ K s T x t ht)
  have hu := (profile_spec B M A hA hB hs u₀).2.2.1 t
  have ha := numberCoefficient_bound B M A hA hB _ hu
  have hb := pairCoefficient_bound B M A hA hB _ hu
  have hab : ‖numberCoefficient B (profile B M A hA hB hs u₀ t)‖+
      ‖pairCoefficient B (profile B M A hA hB hs u₀ t)‖ ≤ M*(numberMajorant A+pairMajorant A) := by
    nlinarith only [ha, hb]
  rw [Real.sq_sqrt (radiusSq_nonneg M A T x)] at hm
  exact hm.trans (by dsimp only [overlapConstant]; gcongr; exact radiusSq_nonneg M A T x)

/-- Quantitative Cauchy estimate for the actual evolved projected data. -/
theorem actual_square_distance (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : FactorialBound B M A)
    (hs : ∀ m, (B m).adjoint = B m) (u₀ : Prop001.Sphere (PhysicalTensor.L2T L))
    (N K : ℕ) (s T : ℝ) (x : momentDomain (L := L) 3) (t : ℝ)
    (ht : t ∈ Icc (s-T) (s+T)) :
    ‖solution B M A hA hB hs u₀ N s x.val t-solution B M A hA hB hs u₀ K s x.val t‖^2 ≤
      ‖cutoff N x.val-cutoff K x.val‖^2+
        2*(overlapConstant M A T x * (((N : ℝ)+1)⁻¹+((K : ℝ)+1)⁻¹))*|t-s| := by
  have h := derivative_segment_bound _ _
    (actual_overlap_derivative B M A hA hB hs u₀ N K s x.val) s T _
    (fun r hr => actual_overlap_bound B M A hM hA hB hs u₀ N K s T x r hr) t ht
  have hN : ‖solution B M A hA hB hs u₀ N s x.val t‖ =
      ‖solution B M A hA hB hs u₀ N s x.val s‖ := by
    rw [solution_initial]
    exact propagator_norm B M A hA hB hs u₀ N s t (cutoff N x.val)
  have hK : ‖solution B M A hA hB hs u₀ K s x.val t‖ =
      ‖solution B M A hA hB hs u₀ K s x.val s‖ := by
    rw [solution_initial]
    exact propagator_norm B M A hA hB hs u₀ K s t (cutoff K x.val)
  have hh := square_distance_control _ _ s t _ hN hK h
  rw [solution_initial, solution_initial] at hh
  simpa only [mul_assoc] using hh

end QuantumNLS.Prop022CutoffCauchyR120
#print axioms QuantumNLS.Prop022CutoffCauchyR120.actual_overlap_derivative
#print axioms QuantumNLS.Prop022CutoffCauchyR120.actual_root_bound
#print axioms QuantumNLS.Prop022CutoffCauchyR120.actual_square_distance

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022CutoffCauchyR120." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022CutoffCauchyR120." then
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
