import QuantumNLS.Prop022FormLimitR120
import QuantumNLS.Ext005WeakEquationR37b
import QuantumNLS.Ext005WeakLimitR34b

/-! The common physical weak equation for the ACTUAL cutoff limit.
Both coordinate and force limits are derived from the cutoff solutions and
their proved moment bounds. No weak equation is supplied as an input. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
open scoped InnerProductSpace Topology ComplexConjugate ContDiff
open Set Filter ContinuousLinearMap MeasureTheory
namespace QuantumNLS.Prop022WeakEquationR120
open BetheCoefficientTransform Ext025B3PhysicalSectors Ext005Moments Ext005MomentEnergyR108
open Ext005FormCutoffR109 Ext005FormScaleR109 Prop022FormLimitR120 Prop022MixedCutoffR120
open Prop022CutoffEvolutionR119 Prop022CutoffCauchyR120 Prop022CutoffLimitR120
open Prop022FactorialCoefficientsR115 Prop022FactorialMajorantR115 Prop022ActualProfileR117
open Ext005PhysicalNumberFormR114 Ext005ComplexRieszR113 Ext005IntervalChainR111
variable {L : ℝ} [Fact (0 < L)]
local instance : NormedSpace ℝ (Fock L) := NormedSpace.restrictScalars ℝ ℂ (Fock L)
local instance : InnerProductSpace ℝ (Fock L) := InnerProductSpace.complexToReal
variable (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
    (u₀ : Prop001.Sphere (PhysicalTensor.L2T L)) (s : ℝ) (x : momentDomain (L := L) 3)
local notation "ψ" => (fun N t => solution B M A hA hB hs u₀ N s x.val t)
local notation "χ" => limit B M A hM hA hB hs u₀ s x
local notation "q" => (fun t => quadraticContinuous
    (numberCoefficient B (profile B M A hA hB hs u₀ t))
    (pairCoefficient B (profile B M A hA hB hs u₀ t)))
local notation "K" => (fun t => formOperator (q t))
local notation "GN" => (fun N t => (-Complex.I) •
    embedding (L := L) 1 (generator B M A hA hB hs u₀ N t (ψ N t)))
local notation "G" => (fun t => (-Complex.I) • K t (rootLift 1 (χ t)))

lemma rootCutoff_solution (N : ℕ) (t : ℝ) :
    rootCutoff 1 N (ψ N t) = rootLift 1 (ψ N t) := by
  have hd := solution_momentDomain B M A hA hB hs u₀ N 1 s x.val t
  exact (supported_root 1 N ⟨ψ N t, hd⟩ (solution_cutoff B M A hA hB hs u₀ N s x.val t)).trans
    (rootLift_eq 1 (ψ N t) hd).symm

lemma root_coordinates_tendsto (t : ℝ) :
    Tendsto (fun N => rootCutoff 1 N (ψ N t)) atTop (𝓝 (rootLift 1 (χ t))) := by
  have ht : t ∈ Icc (s-|t-s|) (s+|t-s|) :=
    ⟨by linarith [neg_abs_le (t-s)], by linarith [le_abs_self (t-s)]⟩
  have h := rootLift_tendsto (fun N => ψ N t) (χ t)
    (Real.sqrt (radiusSq M A |t-s| x)) (Real.sqrt_nonneg _)
    (fun N => solution_momentDomain B M A hA hB hs u₀ N 3 s x.val t)
    (fun N => actual_root_bound B M A hM hA hB hs u₀ N s |t-s| x t ht)
    (limit_tendsto B M A hM hA hB hs u₀ s x t)
  have he : (fun N => rootCutoff 1 N (ψ N t)) = (fun N => rootLift 1 (ψ N t)) :=
    funext (fun N => rootCutoff_solution B M A hA hB hs u₀ s x N t)
  rw [he]
  exact h

lemma force_tendsto (t : ℝ) : Tendsto (fun N => GN N t) atTop (𝓝 (G t)) := by
  have hk := ((K t).continuous.tendsto (rootLift 1 (χ t))).comp
    (root_coordinates_tendsto B M A hM hA hB hs u₀ s x t)
  have h := (cutoff_dynamic_tendsto _ _ hk).const_smul (-Complex.I)
  have he : (fun N => GN N t) =
      (fun N => (-Complex.I) • cutoff N (K t (rootCutoff 1 N (ψ N t)))) := by
    funext N
    exact congrArg (fun z : Fock L => (-Complex.I) • z)
      (embedding_cutoffHamiltonian _ _ N (ψ N t))
  rw [he]
  exact h

lemma force_continuous (N : ℕ) : Continuous (GN N) := by
  have hc := (generator_continuous B M A hA hB hs u₀ N).clm_apply
    (solution_continuous B M A hA hB hs u₀ N s x.val)
  exact ((embedding (L := L) 1).continuous.comp hc).const_smul (-Complex.I)

lemma coordinate_derivative (N : ℕ) (t : ℝ) :
    HasDerivAt (fun r => embedding (L := L) 1 (ψ N r)) (GN N t) t := by
  have h := ((embedding (L := L) 1).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (propagator_derivative B M A hA hB hs u₀ N s (cutoff N x.val) t)
  change HasDerivAt (fun r => embedding (L := L) 1 (ψ N r))
    (embedding (L := L) 1 ((-Complex.I) • generator B M A hA hB hs u₀ N t (ψ N t))) t at h
  simpa only [map_smul] using h

include hM in
/-- Uniform antidual bound for the actual cutoff forces, derived from the
literal form bound and the actual propagated third moment. -/
lemma force_bound (N : ℕ) (T t : ℝ) (ht : t ∈ Icc (s-T) (s+T)) :
    ‖GN N t‖ ≤ 3*(M*(numberMajorant A+pairMajorant A))*Real.sqrt (radiusSq M A T x) := by
  simp only [norm_smul, norm_neg, Complex.norm_I, one_mul]
  change ‖embedding (L := L) 1 (Prop022CutoffHamiltonianR115.cutoffHamiltonian
    (numberCoefficient B (profile B M A hA hB hs u₀ t))
    (pairCoefficient B (profile B M A hA hB hs u₀ t)) N (ψ N t))‖ ≤ _
  rw [embedding_cutoffHamiltonian]
  have hroot : ‖rootCutoff 1 N (ψ N t)‖ ≤ Real.sqrt (radiusSq M A T x) := by
    have hd := solution_momentDomain B M A hA hB hs u₀ N 3 s x.val t
    have he := supported_root 1 N (first ⟨ψ N t, hd⟩)
      (solution_cutoff B M A hA hB hs u₀ N s x.val t)
    calc
      _ = ‖momentRoot 1 (first ⟨ψ N t, hd⟩)‖ := congrArg norm he
      _ ≤ ‖momentRoot 3 ⟨ψ N t, hd⟩‖ := first_root_le ⟨ψ N t, hd⟩
      _ ≤ _ := actual_root_bound B M A hM hA hB hs u₀ N s T x t ht
  have hu := (profile_spec B M A hA hB hs u₀).2.2.1 t
  have ha := numberCoefficient_bound B M A hA hB _ hu
  have hb := pairCoefficient_bound B M A hA hB _ hu
  have hab : ‖numberCoefficient B (profile B M A hA hB hs u₀ t)‖+
      ‖pairCoefficient B (profile B M A hA hB hs u₀ t)‖ ≤ M*(numberMajorant A+pairMajorant A) := by
    nlinarith only [ha, hb]
  have hC : 0 ≤ M*(numberMajorant A+pairMajorant A) :=
    mul_nonneg hM (add_nonneg (numberMajorant_nonneg A hA) (pairMajorant_nonneg A hA))
  calc
    _ ≤ ‖K t (rootCutoff 1 N (ψ N t))‖ := cutoff_norm_le N _
    _ ≤ (3*(‖numberCoefficient B (profile B M A hA hB hs u₀ t)‖+
        ‖pairCoefficient B (profile B M A hA hB hs u₀ t)‖))*‖rootCutoff 1 N (ψ N t)‖ :=
      physical_force_bound _ (numberCoefficient_adjoint B hs _) _ _
    _ ≤ _ := by gcongr

/-- The common antidual weak equation for the constructed norm-continuous
limit, on every nonnegative finite centered interval. -/
theorem common_weak_equation (T : ℝ) (hT : 0 ≤ T) :
    WeakDerivativeOn (Ioo (s-T) (s+T)) (fun t => embedding (L := L) 1 (χ t)) G := by
  apply Ext005WeakLimitR34b.weak_derivative_limit (s-T) (s+T)
    (fun N t => embedding (L := L) 1 (ψ N t)) GN (fun t => embedding (L := L) 1 (χ t)) G
    ‖x.val‖ (3*(M*(numberMajorant A+pairMajorant A))*Real.sqrt (radiusSq M A T x))
  · intro N
    exact ((embedding (L := L) 1).continuous.comp (solution_continuous B M A hA hB hs u₀ N s x.val)).aestronglyMeasurable
  · intro N
    exact (force_continuous B M A hA hB hs u₀ s x N).aestronglyMeasurable
  · intro N t _
    exact (embedding_norm_le 1 (ψ N t)).trans
      ((propagator_norm B M A hA hB hs u₀ N s t (cutoff N x.val)).le.trans (cutoff_norm_le N x.val))
  · intro N t ht
    exact force_bound B M A hM hA hB hs u₀ s x N T t ht
  · intro t _ v
    exact tendsto_const_nhds.inner (((embedding (L := L) 1).continuous.tendsto (χ t)).comp
      (limit_tendsto B M A hM hA hB hs u₀ s x t))
  · intro t _ v
    exact tendsto_const_nhds.inner (force_tendsto B M A hM hA hB hs u₀ s x t)
  · intro N
    exact Ext005WeakEquationR37b.classical_weak (s-T) (s+T) (by linarith)
      (fun t => embedding (L := L) 1 (ψ N t)) (GN N)
      ((embedding (L := L) 1).continuous.comp (solution_continuous B M A hA hB hs u₀ N s x.val)).continuousOn
      (force_continuous B M A hA hB hs u₀ s x N).continuousOn
      (fun t _ => coordinate_derivative B M A hA hB hs u₀ s x N t)

/-- Source-oriented scalar weak equation on the physical first-moment
form scale. This is a conclusion for the actual cutoff limit. -/
theorem common_scalar_weak (T : ℝ) (hT : 0 ≤ T) (v : Fock L) (p : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hc : HasCompactSupport p)
    (hsup : tsupport p ⊆ Ioo (s-T) (s+T)) :
    (∫ t, deriv p t * (⟪embedding (L := L) 1 v, χ t⟫_ℂ).re) =
      -(∫ t, p t * (q t (rootLift 1 (χ t)) v).im) := by
  have h := common_weak_equation B M A hM hA hB hs u₀ s x T hT v p hp hc hsup
  have hleft (t : ℝ) : ⟪v, embedding (L := L) 1 (χ t)⟫_ℝ = (⟪embedding (L := L) 1 v, χ t⟫_ℂ).re := by
    change (⟪v, embedding (L := L) 1 (χ t)⟫_ℂ).re = _
    exact congrArg Complex.re (embedding_symmetric 1 v (χ t)).symm
  have hright (t : ℝ) : ⟪v, G t⟫_ℝ = (q t (rootLift 1 (χ t)) v).im := by
    change (⟪v, (-Complex.I) • K t (rootLift 1 (χ t))⟫_ℂ).re = _
    rw [inner_smul_right, form_pair]
    simp [Complex.mul_re]
  simp_rw [hleft, hright] at h
  exact h

/-- All three physical energy-weak conditions for the constructed limit.
The native source A,B,H(t) record remains a separate obligation. -/
theorem actual_limit_energy_weak_record :
    Continuous χ ∧ (∀ T : ℝ, EnergyBounded 1 (Icc (s-T) (s+T)) χ) ∧
      ∀ T : ℝ, 0 ≤ T → WeakDerivativeOn (Ioo (s-T) (s+T)) (fun t => embedding (L := L) 1 (χ t)) G := by
  refine ⟨limit_continuous B M A hM hA hB hs u₀ s x, ?_, ?_⟩
  · intro T
    exact limit_energyBounded B M A hM hA hB hs u₀ s T x 1 (by decide)
      (domain_mono (by decide : 1 ≤ 3) x.property)
  · intro T hT
    exact common_weak_equation B M A hM hA hB hs u₀ s x T hT

/-- The actual zero-sector evolution, with its initial third moment PROVED. -/
def zeroSectorLimit (v : HN L 0) (t : ℝ) : Fock L :=
  limit B M A hM hA hB hs u₀ s ⟨inclusion L 0 v, (vacuum_sector_energy 3 v).1⟩ t

/-- All propagated zero-sector moments have proved initial energies. -/
theorem zeroSectorLimit_moments (v : HN L 0) (j : ℕ) (hj : 1 ≤ j) (t : ℝ) :
    zeroSectorLimit B M A hM hA hB hs u₀ s v t ∈ momentDomain (L := L) j ∧
      energy j (zeroSectorLimit B M A hM hA hB hs u₀ s v t) ≤
        ‖v‖^2 * Real.exp (Ext005PairCommutatorR108.differenceConstant j*(M*pairMajorant A)*|t-s|) := by
  have h := limit_energy_envelope B M A hM hA hB hs u₀ s
    ⟨inclusion L 0 v, (vacuum_sector_energy 3 v).1⟩ j hj (vacuum_sector_energy j v).1 t
  simpa only [zeroSectorLimit, (vacuum_sector_energy j v).2] using h

theorem zeroSectorLimit_norm (v : HN L 0) (t : ℝ) :
    ‖zeroSectorLimit B M A hM hA hB hs u₀ s v t‖ = ‖v‖ := by
  exact (limit_norm B M A hM hA hB hs u₀ s
    ⟨inclusion L 0 v, (vacuum_sector_energy 3 v).1⟩ t).trans ((inclusion L 0).norm_map v)

end QuantumNLS.Prop022WeakEquationR120
#print axioms QuantumNLS.Prop022WeakEquationR120.root_coordinates_tendsto
#print axioms QuantumNLS.Prop022WeakEquationR120.force_bound
#print axioms QuantumNLS.Prop022WeakEquationR120.common_weak_equation
#print axioms QuantumNLS.Prop022WeakEquationR120.common_scalar_weak
#print axioms QuantumNLS.Prop022WeakEquationR120.actual_limit_energy_weak_record
#print axioms QuantumNLS.Prop022WeakEquationR120.zeroSectorLimit_moments

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022WeakEquationR120." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022WeakEquationR120." then
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
