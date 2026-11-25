import QuantumNLS.Ext005RootEvolutionR127

/-! The common physical evolution satisfies the native energy-bounded weak
class on the FULL j-th moment domain, including j=1. Finite-particle initial
approximations pass through proved form-norm convergence and uniform bounds. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
open scoped InnerProductSpace Topology ComplexConjugate ContDiff
open Set Filter ContinuousLinearMap MeasureTheory
namespace QuantumNLS.Ext005CommonWeakR127
open BetheCoefficientTransform Ext025B3PhysicalSectors Ext005Moments Ext005MomentEnergyR108
open Ext005FormScaleR109 Ext005FormCutoffR109 Ext005PairCommutatorR108
open Ext005PhysicalNumberFormR114 Ext005ComplexRieszR113 Ext005IntervalChainR111
open Prop022FactorialCoefficientsR115 Prop022FactorialMajorantR115 Prop022ActualProfileR117
open Prop022FockPropagatorR122 Prop022DomainR122 Prop022FormLimitR120
open Prop022NativeCompetitorR121 Ext005RootEvolutionR127
variable {L : ℝ} [Fact (0 < L)]
local instance : NormedSpace ℝ (Fock L) := NormedSpace.restrictScalars ℝ ℂ (Fock L)
local instance : InnerProductSpace ℝ (Fock L) := InnerProductSpace.rclikeToReal ℂ (Fock L)
variable (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
  (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
  (u₀ : Prop001.Sphere (PhysicalTensor.L2T L))
local notation "V" => evolution B M A hM hA hB hs u₀
local notation "q" => (fun t => quadraticContinuous
  (numberCoefficient B (profile B M A hA hB hs u₀ t))
  (pairCoefficient B (profile B M A hA hB hs u₀ t)))
local notation "K" => (fun t => formOperator (q t))

lemma approximate_force_measurable (s : ℝ) (x : Fock L) (N : ℕ) :
    AEStronglyMeasurable (fun t => (-Complex.I) • K t (rootLift 1 (V s t (cutoff N x)))) := by
  let z : momentDomain (L := L) 3 := ⟨cutoff N x, cutoff_mem 3 N x⟩
  have he (t : ℝ) : V s t (cutoff N x) =
      Prop022CutoffLimitR120.limit B M A hM hA hB hs u₀ s z t :=
    evolution_on_domain B M A hM hA hB hs u₀ s t z
  simp_rw [he]
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun J t => (-Complex.I) • embedding (L := L) 1
      (Prop022CutoffEvolutionR119.generator B M A hA hB hs u₀ J t
        (Prop022CutoffEvolutionR119.solution B M A hA hB hs u₀ J s z.val t)))
  · intro J
    exact (Prop022WeakEquationR120.force_continuous B M A hA hB hs u₀ s z J).aestronglyMeasurable
  · exact Eventually.of_forall (fun t =>
      Prop022WeakEquationR120.force_tendsto B M A hM hA hB hs u₀ s z t)

lemma approximate_root_bound (s T t : ℝ) (x : momentDomain (L := L) 1)
    (N : ℕ) (ht : t ∈ Icc (s-T) (s+T)) :
    ‖rootLift 1 (V s t (cutoff N x.val))‖ ≤
      Real.sqrt (energy 1 x.val * Real.exp (differenceConstant 1*(M*pairMajorant A)*T)) := by
  let c := differenceConstant 1*(M*pairMajorant A)
  have hc : 0 ≤ c := mul_nonneg (differenceConstant_nonneg 1)
    (mul_nonneg hM (pairMajorant_nonneg A hA))
  have hst : |t-s| ≤ T := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have he := evolution_energy B M A hM hA hB hs u₀ 1 (by decide) s t
    ⟨cutoff N x.val, cutoff_mem 1 N x.val⟩
  have hb : energy 1 (V s t (cutoff N x.val)) ≤ energy 1 x.val * Real.exp (c*T) :=
    he.2.trans (mul_le_mul (cutoff_energy_le 1 N x)
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hst hc))
      (Real.exp_pos _).le (energy_nonneg 1 x.val))
  rw [energy_eq_root 1 ⟨V s t (cutoff N x.val), he.1⟩] at hb
  rw [rootLift_eq 1 _ he.1]
  exact Real.le_sqrt_of_sq_le hb

lemma approximate_force_bound (s T t : ℝ) (x : momentDomain (L := L) 1)
    (N : ℕ) (ht : t ∈ Icc (s-T) (s+T)) :
    ‖(-Complex.I) • K t (rootLift 1 (V s t (cutoff N x.val)))‖ ≤
      (3*(M*(numberMajorant A+pairMajorant A))) *
        Real.sqrt (energy 1 x.val * Real.exp (differenceConstant 1*(M*pairMajorant A)*T)) := by
  simp only [norm_smul, norm_neg, Complex.norm_I, one_mul]
  have hu := (profile_spec B M A hA hB hs u₀).2.2.1 t
  have ha := numberCoefficient_bound B M A hA hB _ hu
  have hb := pairCoefficient_bound B M A hA hB _ hu
  have hab : ‖numberCoefficient B (profile B M A hA hB hs u₀ t)‖+
      ‖pairCoefficient B (profile B M A hA hB hs u₀ t)‖ ≤ M*(numberMajorant A+pairMajorant A) := by
    nlinarith only [ha, hb]
  calc
    _ ≤ (3*(‖numberCoefficient B (profile B M A hA hB hs u₀ t)‖+
        ‖pairCoefficient B (profile B M A hA hB hs u₀ t)‖))*
        ‖rootLift 1 (V s t (cutoff N x.val))‖ :=
      physical_force_bound _ (numberCoefficient_adjoint B hs _) _ _
    _ ≤ _ := mul_le_mul (by linarith only [hab])
      (approximate_root_bound B M A hM hA hB hs u₀ s T t x N ht)
      (norm_nonneg _) (mul_nonneg (by norm_num)
        (mul_nonneg hM (add_nonneg (numberMajorant_nonneg A hA) (pairMajorant_nonneg A hA))))

/-- The physical distributional equation on the entire first-moment domain.
The uniform force bound and form-coordinate convergence are proved above. -/
theorem common_weak (s T : ℝ) (hT : 0 ≤ T) (x : momentDomain (L := L) 1) :
    WeakDerivativeOn (Ioo (s-T) (s+T)) (fun t => embedding (L := L) 1 (V s t x.val))
      (fun t => (-Complex.I) • K t (rootLift 1 (V s t x.val))) := by
  apply Ext005WeakLimitR34b.weak_derivative_limit (s-T) (s+T)
    (fun N t => embedding (L := L) 1 (V s t (cutoff N x.val)))
    (fun N t => (-Complex.I) • K t (rootLift 1 (V s t (cutoff N x.val)))) _ _
    ‖x.val‖ ((3*(M*(numberMajorant A+pairMajorant A))) *
      Real.sqrt (energy 1 x.val * Real.exp (differenceConstant 1*(M*pairMajorant A)*T)))
  · intro N
    exact ((embedding (L := L) 1).continuous.comp
      (evolution_continuous B M A hM hA hB hs u₀ s (cutoff N x.val))).aestronglyMeasurable
  · intro N
    exact approximate_force_measurable B M A hM hA hB hs u₀ s x.val N
  · intro N t _
    exact (embedding_norm_le 1 _).trans
      (((V s t).norm_map (cutoff N x.val)).le.trans (cutoff_norm_le N x.val))
  · intro N t ht
    exact approximate_force_bound B M A hM hA hB hs u₀ s T t x N ht
  · intro t _ v
    exact tendsto_const_nhds.inner (((embedding (L := L) 1).continuous.tendsto _).comp
      (((V s t).continuous.tendsto x.val).comp (cutoff_tendsto x.val)))
  · intro t _ v
    exact tendsto_const_nhds.inner
      ((((K t).continuous.tendsto _).comp
        (evolved_cutoff_root_tendsto B M A hM hA hB hs u₀ 1 (by decide) s t x)).const_smul (-Complex.I))
  · intro N
    let z : momentDomain (L := L) 3 := ⟨cutoff N x.val, cutoff_mem 3 N x.val⟩
    have he (t : ℝ) : V s t (cutoff N x.val) =
        Prop022CutoffLimitR120.limit B M A hM hA hB hs u₀ s z t :=
      evolution_on_domain B M A hM hA hB hs u₀ s t z
    simp_rw [he]
    exact Prop022WeakEquationR120.common_weak_equation B M A hM hA hB hs u₀ s z T hT

lemma common_scalar_weak (s T : ℝ) (hT : 0 ≤ T) (x : momentDomain (L := L) 1)
    (w : Fock L) (p : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hc : HasCompactSupport p)
    (hsup : tsupport p ⊆ Ioo (s-T) (s+T)) :
    (∫ t, deriv p t * (⟪embedding (L := L) 1 w, V s t x.val⟫_ℂ).re) =
      -(∫ t, p t * (q t (rootLift 1 (V s t x.val)) w).im) := by
  have h := common_weak B M A hM hA hB hs u₀ s T hT x w p hp hc hsup
  have hleft (t : ℝ) : ⟪w, embedding (L := L) 1 (V s t x.val)⟫_ℝ =
      (⟪embedding (L := L) 1 w, V s t x.val⟫_ℂ).re :=
    congrArg Complex.re (embedding_symmetric 1 w (V s t x.val)).symm
  have hright (t : ℝ) : ⟪w, (-Complex.I) • K t (rootLift 1 (V s t x.val))⟫_ℝ =
      (q t (rootLift 1 (V s t x.val)) w).im := by
    change (⟪w, (-Complex.I) • K t (rootLift 1 (V s t x.val))⟫_ℂ).re = _
    rw [inner_smul_right, form_pair]
    simp [Complex.mul_re]
  simp_rw [hleft, hright] at h
  exact h

/-- A proved native D3 record for EVERY j>=1 on its FULL initial domain. -/
theorem common_competitor (j : ℕ) (hj : 1 ≤ j) (s T : ℝ) (hT : 0 ≤ T)
    (x : momentDomain (L := L) j) :
    Competitor B M A hA hB hs u₀ j (s-T) (s+T) (fun t => V s t x.val) where
  continuous := (evolution_continuous B M A hM hA hB hs u₀ s x.val).continuousOn
  moments := evolution_energyBounded B M A hM hA hB hs u₀ j hj s T x
  weak := common_scalar_weak B M A hM hA hB hs u₀ s T hT
    ⟨x.val, domain_mono hj x.property⟩

end QuantumNLS.Ext005CommonWeakR127
#print axioms QuantumNLS.Ext005CommonWeakR127.common_weak
#print axioms QuantumNLS.Ext005CommonWeakR127.common_competitor

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005CommonWeakR127." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005CommonWeakR127." then
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
  Lean.logInfo m!"R127 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
