import NlsGge.Atomic.LIB.LIB031
import NlsGge.Atomic.IntervalZSAction

/-!
# LIB-032: uniform control of H1 by the actual Dirac graph norm

The off-diagonal potential term is constructed in the actual paired L2 space
before any action identity is used. Its norm is at most the potential L2 norm
times the canonical Euclidean-pair supremum. The diagonal derivative phases
preserve the paired L2 norm. The resulting derivative estimate and LIB-031 at
`ε = 1 / (2 * (B + 1))` give a uniform graph bound by absorption.

Both the sum H1 norm and the usual square-root energy norm are defined
explicitly from the actual paired value and weak derivative. The constant
works for all complex potentials in the entire L2 ball and all interval H1
pairs, hence for every one of the four source boundary domains.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace NlsGge.Atomic.LIB032
open NlsGge.Schur NlsGge.Atomic.Interval NlsGge.Atomic.LIB026 NlsGge.Atomic.LIB031

/-- The genuine sum norm of the value and weak derivative in the actual paired L2 space. -/
def h1SumNorm (f : H1Pair) : ℝ := ‖h1PairValue f‖ + ‖pairDerivative f‖

/-- The standard squared-energy Hilbert H1 norm, on the same actual value/derivative pair. -/
def h1Norm (f : H1Pair) : ℝ := Real.sqrt (‖h1PairValue f‖ ^ 2 + ‖pairDerivative f‖ ^ 2)

lemma h1Norm_le_sum (f : H1Pair) : h1Norm f ≤ h1SumNorm f := by
  rw [h1Norm, h1SumNorm, Real.sqrt_le_iff]
  constructor
  · positivity
  · nlinarith [mul_nonneg (norm_nonneg (h1PairValue f)) (norm_nonneg (pairDerivative f))]

lemma representative_component_le_sup (f : H1Pair) (b : Bool) (x : Icc (0 : ℝ) 1) :
    ‖representative (f b) x‖ ≤ ‖pairRepresentative f‖ := by
  have hp : ‖representative (f b) x‖ ≤ ‖pairRepresentative f x‖ := by
    simpa only [pairRepresentative] using! PiLp.norm_apply_le (pairRepresentative f x) b
  exact hp.trans (ContinuousMap.norm_coe_le_norm (pairRepresentative f) x)

lemma value_component_le_sup_ae (f : H1Pair) (b : Bool) :
    ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), ‖(f b).value x‖ ≤ ‖pairRepresentative f‖ := by
  filter_upwards [representative_ae (f b), ae_restrict_mem measurableSet_Ioc] with x hx hmem
  rw [← hx, IccExtend_of_mem zero_le_one (representative (f b)) ⟨hmem.1.le, hmem.2⟩]
  exact representative_component_le_sup f b ⟨x, ⟨hmem.1.le, hmem.2⟩⟩

lemma potentialProduct_memLp (φ : SourcePairL2) (f : H1Pair) (b : Bool) :
    MemLp (fun x => φ b x * (f (!b)).value x) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
  (Lp.memLp (φ b)).mul (h1Value_memLp_top (f (!b)))

/-- The actual L2 off-diagonal potential term, constructed after L2 membership. -/
def potentialProduct (φ : SourcePairL2) (f : H1Pair) : SourcePairL2 :=
  WithLp.toLp 2 (fun b => (potentialProduct_memLp φ f b).toLp
    (fun x => φ b x * (f (!b)).value x))

lemma potentialProduct_ae (φ : SourcePairL2) (f : H1Pair) (b : Bool) :
    (fun x => potentialProduct φ f b x) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      fun x => φ b x * (f (!b)).value x :=
  (potentialProduct_memLp φ f b).coeFn_toLp

lemma potentialProduct_component_norm_le (φ : SourcePairL2) (f : H1Pair) (b : Bool) :
    ‖potentialProduct φ f b‖ ≤ ‖pairRepresentative f‖ * ‖φ b‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [potentialProduct_ae φ f b, value_component_le_sup_ae f (!b)] with x hx hb
  rw [hx, norm_mul]
  nlinarith [mul_le_mul_of_nonneg_left hb (norm_nonneg (φ b x))]

lemma pair_norm_le_of_component_norm_le (u v : SourcePairL2)
    (h : ∀ b : Bool, ‖u b‖ ≤ ‖v b‖) : ‖u‖ ≤ ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  calc
    _ = ∑ b : Bool, ‖u b‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ u
    _ ≤ ∑ b : Bool, ‖v b‖ ^ 2 := Finset.sum_le_sum
      (fun b _ => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (h b))
    _ = _ := (PiLp.norm_sq_eq_of_L2 _ v).symm

lemma potentialProduct_norm_le (φ : SourcePairL2) (f : H1Pair) :
    ‖potentialProduct φ f‖ ≤ ‖φ‖ * ‖pairRepresentative f‖ := by
  have hc (b : Bool) : ‖potentialProduct φ f b‖ ≤ ‖((‖pairRepresentative f‖ : ℂ) • φ) b‖ := by
    change ‖potentialProduct φ f b‖ ≤ ‖(‖pairRepresentative f‖ : ℂ) • φ b‖
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    exact potentialProduct_component_norm_le φ f b
  have h := pair_norm_le_of_component_norm_le (potentialProduct φ f)
    ((‖pairRepresentative f‖ : ℂ) • φ) hc
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)] at h
  simpa only [mul_comm] using h

/-- The actual phase-multiplied derivative term of the Dirac expression. -/
def phaseDerivative (f : H1Pair) : SourcePairL2 :=
  WithLp.toLp 2 (fun b => (if b then Complex.I else -Complex.I) • (f b).derivative)

lemma phaseDerivative_component_norm (f : H1Pair) (b : Bool) :
    ‖phaseDerivative f b‖ = ‖(f b).derivative‖ := by
  change ‖(if b then Complex.I else -Complex.I) • (f b).derivative‖ = _
  rw [norm_smul]
  cases b <;> simp

lemma phaseDerivative_norm (f : H1Pair) : ‖phaseDerivative f‖ = ‖pairDerivative f‖ := by
  have hs : ‖phaseDerivative f‖ ^ 2 = ‖pairDerivative f‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro b hb
    rw [phaseDerivative_component_norm]
    rfl
  nlinarith [norm_nonneg (phaseDerivative f), norm_nonneg (pairDerivative f)]

lemma zsApply_eq_phase_add_potential (φ : SourcePairL2) (f : H1Pair) :
    zsApply φ f = phaseDerivative f + potentialProduct φ f := by
  apply PiLp.ext
  intro b
  apply Lp.ext
  filter_upwards [zsApply_ae φ f b,
    Lp.coeFn_add (phaseDerivative f b) (potentialProduct φ f b),
    Lp.coeFn_smul (if b then Complex.I else -Complex.I) (f b).derivative,
    potentialProduct_ae φ f b] with x ha hadd hs hp
  change zsApply φ f b x = (phaseDerivative f b + potentialProduct φ f b) x
  rw [hadd, ha]
  simp only [Pi.add_apply]
  rw [hp]
  change (if b then Complex.I else -Complex.I) * (f b).derivative x +
    φ b x * (f (!b)).value x = _
  rw [show phaseDerivative f b x =
    (if b then Complex.I else -Complex.I) * (f b).derivative x from by
      simpa only [phaseDerivative, Pi.smul_apply, smul_eq_mul] using hs]

/-- The actual derivative is bounded by the actual action and potential term. -/
theorem derivative_norm_le_action_add_potential (φ : SourcePairL2) (f : H1Pair) :
    ‖pairDerivative f‖ ≤ ‖zsApply φ f‖ + ‖φ‖ * ‖pairRepresentative f‖ := by
  have he : phaseDerivative f = zsApply φ f - potentialProduct φ f := by
    rw [zsApply_eq_phase_add_potential, add_sub_cancel_right]
  calc
    _ = ‖phaseDerivative f‖ := (phaseDerivative_norm f).symm
    _ = ‖zsApply φ f - potentialProduct φ f‖ := congrArg norm he
    _ ≤ ‖zsApply φ f‖ + ‖potentialProduct φ f‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add le_rfl (potentialProduct_norm_le φ f)


lemma h1Norm_sq (f : H1Pair) :
    h1Norm f ^ 2 = ‖h1PairValue f‖ ^ 2 + ‖pairDerivative f‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- A single explicit graph-bound constant for the entire complex potential ball. -/
def graphBoundConstant (B : ℝ) : ℝ := 2 + 2 * B * (1 + 2 * (B + 1))

lemma graphBoundConstant_nonneg {B : ℝ} (hB : 0 ≤ B) : 0 ≤ graphBoundConstant B := by
  dsimp [graphBoundConstant]
  positivity

/-- Epsilon absorption with no boundary condition and no real-type restriction. -/
theorem zs_h1SumNorm_le_graph {B : ℝ} (hB : 0 ≤ B)
    (φ : SourcePairL2) (hφ : ‖φ‖ ≤ B) (f : H1Pair) :
    h1SumNorm f ≤ graphBoundConstant B * (‖zsApply φ f‖ + ‖h1PairValue f‖) := by
  let ε : ℝ := (2 * (B + 1))⁻¹
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsup := pair_sup_le_epsilon_deriv hε f
  have hCε : 1 + ε⁻¹ = 1 + 2 * (B + 1) := by simp [ε]
  rw [hCε] at hsup
  have hgraph := derivative_norm_le_action_add_potential φ f
  have hgB : ‖pairDerivative f‖ ≤ ‖zsApply φ f‖ + B * ‖pairRepresentative f‖ :=
    hgraph.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right hφ (norm_nonneg (pairRepresentative f))))
  have hsub : ‖pairDerivative f‖ ≤ ‖zsApply φ f‖ +
      B * (ε * ‖pairDerivative f‖ + (1 + 2 * (B + 1)) * ‖h1PairValue f‖) :=
    hgB.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hsup hB))
  have heq : ε * (2 * (B + 1)) = 1 := by
    dsimp [ε]
    exact inv_mul_cancel₀ (by positivity)
  have hhalf : B * ε ≤ (1 / 2 : ℝ) := by nlinarith [hε.le]
  have hhalfD := mul_le_mul_of_nonneg_right hhalf (norm_nonneg (pairDerivative f))
  have hd : ‖pairDerivative f‖ ≤ 2 * ‖zsApply φ f‖ +
      2 * B * (1 + 2 * (B + 1)) * ‖h1PairValue f‖ := by
    nlinarith only [hsub, hhalfD]
  have hCtwo : 2 ≤ graphBoundConstant B := by
    have hp : 0 ≤ 2 * B * (1 + 2 * (B + 1)) := by positivity
    dsimp [graphBoundConstant]
    linarith
  have hCvalue : 1 + 2 * B * (1 + 2 * (B + 1)) ≤ graphBoundConstant B := by
    dsimp [graphBoundConstant]
    linarith
  calc
    h1SumNorm f ≤ 2 * ‖zsApply φ f‖ +
        (1 + 2 * B * (1 + 2 * (B + 1))) * ‖h1PairValue f‖ := by
      dsimp [h1SumNorm]
      nlinarith only [hd]
    _ ≤ graphBoundConstant B * ‖zsApply φ f‖ + graphBoundConstant B * ‖h1PairValue f‖ :=
      add_le_add (mul_le_mul_of_nonneg_right hCtwo (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hCvalue (norm_nonneg _))
    _ = _ := by ring

/-- The usual squared-energy H1 norm has the same uniform graph bound. -/
theorem zs_h1Norm_le_graph {B : ℝ} (hB : 0 ≤ B)
    (φ : SourcePairL2) (hφ : ‖φ‖ ≤ B) (f : H1Pair) :
    h1Norm f ≤ graphBoundConstant B * (‖zsApply φ f‖ + ‖h1PairValue f‖) :=
  (h1Norm_le_sum f).trans (zs_h1SumNorm_le_graph hB φ hφ f)

/-- The source quantifier order: one constant for all complex potentials and all H1 pairs.
In particular, the same constant works on each of the four boundary domains. -/
theorem zs_graph_norm_estimate (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : SourcePairL2, ‖φ‖ ≤ B → ∀ f : H1Pair,
      h1Norm f ≤ C * (‖zsApply φ f‖ + ‖h1PairValue f‖) :=
  ⟨graphBoundConstant B, graphBoundConstant_nonneg hB, fun φ hφ f => zs_h1Norm_le_graph hB φ hφ f⟩

end NlsGge.Atomic.LIB032
