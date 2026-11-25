import Mathlib

/-!
# C1: the twist-map lemma (GWP plan, §5.3 and §7 Part C)

Let `κ : (ι → ℂ) → ι → ℝ` be measurable and invariant under all coordinatewise rotations.  The
twist `z ↦ (e^{i κ(z)_i} z_i)_i` preserves Lebesgue measure on `ι → ℂ`.

Proof (group averaging, no skew product is needed).  Let `G = ι → AddCircle (2π)` carry the product
`μ` of the probability Haar measures.  For a measurable `f ≥ 0` and `g ∈ G`:
1. rotation by `g` preserves Lebesgue measure and commutes with the twist (`κ` is rotation invariant),
   so `∫ f(T z) dz = ∫ f(T(g z)) dz = ∫ f(g (T z)) dz`;
2. average over `g ∈ G` and swap the integrals (Tonelli);
3. `T z = h(z) z` is itself a rotation of `z`, and `μ` is translation invariant, so
   `∫ f(g (T z)) dμ(g) = ∫ f(g z) dμ(g)`;
4. swap back and use step 1 for the identity twist: `∫ f(g z) dz = ∫ f(z) dz`.

Everything is Phi-free and does not depend on the rest of the project.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.NLS38

open MeasureTheory Real
open scoped ENNReal

variable {ι : Type*} [Fintype ι]
set_option linter.unusedSectionVars false

/-- The twist of `ι → ℂ` by the angle field `κ`: `(twist κ z)_i = e^{i κ(z)_i} z_i`. -/
def twist (κ : (ι → ℂ) → ι → ℝ) (z : ι → ℂ) : ι → ℂ :=
  fun i => Complex.exp (κ z i * Complex.I) * z i

/-- Rotation of `ι → ℂ` by a point of the torus `ι → AddCircle (2π)`. -/
def rotTorus (g : ι → AddCircle (2 * π)) (z : ι → ℂ) : ι → ℂ :=
  fun i => ((AddCircle.toCircle (g i) : Circle) : ℂ) * z i

theorem toCircle_coe_real (x : ℝ) :
    ((AddCircle.toCircle ((x : ℝ) : AddCircle (2 * π)) : Circle) : ℂ) =
      Complex.exp (x * Complex.I) := by
  rw [AddCircle.toCircle, Function.Periodic.lift_coe, Circle.coe_exp]
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  congr 2
  push_cast
  field_simp

theorem measurable_twist (κ : (ι → ℂ) → ι → ℝ) (hκ : Measurable κ) : Measurable (twist κ) := by
  refine measurable_pi_iff.mpr fun i => ?_
  have h1 : Measurable fun z => κ z i := (measurable_pi_apply i).comp hκ
  have h2 : Measurable fun z : ι → ℂ => z i := measurable_pi_apply i
  unfold twist
  fun_prop

theorem measurable_rotTorus_uncurry :
    Measurable (fun p : (ι → AddCircle (2 * π)) × (ι → ℂ) => rotTorus p.1 p.2) := by
  refine measurable_pi_iff.mpr fun i => ?_
  have h1 : Measurable fun p : (ι → AddCircle (2 * π)) × (ι → ℂ) => p.1 i :=
    (measurable_pi_apply i).comp measurable_fst
  have h2 : Measurable fun p : (ι → AddCircle (2 * π)) × (ι → ℂ) => p.2 i :=
    (measurable_pi_apply i).comp measurable_snd
  have h3 : Measurable fun p : (ι → AddCircle (2 * π)) × (ι → ℂ) =>
      ((AddCircle.toCircle (p.1 i) : Circle) : ℂ) :=
    (continuous_subtype_val.comp
      (AddCircle.continuous_toCircle (T := 2 * π))).measurable.comp h1
  unfold rotTorus
  exact h3.mul h2

theorem measurePreserving_rotTorus (g : ι → AddCircle (2 * π)) :
    MeasurePreserving (rotTorus g) (volume : Measure (ι → ℂ)) volume := by
  have h := measurePreserving_pi (fun _ : ι => (volume : Measure ℂ)) (fun _ : ι => (volume : Measure ℂ))
    (f := fun i (w : ℂ) => (rotation (AddCircle.toCircle (g i))) w)
    (fun i => (rotation (AddCircle.toCircle (g i))).measurePreserving)
  have h2 : MeasurePreserving (rotTorus g) (Measure.pi fun _ : ι => (volume : Measure ℂ))
      (Measure.pi fun _ : ι => (volume : Measure ℂ)) := by
    simp only [rotation_apply] at h
    exact h
  exact h2

theorem rotTorus_add (g h : ι → AddCircle (2 * π)) (z : ι → ℂ) :
    rotTorus g (rotTorus h z) = rotTorus (g + h) z := by
  funext i
  simp [rotTorus, AddCircle.toCircle_add, mul_assoc]

/-- Every rotation of the torus is `e^{iθ}` for a real angle vector. -/
theorem exists_angle (g : ι → AddCircle (2 * π)) :
    ∃ θ : ι → ℝ, ∀ i, g i = ((θ i : ℝ) : AddCircle (2 * π)) := by
  choose θ hθ using fun i => QuotientAddGroup.mk_surjective (g i)
  exact ⟨θ, fun i => (hθ i).symm⟩

theorem rotTorus_coe (θ : ι → ℝ) (z : ι → ℂ) :
    rotTorus (fun i => ((θ i : ℝ) : AddCircle (2 * π))) z =
      fun i => Complex.exp (θ i * Complex.I) * z i := by
  funext i
  simp [rotTorus, toCircle_coe_real]

/-- The twist is the rotation by the angle field itself. -/
theorem twist_eq_rotTorus (κ : (ι → ℂ) → ι → ℝ) (z : ι → ℂ) :
    twist κ z = rotTorus (fun i => ((κ z i : ℝ) : AddCircle (2 * π))) z := by
  rw [rotTorus_coe]; rfl

/-- The twist commutes with the rotations when `κ` is rotation invariant. -/
theorem twist_rotTorus (κ : (ι → ℂ) → ι → ℝ)
    (hinv : ∀ (z : ι → ℂ) (θ : ι → ℝ),
      κ (fun i => Complex.exp (θ i * Complex.I) * z i) = κ z)
    (g : ι → AddCircle (2 * π)) (z : ι → ℂ) :
    twist κ (rotTorus g z) = rotTorus g (twist κ z) := by
  obtain ⟨θ, hθ⟩ := exists_angle g
  have hg : g = fun i => ((θ i : ℝ) : AddCircle (2 * π)) := funext hθ
  subst hg
  have hk : κ (rotTorus (fun i => ((θ i : ℝ) : AddCircle (2 * π))) z) = κ z := by
    rw [rotTorus_coe]; exact hinv z θ
  rw [twist_eq_rotTorus, hk, twist_eq_rotTorus, rotTorus_add, rotTorus_add, add_comm]

instance fact_two_pi_pos38 : Fact (0 < 2 * π) := ⟨by positivity⟩

/-- The Haar probability measure on the torus `ι → AddCircle (2π)`. -/
def haarTorus (ι : Type*) [Fintype ι] : Measure (ι → AddCircle (2 * π)) :=
  Measure.pi fun _ => (AddCircle.haarAddCircle : Measure (AddCircle (2 * π)))

instance : IsProbabilityMeasure (haarTorus ι) := by
  unfold haarTorus; infer_instance

instance : (haarTorus ι).IsAddLeftInvariant := by
  unfold haarTorus; infer_instance

/-- Group-averaging identity: `∫ f ∘ twist = ∫ f` for measurable `f ≥ 0`. -/
theorem lintegral_comp_twist (κ : (ι → ℂ) → ι → ℝ) (hκ : Measurable κ)
    (hinv : ∀ (z : ι → ℂ) (θ : ι → ℝ),
      κ (fun i => Complex.exp (θ i * Complex.I) * z i) = κ z)
    (f : (ι → ℂ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f (twist κ z) = ∫⁻ z, f z := by
  have hT := measurable_twist κ hκ
  have hR := measurable_rotTorus_uncurry (ι := ι)
  have hRs : Measurable (fun p : (ι → ℂ) × (ι → AddCircle (2 * π)) => rotTorus p.2 p.1) :=
    hR.comp measurable_swap
  -- step 4: the average of `f (g z)` over `g` and `z`
  have key1 : ∫⁻ z, ∫⁻ g, f (rotTorus g z) ∂haarTorus ι = ∫⁻ z, f z := by
    have hsw : ∫⁻ g, ∫⁻ z, f (rotTorus g z) ∂volume ∂haarTorus ι =
        ∫⁻ z, ∫⁻ g, f (rotTorus g z) ∂haarTorus ι ∂volume :=
      lintegral_lintegral_swap (μ := haarTorus ι) (ν := (volume : Measure (ι → ℂ)))
        (f := fun g z => f (rotTorus g z)) (hf.comp hR).aemeasurable
    rw [← hsw]
    calc ∫⁻ g, ∫⁻ z, f (rotTorus g z) ∂volume ∂haarTorus ι
        = ∫⁻ g, ∫⁻ z, f z ∂volume ∂haarTorus ι := by
          congr 1; funext g
          exact (measurePreserving_rotTorus g).lintegral_comp hf
      _ = ∫⁻ z, f z := by simp
  -- steps 1-3
  have key2 : ∀ g : ι → AddCircle (2 * π),
      ∫⁻ z, f (twist κ z) = ∫⁻ z, f (rotTorus g (twist κ z)) := by
    intro g
    have h1 : ∫⁻ a, f (twist κ (rotTorus g a)) = ∫⁻ b, f (twist κ b) :=
      (measurePreserving_rotTorus g).lintegral_comp (hf.comp hT)
    rw [← h1]
    congr 1; funext z
    rw [twist_rotTorus κ hinv]
  have key3 : ∀ z : ι → ℂ, ∫⁻ g, f (rotTorus g (twist κ z)) ∂haarTorus ι =
      ∫⁻ g, f (rotTorus g z) ∂haarTorus ι := by
    intro z
    rw [twist_eq_rotTorus]
    simp_rw [rotTorus_add]
    exact lintegral_add_right_eq_self
      (μ := haarTorus ι) (fun g => f (rotTorus g z))
      (fun i => ((κ z i : ℝ) : AddCircle (2 * π)))
  have hsw2 : ∫⁻ g, ∫⁻ z, f (rotTorus g (twist κ z)) ∂volume ∂haarTorus ι =
      ∫⁻ z, ∫⁻ g, f (rotTorus g (twist κ z)) ∂haarTorus ι ∂volume :=
    lintegral_lintegral_swap (μ := haarTorus ι) (ν := (volume : Measure (ι → ℂ)))
      (f := fun g z => f (rotTorus g (twist κ z)))
      (hf.comp (hR.comp (measurable_fst.prodMk (hT.comp measurable_snd)))).aemeasurable
  calc ∫⁻ z, f (twist κ z)
      = ∫⁻ g, ∫⁻ z, f (twist κ z) ∂volume ∂haarTorus ι := by simp
    _ = ∫⁻ g, ∫⁻ z, f (rotTorus g (twist κ z)) ∂volume ∂haarTorus ι := by
        congr 1; funext g; exact key2 g
    _ = ∫⁻ z, ∫⁻ g, f (rotTorus g (twist κ z)) ∂haarTorus ι ∂volume := hsw2
    _ = ∫⁻ z, ∫⁻ g, f (rotTorus g z) ∂haarTorus ι ∂volume := by
        congr 1; funext z; exact key3 z
    _ = ∫⁻ z, f z := key1

theorem measurePreserving_twist {ι : Type*} [Fintype ι] (κ : (ι → ℂ) → ι → ℝ) (hκ : Measurable κ)
    (hinv : ∀ (z : ι → ℂ) (θ : ι → ℝ), κ (fun i => Complex.exp (θ i * Complex.I) * z i) = κ z) :
    MeasureTheory.MeasurePreserving (fun z i => Complex.exp (κ z i * Complex.I) * z i)
      (MeasureTheory.volume : MeasureTheory.Measure (ι → ℂ)) MeasureTheory.volume := by
  have hT : Measurable (fun z i => Complex.exp (κ z i * Complex.I) * z i) :=
    measurable_twist κ hκ
  refine ⟨hT, ?_⟩
  ext s hs
  rw [Measure.map_apply hT hs]
  have := lintegral_comp_twist κ hκ hinv (s.indicator 1) (measurable_one.indicator hs)
  have e1 : ∀ z, (s.indicator (1 : (ι → ℂ) → ℝ≥0∞)) (twist κ z) =
      (twist κ ⁻¹' s).indicator 1 z := by
    intro z; by_cases h : twist κ z ∈ s <;> simp [h]
  simp_rw [e1] at this
  have e2 : ∀ (A : Set (ι → ℂ)), A.indicator (1 : (ι → ℂ) → ℝ≥0∞) = A.indicator (fun _ => 1) :=
    fun A => rfl
  simp_rw [e2] at this
  have hT' : Measurable (twist κ) := hT
  rw [lintegral_indicator_const (hT' hs), lintegral_indicator_const hs] at this
  show volume (twist κ ⁻¹' s) = volume s
  simpa using this

theorem kappa_twist (κ : (ι → ℂ) → ι → ℝ)
    (hinv : ∀ (z : ι → ℂ) (θ : ι → ℝ), κ (fun i => Complex.exp (θ i * Complex.I) * z i) = κ z)
    (z : ι → ℂ) : κ (twist κ z) = κ z := hinv z (κ z)

theorem twist_neg_twist (κ : (ι → ℂ) → ι → ℝ)
    (hinv : ∀ (z : ι → ℂ) (θ : ι → ℝ), κ (fun i => Complex.exp (θ i * Complex.I) * z i) = κ z)
    (z : ι → ℂ) : twist (fun z i => - κ z i) (twist κ z) = z := by
  funext i
  have hk := kappa_twist κ hinv z
  simp only [twist, hk, Complex.ofReal_neg]
  rw [← mul_assoc, ← Complex.exp_add]
  simp

theorem twist_twist_neg (κ : (ι → ℂ) → ι → ℝ)
    (hinv : ∀ (z : ι → ℂ) (θ : ι → ℝ), κ (fun i => Complex.exp (θ i * Complex.I) * z i) = κ z)
    (z : ι → ℂ) : twist κ (twist (fun z i => - κ z i) z) = z := by
  funext i
  have hk : κ (twist (fun z i => - κ z i) z) = κ z := by
    have := hinv z (fun i => - κ z i)
    exact this
  simp only [twist, hk, Complex.ofReal_neg]
  rw [← mul_assoc, ← Complex.exp_add]
  simp

/-- The twist as a measurable equivalence; the inverse is the twist by `-κ`. -/
def twistEquiv (κ : (ι → ℂ) → ι → ℝ) (hκ : Measurable κ)
    (hinv : ∀ (z : ι → ℂ) (θ : ι → ℝ), κ (fun i => Complex.exp (θ i * Complex.I) * z i) = κ z) :
    (ι → ℂ) ≃ᵐ (ι → ℂ) where
  toFun := twist κ
  invFun := twist (fun z i => - κ z i)
  left_inv := twist_neg_twist κ hinv
  right_inv := twist_twist_neg κ hinv
  measurable_toFun := measurable_twist κ hκ
  measurable_invFun := measurable_twist _ (by
    refine measurable_pi_iff.mpr fun i => ?_
    exact ((measurable_pi_apply i).comp hκ).neg)

theorem twistEquiv_apply (κ : (ι → ℂ) → ι → ℝ) (hκ : Measurable κ)
    (hinv : ∀ (z : ι → ℂ) (θ : ι → ℝ), κ (fun i => Complex.exp (θ i * Complex.I) * z i) = κ z)
    (z : ι → ℂ) : twistEquiv κ hκ hinv z = twist κ z := rfl

theorem twistEquiv_symm_apply (κ : (ι → ℂ) → ι → ℝ) (hκ : Measurable κ)
    (hinv : ∀ (z : ι → ℂ) (θ : ι → ℝ), κ (fun i => Complex.exp (θ i * Complex.I) * z i) = κ z)
    (z : ι → ℂ) : (twistEquiv κ hκ hinv).symm z = twist (fun z i => - κ z i) z := rfl

theorem measurePreserving_twistEquiv (κ : (ι → ℂ) → ι → ℝ) (hκ : Measurable κ)
    (hinv : ∀ (z : ι → ℂ) (θ : ι → ℝ), κ (fun i => Complex.exp (θ i * Complex.I) * z i) = κ z) :
    MeasurePreserving (twistEquiv κ hκ hinv) (volume : Measure (ι → ℂ)) volume :=
  measurePreserving_twist κ hκ hinv

theorem map_withDensity_twist (κ : (ι → ℂ) → ι → ℝ) (hκ : Measurable κ)
    (hinv : ∀ (z : ι → ℂ) (θ : ι → ℝ), κ (fun i => Complex.exp (θ i * Complex.I) * z i) = κ z)
    (ρ : (ι → ℂ) → ℝ≥0∞) (hρ : Measurable ρ) (hρ' : ∀ z, ρ (twist κ z) = ρ z) :
    (volume.withDensity ρ).map (twist κ) = volume.withDensity ρ := by
  have hT := measurable_twist κ hκ
  ext s hs
  rw [Measure.map_apply hT hs, withDensity_apply _ (hT hs), withDensity_apply _ hs,
    ← lintegral_indicator (hT hs), ← lintegral_indicator hs]
  have e1 : ∀ z, (twist κ ⁻¹' s).indicator ρ z = (s.indicator ρ) (twist κ z) := by
    intro z
    by_cases h : twist κ z ∈ s <;> simp [Set.indicator, h, hρ']
  simp_rw [e1]
  exact lintegral_comp_twist κ hκ hinv _ (hρ.indicator hs)

/-! ### Regression probes (the hypotheses are satisfiable and the two basic cases are covered) -/

/-- Constant angle (pure rotation) preserves Lebesgue measure. -/
theorem measurePreserving_twist_const (c : ι → ℝ) :
    MeasurePreserving (twist (fun _ => c)) (volume : Measure (ι → ℂ)) volume :=
  measurePreserving_twist (fun _ => c) measurable_const (fun _ _ => rfl)

/-- The radial twist `κ z i = ‖z i‖` preserves Lebesgue measure. -/
theorem measurePreserving_twist_radial :
    MeasurePreserving (twist (fun (z : ι → ℂ) i => ‖z i‖)) (volume : Measure (ι → ℂ)) volume := by
  refine measurePreserving_twist _ ?_ ?_
  · exact measurable_pi_iff.mpr fun i => (measurable_pi_apply i).norm
  · intro z θ
    funext i
    simp

/-- A mixed radial twist with a coupling between sites, `κ z i = ∑ j ‖z j‖² + ‖z i‖`. -/
theorem measurePreserving_twist_coupled :
    MeasurePreserving (twist (fun (z : ι → ℂ) i => ∑ j, ‖z j‖ ^ 2 + ‖z i‖))
      (volume : Measure (ι → ℂ)) volume := by
  refine measurePreserving_twist _ ?_ ?_
  · refine measurable_pi_iff.mpr fun i => ?_
    have h : ∀ j, Measurable fun z : ι → ℂ => ‖z j‖ := fun j => (measurable_pi_apply j).norm
    exact (Finset.measurable_sum _ fun j _ => (h j).pow_const 2).add (h i)
  · intro z θ
    funext i
    simp

/-- Corollary for angles depending only on the squared moduli (the form used by the NLS flow on
finite-gap tori): `z_i ↦ e^{i θ_i(|z_1|², …, |z_n|²)} z_i`. -/
theorem measurePreserving_twist_modulus (θ : ι → (ι → ℝ) → ℝ) (hθ : ∀ i, Measurable (θ i)) :
    MeasurePreserving (fun (z : ι → ℂ) i => Complex.exp (θ i (fun j => ‖z j‖ ^ 2) * Complex.I) * z i)
      (volume : Measure (ι → ℂ)) volume := by
  refine measurePreserving_twist (fun (z : ι → ℂ) i => θ i (fun j => ‖z j‖ ^ 2)) ?_ ?_
  · refine measurable_pi_iff.mpr fun i => (hθ i).comp ?_
    exact measurable_pi_iff.mpr fun j => ((measurable_pi_apply j).norm).pow_const 2
  · intro z φ
    funext i
    simp

end NlsGge.NLS38
