import QuantumNLS.R52CFDeriv
import QuantumNLS.RF535Final

/-!
# R-52CF5DA1 stage 2: invariance along the finite action flows and transport of the fixed-contour differential

`prop:audit-finite-count-propagation` (GAUGE_RETARGETING.tex:101), proof paragraph "The full-space reduction ...
every real and imaginary transfer component Poisson commutes with this frozen-contour Hamiltonian. Its flow
consequently preserves every transfer value and the full discriminant. Along that flow, the last identity in
Lemma `lem:audit-scalar-period` identifies its full vector field with `Σ t_n X_{I_n}` at every point of that level,
including points outside the original rough-center neighborhood."

For the actual chart data of the accepted R-F5355ABD (`RF535Final.GlobalStatement`) and a FINITELY supported
angle vector `θ` (support in a finite set `F`):
* `Hθ θ = Σ_{n∈F} θ_n I_n` and `X_{Hθ θ} = Σ_{n∈F} θ_n X_{I_n}` (`hamField_Hθ`);
* along the complete flow of `X_{Hθ θ}` every Cauchy value `G_z`, `Im z ≠ 0`, is constant, by the accepted
  brackets `{I_n, Re G_z} = {I_n, Im G_z} = 0` (R-507DD869 batch, `mass_bracket_components`); hence
  `G_z ∘ T_θ = G_z` off the real axis and `s(z;·) ∘ T_θ = s(z;·)` for EVERY `z` (by the accepted transfer
  identity and continuity in `z`), and `I_n ∘ T_θ = I_n` (chart intertwining of R-F5355ABD);
* `T_θ = Φ_κ^{-1} ∘ R_θ ∘ Φ_κ` is differentiable with a SURJECTIVE differential at every point;
* **transport**: if `dI_n(v)[k] = -(2πκ)⁻¹ Re ∮_Γ ∂_v s(z;v)[k] D(z)⁻¹ dz` for all `k` (any fixed contour `Γ`
  and any fixed denominator `D`), then the same identity holds at `T_θ v` with `∂_v s(z; T_θ v)` and the SAME `D`.
No hypothesis is added; all inherited modules are read-only.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
noncomputable section
open Set Filter Topology Complex MeasureTheory
open scoped BigOperators

attribute [local instance] InnerProductSpace.complexToReal

namespace QuantumNLS.R52CFOrbit

open PhysicalTensor (L2T)
open RootCauchyFullBracketR8 (G)
open RootCauchyJointR9 (Regular)
open RootMassInvolutionR8 (mass)
open LabelExactPeriod (rectIntegral)
open SymplecticBracket (hamField pbR)
open QuantumNLS.D01LocalPrimitive (K)
open QuantumNLS.ProductTorusGenerator (Linf)
open QuantumNLS.RF535Final (Hθ Tθ Tact GlobalStatement)

variable {L κ : ℝ} [Fact (0 < L)]

/-! ### Finite-support Hamiltonians -/

theorem Hθ_eq_sum (hκ : 0 < κ) (F : Finset ℤ) (θ : Linf) (hθ : ∀ n ∉ F, θ n = 0) :
    Hθ (L := L) hκ θ = fun u => ∑ n ∈ F, θ n * mass hκ n u := by
  funext u
  unfold Hθ
  exact tsum_eq_sum (fun n hn => by rw [hθ n hn, zero_mul])

theorem differentiableAt_mass (hκ : 0 < κ) (n : ℤ) (u : L2T L) :
    DifferentiableAt ℝ (mass hκ n) u :=
  (DEF014MassAnalytic.analyticAt_physical_coordinate hκ n u).differentiableAt

section Generic
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ι : Type*}

theorem gradient_sum_gen (F : Finset ι) (c : ι → ℝ) (f : ι → H → ℝ) (u : H)
    (hf : ∀ i, DifferentiableAt ℝ (f i) u) :
    SymplecticBracket.gradient (fun v => ∑ i ∈ F, c i * f i v) u =
      ∑ i ∈ F, c i • SymplecticBracket.gradient (f i) u := by
  unfold SymplecticBracket.gradient
  have hd : fderiv ℝ (fun v => ∑ i ∈ F, c i * f i v) u = ∑ i ∈ F, c i • fderiv ℝ (f i) u := by
    have h1 : HasFDerivAt (fun v => ∑ i ∈ F, c i * f i v) (∑ i ∈ F, c i • fderiv ℝ (f i) u) u := by
      apply HasFDerivAt.fun_sum
      intro i _
      exact ((hf i).hasFDerivAt).const_mul (c i)
    exact h1.fderiv
  rw [hd, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_smulₛₗ, starRingEnd_apply, star_trivial]
  rw [smul_comm]

theorem hamField_sum_gen (F : Finset ι) (c : ι → ℝ) (f : ι → H → ℝ) (u : H)
    (hf : ∀ i, DifferentiableAt ℝ (f i) u) :
    hamField (fun v => ∑ i ∈ F, c i * f i v) u = ∑ i ∈ F, c i • hamField (f i) u := by
  unfold hamField
  rw [gradient_sum_gen F c f u hf, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_comm]

end Generic

theorem hamField_Hθ (hκ : 0 < κ) (F : Finset ℤ) (θ : Linf) (hθ : ∀ n ∉ F, θ n = 0) (u : L2T L) :
    hamField (Hθ (L := L) hκ θ) u = ∑ n ∈ F, θ n • hamField (mass hκ n) u := by
  rw [Hθ_eq_sum hκ F θ hθ]
  exact hamField_sum_gen F (fun n => θ n) (fun n => mass hκ n) u (fun n => differentiableAt_mass hκ n u)

/-! ### Constancy of the Cauchy values along the flow -/

theorem differentiableAt_G (hκ : 0 < κ) {z : ℂ} (hz : z.im ≠ 0) (u : L2T L) :
    DifferentiableAt ℝ (G hκ z) u :=
  ((RootCauchyJointR9.analyticAt_joint_regular hκ (u, z) (Or.inl hz)).comp
    (f := fun v : L2T L => (v, z)) (analyticAt_id.prod analyticAt_const)).differentiableAt

/-- The derivative of `G_z` vanishes on every `X_{I_n}`. -/
theorem fderiv_G_hamField_mass (hκ : 0 < κ) {z : ℂ} (hz : z.im ≠ 0) (n : ℤ) (u : L2T L) :
    fderiv ℝ (G hκ z) u (hamField (mass hκ n) u) = 0 := by
  have hb := RootMassInvolutionR9.mass_bracket_components hκ u n z (Or.inl hz)
  have hre : pbR (fun v => (G hκ z v).re) (mass hκ n) u = 0 := by
    rw [SymplecticBracket.pbR_swap, hb.1, neg_zero]
  have him : pbR (fun v => (G hκ z v).im) (mass hκ n) u = 0 := by
    rw [SymplecticBracket.pbR_swap, hb.2, neg_zero]
  have hd := (differentiableAt_G hκ hz u).hasFDerivAt
  unfold pbR at hre him
  have e1 : fderiv ℝ (fun v => (G hκ z v).re) u (hamField (mass hκ n) u) =
      (fderiv ℝ (G hκ z) u (hamField (mass hκ n) u)).re :=
    DFunLike.congr_fun (Complex.reCLM.hasFDerivAt.comp u hd).fderiv (hamField (mass hκ n) u)
  have e2 : fderiv ℝ (fun v => (G hκ z v).im) u (hamField (mass hκ n) u) =
      (fderiv ℝ (G hκ z) u (hamField (mass hκ n) u)).im :=
    DFunLike.congr_fun (Complex.imCLM.hasFDerivAt.comp u hd).fderiv (hamField (mass hκ n) u)
  apply Complex.ext
  · exact e1.symm.trans hre
  · exact e2.symm.trans him

/-- Along any integral curve of `X_{Hθ θ}` (finite support) every off-axis Cauchy value is constant. -/
theorem G_const_along (hκ : 0 < κ) (F : Finset ℤ) (θ : Linf) (hθ : ∀ n ∉ F, θ n = 0)
    (γ : ℝ → L2T L) (hγ : ∀ t, HasDerivAt γ (hamField (Hθ (L := L) hκ θ) (γ t)) t)
    {z : ℂ} (hz : z.im ≠ 0) (s : ℝ) : G hκ z (γ s) = G hκ z (γ 0) := by
  have hder : ∀ t, HasDerivAt (fun r => G hκ z (γ r)) 0 t := by
    intro t
    have h1 := (differentiableAt_G hκ hz (γ t)).hasFDerivAt.comp_hasDerivAt t (hγ t)
    have h0 : fderiv ℝ (G hκ z) (γ t) (hamField (Hθ (L := L) hκ θ) (γ t)) = 0 := by
      rw [hamField_Hθ hκ F θ hθ, map_sum]
      apply Finset.sum_eq_zero
      intro n _
      rw [map_smul, fderiv_G_hamField_mass hκ hz n (γ t), smul_zero]
    rw [h0] at h1
    exact h1
  have hc := is_const_of_deriv_eq_zero (f := fun r => G hκ z (γ r))
    (fun t => (hder t).differentiableAt) (fun t => (hder t).deriv)
  exact hc s 0

/-! ### Invariance under the time-one map `T_θ` -/

variable {d : ℝ} {Φl : L2T L → K} {Ψl : K → L2T L}

theorem G_invariant (hκ : 0 < κ) (hG : GlobalStatement L κ hκ d Φl Ψl) (F : Finset ℤ) (θ : Linf)
    (hθ : ∀ n ∉ F, θ n = 0) (u : L2T L) {z : ℂ} (hz : z.im ≠ 0) :
    G hκ z (Tθ (L := L) hκ θ u) = G hκ z u := by
  obtain ⟨γ, h0, hγ, -, h1⟩ := hG.1.1 θ u
  rw [← h1, G_const_along hκ F θ hθ γ hγ hz 1, h0]

theorem symbol_invariant (hκ : 0 < κ) (hG : GlobalStatement L κ hκ d Φl Ψl) (F : Finset ℤ) (θ : Linf)
    (hθ : ∀ n ∉ F, θ n = 0) (u : L2T L) (z : ℂ) :
    RootScalarPeriodR10.symbol κ (Tθ (L := L) hκ θ u) z = RootScalarPeriodR10.symbol κ u z := by
  have hoff : ∀ w : ℂ, w.im ≠ 0 →
      RootScalarPeriodR10.symbol κ (Tθ (L := L) hκ θ u) w - RootScalarPeriodR10.symbol κ u w = 0 := by
    intro w hw
    rw [RootScalarPeriodR10.transfer_identity hκ _ w (Or.inl hw),
      RootScalarPeriodR10.transfer_identity hκ u w (Or.inl hw)]
    unfold RootScalarPeriodR10.exponent
    rw [G_invariant hκ hG F θ hθ u hw, sub_self]
  have hcont : ∀ v : L2T L, Continuous (fun w : ℂ => RootScalarPeriodR10.symbol κ v w) := by
    intro v
    simp_rw [Prop010ClassicalR10.symbol_eq_trace hκ]
    exact (by fun_prop : Continuous (fun w : ℂ => exp (I * w * L / 2))).mul
      (L2DiscriminantRegularity.continuous_discriminant κ v)
  have h := RootBracketContinuationR9.continuous_zero_of_nonreal
    (((hcont _).sub (hcont u)).continuousAt (x := z)) hoff
  exact sub_eq_zero.mp h

/-- The chart data of `GlobalStatement` give the intertwined form `T_θ = Ψ ∘ R ∘ Φ`. -/
def rot (θ : Linf) : K →L[ℝ] K :=
  LinearMap.mkContinuous
    { toFun := fun z => ActionTorus.rotate (fun n => Circle.exp (-(θ n))) z
      map_add' := fun z w => lp.ext (funext fun n => by
        simp only [ActionTorus.rotate_apply, lp.coeFn_add, Pi.add_apply]; ring)
      map_smul' := fun c z => lp.ext (funext fun n => by
        simp only [ActionTorus.rotate_apply, lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]
        rw [Complex.real_smul, Complex.real_smul]; ring) }
    1 (fun z => by
      have h := ActionTorus.norm_rotate_sub (fun n => Circle.exp (-(θ n))) z 0
      have h0 : ActionTorus.rotate (fun n => Circle.exp (-(θ n))) (0 : K) = 0 :=
        lp.ext (funext fun n => by simp)
      simp only [h0, sub_zero] at h
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      exact h.le)

theorem rot_apply (θ : Linf) (z : K) (n : ℤ) :
    rot θ z n = Complex.exp (-(θ n : ℂ) * Complex.I) * z n := by
  change (Circle.exp (-(θ n)) : ℂ) * z n = _
  rw [Circle.coe_exp]
  congr 2
  push_cast
  ring

theorem rot_neg (θ : Linf) (z : K) : rot θ (rot (-θ) z) = z := by
  refine lp.ext (funext fun n => ?_)
  rw [rot_apply, rot_apply, ← mul_assoc, ← Complex.exp_add]
  have hn : ((-θ : Linf) n : ℝ) = -(θ n) := by simp
  have h0 : -((θ n : ℝ) : ℂ) * Complex.I + -((((-θ : Linf) n : ℝ)) : ℂ) * Complex.I = 0 := by
    rw [hn]; push_cast; ring
  rw [h0, Complex.exp_zero, one_mul]

/-- `I_n ∘ T_θ = I_n`, the differentiable intertwined form of `T_θ`, and a surjective differential. -/
theorem chart_facts (hκ : 0 < κ) (hG : GlobalStatement L κ hκ d Φl Ψl) (θ : Linf) :
    (∀ (n : ℤ) (u : L2T L), mass hκ n (Tθ (L := L) hκ θ u) = mass hκ n u) ∧
    ∀ u : L2T L, ∃ E : L2T L →L[ℝ] L2T L, HasFDerivAt (Tθ (L := L) hκ θ) E u ∧ Function.Surjective E := by
  obtain ⟨Y, Fl, Φ, Ψ, -, -, -, -, -, -, -, -, -, hΨΦ, -, hmass, -, -, hdiff, -, -, -, -, -, hrotθ, -, -⟩ :=
    hG.2
  have hT : ∀ u, Tθ (L := L) hκ θ u = Ψ (rot θ (Φ u)) := by
    intro u
    have hΦ : Φ (Tθ (L := L) hκ θ u) = rot θ (Φ u) := by
      refine lp.ext (funext fun n => ?_)
      rw [hrotθ θ u n, rot_apply]
    rw [← hΦ, hΨΦ]
  refine ⟨fun n u => ?_, fun u => ?_⟩
  · change (RootIndexedMasses.masses hκ (Tθ (L := L) hκ θ u)).1 n = (RootIndexedMasses.masses hκ u).1 n
    rw [← hmass, ← hmass, hrotθ θ u n, norm_mul, Complex.norm_exp]
    simp
  · obtain ⟨e, he, -⟩ := hdiff u
    obtain ⟨e', -, he'⟩ := hdiff (Tθ (L := L) hκ θ u)
    have hΦT : Φ (Tθ (L := L) hκ θ u) = rot θ (Φ u) := by
      refine lp.ext (funext fun n => ?_)
      rw [hrotθ θ u n, rot_apply]
    rw [hΦT] at he'
    have hcomp := he'.comp u ((rot θ).hasFDerivAt.comp u he)
    have hfun : (Ψ ∘ (rot θ ∘ Φ)) = Tθ (L := L) hκ θ := funext fun v => (hT v).symm
    rw [hfun] at hcomp
    refine ⟨_, hcomp, ?_⟩
    intro k
    refine ⟨e.symm (rot (-θ) (e' k)), ?_⟩
    simp [rot_neg]

/-- **Stage 2 headline (transport).**  For finitely supported `θ`: `I_n`, `G_z` (`Im z ≠ 0`) and every
transfer value `s(z;·)` are invariant under `T_θ`, and any fixed-contour, fixed-denominator differential identity
for `I_n` at `v` holds verbatim at `T_θ v` with the transfer differential taken at `T_θ v`. -/
theorem orbit_transport (hκ : 0 < κ) (hG : GlobalStatement L κ hκ d Φl Ψl) (F : Finset ℤ) (θ : Linf)
    (hθ : ∀ n ∉ F, θ n = 0) :
    (∀ (n : ℤ) (u : L2T L), mass hκ n (Tθ (L := L) hκ θ u) = mass hκ n u) ∧
    (∀ (u : L2T L) (z : ℂ), z.im ≠ 0 → G hκ z (Tθ (L := L) hκ θ u) = G hκ z u) ∧
    (∀ (u : L2T L) (z : ℂ),
      RootScalarPeriodR10.symbol κ (Tθ (L := L) hκ θ u) z = RootScalarPeriodR10.symbol κ u z) ∧
    ∀ (n : ℤ) (v : L2T L) (Dn : ℂ → ℂ) (a b h : ℝ),
      (∀ k : L2T L, fderiv ℝ (mass hκ n) v k = -(2 * Real.pi * κ)⁻¹ *
        (rectIntegral (fun z => fderiv ℝ (fun w : L2T L => RootScalarPeriodR10.symbol κ w z) v k / Dn z)
          a b h).re) →
      ∀ k : L2T L, fderiv ℝ (mass hκ n) (Tθ (L := L) hκ θ v) k = -(2 * Real.pi * κ)⁻¹ *
        (rectIntegral (fun z => fderiv ℝ (fun w : L2T L => RootScalarPeriodR10.symbol κ w z)
          (Tθ (L := L) hκ θ v) k / Dn z) a b h).re := by
  obtain ⟨hm, hdiff⟩ := chart_facts hκ hG θ
  refine ⟨hm, fun u z hz => G_invariant hκ hG F θ hθ u hz,
    fun u z => symbol_invariant hκ hG F θ hθ u z, ?_⟩
  intro n v Dn a b h hv k
  obtain ⟨E, hE, hsurj⟩ := hdiff v
  obtain ⟨k', rfl⟩ := hsurj k
  have hmT : (mass hκ n ∘ Tθ (L := L) hκ θ) = mass hκ n := funext fun u => hm n u
  have h1 : fderiv ℝ (mass hκ n) v = (fderiv ℝ (mass hκ n) (Tθ (L := L) hκ θ v)).comp E := by
    have hc := (differentiableAt_mass hκ n (Tθ (L := L) hκ θ v)).hasFDerivAt.comp v hE
    rw [hmT] at hc
    exact hc.fderiv
  have hs : ∀ z : ℂ, fderiv ℝ (fun w : L2T L => RootScalarPeriodR10.symbol κ w z) v k' =
      fderiv ℝ (fun w : L2T L => RootScalarPeriodR10.symbol κ w z) (Tθ (L := L) hκ θ v) (E k') := by
    intro z
    have hsT : ((fun w : L2T L => RootScalarPeriodR10.symbol κ w z) ∘ Tθ (L := L) hκ θ) =
        fun w : L2T L => RootScalarPeriodR10.symbol κ w z :=
      funext fun u => symbol_invariant hκ hG F θ hθ u z
    have hc := (Prop010ClassicalR10.analyticAt_symbol hκ (Tθ (L := L) hκ θ v) z).differentiableAt.hasFDerivAt.comp
      v hE
    rw [hsT] at hc
    rw [hc.fderiv]
    rfl
  have h2 := hv k'
  rw [h1] at h2
  change fderiv ℝ (mass hκ n) (Tθ (L := L) hκ θ v) (E k') = _ at h2
  rw [h2]
  simp_rw [hs]

end QuantumNLS.R52CFOrbit

#print axioms QuantumNLS.R52CFOrbit.orbit_transport
#print axioms QuantumNLS.R52CFOrbit.hamField_Hθ
