import QuantumNLS.WindowStrongPathR46b
import QuantumNLS.WindowComparisonR45b
import QuantumNLS.RB7Rot
import QuantumNLS.Prop025OInputs
import QuantumNLS.Q07BUniformCutsR16
import QuantumNLS.WindowAssemblyR45b
import QuantumNLS.RB7Jet
import QuantumNLS.RB7Rotation

/-! The diagonal formula and closed-interval uniqueness for the genuine
unweighted Hilbert Hamiltonian equation, including trajectories with zeros. -/
noncomputable section WindowAmbientR46b
set_option autoImplicit false
set_option maxHeartbeats 2500000
attribute [local instance] InnerProductSpace.complexToReal
open Set
open scoped ComplexConjugate
open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.WindowPhaseR44b QuantumNLS.WindowGradientIdentificationR44b
open QuantumNLS.WindowRadialR45b QuantumNLS.WindowTrajectoryR45b
open QuantumNLS.WindowStrongPathR46b QuantumNLS.WindowInterpolationR44b QuantumNLS.WindowRateEstimateR44b
open QuantumNLS.SymplecticBracket

namespace QuantumNLS.WindowAmbientR46b

abbrev E := WSeq unitWeight

theorem inner_coordinate (z : E) (j : ℤ) (c : ℂ) :
    inner ℂ z (coordinate unitWeight j c) = conj (z.val j) * c := by
  rw [inner_def, ← (lp.hasSum_inner (𝕜 := ℂ) _ _).tsum_eq, tsum_eq_single j]
  · change inner ℂ (toL2 unitWeight z j) (toL2 unitWeight (coordinate unitWeight j c) j) = _
    rw [toL2_apply, toL2_apply, coordinate_val]
    simp [RCLike.inner_apply, unitWeight, mul_comm]
  · intro n hn
    change inner ℂ (toL2 unitWeight z n) (toL2 unitWeight (coordinate unitWeight j c) n) = 0
    have hzero : toL2 unitWeight (coordinate unitWeight j c) n = 0 := by
      rw [toL2_apply, coordinate_val, ite_eq_right hn, mul_zero]
    erw [hzero, inner_zero_right]

theorem hamField_coordinate {G : E → ℝ} {z : E} (hd : DifferentiableAt ℝ G z)
    (hi : ∀ α x, G (rotate α x) = G x) (j : ℤ) :
    (hamField G z).val j = -Complex.I * (frequency G z j : ℂ) * z.val j := by
  have hg (c : ℂ) :
      (conj ((SymplecticBracket.gradient G z).val j) * c).re =
      (conj ((frequency G z j : ℂ) * z.val j) * c).re := by
    have h := coordinate_gradient hd hi j c
    rw [fderiv_eq_two_inner_gradient, real_inner_eq_re_inner ℂ, inner_coordinate] at h
    change 2 * (conj ((SymplecticBracket.gradient G z).val j) * c).re = _ at h
    linarith
  have he : (SymplecticBracket.gradient G z).val j = (frequency G z j : ℂ) * z.val j := by
    apply Complex.ext
    · simpa using hg 1
    · simpa [Complex.mul_re] using hg Complex.I
  change -Complex.I * (SymplecticBracket.gradient G z).val j = _
  rw [he, mul_assoc]

theorem differentiableAt_rotate {G : E → ℝ} {x : E}
    (hd : DifferentiableAt ℝ G x) (hi : ∀ α z, G (rotate α z) = G z) (α : ℤ → ℝ) :
    DifferentiableAt ℝ G (rotate α x) := by
  have he : rotate (-α) (rotate α x) = x := by
    apply WSeq.ext
    funext j
    simp only [rotate_val, Circle.coe_exp, Pi.neg_apply]
    rw [← mul_assoc, ← Complex.exp_add]
    simp
  have h : DifferentiableAt ℝ (fun z => G (rotate (-α) z)) (rotate α x) :=
    (he.symm ▸ hd).comp _ (RB7.rotCLM (fun j => Circle.exp ((-α) j))).differentiableAt
  exact (funext (hi (-α))) ▸ h

/-- Norm derivative of the ambient solution. The initial Hilbert gradient
supplies the summable generator and phase invariance gives the field at time t. -/
theorem ambient_solution {G : E → ℝ} {x : E} (hd : DifferentiableAt ℝ G x)
    (hi : ∀ α z, G (rotate α z) = G z) (τ : ℝ) :
    HasDerivAt (phasePath (frequency G x) x)
      (hamField G (phasePath (frequency G x) x τ)) τ := by
  have h := phasePath_deriv (frequency G x) x (hamField G x)
    (hamField_coordinate hd hi) τ
  convert h using 1
  apply WSeq.ext
  funext j
  let α := fun n => -τ * frequency G x n
  have hd' := differentiableAt_rotate hd hi α
  have he := frequency_rotate α hd hd' hi j
  change (hamField G (rotate α x)).val j = (rotate α (hamField G x)).val j
  rw [hamField_coordinate hd' hi, he]
  simp only [rotate_val, hamField_coordinate hd hi]
  ring

theorem ambient_unique {G : E → ℝ} (hi : ∀ α z, G (rotate α z) = G z)
    {γ : ℝ → E}
    (hγ : ∀ τ ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ G (γ τ) ∧
      HasDerivWithinAt γ (hamField G (γ τ)) (Icc 0 1) τ)
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    γ τ = phasePath (frequency G (γ 0)) (γ 0) τ := by
  have hcoord (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (j : ℤ) :
      HasDerivWithinAt (fun b => (γ b).val j)
        (-Complex.I * (frequency G (γ a) j : ℂ) * (γ a).val j) (Icc 0 1) a := by
    have h := (evalReal unitWeight j).hasFDerivAt.comp_hasDerivWithinAt a (hγ a ha).2
    change HasDerivWithinAt (fun b => (γ b).val j) ((hamField G (γ a)).val j) (Icc 0 1) a at h
    rw [hamField_coordinate (hγ a ha).1 hi] at h
    exact h
  have hm (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (j : ℤ) :
      ‖(γ a).val j‖ = ‖(γ 0).val j‖ :=
    modulus_on_interval (fun b => (γ b).val j) (fun b => frequency G (γ b) j)
      (fun b hb => hcoord b hb j) ha
  apply WSeq.ext
  funext j
  exact scalar_unique_on_interval (fun b => (γ b).val j) (frequency G (γ 0) j)
    (fun a ha => by
      have he := frequency_of_moduli (hγ 0 (by norm_num)).1 (hγ a ha).1 hi
        (fun n => (hm a ha n).symm) j
      simpa only [he] using hcoord a ha j) hτ

/-- Restricting a differentiable scalar to a higher sequence order keeps
every radial line differential, and hence its actual real multiplier. -/
theorem frequency_lower {W : PosWeight} (hW : ∀ j, 1 ≤ W.w j) {F : E → ℝ}
    {z : WSeq W} (hd : DifferentiableAt ℝ F (lower W hW z)) (j : ℤ) :
    frequency (fun x => F (lower W hW x)) z j = frequency F (lower W hW z) j := by
  let A := WindowComparisonR45b.lowerCLM W hW
  have h := (hd.hasFDerivAt.comp z A.hasFDerivAt).fderiv
  change fderiv ℝ (fun x => F (lower W hW x)) z = (fderiv ℝ F (lower W hW z)).comp A at h
  unfold frequency
  rw [h, ContinuousLinearMap.comp_apply]
  have he : A (coordinate W j (z.val j)) = coordinate unitWeight j ((lower W hW z).val j) := by
    apply WSeq.ext
    funext n
    change (coordinate W j (z.val j)).val n = (coordinate unitWeight j (z.val j)).val n
    simp only [coordinate_val]
  rw [he]
  rfl

end QuantumNLS.WindowAmbientR46b

#print axioms QuantumNLS.WindowAmbientR46b.ambient_solution
#print axioms QuantumNLS.WindowAmbientR46b.ambient_unique
#print axioms QuantumNLS.WindowAmbientR46b.frequency_lower

end WindowAmbientR46b

/-! The auxiliary path for the actual full-mass window Hamiltonian, with
full real physical differentials. The construction and uniqueness use L²
norm derivatives, including at zero chart coordinates. -/
noncomputable section WindowPhysicalPathR46b
set_option autoImplicit false
set_option maxHeartbeats 4500000
attribute [local instance] InnerProductSpace.complexToReal
open Set Filter Topology
open scoped ComplexConjugate
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.Prop025OInputs QuantumNLS.Reg015Setting
open QuantumNLS.WindowInterpolationR44b QuantumNLS.WindowPhaseR44b
open QuantumNLS.WindowStrongPathR46b QuantumNLS.WindowAmbientR46b
open QuantumNLS.WindowActualEstimatesR44b QuantumNLS.WindowScalarsR45b
open QuantumNLS.WindowRadialR45b QuantumNLS.WindowGradientIdentificationR44b
open QuantumNLS.SymplecticBracket QuantumNLS.WindowSymplecticR45b
open QuantumNLS.PROP017UniformN

namespace QuantumNLS.WindowPhysicalPathR46b
variable {L κ : ℝ} [Fact (0 < L)]

private abbrev U := toL2ᵢ unitWeight

theorem U_apply (x : E) (j : ℤ) : U x j = x.val j := by
  change toL2 unitWeight x j = x.val j
  rw [toL2_apply]
  simp [unitWeight]

def toChart {hκ : 0 < κ} (C : Def021ChartR41b.Chart L κ hκ) (u : L2T L) : E :=
  U.symm (C.Φ u)

def fromChart {hκ : 0 < κ} (C : Def021ChartR41b.Chart L κ hκ) (x : E) : L2T L :=
  C.Ψ (U x)

@[simp] theorem from_to {hκ : 0 < κ} (C : Def021ChartR41b.Chart L κ hκ) (u : L2T L) :
    fromChart C (toChart C u) = u := by simp [fromChart, toChart, C.left_inverse]

@[simp] theorem to_from {hκ : 0 < κ} (C : Def021ChartR41b.Chart L κ hκ) (x : E) :
    toChart C (fromChart C x) = x := by simp [fromChart, toChart, C.right_inverse]

private theorem symplectic_differential {hκ : 0 < κ} (C : Def021ChartR41b.Chart L κ hκ)
    (u : L2T L) :
    ∃ e : L2T L ≃L[ℝ] E,
      HasFDerivAt (toChart C) e.toContinuousLinearMap u ∧
      HasFDerivAt (fromChart C) e.symm.toContinuousLinearMap (toChart C u) ∧
      ∀ v w, omega (e v) (e w) = omega v w := by
  obtain ⟨J, hJ, hJinv⟩ := C.differential u
  let I : Seq ≃L[ℝ] E :=
    { toLinearEquiv := U.symm.toLinearEquiv.restrictScalars ℝ
      continuous_toFun := U.symm.continuous
      continuous_invFun := U.continuous }
  let e := J.trans I
  have hP : HasFDerivAt (toChart C) e.toContinuousLinearMap u :=
    I.toContinuousLinearMap.hasFDerivAt.comp u hJ
  have hQ : HasFDerivAt (fromChart C) e.symm.toContinuousLinearMap (toChart C u) := by
    have heq : I.symm (toChart C u) = C.Φ u := U.apply_symm_apply _
    have hJinv' : HasFDerivAt C.Ψ J.symm.toContinuousLinearMap (I.symm (toChart C u)) :=
      heq.symm ▸ hJinv
    have h := hJinv'.comp (toChart C u) (I.symm.toContinuousLinearMap.hasFDerivAt :
      HasFDerivAt (fun x => U x) I.symm.toContinuousLinearMap (toChart C u))
    exact h
  refine ⟨e,hP,hQ,fun v w => ?_⟩
  change 2 * (inner ℂ (toL2 unitWeight (U.symm (J v))) (toL2 unitWeight (U.symm (J w)))).im = _
  change 2 * (inner ℂ (U (U.symm (J v))) (U (U.symm (J w)))).im = _
  rw [U.apply_symm_apply, U.apply_symm_apply]
  simpa only [hJ.fderiv, ContinuousLinearEquiv.coe_coe, omega] using C.symplectic u v w

private theorem fields {hκ : 0 < κ} (C : Def021ChartR41b.Chart L κ hκ)
    (F : L2T L → ℝ) {u : L2T L} (hF : DifferentiableAt ℝ F u) :
    fderiv ℝ (toChart C) u (hamField F u) =
      hamField (F ∘ fromChart C) (toChart C u) := by
  obtain ⟨e,hP,hQ,hs⟩ := symplectic_differential C u
  rw [hP.fderiv]
  apply omega_ext
  intro k
  have hf : HasFDerivAt F (fderiv ℝ F u) (fromChart C (toChart C u)) := by
    simpa only [from_to] using hF.hasFDerivAt
  have h := (hf.comp _ hQ).fderiv
  calc omega (e (hamField F u)) k =
        omega (hamField F u) (e.symm k) := by rw [← hs, e.apply_symm_apply]
    _ = fderiv ℝ F u (e.symm k) := omega_hamField F u _
    _ = omega (hamField (F ∘ fromChart C) (toChart C u)) k := by
      rw [omega_hamField, h, ContinuousLinearMap.comp_apply]
      rfl

private theorem gradient_spec (F : L2T L → ℝ) (u : L2T L)
    (hF : DifferentiableAt ℝ F u) : IsPhysGradient F u (SymplecticBracket.gradient F u) := by
  unfold IsPhysGradient
  have he : fderiv ℝ F u = (2 : ℝ) •
      (Complex.reCLM.comp ((innerSL ℂ (SymplecticBracket.gradient F u)).restrictScalars ℝ)) := by
    apply ContinuousLinearMap.ext
    intro v
    have hd := fderiv_eq_two_inner_gradient F u v
    rw [real_inner_eq_re_inner ℂ] at hd
    change fderiv ℝ F u v = 2 * (inner ℂ (SymplecticBracket.gradient F u) v).re
    exact hd
  exact he ▸ hF.hasFDerivAt

private theorem gradient_eq {F : L2T L → ℝ} {u g : L2T L}
    (hg : IsPhysGradient F u g) : hamField F u = (-Complex.I) • g := by
  have hd := (show HasFDerivAt F _ u from hg).fderiv
  apply omega_ext
  intro v
  rw [omega_hamField]
  erw [hd]
  change 2 * (inner ℂ g v).re = 2 * (inner ℂ ((-Complex.I) • g) v).im
  rw [inner_smul_left]
  simp

theorem pulled_invariant (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (R : Finset ℕ) (t : ℕ → ℝ) (a : ℝ) (α : ℤ → ℝ) (x : E) :
    (windowFamily κ R t a ∘ fromChart C) (rotate α x) =
      (windowFamily κ R t a ∘ fromChart C) x := by
  have hm : ∀ j, ‖U (rotate α x) j‖ = ‖U x j‖ := by
    intro j
    rw [U_apply,U_apply,rotate_val,norm_mul,Circle.norm_coe,one_mul]
  have he := WindowActionInvariantR44b.measure_of_moduli hκ C _ _ hm
  rw [PhysicalL2Normalization.measure_eq_Mmeas hκ, PhysicalL2Normalization.measure_eq_Mmeas hκ] at he
  simp only [Function.comp_apply, windowFamily, windowHam, fromChart, he]

/-- Every physical solution is the inverse image of the ambient phase path.
The solution itself supplies the differentiation along its path. -/
theorem physical_unique (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    {R : Finset ℕ} {t : ℕ → ℝ} {a : ℝ} {u : L2T L} {y : ℝ → L2T L}
    (hy : IsWindowTrajectory κ R t a u y) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    y τ = fromChart C
      (phasePath (frequency (windowFamily κ R t a ∘ fromChart C) (toChart C u)) (toChart C u) τ) := by
  let F := windowFamily (L := L) κ R t a
  let γ : ℝ → E := toChart C ∘ y
  have hγ (b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) :
      DifferentiableAt ℝ (F ∘ fromChart C) (γ b) ∧
      HasDerivWithinAt γ (hamField (F ∘ fromChart C) (γ b)) (Icc 0 1) b := by
    obtain ⟨g,hg,hdy⟩ := hy.2 b hb
    obtain ⟨e,hP,hQ,-⟩ := symplectic_differential C (y b)
    have hF : DifferentiableAt ℝ F (y b) := (show HasFDerivAt F _ (y b) from hg).differentiableAt
    have hF' : DifferentiableAt ℝ F (fromChart C (γ b)) := by
      simpa only [γ, Function.comp_apply, from_to] using hF
    refine ⟨hF'.comp _ hQ.differentiableAt,?_⟩
    have hh := hP.comp_hasDerivWithinAt b hdy
    have he := fields C F hF
    rw [gradient_eq hg, hP.fderiv] at he
    exact he ▸ hh
  have eq := ambient_unique (pulled_invariant hκ C R t a) hγ hτ
  have h0 : γ 0 = toChart C u := congrArg (toChart C) hy.1
  rw [h0] at eq
  exact (from_to C (y τ)).symm.trans (congrArg (fromChart C) eq)

/-- For a cutoff with a genuine L² differential at the initial point,
the phase path provides the physical solution itself. -/
theorem physical_exists (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    {R : Finset ℕ} {t : ℕ → ℝ} {a : ℝ} {u : L2T L}
    (hd : DifferentiableAt ℝ (windowFamily κ R t a) u) :
    IsWindowTrajectory κ R t a u (fun τ => fromChart C
      (phasePath (frequency (windowFamily κ R t a ∘ fromChart C) (toChart C u)) (toChart C u) τ)) := by
  let F := windowFamily (L := L) κ R t a
  let G := F ∘ fromChart C
  let x := toChart C u
  let z := phasePath (frequency G x) x
  have h0 : z 0 = x := by
    apply WSeq.ext
    funext j
    simp [z,phasePath]
  refine ⟨by change fromChart C (z 0) = u; rw [h0,from_to],?_⟩
  intro τ _
  have hi := pulled_invariant hκ C R t a
  obtain ⟨e,hP,hQ,-⟩ := symplectic_differential C u
  have hd' : DifferentiableAt ℝ G x := by
    apply DifferentiableAt.comp _ _ hQ.differentiableAt
    simpa only [x,from_to] using hd
  have hzt : DifferentiableAt ℝ G (z τ) :=
    differentiableAt_rotate hd' hi (fun j => -τ * frequency G x j)
  obtain ⟨D,hD,hDi,-⟩ := symplectic_differential C (fromChart C (z τ))
  have ht : DifferentiableAt ℝ F (fromChart C (z τ)) := by
    have hzt' : DifferentiableAt ℝ G (toChart C (fromChart C (z τ))) := by
      rw [to_from]; exact hzt
    have h := hzt'.comp (fromChart C (z τ)) hD.differentiableAt
    simpa only [G, Function.comp_def, from_to] using h
  have hf := fields C F ht
  rw [to_from,hD.fderiv] at hf
  rw [to_from] at hDi
  have hv := hDi.comp_hasDerivAt τ (ambient_solution hd' hi τ)
  refine ⟨SymplecticBracket.gradient F (fromChart C (z τ)),gradient_spec F _ ht,?_⟩
  have hv' : HasDerivAt (fun b => fromChart C (z b)) (hamField F (fromChart C (z τ))) τ := by
    rw [← hf] at hv
    change HasDerivAt (fromChart C ∘ z)
      (D.symm (D (hamField F (fromChart C (z τ))))) τ at hv
    rwa [D.symm_apply_apply] at hv
  exact hv'.hasDerivWithinAt

end QuantumNLS.WindowPhysicalPathR46b

#print axioms QuantumNLS.WindowPhysicalPathR46b.physical_unique
#print axioms QuantumNLS.WindowPhysicalPathR46b.physical_exists

end WindowPhysicalPathR46b

/-! The concrete smooth-jet topology used by PROP-025 controls every fixed
physical Sobolev norm, and hence the compact high-order chart class. -/
noncomputable section WindowSmoothClassR46b
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.Fourier QuantumNLS.ClassicalCharges QuantumNLS.WeakDerivatives
open QuantumNLS.Def033HierarchyR24m QuantumNLS.SmoothScalarMomentsPhysical
open QuantumNLS.WindowActualEstimatesR44b QuantumNLS.Reg015Setting
open QuantumNLS.RB7

namespace QuantumNLS.WindowSmoothClassR46b
variable {L κ : ℝ} [Fact (0 < L)]

theorem physical_eq_smoothL2 (u : Smooth L) : physical u = smoothL2 u.property := rfl

def jetL2 (k : ℕ) (u : Smooth L) : L2T L := smoothL2 (smooth_iter u.property k)

theorem continuous_jetL2 (k : ℕ) : Continuous (jetL2 (L := L) k) := by
  let lift (u : Smooth L) : C(AddCircle L, ℂ) :=
    liftC (smooth_iter u.property k).smooth.continuous (smooth_iter u.property k).periodic
  have hj : Continuous (fun u : Smooth L => jet L u k) :=
    (continuous_apply k).comp (continuous_induced_dom : Continuous (jet L))
  have hl : Continuous lift := by
    rw [continuous_iff_continuousAt]
    intro u
    apply Metric.continuousAt_iff'.mpr
    intro ε hε
    have h := Metric.continuousAt_iff'.mp (hj.continuousAt (x := u)) ε hε
    filter_upwards [h] with v hv
    apply lt_of_le_of_lt _ hv
    rw [dist_eq_norm, dist_eq_norm]
    apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro x
    let a := AddCircle.equivIoc L (0 : ℝ) x
    have ha : a.val ∈ Icc (0 : ℝ) L := ⟨a.property.1.le, by simpa using a.property.2⟩
    have hx : (a.val : AddCircle L) = x := AddCircle.coe_equivIoc
    rw [← hx]
    change ‖lift v (a.val : AddCircle L) - lift u (a.val : AddCircle L)‖ ≤ _
    simp only [lift, liftC_coe]
    exact ContinuousMap.norm_coe_le_norm (jet L v k - jet L u k) ⟨a.val, ha⟩
  exact ((ContinuousMap.toLp (E := ℂ) 2 (volume : Measure (AddCircle L)) ℂ).continuous.comp hl)

def smoothSob (s : ℝ) (u : Smooth L) : H02 L s :=
  WField.mk (physical u) (by rw [physical_eq_smoothL2]; exact memHs_of_smooth u.property s)

private theorem fourier_jetL2 (k : ℕ) (u : Smooth L) (n : ℤ) :
    fourierL2 L (jetL2 k u) n = (ikn L n)^k * fourierL2 L (physical u) n := by
  rw [jetL2, physical_eq_smoothL2, fourierL2_smoothL2, fourierL2_smoothL2, cof_iterated]

omit [Fact (0 < L)] in
private theorem weight_bound {s : ℝ} {k : ℕ} (hk : s ≤ k) (n : ℤ) :
    (def002 L s).w n ≤ 2^(2*k-1) * (1+‖(ikn L n)^k‖^2) := by
  have hn : 1 ≤ 1 + |freq L n| := by linarith [abs_nonneg (freq L n)]
  have h1 : (def002 L s).w n ≤ (1 + |freq L n|) ^ (2*k) := by
    change (1 + |freq L n|) ^ (2*s) ≤ _
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hn
    push_cast
    linarith
  have h2 := add_pow_le (zero_le_one' ℝ) (abs_nonneg (freq L n)) (2*k)
  rw [one_pow] at h2
  have h3 : ‖(ikn L n)^k‖^2 = |freq L n| ^ (2*k) := by
    rw [norm_pow, ← pow_mul, Nat.mul_comm k 2]
    simp [ikn, Complex.norm_real, Real.norm_eq_abs]
  simpa only [h3] using h1.trans h2

theorem squared_sobolev_distance {s : ℝ} {k : ℕ} (hk : s ≤ k) (u v : Smooth L) :
    dist (smoothSob s u) (smoothSob s v) ^ 2 ≤
      2^(2*k-1) * (dist (jetL2 0 u) (jetL2 0 v)^2 + dist (jetL2 k u) (jetL2 k v)^2) := by
  let x := smoothSob s u - smoothSob s v
  let a := fourierL2 L (jetL2 0 u - jetL2 0 v)
  let b := fourierL2 L (jetL2 k u - jetL2 k v)
  have ha (n : ℤ) : a n = fourierL2 L x.val n := by
    change a n = fourierL2 L (physical u - physical v) n
    simp only [a, map_sub, lp.coeFn_sub,Pi.sub_apply, fourier_jetL2, pow_zero, one_mul]
  have hb (n : ℤ) : b n = (ikn L n)^k * a n := by
    simp only [b, a, map_sub, lp.coeFn_sub,Pi.sub_apply, fourier_jetL2, pow_zero, one_mul, mul_sub]
  have hsa : HasSum (fun n => ‖a n‖^2) (‖a‖^2) := by
    simpa [Real.rpow_two] using lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) a
  have hsb : HasSum (fun n => ‖b n‖^2) (‖b‖^2) := by
    simpa [Real.rpow_two] using lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) b
  simp only [dist_eq_norm]
  change ‖x‖^2 ≤ _
  rw [WField.norm_sq_eq_tsum]
  have hs := (hsa.add hsb).mul_left ((2 : ℝ)^(2*k-1))
  have hpoint (n : ℤ) : (def002 L s).w n * ‖fourierL2 L x.val n‖^2 ≤
      2^(2*k-1) * (‖a n‖^2 + ‖b n‖^2) := by
    rw [hb, norm_mul, mul_pow, ← ha]
    calc _ ≤ (2^(2*k-1) * (1 + ‖(ikn L n)^k‖^2)) * ‖a n‖^2 :=
          mul_le_mul_of_nonneg_right (weight_bound hk n) (sq_nonneg _)
      _ = _ := by ring
  have h := (WField.summable x).tsum_le_tsum hpoint hs.summable
  rwa [hs.tsum_eq, show ‖a‖ = ‖jetL2 0 u - jetL2 0 v‖ from
      (fourierL2 L).norm_map _, show ‖b‖ = ‖jetL2 k u - jetL2 k v‖ from
      (fourierL2 L).norm_map _] at h

/-- Arbitrary compact smooth classes, in the exact topology of WindowInput,
have compact images at every fixed physical Sobolev order. -/
theorem continuous_smoothSob (s : ℝ) : Continuous (smoothSob (L := L) s) := by
  obtain ⟨k,hk⟩ := exists_nat_ge s
  rw [continuous_iff_continuousAt]
  intro u
  let m : Smooth L → ℝ := fun v =>
    2^(2*k-1) * (dist (jetL2 0 v) (jetL2 0 u)^2 +
      dist (jetL2 k v) (jetL2 k u)^2)
  have hm : Continuous m := continuous_const.mul
    ((((continuous_jetL2 0).dist continuous_const).pow 2).add
      (((continuous_jetL2 k).dist continuous_const).pow 2))
  have he : m u = 0 := by simp [m]
  have hm0 : Tendsto m (𝓝 u) (𝓝 0) := he ▸ hm.continuousAt.tendsto
  have hdist : Tendsto (fun v => dist (smoothSob s v) (smoothSob s u)) (𝓝 u) (𝓝 0) := by
    have hsq : Tendsto (fun v => Real.sqrt (m v)) (𝓝 u) (𝓝 0) := by
      have ht := (Real.continuous_sqrt.continuousAt (x := 0)).tendsto.comp hm0
      rw [Real.sqrt_zero] at ht
      exact ht
    refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hsq
    filter_upwards [] with v
    exact Real.le_sqrt_of_sq_le (squared_sobolev_distance hk v u)
  exact tendsto_iff_dist_tendsto_zero.mpr hdist

/-- The fixed h^(4d+9) chart image is compact for the printed class. -/
theorem compact_chart_lift (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (d : ℕ) {K : Set (Smooth L)} (hK : IsCompact K) :
    ∃ Z : Smooth L → h02 L (sequenceOrder d),
      Continuous Z ∧ IsCompact (Z '' K) ∧
      ∀ u : Smooth L, toBase (sequenceOrder d) (sequenceOrder d).2 (Z u) = C.Φ (physical u) := by
  let s := sequenceOrder d
  let e := WindowInverseRestrictionR44b.baseHomeo hκ C
  have hm : ExactModuli (V := Set.univ) (e.trans (Homeomorph.Set.univ Seq).symm) hκ :=
    fun u n => C.actions u n
  obtain ⟨F,hF⟩ := (Reg015HFinal.REG015_final hκ s s.2).2.2 univ _ hm
  let G : H02 L s ≃ₜ h02 L s := F.trans (WindowInverseRestrictionR44b.targetUniv s s.2).symm
  let Z := G ∘ smoothSob s
  have hc : Continuous Z := G.continuous.comp (continuous_smoothSob _)
  refine ⟨Z,hc,hK.image hc,?_⟩
  intro u
  apply lp.ext
  funext j
  exact (toBase_apply _ _ _ j).trans (hF (smoothSob s u) j)

end QuantumNLS.WindowSmoothClassR46b

#print axioms QuantumNLS.WindowSmoothClassR46b.continuous_smoothSob
#print axioms QuantumNLS.WindowSmoothClassR46b.compact_chart_lift

end WindowSmoothClassR46b

/-! Identification of the full scalar rotation with the physical Riccati
Hamiltonian flow. The radial derivatives of the two Sobolev extensions agree
on actual smooth one-coordinate perturbations. -/
noncomputable section WindowFullPathR46b
set_option autoImplicit false
set_option maxHeartbeats 4500000
attribute [local instance] InnerProductSpace.complexToReal
open Set Filter Topology MeasureTheory
open scoped ComplexConjugate NNReal
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.ClassicalCharges QuantumNLS.HierarchyFlow QuantumNLS.Def033HierarchyR24m
open QuantumNLS.Def024LowEquivariance QuantumNLS.SmoothScalarMomentsPhysical
open QuantumNLS.WindowActualEstimatesR44b QuantumNLS.WindowScalarsR45b
open QuantumNLS.WindowPhaseR44b QuantumNLS.WindowRadialR45b QuantumNLS.WindowTrajectoryR45b
open QuantumNLS.WindowGradientIdentificationR44b QuantumNLS.WindowSmoothClassR46b
open QuantumNLS.Reg015Setting QuantumNLS.RB7 QuantumNLS.Q07TailBindingR24 QuantumNLS.Fourier
open QuantumNLS.Q07SobolevModelR24 QuantumNLS.Q07ChargeBoundsR24

namespace QuantumNLS.WindowFullPathR46b
variable {L κ : ℝ} [Fact (0 < L)]

def chartFacts (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ) : ChartFacts (L := L) hκ where
  Φ := C.Φ
  Ψ := C.Ψ
  ΦΨ := C.right_inverse
  mass := C.actions
  ana_Φ := C.analytic
  ana_Ψ := C.inverse_analytic
  ΨΦ := C.left_inverse
  symp := C.symplectic
  iso := C.differential

private theorem full_value (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    {d r : ℕ} (hr : r ≤ d) (z : h02 L (sequenceOrder d)) (u : Smooth L)
    (hu : physical u = C.Ψ (toBase (sequenceOrder d) (sequenceOrder d).2 z)) :
    full hκ C d r hr z = hamiltonian L κ r u.val := by
  let x := coordinates (regularity_pos r).le (inverseForCharge hκ C d r hr z)
  have hs : 1/2 < regularity r := by unfold regularity; push_cast; linarith [Nat.cast_nonneg (α := ℝ) r]
  obtain ⟨g,hg,hrep,hval,-⟩ := RiccatiPointwiseRep.fieldMap_rep L hs x
  have he : ComplexifiedSobolevField.fieldMap L (regularity r) (regularity_pos r).le x = physical u := by
    rw [fieldMap_coordinates, inverseForCharge_val, hu]
  have hgu : g = WeakDerivatives.liftC u.property.smooth.continuous u.property.periodic := by
    apply (Continuous.ae_eq_iff_eq volume hg (ContinuousMap.continuous _)).mp
    change (ComplexifiedSobolevField.fieldMap L (regularity r) (regularity_pos r).le x : AddCircle L → ℂ) =ᵐ[volume] g at hrep
    rw [he] at hrep
    exact hrep.symm.trans (PhysicalProductPreparation.smoothClass_ae u.property)
  have hv : RiccatiPointwiseDisc.physRep L (regularity r) x = u.val := by
    funext t
    unfold RiccatiPointwiseDisc.physRep
    rw [← hval t, hgu, WeakDerivatives.liftC_coe]
  unfold full hamiltonian
  exact physical_charge (sharp r) (by dsimp [order]; omega) κ (r+1)
    (by omega) (by dsimp [order]; omega) x ((physical_rep r x).trans hv)

private theorem perturbation_smooth {hκ : 0 < κ} (C : Def021ChartR41b.Chart L κ hκ)
    (u : Smooth L) (j : ℤ) (c : ℂ) (t : ℝ) :
    ∃ v : Smooth L, ∀ n, C.Φ (physical v) n =
      C.Φ (physical u) n + (if n = j then (t : ℂ) * c else 0) := by
  let A := chartFacts hκ C
  let hR := Reg015HFinal.REG015_final (L := L) hκ
  let x : Seq := C.Φ (physical u) + lp.single 2 j ((t : ℂ) * c)
  have hx (s : ℝ) (hs : 0 ≤ s) : ∃ z : h02 L s, toBase s hs z = x := by
    let w : h02 L s := h02.ofMem (RB7.hinf_smooth hR A u.property s hs)
    refine ⟨w + coordinate (def002 L s) j ((t : ℂ)*c),?_⟩
    apply lp.ext
    funext n
    rw [toBase_apply, lp.coeFn_add, Pi.add_apply, lp.single_apply, WSeq.val_add, Pi.add_apply, coordinate_val]
    simp [Pi.single_apply]
    rfl
  have hS (s : ℝ) : MemHsLp L s (C.Ψ x) := by
    let b := max s 0
    have hb : 0 ≤ b := le_max_right _ _
    obtain ⟨z,hz⟩ := hx b hb
    obtain ⟨g,-,hg⟩ := WindowInverseRestrictionR44b.inverse_restriction hκ C b hb
    let q : H02 L s := H02.mono (le_max_left s 0) (g z)
    have hm : MemHsLp L s (g z).val := q.summable
    rw [hg z, hz] at hm
    exact hm
  obtain ⟨v,hv,he⟩ := RB7.smooth_of_memHs (C.Ψ x) hS
  refine ⟨⟨v,hv⟩,fun n => ?_⟩
  change C.Φ (smoothL2 hv) n = _
  rw [he,C.right_inverse]
  simp [x, lp.single_apply, Pi.single_apply]

/-- The two frequency definitions act on the same radial line. -/
theorem full_frequency_eq (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    {d r : ℕ} (hr : r ≤ d) (u : Smooth L) (z : h02 L (sequenceOrder d))
    (hz : toBase (sequenceOrder d) (sequenceOrder d).2 z = C.Φ (physical u)) (j : ℤ) :
    frequency (full hκ C d r hr) z j =
      omegaOf (Reg015HFinal.REG015_final (L := L) hκ) (chartFacts hκ C) r u.property j := by
  let hR := Reg015HFinal.REG015_final (L := L) hκ
  let A := chartFacts hκ C
  let w := zS hR A r u.property
  have hzn (n : ℤ) : z.val n = C.Φ (physical u) n :=
    (toBase_apply _ _ _ n).symm.trans (congrArg (fun q : Seq => q n) hz)
  have hzw : w.val j = z.val j := (hzn j).symm
  let B := full hκ C d r hr
  let D := Fd hR A r
  let b := coordinateCLM (W := def002 L (sequenceOrder d)) j
  let e := coordinateCLM (W := def002 L (SOf r)) j
  have hline (t : ℝ) : B (z + t • b (z.val j)) = D (w + t • e (z.val j)) := by
    obtain ⟨v,hv⟩ := perturbation_smooth C u j (z.val j) t
    have hcoord (W : PosWeight) (y : WSeq W) (n : ℤ) :
        (y + t • coordinate W j (z.val j)).val n =
          y.val n + (if n = j then (t : ℂ) * z.val j else 0) := by
      simp only [WSeq.val_add, Pi.add_apply,real_smul_val,coordinate_val]
      split_ifs <;> simp
    have hb : toBase (sequenceOrder d) (sequenceOrder d).2 (z + t • b (z.val j)) = C.Φ (physical v) := by
      apply lp.ext
      funext n
      erw [toBase_apply]
      change (z + t • coordinate _ j (z.val j)).val n = _
      rw [hcoord, hzn, hv]
    have hd : w + t • e (z.val j) = zS hR A r v.property := by
      apply WSeq.ext
      funext n
      change (w + t • coordinate _ j (z.val j)).val n = _
      rw [hcoord]
      change C.Φ (physical u) n + (if n = j then (t : ℂ) * z.val j else 0) =
        C.Φ (physical v) n
      exact (hv n).symm
    calc B (z + t • b (z.val j)) = hamiltonian L κ r v.val :=
          full_value hκ C hr _ v (by rw [hb,C.left_inverse])
      _ = D (w + t • e (z.val j)) := by rw [hd]; exact (Fd_charge hR A r v.property).symm
  have hder {W : PosWeight} {F : WSeq W → ℝ} {q : WSeq W}
      (hF : DifferentiableAt ℝ F q) (v : WSeq W) :
      HasDerivAt (fun t : ℝ => F (q + t • v)) (fderiv ℝ F q v) 0 := by
    have hh : HasFDerivAt F (fderiv ℝ F q) (q + (0 : ℝ) • v) := by
      simpa using hF.hasFDerivAt
    exact hh.comp_hasDerivAt 0 (hasDerivAt_line q v)
  have hb := hder ((full_contDiff hκ C d r hr).differentiable (by norm_num) z) (b (z.val j))
  have hd := hder ((Fd_contDiff hR A r).differentiable (by norm_num) w) (e (z.val j))
  have hd' := (funext hline) ▸ hb
  have hdEq := hd'.unique hd
  have heq : coordinate (def002 L (SOf r)) j (z.val j) = w.val j • ev _ j := by
    apply WSeq.ext
    funext n
    rw [coordinate_val,smul_ev_val,hzw]
  change fderiv ℝ B z (coordinate _ j (z.val j)) = fderiv ℝ D w (coordinate _ j (z.val j)) at hdEq
  rw [heq,map_smul_ev_eq] at hdEq
  change frequency B z j = omegaOf hR A r u.property j
  erw [omegaOf_eq hR A r u.property j]
  unfold frequency RB7.freq
  change fderiv ℝ B z (coordinate _ j (z.val j)) / (2 * ‖z.val j‖^2) =
    if w.val j = 0 then 0 else (conj (w.val j) * grad (fderiv ℝ D w) j).re / ‖w.val j‖^2
  rw [hdEq,← hzw]
  by_cases h0 : w.val j = 0
  · simp [h0]
  · rw [ite_eq_right h0]
    have hn : ‖w.val j‖ ^ 2 ≠ 0 := by positivity
    rw [show (conj (grad (fderiv ℝ D w) j) * w.val j).re =
      (conj (w.val j) * grad (fderiv ℝ D w) j).re by
        simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring]
    field_simp

/-- Single-step physical identification using the hierarchy's uniqueness clause. -/
theorem full_step (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    {d r : ℕ} (hr : r ≤ d)
    {Φ : ℝ → (ℝ → ℂ) → (ℝ → ℂ)}
    (hΦ : IsHamFlow L (hamiltonian L κ r) Φ)
    (huniq : UniqueHamFlow L (hamiltonian L κ r) Φ)
    (u : Smooth L) (z : h02 L (sequenceOrder d))
    (hz : toBase (sequenceOrder d) (sequenceOrder d).2 z = C.Φ (physical u))
    (t : ℝ) (j : ℤ) :
    C.Φ (physical (⟨Φ t u.val, ((hΦ u.val u.property).2.2 t).1⟩ : Smooth L)) j =
      (trajectory (full hκ C d r hr) z t).val j := by
  let hR := Reg015HFinal.REG015_final (L := L) hκ
  let A := chartFacts hκ C
  have hc := isHamFlow_chart hR A r
  have hf := huniq (chartFlow hR A r) hc u.val u.property t
  let v : Smooth L := ⟨chartFlow hR A r t u.val, ((hc u.val u.property).2.2 t).1⟩
  have hv : v = (⟨Φ t u.val, ((hΦ u.val u.property).2.2 t).1⟩ : Smooth L) :=
    Subtype.ext hf
  rw [← hv]
  have he := coords_chartFlow hR A r u.property t v.property j
  change C.Φ (physical v) j =
    Complex.exp (((-(t * omegaOf hR A r u.property j) : ℝ) : ℂ)*Complex.I) * C.Φ (physical u) j at he
  have hzj : C.Φ (physical u) j = z.val j :=
    (congrArg (fun q : Seq => q j) hz).symm.trans (toBase_apply _ _ _ j)
  have hfreq : frequency (full hκ C d r hr) z j = omegaOf hR A r u.property j :=
    full_frequency_eq hκ C hr u z hz j
  rw [he, trajectory, rotate_val, Circle.coe_exp, hfreq, hzj, neg_mul]

end QuantumNLS.WindowFullPathR46b

#print axioms QuantumNLS.WindowFullPathR46b.full_frequency_eq
#print axioms QuantumNLS.WindowFullPathR46b.full_step

end WindowFullPathR46b

/-! Pre-start assembly. The one unaccepted source predecessor is exactly
HierarchyR7B122087Input. The PROP-025 corollary has conclusion definitionally
equal to its frozen WindowInput. -/
noncomputable section WindowAssemblyR46b
set_option autoImplicit false
set_option maxHeartbeats 1000000
attribute [local instance] InnerProductSpace.complexToReal
open Set Filter Topology
open scoped ComplexConjugate
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.HierarchyFlow QuantumNLS.Def033HierarchyR24m QuantumNLS.Def024LowEquivariance
open QuantumNLS.Prop025OInputs QuantumNLS.Reg015Setting QuantumNLS.PROP017UniformN
open QuantumNLS.WindowInterpolationR44b QuantumNLS.WindowPhaseR44b QuantumNLS.WindowRateEstimateR44b
open QuantumNLS.WindowStrongPathR46b QuantumNLS.WindowAmbientR46b QuantumNLS.WindowPhysicalPathR46b
open QuantumNLS.WindowActualEstimatesR44b QuantumNLS.WindowScalarsR45b
open QuantumNLS.WindowRadialR45b QuantumNLS.WindowComparisonR45b
open QuantumNLS.WindowSmoothClassR46b QuantumNLS.WindowFullPathR46b

namespace QuantumNLS.WindowAssemblyR46b
variable {L κ : ℝ} [Fact (0 < L)]

private theorem large_cut_window (hκ : 0 < κ) (d : ℕ) {K : Set (Smooth L)} (hK : IsCompact K) :
    ∃ l0 : ℕ, ∀ l ≥ l0, ∀ u ∈ K, ∀ r ≤ d,
      (fun v : L2T L => windowHam κ r (cutSeq L l) v) =ᶠ[𝓝 (physical u)]
        Q07IntegratedHessiansR16.windowContour hκ r (cutSeq L l) 1 ∧
      DifferentiableAt ℝ (Q07IntegratedHessiansR16.windowContour hκ r (cutSeq L l) 1)
        (physical u) := by
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn
    (continuous_smoothSob (L := L) 1).continuousOn
  have hcut (r : ℕ) : ∃ n : ℕ, ∀ l ≥ n, ∀ u ∈ K,
      (fun v : L2T L => windowHam κ r (cutSeq L l) v) =ᶠ[𝓝 (physical u)]
        Q07IntegratedHessiansR16.windowContour hκ r (cutSeq L l) 1 ∧
      DifferentiableAt ℝ (Q07IntegratedHessiansR16.windowContour hκ r (cutSeq L l) 1)
        (physical u) := by
    obtain ⟨η,hη,l0,A,hA,h⟩ :=
      (Q07BUniformCutsR16.q07Buniformcuts (L := L) hκ (s := 1) (by norm_num) B
        (h := 1) (by norm_num) r).2
    refine ⟨l0,fun l hl u hu => ?_⟩
    have hm : physical u ∈ Q07SobolevCutsR16.sobolevClass (L := L) 1 B :=
      ⟨smoothSob 1 u,hB u hu,rfl⟩
    have hloc := (h l hl).2 (physical u) hm
    refine ⟨?_,(hloc (physical u) (by simpa using hη)).2.2.1⟩
    filter_upwards [Metric.ball_mem_nhds (physical u) hη] with v hv
    have hnorm : ‖v-physical u‖ < η := by simpa [Metric.mem_ball,dist_eq_norm] using hv
    exact (hloc v hnorm).2.1.symm
  choose n hn using hcut
  refine ⟨(Finset.range (d+1)).sup n,fun l hl u hu r hr => ?_⟩
  exact hn r l ((Finset.le_sup (f := n) (Finset.mem_range.mpr (by omega))).trans hl) u hu

private theorem frequency_sum {W : PosWeight} (R : Finset ℕ)
    (f : ℕ → WSeq W → ℝ) (t : ℕ → ℝ) (z : WSeq W)
    (hd : ∀ r ∈ R, DifferentiableAt ℝ (f r) z) (j : ℤ) :
    frequency (fun x => ∑ r ∈ R, t r * f r x) z j =
      ∑ r ∈ R, t r * frequency (f r) z j := by
  have h (r : ℕ) (hr : r ∈ R) : HasFDerivAt (fun x => t r * f r x)
      (t r • fderiv ℝ (f r) z) z := (hd r hr).hasFDerivAt.const_smul (t r)
  have he := (HasFDerivAt.fun_sum (u := R) h).fderiv
  unfold frequency
  rw [he, sum_apply]
  simp only [smul_apply,smul_eq_mul,Finset.sum_div]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

private theorem full_joint (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    {d : ℕ} {R : Finset ℕ} (hR : ∀ r ∈ R, r ≤ d)
    (F : HamFlows L κ R)
    (huF : ∀ r ∈ R, UniqueHamFlow L (hamiltonian L κ r) (F.Φ r))
    (t : ℕ → ℝ) (u : Smooth L) (z : h02 L (sequenceOrder d))
    (hz : toBase (sequenceOrder d) (sequenceOrder d).2 z = C.Φ (physical u))
    (B : ℕ → h02 L (sequenceOrder d) → ℝ)
    (hB : ∀ r (hr : r ∈ R), B r = full hκ C d r (hR r hr)) :
    C.Ψ (toBase (sequenceOrder d) (sequenceOrder d).2 (rotate (angle R B t z) z)) =
      physical (jointSmooth F t u) := by
  classical
  let s := sequenceOrder d
  let w := def002 L s
  have hfold (S : List ℕ) (hS : ∀ r ∈ S, r ∈ R) (j : ℤ) :
      C.Φ (physical (S.foldr (fun r v => smoothStep F r (t r) v) u)) j =
        (rotate (fun n => -(S.map fun r => t r * frequency (B r) z n).sum) z).val j := by
    induction S generalizing j with
    | nil =>
      have h : C.Φ (physical u) j = z.val j :=
        (congrArg (fun q : Seq => q j) hz).symm.trans (toBase_apply _ _ _ j)
      simpa [rotate_val] using h
    | cons r S ih =>
      let v := S.foldr (fun r v => smoothStep F r (t r) v) u
      let z' := rotate (fun n => -(S.map fun r => t r * frequency (B r) z n).sum) z
      have htail : ∀ q ∈ S, q ∈ R := fun q hq => hS q (List.mem_cons_of_mem _ hq)
      have hr := hS r (by simp)
      have hz' : toBase s s.2 z' = C.Φ (physical v) := by
        apply lp.ext
        funext n
        erw [toBase_apply]
        exact (ih htail n).symm
      have h := full_step hκ C (hR r hr) (F.ham r hr) (huF r hr) v z' hz' (t r) j
      have hdiff := (full_contDiff hκ C d r (hR r hr)).differentiable (by norm_num)
      have hfreq := frequency_rotate _ (hdiff z) (hdiff z') (full_rotation hκ C d r (hR r hr)) j
      rw [List.foldr_cons]
      change C.Φ (physical (smoothStep F r (t r) v)) j = _
      rw [smoothStep, dite_eq_left hr, h, WindowTrajectoryR45b.trajectory, rotate_val, hfreq]
      simp only [z', rotate_val, hB r hr, List.map_cons, List.sum_cons, Circle.coe_exp, ← mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
  apply Function.LeftInverse.injective C.left_inverse
  rw [C.right_inverse]
  apply lp.ext
  funext j
  erw [toBase_apply]
  unfold jointSmooth
  have h := hfold (R.sort (· ≤ ·)) (fun r hr => (Finset.mem_sort _).mp hr) j
  rw [h]
  have hs : ((R.sort (· ≤ ·)).map fun r => t r * frequency (B r) z j).sum =
      ∑ r ∈ R, t r * frequency (B r) z j := by
    rw [← List.sum_toFinset _ (R.sort_nodup (· ≤ ·)), Finset.sort_toFinset]
  simp only [rotate_val, angle, hs]

private theorem window_joint (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    {d : ℕ} {R : Finset ℕ} (hR : ∀ r ∈ R, r ≤ d) (t : ℕ → ℝ)
    (u : Smooth L) (z : h02 L (sequenceOrder d))
    (hz : toBase (sequenceOrder d) (sequenceOrder d).2 z = C.Φ (physical u)) (l : ℕ)
    (hcut : ∀ r ≤ d,
      (fun v : L2T L => windowHam κ r (cutSeq L l) v) =ᶠ[𝓝 (physical u)]
        Q07IntegratedHessiansR16.windowContour hκ r (cutSeq L l) 1 ∧
      DifferentiableAt ℝ (Q07IntegratedHessiansR16.windowContour hκ r (cutSeq L l) 1)
        (physical u))
    (G : ℕ → h02 L (sequenceOrder d) → ℝ) (hG : ∀ r ∈ R, G r = window hκ C d r 1 l) :
    (∃ y, IsWindowTrajectory κ R t (cutSeq L l) (physical u) y) ∧
    ∀ y, IsWindowTrajectory κ R t (cutSeq L l) (physical u) y →
      y 1 = C.Ψ (toBase (sequenceOrder d) (sequenceOrder d).2 (rotate (angle R G t z) z)) := by
  let s := sequenceOrder d
  let W := def002 L s
  have hW := one_le_def002 L s.2
  let x := toChart C (physical u)
  have hx : lower W hW z = x := by
    apply (toL2ᵢ unitWeight).injective
    change toL2 unitWeight (lower W hW z) = _
    rw [unit_base s s.2 z hW,hz]
    exact ((toL2ᵢ unitWeight).apply_symm_apply _).symm
  have hd (r : ℕ) (hr : r ∈ R) :
      DifferentiableAt ℝ (fun v : L2T L => windowHam κ r (cutSeq L l) v) (physical u) :=
    (hcut r (hR r hr)).2.congr_of_eventuallyEq (hcut r (hR r hr)).1
  have hF : DifferentiableAt ℝ (windowFamily κ R t (cutSeq L l)) (physical u) := by
    exact DifferentiableAt.fun_sum (fun r hr => (hd r hr).const_mul (t r))
  refine ⟨⟨_,physical_exists hκ C hF⟩,?_⟩
  intro y hy
  rw [physical_unique hκ C hy (τ := 1) (by norm_num)]
  change C.Ψ (toL2ᵢ unitWeight (phasePath _ x 1)) = _
  congr 1
  apply lp.ext
  funext j
  erw [U_apply,toBase_apply,phasePath,rotate_val,rotate_val,neg_mul,one_mul]
  have hxx : x.val j = z.val j := by rw [← hx]; rfl
  rw [hxx]
  let f := fun r (v : E) => windowHam κ r (cutSeq L l) (fromChart C v)
  have hc : DifferentiableAt ℝ (fromChart C) x :=
    ((C.inverse_analytic _).differentiableAt).comp _
      ((toL2ᵢ unitWeight).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).differentiableAt
  have hdf (r : ℕ) (hr : r ∈ R) : DifferentiableAt ℝ (f r) x := by
    have hh : DifferentiableAt ℝ (fun v : L2T L => windowHam κ r (cutSeq L l) v) (fromChart C x) := by
      simpa only [x,from_to] using hd r hr
    exact hh.comp x hc
  have hsum : frequency (windowFamily κ R t (cutSeq L l) ∘ fromChart C) x j =
      ∑ r ∈ R, t r * frequency (G r) z j := by
    rw [show (windowFamily κ R t (cutSeq L l) ∘ fromChart C) =
        (fun v => ∑ r ∈ R, t r * f r v) from rfl,frequency_sum R f t x hdf]
    apply Finset.sum_congr rfl
    intro r hr
    congr 1
    rw [hG r hr, ← hx]
    have hh : DifferentiableAt ℝ (f r) (lower W hW z) := hx.symm ▸ hdf r hr
    erw [← frequency_lower hW hh j]
    unfold frequency
    have he : Continuous (fun v : h02 L s => C.Ψ (toBase s s.2 v)) :=
      (continuous_iff_continuousAt.mpr fun b => (C.inverse_analytic b).continuousAt).comp
        (toBase s s.2).continuous
    have hnb := (hcut r (hR r hr)).1
    rw [← C.left_inverse (physical u), ← hz] at hnb
    have hnb' := he.continuousAt.eventually hnb
    have hEq : (fun w => f r (lower W hW w)) =ᶠ[𝓝 z] window hκ C d r 1 l := by
      filter_upwards [hnb'] with w hw
      change windowHam κ r (cutSeq L l) (C.Ψ (toL2 unitWeight (lower W hW w))) =
        Q07IntegratedHessiansR16.windowContour hκ r (cutSeq L l) 1
          (C.Ψ (toBase s s.2 w))
      erw [unit_base s s.2 w hW]
      exact hw
    exact congrArg (fun D : h02 L s →L[ℝ] ℝ =>
      D (WindowGradientIdentificationR44b.coordinate (def002 L s) j (z.val j)) /
        (2 * ‖z.val j‖ ^ 2)) (hEq.fderiv_eq (𝕜 := ℝ))
  rw [hsum,angle]

/-- Uniform comparison with the physical finite hierarchy at all orders
present in the fixed finite family, including the staged orders 0 and 1.
The existence assertion supplies an actual L² auxiliary window solution. -/
theorem rate_for_unique_flows (hκ : 0 < κ) (d : ℕ) (R : Finset ℕ) (hR : ∀ r ∈ R, r ≤ d)
    (F : HamFlows L κ R) (huF : ∀ r ∈ R, UniqueHamFlow L (hamiltonian L κ r) (F.Φ r))
    (T : ℕ → ℝ) (_hT : ∀ r, 0 ≤ T r) (K : Set (Smooth L)) (hK : IsCompact K) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ l0 : ℕ, ∀ l ≥ l0, ∀ u ∈ K,
      ∀ t : ℕ → ℝ, (∀ r ∈ R, |t r| ≤ T r) →
      (∃ y, IsWindowTrajectory κ R t (cutSeq L l) (physical u) y) ∧
      ∀ y, IsWindowTrajectory κ R t (cutSeq L l) (physical u) y →
        ‖y 1 - physical (jointSmooth F t u)‖ ≤ A * (cutSeq L l)^(-(1/4 : ℝ)) := by
  classical
  let C := Def021ChartR41b.chart L κ hκ
  let s := sequenceOrder d
  let W := def002 L s
  have hW : ∀ n, 1 ≤ W.w n := one_le_def002 L s.2
  obtain ⟨Z,hZ,KZ,hz⟩ := compact_chart_lift hκ C d hK
  obtain ⟨lcut,hcut⟩ := large_cut_window hκ d hK
  let f : E → L2T L := fromChart C
  have hf : ContDiff ℝ 1 f := actual_inverse_contDiff hκ C
  obtain ⟨M,hM,hm⟩ := uniform_comparison W hW KZ f hf (ι := ℕ)
  let B (r : ℕ) : WSeq W → ℝ :=
    if hr : r ≤ d then full hκ C d r hr else fun _ => 0
  let G (l r : ℕ) : WSeq W → ℝ :=
    if r ≤ d then window hκ C d r 1 l else fun _ => 0
  have hB (r : ℕ) (hr : r ≤ d) : B r = full hκ C d r hr := dite_eq_left hr
  have hG (l r : ℕ) (hr : r ≤ d) : G l r = window hκ C d r 1 l := ite_eq_left hr
  have hBd (r : ℕ) (z : WSeq W) : DifferentiableAt ℝ (B r) z := by
    by_cases hr : r ≤ d
    · rw [hB r hr]
      exact (full_contDiff hκ C d r hr).differentiable (by norm_num) z
    · simp [B,hr,differentiableAt_const]
  have hBinv (r : ℕ) (α : ℤ → ℝ) (z : WSeq W) : B r (rotate α z) = B r z := by
    by_cases hr : r ≤ d
    · rw [hB r hr]
      exact full_rotation hκ C d r hr α z
    · simp [B,hr]
  have hGinv (l r : ℕ) (α : ℤ → ℝ) (z : WSeq W) : G l r (rotate α z) = G l r z := by
    by_cases hr : r ≤ d
    · rw [hG l r hr]
      exact window_rotation hκ C d r 1 l α z
    · simp [G,hr]
  have hdata (r : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∃ n : ℕ, ∀ l ≥ n, ∀ z ∈ Z '' K,
      DifferentiableAt ℝ (G l r) z ∧ ‖fderiv ℝ (B r) z - fderiv ℝ (G l r) z‖ ≤
        A * (cutSeq L l)^(-(1/2 : ℝ)) := by
    by_cases hr : r ≤ d
    · obtain ⟨A,hA,n,hn⟩ := scalar_data hκ C d r hr (h := 1) (by norm_num) KZ
      exact ⟨A,hA,n,fun l hl z hz => by rw [hB r hr,hG l r hr]; exact hn l hl z hz⟩
    · refine ⟨0,le_rfl,0,fun l _ z _ => ?_⟩
      simp [G,B,hr,differentiableAt_const]
  choose A hA n hn using hdata
  obtain ⟨b,hb⟩ := KZ.exists_bound_of_continuousOn (continuous_id.continuousOn :
    ContinuousOn (fun z : WSeq W => z) (Z '' K))
  let b₀ := max b 0
  let l0 := max lcut ((Finset.range (d+1)).sup n)
  refine ⟨M * Real.sqrt ((∑ r ∈ R, T r * A r) * (2 * b₀)),by positivity,l0,?_⟩
  intro l hl u hu t ht
  have hbound (r : ℕ) (hr : r ≤ d) : n r ≤ l :=
    (Finset.le_sup (f := n) (Finset.mem_range.mpr (by omega))).trans
      ((le_max_right _ _).trans hl)
  have hGd (r : ℕ) (z : WSeq W) (hz' : z ∈ Z '' K) : DifferentiableAt ℝ (G l r) z := by
    by_cases hr : r ≤ d
    · exact (hn r l (hbound r hr) z hz').1
    · simp [G,hr,differentiableAt_const]
  have ha : 0 < cutSeq L l := by unfold cutSeq; positivity [(Fact.out : 0 < L)]
  have hZK : Z u ∈ Z '' K := ⟨u,hu,rfl⟩
  have hrate := hm R (G l) B T A b₀ hGd (fun r z _ => hBd r z) (hGinv l) hBinv
    (fun r _ => hA r) (fun z hz' => (hb z hz').trans (le_max_left _ _)) (cutSeq L l) ha
    (fun r hr z hz' => by
      rw [norm_sub_rev]
      exact (hn r l (hbound r (hR r hr)) z hz').2)
    (Z u) hZK t ht
  have hfull := full_joint hκ C hR F huF t u (Z u) (hz u) B (fun r hr => hB r (hR r hr))
  obtain ⟨hex,hwindow⟩ := window_joint hκ C hR t u (Z u) (hz u) l
    (hcut l ((le_max_left _ _).trans hl) u hu) (G l) (fun r hr => hG l r (hR r hr))
  refine ⟨hex,fun y hy => ?_⟩
  change ‖C.Ψ (toL2 _ (lower W hW _)) - C.Ψ (toL2 _ (lower W hW _))‖ ≤ _ at hrate
  rw [unit_base s s.2 _ hW,unit_base s s.2 _ hW,hfull,← hwindow y hy] at hrate
  exact hrate

/-- PRE-START theorem in the exact frozen PROP-025 window interface. -/
theorem window_intermediate (hκ : 0 < κ)
    (HierarchyInput : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ) :
    WindowInput (L := L) hκ := by
  intro w hw hsob _hgrad Φ hΦ d hd R hR T hT K hK
  obtain ⟨Ψ,hΨ,huΨ,-⟩ := HierarchyInput w hw hsob
    (HierarchyInputR25m.scalar_uniqueness hκ) (HierarchyInputR25m.scalar_moments hκ)
  let F : HamFlows L κ R := ⟨Φ,fun r hr => hΦ r (hR r hr).1⟩
  have huF (r : ℕ) (hr : r ∈ R) : UniqueHamFlow L (hamiltonian L κ r) (F.Φ r) := by
    intro f hf u hu t
    exact (huΨ r (hR r hr).1 f hf u hu t).trans
      (huΨ r (hR r hr).1 (Φ r) (hΦ r (hR r hr).1) u hu t).symm
  obtain ⟨A,hA,l0,h⟩ := rate_for_unique_flows hκ d R (fun r hr => (hR r hr).2)
    F huF T hT K hK
  exact ⟨A,hA,l0,fun l hl u hu t ht => (h l hl u hu t ht).2⟩

/-- The same pre-start comparison when the fixed family also contains the
staged orders. This version takes the ordinary finite-family flow carrier. -/
theorem window_all_orders_intermediate (hκ : 0 < κ)
    (HierarchyInput : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (w : L2T L → REF88Chart.K) (hw : REF88PrintedChart.PrintedChart hκ w)
    (d : ℕ) (R : Finset ℕ) (hR : ∀ r ∈ R, r ≤ d)
    (F : HamFlows L κ R) (T : ℕ → ℝ) (hT : ∀ r, 0 ≤ T r)
    (K : Set (Smooth L)) (hK : IsCompact K) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ l0 : ℕ, ∀ l ≥ l0, ∀ u ∈ K,
      ∀ t : ℕ → ℝ, (∀ r ∈ R, |t r| ≤ T r) →
      (∃ y, IsWindowTrajectory κ R t (cutSeq L l) (physical u) y) ∧
      ∀ y, IsWindowTrajectory κ R t (cutSeq L l) (physical u) y →
        ‖y 1 - physical (jointSmooth F t u)‖ ≤ A * (cutSeq L l)^(-(1/4 : ℝ)) := by
  have h := WindowHierarchyInputR45b.hierarchy_intermediate hκ w hw HierarchyInput
  obtain ⟨Ψ,hΨ,huΨ,-⟩ := all_order_commuting hκ.le w _
    (HierarchyInputR25m.conclusion_to_r24 w _ h)
  apply rate_for_unique_flows hκ d R hR F _ T hT K hK
  intro r hr f hf u hu t
  exact (huΨ r f hf u hu t).trans (huΨ r (F.Φ r) (F.ham r hr) u hu t).symm

end QuantumNLS.WindowAssemblyR46b

#print axioms QuantumNLS.WindowAssemblyR46b.window_intermediate
#print axioms QuantumNLS.WindowAssemblyR46b.window_all_orders_intermediate

end WindowAssemblyR46b

-- Recursive type/value audit of every own declaration, including generated declarations.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if (["QuantumNLS.WindowAmbientR46b.", "QuantumNLS.WindowPhysicalPathR46b.", "QuantumNLS.WindowSmoothClassR46b.", "QuantumNLS.WindowFullPathR46b.", "QuantumNLS.WindowAssemblyR46b."] : List String).any (fun pfx => n.toString.startsWith pfx) ||
        n.toString.startsWith "_private.QuantumNLS.WindowBindingR46b." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 then
        throwError "Rejected dependency: {n}"
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
  Lean.logInfo m!"R46b aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only."
