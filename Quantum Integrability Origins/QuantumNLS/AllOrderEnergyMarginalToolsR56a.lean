import QuantumNLS.AllOrderEnergyPairR56a
import QuantumNLS.MarginalSandwichNorm
import QuantumNLS.AllOrderEnergyTraceR55a
import QuantumNLS.RB7BindTopology
import QuantumNLS.IntrinsicContact
import QuantumNLS.AllOrderEnergyInputsR55a
import QuantumNLS.ActualModelCorollaryR56a

/-! Physical marginals, form-graph continuity, and the conditional energy trace upgrade. -/

set_option autoImplicit false
noncomputable section

section
/-! Realize the marginal's positive energy sandwich by applying the first
block's square root to the many-particle vector, then taking the ordinary
partial trace. This construction uses the physical H¹ domain. -/
set_option maxHeartbeats 5000000
open scoped BigOperators InnerProductSpace
namespace QuantumNLS.AllOrderEnergyPartialRootR56a
open Energy EnergyPreparationDef PhysicalEnergy PhysicalTensor TensorCarrier
open MarginalEnergy TraceClass AllOrderEnergyPairR56a
variable {L : ℝ} [Fact (0 < L)] {k m : ℕ}

/-- The first k kinetic terms form a sub-sum of the full kinetic weight. -/
theorem prefix_weight_le (w : Mom (k+m)) :
    kinWeight L k (fun j => w (Fin.castAdd m j)) ≤ kinWeight L (k+m) w := by
  rw [kinWeight, kinWeight, Fin.sum_univ_add]
  have hn : 0 ≤ ∑ j : Fin m, Fourier.freq L (w (Fin.natAdd k j))^2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

/-- The bounded multiplier for the partial root relative to the full root. -/
def prefixRatio (L : ℝ) (k m : ℕ) (w : Mom (k+m)) : ℝ :=
  kinSqrt L k (fun j => w (Fin.castAdd m j)) / kinSqrt L (k+m) w

theorem prefixRatio_bound (w : Mom (k+m)) : |prefixRatio L k m w| ≤ 1 := by
  unfold prefixRatio
  have hd : 0 < kinSqrt L (k+m) w := zero_lt_one.trans_le (one_le_kinSqrt _ _ _)
  have hnum : 0 ≤ kinSqrt L k (fun j => w (Fin.castAdd m j)) :=
    zero_le_one.trans (one_le_kinSqrt _ _ _)
  rw [abs_of_nonneg (div_nonneg hnum hd.le), div_le_one hd]
  exact Real.sqrt_le_sqrt (prefix_weight_le (L := L) (k := k) (m := m) w)

/-- The bounded first-block root on the full form space. -/
def prefixRootMap : PhysH1 L (k+m) →L[ℂ] Xk L (k+m) :=
  (eK L (k+m)).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    mulCLM (prefixRatio L k m) 1 zero_le_one (prefixRatio_bound (L := L)) ∘L
    (momUnitary L (k+m)).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (PhysH1.unitary (L := L) (k := k+m)).toContinuousLinearEquiv.toContinuousLinearMap

/-- Apply `A_k^(1/2)` to the observed block of the actual H¹ vector. -/
def prefixRoot (x : PhysH1 L (k+m)) : Xk L (k+m) :=
  prefixRootMap x

theorem prefixRoot_coeff (x : PhysH1 L (k+m)) (w : Mom (k+m)) :
    (eK L (k+m) (prefixRoot x)) w =
      (kinSqrt L k (fun j => w (Fin.castAdd m j)) : ℂ) * (momUnitary L (k+m) x.val) w := by
  change (eK L (k+m) ((eK L (k+m)).symm (mulCLM (prefixRatio L k m) 1 zero_le_one
    (prefixRatio_bound (L := L)) (momUnitary L (k+m) (PhysH1.unitary x))))) w = _
  rw [LinearIsometryEquiv.apply_symm_apply, mulCLM_apply, PhysH1.unitary_coeff]
  have hd : (kinSqrt L (k+m) w : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (zero_lt_one.trans_le (one_le_kinSqrt L (k+m) w)))
  unfold prefixRatio
  push_cast
  field_simp [hd]

theorem ev_eq_single {ι : Type*} [DecidableEq ι] (w : ι) :
    EnergyRealization.ev w = lp.single (E := fun _ : ι => ℂ) 2 w 1 :=
  (EnergyRealization.stdBasis (ι := ι)).repr_self w

/-- The bounded inverse root acts diagonally on the physical Fourier basis. -/
theorem inverse_root_mode (w : Mom k) : W L k (mode k w) = (↑((kinSqrt L k w)⁻¹) : ℂ) • mode k w := by
  apply (eK L k).injective
  ext v
  rw [eK_W, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  simp only [mode, LinearIsometryEquiv.apply_symm_apply, ev_eq_single]
  classical
  by_cases h : v = w
  · subst v; rfl
  · change _ * (lp.single (E := fun _ : Mom k => ℂ) 2 w 1) v = _ * (lp.single (E := fun _ : Mom k => ℂ) 2 w 1) v
    rw [lp.single_apply_ne _ _ _ h, mul_zero, mul_zero]

private theorem inverse_root_adjoint : (W L k).adjoint = W L k := by
  ext1 v
  apply ext_inner_right ℂ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_left, W_inner]

/-- Removing the observed block's kinetic root gives the original split
wave function, on the whole H¹ domain. -/
theorem prefixRoot_unweight (x : PhysH1 L (k+m)) :
    htmap (W L k) (ContinuousLinearMap.id ℂ (Xk L m)) (splitIsometry k m (prefixRoot x)) =
      splitIsometry k m (toHalf x : Xk L (k+m)) := by
  let B := htmulBasis (modeBasis (L := L) k) (modeBasis (L := L) m)
  apply B.repr.injective
  ext p
  rcases p with ⟨w,v⟩
  have hb : B (w,v) = htmul (mode k w) (mode m v) := by
    simp only [B, htmulBasis_apply, modeBasis_apply]
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply, hb,
    ← ContinuousLinearMap.adjoint_inner_left, adjoint_htmap, ContinuousLinearMap.adjoint_id,
    inverse_root_adjoint, htmap_htmul, ContinuousLinearMap.id_apply, inverse_root_mode,
    htmul_smul_left, inner_smul_left, Complex.conj_ofReal,
    inner_htmul_mode_split, inner_htmul_mode_split, prefixRoot_coeff]
  have hn : (kinSqrt L k w : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (zero_lt_one.trans_le (one_le_kinSqrt L k w)))
  have ha : (fun j : Fin k => Fin.append w v (Fin.castAdd m j)) = w := by
    funext j
    exact Fin.append_left w v j
  rw [ha]
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  change _ = (momUnitary L (k+m) (physUnitary (physUnitary.symm x.val))) (Fin.append w v)
  rw [LinearIsometryEquiv.apply_symm_apply]

/-- The positive trace-class realization used by DEF-031 is exactly the
ordinary reduced density of the first-block rooted vector. -/
theorem marginal_root_realizes (x : PhysH1 L (k+m)) :
    IsFormRealization (reducedDensityPower k m (toHalf x : Xk L (k+m)))
      (reducedDensity (splitIsometry k m (prefixRoot x))) := by
  apply (isFormRealization_iff _ _).mpr
  have h := MarginalSandwichNorm.sandwich_reducedDensity (W L k) (splitIsometry k m (prefixRoot x))
  rw [inverse_root_adjoint, prefixRoot_unweight] at h
  exact h.symm

end QuantumNLS.AllOrderEnergyPartialRootR56a
end

section
/-! Kinetic traces and compact contact passage on actual physical marginals. -/
set_option maxHeartbeats 5000000
open Filter Topology
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.AllOrderEnergyPhysicalR56a
open EnergyPreparationDef PhysicalEnergy PhysicalTensor TensorCarrier
open BetheCoefficientTransform CollisionIdentification MarginalEnergy TraceClass
open EnergyTraceConvergence AllOrderEnergyPairR56a AllOrderEnergyTraceR55a Ext025B10EnergyFamily

variable {L : ℝ} [Fact (0 < L)]

/-- The positive finite-energy marginal of the physical H¹ vector. -/
def marginal {N k : ℕ} (hk : k ≤ N) (ψ : Xk L N) (x : PhysH1 L N)
    (hx : x.val = physUnitary ψ) : FiniteEnergy L k :=
  ⟨reducedDensityN N k hk ψ, reducedDensityN_isPositive N k hk ψ, by
    rw [energyTrace_marginal hk ψ x hx]
    exact ENNReal.ofReal_ne_top⟩

theorem marginal_trace_one {N k : ℕ} (hk : k ≤ N) (ψ : Xk L N) (x : PhysH1 L N)
    (hx : x.val = physUnitary ψ) (hψ : ‖ψ‖ = 1) : posTrace (marginal hk ψ x hx).val = 1 :=
  traceIn_reducedDensityN_eq_one N k hk _ ψ hψ

/-- Symmetry identifies every observed derivative norm with the same
single-coordinate kinetic expectation, even for the full marginal. -/
theorem marginal_energy_sym {N k : ℕ} (hk : k ≤ N) (ψ : Xk L N) (x : PhysH1 L N)
    (hx : x.val = physUnitary ψ) (hψ : ‖ψ‖ = 1)
    (hsym : x ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L N))) (a : Fin N) :
    energyTrace (marginal hk ψ x hx).val =
      ENNReal.ofReal (1 + k * ‖gradientCLM a x‖ ^ 2) := by
  change energyTrace (reducedDensityN N k hk ψ) = _
  rw [energyTrace_marginal hk ψ x hx, hψ, one_pow]
  simp_rw [fun j : Fin k => norm_gradient_sym hsym (Fin.castLE hk j) a,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The physical form controls the marginal kinetic traces uniformly in
every parameter along which it is conserved. -/
theorem marginal_energy_bound {N k : ℕ} (hk : k ≤ N) (ψ : Xk L N) (x : PhysH1 L N)
    (hx : x.val = physUnitary ψ) (hψ : ‖ψ‖ = 1) (hsec : ψ ∈ physSector L N)
    (hk1 : 1 ≤ k) (κ : ℝ) (hκ : 0 ≤ κ) :
    energyTrace (marginal hk ψ x hx).val ≤ ENNReal.ofReal (1 + (k / N : ℝ) * hN κ N x) :=
  (marginal_physical_inputs hk1 hk hsec hψ x hx).2.2.2.2.2.2.2 κ hκ

/-- The compact rank-two contact expectations converge uniformly under
ordinary marginal convergence and an eventual kinetic bound. -/
theorem compact_contact_limit {T : Type*} (ρ : ℕ → T → FiniteEnergy L 2)
    (u : T → L2T L) (hu : ∀ t, ‖u t‖ = 1)
    (hH : ∀ t, ProductEnergyPreparation.OneH1 (u t))
    (B : ℝ) (hB : 0 ≤ B)
    (hρ : ∀ᶠ n in atTop, ∀ t, energyTrace (ρ n t).val ≤ ENNReal.ofReal B)
    (hσ : ∀ t, 1 + 2 * ChargeEnergy.kinetic ((u t : L2T L) : AddCircle L → ℂ) ≤ B)
    (hOrd : Tendsto (fun n => ⨆ t, traceNorm ((ρ n t).val -
      (EnergyTraceConvergence.pure (productHalf 2 (hu t) (hH t))).val)) atTop (𝓝 0)) :
    TendstoUniformly (fun n t =>
      (EnergyFormPass.expectation (contactSandwich (0 : Fin 2) 1 (by decide)) (ρ n t)).re)
      (fun t => ChargeEnergy.quartic ((u t : L2T L) : AddCircle L → ℂ)) atTop := by
  let σ : T → FiniteEnergy L 2 := fun t => EnergyTraceConvergence.pure (productHalf 2 (hu t) (hH t))
  have hσ' (t : T) : energyTrace (σ t).val ≤ ENNReal.ofReal B := by
    let f := productHalf 2 (hu t) (hH t)
    change energyTrace (InnerProductSpace.rankOne ℂ (f : Xk L 2) (f : Xk L 2)) ≤ _
    rw [pure_energy f]
    exact ENNReal.ofReal_le_ofReal ((productHalf_energy 2 (hu t) (hH t)).trans_le (hσ t))
  let C := contactSandwich (L := L) (0 : Fin 2) 1 (by decide)
  have h := compact_forms_eventually ρ σ B hB hρ hσ'
    (eventually_traceNorm_le (fun n t => (ρ n t).val) (fun t => (σ t).val) hOrd) C
    (contactSandwich_compact (L := L) (0 : Fin 2) 1 (by decide))
  apply Metric.tendstoUniformly_iff.2
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.1 h ε hε] with n hn
  intro t
  rw [← product_contact (0 : Fin 2) 1 (by decide) (hu t) (hH t)]
  rw [dist_eq_norm, Real.norm_eq_abs, ← Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans_lt (by simpa only [dist_eq_norm] using hn t)

end QuantumNLS.AllOrderEnergyPhysicalR56a
end

section
/-! Form-norm continuity of normalized smooth tensor powers. This is the
fixed-rank continuity needed by the positive energy trace theorem. -/
set_option maxHeartbeats 5000000
open Filter Topology
open scoped BigOperators InnerProductSpace
namespace QuantumNLS.AllOrderEnergyProductR56a
open Def033HierarchyR24m PhysicalTensor TensorCarrier PhysicalEnergy ProductEnergyPreparation
open RB7 RB7BindTopology SmoothScalarMomentsPhysical ClassicalCharges QuantumNLS.Fourier
open EnergyPreparationDef AllOrderEnergyPairR56a CollisionIdentification
variable {L : ℝ} [Fact (0 < L)]

/-- Every fixed physical derivative of a smooth periodic profile is continuous
into L² for the smooth jet topology. -/
theorem continuous_physical_jet (a : ℕ) :
    Continuous (fun u : Smooth L => smoothL2 (smooth_iter u.property a)) := by
  rw [continuous_iff_continuousAt]
  intro u₀
  have hj : Continuous (fun u : Smooth L => Def033HierarchyR24m.jet L u a) :=
    (continuous_apply a).comp (continuous_induced_dom : Continuous (Def033HierarchyR24m.jet L))
  have ht : Tendsto (fun u : Smooth L => ‖Def033HierarchyR24m.jet L u a - Def033HierarchyR24m.jet L u₀ a‖)
      (𝓝 u₀) (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 (hj.tendsto u₀)
  have hu := (ht.const_mul (Real.sqrt L))
  rw [mul_zero] at hu
  apply tendsto_iff_norm_sub_tendsto_zero.2
  apply squeeze_zero (fun _ => norm_nonneg _) _ hu
  intro u
  let A := ‖Def033HierarchyR24m.jet L u a - Def033HierarchyR24m.jet L u₀ a‖
  have h := sq_norm_smoothL2_sub_le (smooth_iter u.property a) (smooth_iter u₀.property a)
    (M := A) (norm_nonneg _) (fun x hx => by
      exact ContinuousMap.norm_coe_le_norm
        (Def033HierarchyR24m.jet L u a - Def033HierarchyR24m.jet L u₀ a) ⟨x,hx⟩)
  apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by positivity)
  rw [mul_pow, Real.sq_sqrt (Fact.out : 0 < L).le]
  exact h

theorem continuous_physical : Continuous (physical (L := L)) := by
  have h := continuous_physical_jet (L := L) 0
  have he (u : Smooth L) : smoothL2 (smooth_iter u.property 0) = physical u := by
    change smoothL2 (smooth_iter u.property 0) = smoothL2 u.property
    apply (fourierL2 L).injective
    ext n
    rw [fourierL2_smoothL2, fourierL2_smoothL2, cof_iterated, pow_zero, one_mul]
  simpa only [he] using h

/-- Product differentiation in the j-th coordinate. This is the physical
weak partial on the H¹ tensor product. -/
theorem gradient_product {k : ℕ} (u : Smooth L) (hu : ‖physical u‖ = 1) (j : Fin k) :
    gradientCLM j (productH1 hu (PhysicalProductPreparation.oneH1_smooth u.property) k) =
      prodLp (Function.update (fun _ : Fin k => physical u) j (smoothL2 (smooth_iter u.property 1))) := by
  classical
  let x := productH1 hu (PhysicalProductPreparation.oneH1_smooth u.property) k
  apply (momUnitary L k).injective
  ext w
  change (momUnitary L k ((momUnitary L k).symm (Complex.I • ContactForm.Dj j x))) w = _
  rw [LinearIsometryEquiv.apply_symm_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    ContactForm.Dj_apply]
  dsimp only [x]
  erw [coeffFun_productH1 hu (PhysicalProductPreparation.oneH1_smooth u.property) k w]
  rw [momUnitary_prodLp]
  rw [← Finset.mul_prod_erase _ (fun l : Fin k => fourierL2 L (physical u) (w l))
    (Finset.mem_univ j), ← Finset.mul_prod_erase _
      (fun l : Fin k => fourierL2 L (Function.update (fun _ : Fin k => physical u) j
        (smoothL2 (smooth_iter u.property 1)) l) (w l)) (Finset.mem_univ j)]
  rw [Function.update_self, fourierL2_smoothL2, cof_iterated, pow_one]
  have hp : ∏ l ∈ (Finset.univ.erase j), fourierL2 L (Function.update (fun _ : Fin k => physical u)
      j (smoothL2 (smooth_iter u.property 1)) l) (w l) =
      ∏ l ∈ (Finset.univ.erase j), fourierL2 L (physical u) (w l) := by
    refine Finset.prod_congr rfl fun l hl => ?_
    rw [Function.update_of_ne (Finset.mem_erase.mp hl).1]
  rw [hp]
  have hphys : cof u.property (w j) = fourierL2 L (physical u) (w j) :=
    (fourierL2_smoothL2 u.property (w j)).symm
  rw [hphys, WeakDerivatives.ikn]
  ring
  all_goals exact u.property

/-- The continuous multilinear tensor map also gives continuity of the
position-space product over individually varying factors. -/
theorem continuous_prodLp (k : ℕ) : Continuous (prodLp (L := L) (N := k)) := by
  have h := (physUnitary (L := L) (N := k)).continuous.comp
    (map_continuous (IntrinsicContact.htpowML (E := L2T L) k))
  simpa only [Function.comp_def, IntrinsicContact.htpowML_apply, physUnitary_ptprod] using h

/-- Tensor powers are continuous in the H¹ norm on the smooth unit sphere.
The L² term and each differentiated factor are treated by the same
multilinear tensor map. -/
theorem continuous_productH1 (k : ℕ) :
    Continuous (fun u : {u : Smooth L // ‖physical u‖ = 1} =>
      productH1 u.property (PhysicalProductPreparation.oneH1_smooth u.val.property) k) := by
  let S := {u : Smooth L // ‖physical u‖ = 1}
  let x : S → PhysH1 L k := fun u => productH1 u.property (PhysicalProductPreparation.oneH1_smooth u.val.property) k
  have hv : Continuous (fun u : S => u.val) := continuous_subtype_val
  have h0 : Continuous (fun u : S => (x u).val) := by
    have h := (continuous_prodLp (L := L) k).comp (continuous_pi fun (_ : Fin k) =>
      continuous_physical.comp hv)
    apply h.congr
    intro u
    exact (productH1_val u.property (PhysicalProductPreparation.oneH1_smooth u.val.property) k).symm
  have hD (j : Fin k) : Continuous (fun u : S => gradientCLM j (x u)) := by
    have hcoord (l : Fin k) : Continuous (fun u : S => Function.update (fun _ : Fin k => physical u.val) j
        (smoothL2 (smooth_iter u.val.property 1)) l) := by
      by_cases hl : l = j
      · subst l
        simpa only [Function.update_self, Function.comp_def] using (continuous_physical_jet (L := L) 1).comp hv
      · simpa only [Function.update_of_ne hl, Function.comp_def] using (continuous_physical (L := L)).comp hv
    have h := (continuous_prodLp (L := L) k).comp (continuous_pi hcoord)
    simpa only [Function.comp_def, x, gradient_product] using h
  change Continuous x
  rw [continuous_iff_continuousAt]
  intro u₀
  have hform (u : S) : ‖x u - x u₀‖^2 = ‖(x u).val - (x u₀).val‖^2 +
      ∑ j : Fin k, ‖gradientCLM j (x u) - gradientCLM j (x u₀)‖^2 := by
    have h := ContactForm.sum_norm_sq_Dj (x u - x u₀)
    simp_rw [← PhysicalProductPreparation.norm_gradientCLM, map_sub] at h
    have hvsub : (x u - x u₀).val = (x u).val - (x u₀).val :=
      map_sub (PhysH1.valCLM (L := L) (k := k)) (x u) (x u₀)
    rw [hvsub] at h
    linarith
  have hcont : Continuous (fun u : S => ‖x u - x u₀‖^2) := by
    simp_rw [hform]
    exact ((h0.sub continuous_const).norm.pow 2).add
      (continuous_finsetSum _ (fun j _ => ((hD j).sub continuous_const).norm.pow 2))
  have h := hcont.tendsto u₀
  apply tendsto_iff_norm_sub_tendsto_zero.2
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), Real.sqrt_zero] using
    (Real.continuous_sqrt.continuousAt.tendsto.comp h)

/-- The form graph continuity for the actual tensor-power target. -/
theorem continuous_productHalf_graph (k : ℕ) :
    Continuous (fun u : {u : Smooth L // ‖physical u‖ = 1} =>
      let f := productHalf k u.property (PhysicalProductPreparation.oneH1_smooth u.val.property)
      ((f : Xk L k), AhalfT L k f)) := by
  let S := {u : Smooth L // ‖physical u‖ = 1}
  let x : S → PhysH1 L k := fun u => productH1 u.property (PhysicalProductPreparation.oneH1_smooth u.val.property) k
  let e := physUnitary (L := L) (N := k)
  have hx : Continuous x := continuous_productH1 k
  have h₁ := e.symm.continuous.comp (PhysH1.valCLM (L := L) (k := k)).continuous |>.comp hx
  have h₂ := e.symm.continuous.comp (PhysH1.unitary (L := L) (k := k)).continuous |>.comp hx
  apply h₁.prodMk h₂ |>.congr
  intro u
  apply Prod.ext
  · rfl
  · exact (e.symm_apply_eq.mpr (root_toHalf (x u)).symm)

end QuantumNLS.AllOrderEnergyProductR56a
end

section
/-! The printed predecessor statements available to the R-568BCDF8
intermediate. The input types state the predecessor results, and the energy sandwich is
handled by the separate physical form argument. -/
set_option maxHeartbeats 4000000
open Filter Topology MeasureTheory
open scoped ENNReal InnerProductSpace
namespace QuantumNLS.AllOrderEnergyInputsR56a
open PhysicalTensor TensorCarrier Def033HierarchyR24m BetheCoefficientTransform HierarchyFlow
open ActualModelBindingR53a ActualModelTargetR53a ActualModelCorollaryR53a
open BetheLabels EmpiricalRapidity BulkResponseActual ClassicalCharges SmoothScalarMomentsPhysical
open CommonBethePacket AuditWeightedProbabilityR49a AllOrderEnergyInputsR55a
variable {L κ : ℝ} [Fact (0 < L)]

/-- The joint-flow data supplied by the exact printed hierarchy input. -/
theorem hierarchy (hκ : 0 < κ)
    (HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ) :
    HierarchyInputR25m.HierarchyConclusion (κ := κ) (chart (L := L) hκ).Φ
      (Def044ChartR51a.action hκ) :=
  hierarchy_intermediate hκ HierarchyR7B122087Input

def flows (hκ : 0 < κ)
    (HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ) :
    HigherFlows L κ := higher (hierarchy hκ HierarchyR7B122087Input)

/-- The actual-model input with the corollary's fixed-box order. -/
def ActualModelRE679E41DInput (hκ : 0 < κ)
    (HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ) : Prop :=
  ∀ (u : Smooth L), ‖physical u‖ = 1 →
  ∀ (I : Finset ℤ) (R : Finset ℕ) (k : ℕ) (Θ : ℤ → ℝ) (T : ℕ → ℝ),
    (∀ n ∈ I, 0 ≤ Θ n) → (∀ r ∈ R, 0 ≤ T r) →
    MainEstimate hκ (chart (L := L) hκ) (flows hκ HierarchyR7B122087Input) u I R k Θ T

/-- With no action angles the classical target is the joint Riccati flow of
the given initial datum. -/
theorem target_empty (hκ : 0 < κ)
    (HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ) (R : Finset ℕ) (θ : ℤ → ℝ) (t : ℕ → ℝ) (u : Smooth L) :
    target (chart (L := L) hκ) (flows hκ HierarchyR7B122087Input) ∅ R θ t u =
      physical (jointSmooth (hamFlows (flows hκ HierarchyR7B122087Input) R) t u) := by
  let C := chart (L := L) hκ
  have he : rotateSmooth C ∅ θ u = u := by
    apply physical_injective
    rw [rotateSmooth_physical]
    apply (Function.LeftInverse.injective C.left_inverse)
    ext n
    rw [rotate_coordinate]
    simp
  simp only [target, C] at he ⊢
  rw [he]

/-- Exactly the ordinary marginal convergence invoked in the energy proof.
This uses the named hierarchy and actual-model inputs
with the action set empty. -/
theorem empty_action_trace_limit (hκ : 0 < κ)
    (HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (ActualModelInput : ActualModelRE679E41DInput (L := L) hκ HierarchyR7B122087Input)
    (u : Smooth L) (hu : ‖physical u‖ = 1)
    (R : Finset ℕ) (T : ℕ → ℝ) (hT : ∀ r ∈ R, 0 ≤ T r) (k : ℕ)
    (ψ : ∀ N : ℕ, HN L (N + 1)) (hψ : ∀ N, ‖ψ N‖ = 1)
    (hprep : Tendsto (fun N => preparationError u N (ψ N)) atTop (𝓝 0)) :
    Tendsto (fun N => if hk : k ≤ N + 1 then
      ⨆ t : {t : ℕ → ℝ // ∀ r ∈ R, |t r| ≤ T r},
        TraceClass.traceNorm (reducedDensityN (N + 1) k hk
          (ActualModelQuantumR52a.chargeUnitary hκ R t.val N (ψ N) : HilbertTensorPower ℂ (L2T L) (N + 1)) -
          Prop025OInputs.tensorProj k (physical (jointSmooth (hamFlows (flows hκ HierarchyR7B122087Input) R) t.val u)))
      else 0) atTop (𝓝 0) := by
  let Θ : ℤ → ℝ := fun _ => 0
  have hm := ActualModelInput u hu ∅ R k Θ T (by simp) hT
  have hout := convergence hκ (chart (L := L) hκ) (flows hκ HierarchyR7B122087Input) u ∅ R k Θ T hm ψ hψ hprep
  have hθ : Nonempty {θ : ℤ → ℝ // ∀ n ∈ (∅ : Finset ℤ), |θ n| ≤ Θ n} := ⟨⟨Θ, by simp⟩⟩
  letI := hθ
  simpa only [boxError, countUnitary_empty, target_empty hκ HierarchyR7B122087Input, iSup_const] using hout

/-- Restrict joint smooth continuity to a fixed profile and a
compact box. The supplied smooth family is the very one in the model estimate. -/
theorem joint_smooth_continuous (hκ : 0 < κ)
    (HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ) (R : Finset ℕ) (u : Smooth L)
    (K : Set (ℕ → ℝ)) (hK : IsCompact K) :
    Continuous (fun t : K => jointSmooth (hamFlows (flows hκ HierarchyR7B122087Input) R) t.val u) := by
  have h := RB7BindMain.joint_continuous (RB7HBridge.jointContInput_of hκ R)
    (hamFlows (flows hκ HierarchyR7B122087Input) R) {u} isCompact_singleton K hK
  exact h.comp_continuous (continuous_const.prodMk continuous_subtype_val) (fun t => ⟨rfl, t.property⟩)

/-- Conservation on the chosen higher-order solution follows from uniqueness
and the shared hierarchy theorem. The first two orders use the accepted
physical phase and translation laws. -/
theorem flow_charge_conserved (hκ : 0 < κ)
    (HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ) (u : Smooth L) (r : ℕ) (t : ℝ) (j : ℕ) :
    charge L κ (flowMap (flows (L := L) hκ HierarchyR7B122087Input) r t u.val) j = charge L κ u.val j := by
  match r with
  | 0 => exact (Def024LowEquivariance.charge_conserved_low L κ u.property t j).1
  | 1 => exact (Def024LowEquivariance.charge_conserved_low L κ u.property t j).2
  | r + 2 =>
    let F := flows (L := L) hκ HierarchyR7B122087Input
    obtain ⟨Φ, hΦ, hUnique, _, _, _, _, _, hCharge, _⟩ := hierarchy (L := L) hκ HierarchyR7B122087Input
    have he := hUnique (r+2) (by omega) (F.Φ (r+2)) (F.ham (r+2) (by omega)) u.val u.property t
    change charge L κ (F.Φ (r+2) t u.val) j = _
    rw [he]
    exact hCharge (r+2) (by omega) u t j

theorem joint_charge_conserved (hκ : 0 < κ)
    (HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ) (u : Smooth L) (R : Finset ℕ) (t : ℕ → ℝ) (j : ℕ) :
    charge L κ (jointSmooth (hamFlows (flows hκ HierarchyR7B122087Input) R) t u).val j = charge L κ u.val j := by
  let F := hamFlows (flows (L := L) hκ HierarchyR7B122087Input) R
  have hs (r) (v : Smooth L) : charge L κ (smoothStep F r (t r) v).val j = charge L κ v.val j := by
    unfold smoothStep
    split_ifs
    · exact flow_charge_conserved hκ HierarchyR7B122087Input v r (t r) j
    · rfl
  change charge L κ ((R.sort (· ≤ ·)).foldr (fun r v => smoothStep F r (t r) v) u).val j = _
  induction R.sort (· ≤ ·) with
  | nil => rfl
  | cons r rs ih => exact (hs r _).trans ih

/-- The named R-E59628C9 input is applied at the same actual chart and full
Riccati family. The scalar gradient antecedent is a proved predecessor. -/
theorem actual_window_rate (hκ : 0 < κ)
    (HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ) (WindowInput : WindowRE59628C9Input (L := L) hκ)
    (d : ℕ) (hd : 2 ≤ d) (R : Finset ℕ) (hR : ∀ r ∈ R, r ≤ d)
    (T : ℕ → ℝ) (hT : ∀ r, 0 ≤ T r) (K : Set (Smooth L)) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ l₀ : ℕ, ∀ l ≥ l₀, ∀ u ∈ K,
      ∀ t : ℕ → ℝ, (∀ r ∈ R, |t r| ≤ T r) →
      (∃ y, Prop025OInputs.IsWindowTrajectory κ R t (PROP017UniformN.cutSeq L l) (physical u) y) ∧
      ∀ y, Prop025OInputs.IsWindowTrajectory κ R t (PROP017UniformN.cutSeq L l) (physical u) y →
        ‖y 1 - physical (jointSmooth (hamFlows (flows hκ HierarchyR7B122087Input) R) t u)‖ ≤ C * (PROP017UniformN.cutSeq L l)^(-(1/4 : ℝ)) :=
  WindowInput (chart (L := L) hκ).Φ (printed_chart hκ) (sobolev hκ) (Prop025OInputs.gradient_removal hκ)
    d hd R hR (hamFlows (flows hκ HierarchyR7B122087Input) R) T hT K hK

/-- The ordinary convergence restricts to any fixed compact joint-time box.
A coordinatewise enclosing centered box uses only continuous evaluation. -/
theorem compact_box_ordinary_limit (hκ : 0 < κ)
    (HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (ActualModelInput : ActualModelRE679E41DInput (L := L) hκ HierarchyR7B122087Input)
    (u : Smooth L) (hu : ‖physical u‖ = 1)
    (R : Finset ℕ) (K : Set (ℕ → ℝ)) (hK : IsCompact K) (k : ℕ)
    (ψ : ∀ N : ℕ, HN L (N + 1)) (hψ : ∀ N, ‖ψ N‖ = 1)
    (hprep : Tendsto (fun N => preparationError u N (ψ N)) atTop (𝓝 0)) :
    Tendsto (fun N => if hk : k ≤ N + 1 then
      ⨆ t : K, TraceClass.traceNorm (reducedDensityN (N + 1) k hk
          (ActualModelQuantumR52a.chargeUnitary hκ R t.val N (ψ N) : HilbertTensorPower ℂ (L2T L) (N + 1)) -
          Prop025OInputs.tensorProj k (physical (jointSmooth (hamFlows (flows hκ HierarchyR7B122087Input) R) t.val u)))
      else 0) atTop (𝓝 0) := by
  have hbound (r : ℕ) : ∃ b : ℝ, ∀ t ∈ K, ‖t r‖ ≤ b :=
    hK.exists_bound_of_continuousOn ((continuous_apply r).continuousOn)
  choose B hB using hbound
  let T : ℕ → ℝ := fun r => max (B r) 0
  have hT : ∀ r ∈ R, 0 ≤ T r := fun _ _ => le_max_right _ _
  have hbig := empty_action_trace_limit hκ HierarchyR7B122087Input ActualModelInput u hu R T hT k ψ hψ hprep
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbig
  · exact Eventually.of_forall fun _ => bot_le
  · filter_upwards [eventually_ge_atTop k] with N hN
    have hk : k ≤ N + 1 := hN.trans (Nat.le_succ _)
    simp only [dite_eq_left hk]
    let E (s : ℕ → ℝ) : ℝ≥0∞ := TraceClass.traceNorm (reducedDensityN (N + 1) k hk
      (ActualModelQuantumR52a.chargeUnitary hκ R s N (ψ N) : HilbertTensorPower ℂ (L2T L) (N + 1)) -
      Prop025OInputs.tensorProj k (physical (jointSmooth (hamFlows (flows hκ HierarchyR7B122087Input) R) s u)))
    change (⨆ t : K, E t.val) ≤ ⨆ t : {t : ℕ → ℝ // ∀ r ∈ R, |t r| ≤ T r}, E t.val
    apply iSup_le
    intro t
    have ht : ∀ r ∈ R, |t.val r| ≤ T r := fun r _ =>
      (by simpa only [Real.norm_eq_abs] using hB r t t.property : |t.val r| ≤ B r).trans (le_max_left _ _)
    let v : {t : ℕ → ℝ // ∀ r ∈ R, |t r| ≤ T r} := ⟨t.val, ht⟩
    exact le_iSup (fun s : {t : ℕ → ℝ // ∀ r ∈ R, |t r| ≤ T r} => E s.val) v

end QuantumNLS.AllOrderEnergyInputsR56a
end

set_option maxHeartbeats 22000000 in
run_cmd do
  let env ← Lean.getEnv
  let prefixes := ["QuantumNLS.AllOrderEnergyInputsR56a.", "QuantumNLS.AllOrderEnergyPartialRootR56a.", "QuantumNLS.AllOrderEnergyPhysicalR56a.", "QuantumNLS.AllOrderEnergyProductR56a."]
  let mut pending := env.constants.toList.filterMap fun (n, _) =>
    if prefixes.any (fun pre => n.toString.startsWith pre) ||
      n.toString.startsWith "_private.QuantumNLS.AllOrderEnergyMarginalToolsR56a." then some n else none
  let roots := pending.length
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    unless seen.contains n do
      seen := seen.insert n
      if n == ``QuantumNLS.AllOrderEnergyInputsR55a.ActualModelRE679E41DInput ||
          n == ``QuantumNLS.AllOrderEnergyInputsR55a.flows ||
          n == ``QuantumNLS.RB7BindFinal.hierarchyInputR25m_unconditional ||
          n == ``QuantumNLS.ActualModelCorollaryR53a.PacketEstimate then
        throwError "Unaccepted predecessor representation: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := ci.type.getUsedConstants.toList ++ pending
        if let some v := ci.value? (allowOpaque := true) then
          pending := v.getUsedConstants.toList ++ pending
      else throwError "Missing dependency: {n}"
  Lean.logInfo m!"R56a audit PASS: {roots} namespace constants; {seen.size} transitive constants."
