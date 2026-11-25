import QuantumNLS.MarginalEnergy
import QuantumNLS.ContactFormTheorem
import QuantumNLS.EnergyContactCommutator
import QuantumNLS.EnergyFormPassFinal
import QuantumNLS.EnergyTraceConvergence
import QuantumNLS.Ext025A12Normal

/-! Rank-one kinetic and one-pair contact reduction of the physical
Hamiltonian form, including the finite-particle coefficient. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace BigOperators ENNReal
namespace QuantumNLS.AllOrderEnergyPairR56a
open ContactForm ContactFormTheorem CollisionIdentification PhysicalEnergy ProductEnergyPreparation
open MarginalEnergy EnergyPreparationDef PhysicalTensor TensorCarrier EnergyContactTrace
variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- All pair contact norms agree on the symmetric form domain. -/
theorem contact_norm_eq_of_sym {x : PhysH1 L N} (hx : x ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L N)))
    (i j a b : Fin N) (hij : i ≠ j) (hab : a ≠ b) :
    ‖productTrace i j hij x‖ ^ 2 = ‖productTrace a b hab x‖ ^ 2 := by
  classical
  let s := Equiv.swap i a
  have hsi : s i = a := Equiv.swap_apply_left _ _
  have hsj : a ≠ s j := fun h => hij (s.injective (hsi.trans h))
  let τ := Equiv.swap (s j) b
  have hτa : τ a = a := Equiv.swap_apply_of_ne_of_ne hsj hab
  have hτj : τ (s j) = b := Equiv.swap_apply_left _ _
  let σ := s.trans τ
  have hσi : σ i = a := (congrArg τ hsi).trans hτa
  have hσj : σ j = b := hτj
  have hsym : x.val = physPerm σ x.val := ((PhysH1.mem_sym_iff x).1 hx σ).symm
  have h := Gp_perm σ x x x x hsym hsym i j
  rw [hσi, hσj] at h
  simp only [Gp, dite_eq_left hij, dite_eq_left hab] at h
  rw [productTrace_norm, productTrace_norm]
  simpa only [← norm_sq_eq_re_inner] using (congrArg (RCLike.re : ℂ → ℝ) h).symm

/-- The per-particle form identity with the literal kinetic expectation and
one physical pair contact. The factor `κ (1-1/N)` comes from the exact pair
count and the coupling `κ/N`. -/
theorem intensive_energy (κ : ℝ) {x : PhysH1 L N}
    (hx : x ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L N)))
    (a b : Fin N) (hab : a ≠ b) :
    EnergyPreparationDef.hN κ N x / N = ‖gradientCLM a x‖ ^ 2 + κ * (1 - (N : ℝ)⁻¹) * ‖productTrace a b hab x‖ ^ 2 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt a.isLt)
  rw [(EnergyPreparationDef.hN_literal κ x).1]
  simp_rw [fun p : Pair N => contact_norm_eq_of_sym hx p.1.1 p.1.2 a b (ne_of_lt p.2) hab,
    fun j : Fin N => norm_gradient_sym hx j a, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hp : (Fintype.card (Pair N) : ℝ) = (N : ℝ) * ((N : ℝ) - 1) / 2 := by
    linarith [card_pair_real N]
  rw [hp]
  field_simp

/-- The contact map after the inverse physical kinetic root, on the tensor
carrier underlying DEF-030. -/
def contactRoot (i j : Fin N) (hij : i ≠ j) :
    Xk L N →L[ℂ] CollisionProductL2 (L := L) i j :=
  (Sop (L := L) hij).comp (physUnitary (L := L) (N := N)).toContinuousLinearEquiv.toContinuousLinearMap

/-- The bounded kinetic sandwich of `T_ij^*T_ij`. -/
def contactSandwich (i j : Fin N) (hij : i ≠ j) : Xk L N →L[ℂ] Xk L N :=
  (contactRoot (L := L) i j hij).adjoint.comp (contactRoot (L := L) i j hij)

theorem contactSandwich_compact (i j : Fin N) (hij : i ≠ j) :
    IsCompactOperator (contactSandwich (L := L) i j hij) := by
  have h : IsCompactOperator (contactRoot (L := L) i j hij) := (Sop_isCompact hij).comp_clm _
  exact h.clm_comp (contactRoot (L := L) i j hij).adjoint

/-- A physical H¹ wave function viewed in the literal square-root domain. -/
def toHalf (x : PhysH1 L N) : (AhalfT L N).domain :=
  ⟨physUnitary.symm x.val, by
    change physUnitary (physUnitary.symm x.val) ∈ (physAhalf L N).domain
    rw [LinearIsometryEquiv.apply_symm_apply, ← SetLike.mem_coe, ← PhysH1.range_val_eq_domain]
    exact ⟨x, rfl⟩⟩

theorem root_toHalf (x : PhysH1 L N) :
    physUnitary (AhalfT L N (toHalf x)) = PhysH1.unitary x := by
  apply (momUnitary L N).injective
  ext w
  rw [PhysH1.unitary_coeff]
  change (eK L N (AhalfT L N (toHalf x)) : Energy.Mom N → ℂ) w = _
  rw [eK_AhalfT]
  change _ * (momUnitary L N (physUnitary (physUnitary.symm x.val)) : Energy.Mom N → ℂ) w = _
  rw [LinearIsometryEquiv.apply_symm_apply, PhysH1.momUnitary_val]

/-- The compact sandwich gives the source form on its whole H¹ domain. -/
theorem contact_expectation_pure (i j : Fin N) (hij : i ≠ j) (x : PhysH1 L N) :
    (EnergyFormPass.expectation (contactSandwich i j hij) (EnergyTraceConvergence.pure (toHalf x))).re =
      ‖productTrace i j hij x‖ ^ 2 := by
  rw [EnergyFormPass.expectation, EnergyTraceConvergence.sandwich_pure, Ext025A12Normal.trace_rankOne_left]
  change (⟪AhalfT L N (toHalf x), (contactRoot i j hij).adjoint
    (contactRoot i j hij (AhalfT L N (toHalf x)))⟫_ℂ).re = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  change RCLike.re ⟪contactRoot i j hij (AhalfT L N (toHalf x)),
    contactRoot i j hij (AhalfT L N (toHalf x))⟫_ℂ = _
  rw [← norm_sq_eq_re_inner]
  change ‖Sop hij (physUnitary (AhalfT L N (toHalf x)))‖ ^ 2 = _
  rw [root_toHalf]
  simp [Sop]

/-- The square-root-domain representative of the exact tensor product. -/
def productHalf (k : ℕ) {u : L2T L} (hu : ‖u‖ = 1) (hH : OneH1 u) : (AhalfT L k).domain :=
  toHalf (productH1 hu hH k)

theorem productHalf_val (k : ℕ) {u : L2T L} (hu : ‖u‖ = 1) (hH : OneH1 u) :
    (productHalf k hu hH : Xk L k) = htpow k u := by
  apply (physUnitary (L := L) (N := k)).injective
  change physUnitary (physUnitary.symm (productH1 hu hH k).val) = _
  rw [LinearIsometryEquiv.apply_symm_apply, productH1_val]
  exact (physEmbed_htpow (N := k) u).symm

theorem productHalf_energy (k : ℕ) {u : L2T L} (hu : ‖u‖ = 1) (hH : OneH1 u) :
    ‖AhalfT L k (productHalf k hu hH)‖^2 = 1 + (k : ℝ) * ChargeEnergy.kinetic (u : AddCircle L → ℂ) := by
  have hp := EnergyTraceConvergence.pure_energy (productHalf k hu hH)
  rw [productHalf_val] at hp
  unfold energyTrace at hp
  rw [PhysicalProductPreparation.physTrace_proj hu hH] at hp
  have hk : 0 ≤ ChargeEnergy.kinetic (u : AddCircle L → ℂ) :=
    tsum_nonneg fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hc : 0 ≤ 1 + (k : ℝ) * ChargeEnergy.kinetic (u : AddCircle L → ℂ) := by positivity
  have hh := congrArg ENNReal.toReal hp
  simpa only [ENNReal.toReal_ofReal hc, ENNReal.toReal_ofReal (sq_nonneg _)] using hh.symm

/-- The rank-two target contact is exactly the classical quartic energy
factor, with the frozen collision measure. -/
theorem product_contact (i j : Fin 2) (hij : i ≠ j) {u : L2T L}
    (hu : ‖u‖ = 1) (hH : OneH1 u) :
    (EnergyFormPass.expectation (contactSandwich i j hij) (EnergyTraceConvergence.pure (productHalf 2 hu hH))).re =
      ChargeEnergy.quartic (u : AddCircle L → ℂ) :=
  (contact_expectation_pure i j hij (productH1 hu hH 2)).trans
    (PhysicalProductPreparation.norm_sq_productTrace_product hu hH i j hij)

end QuantumNLS.AllOrderEnergyPairR56a
set_option maxHeartbeats 15000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := env.constants.toList.filterMap fun (n, _) =>
    if n.toString.startsWith "QuantumNLS.AllOrderEnergyPairR56a." ||
        n.toString.startsWith "_private.QuantumNLS.AllOrderEnergyPairR56a." then some n else none
  let roots := pending.length
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    unless seen.contains n do
      seen := seen.insert n
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
