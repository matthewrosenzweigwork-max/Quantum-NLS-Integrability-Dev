import QuantumNLS.RootEnergyVariation
import QuantumNLS.WeakDerivatives

/-! R-63A99F0E: one named theorem, with H² input and all H¹ directions.
The H^s spaces are the existing complete Fourier realizations of the physical
Sobolev spaces. The weak second derivative, cubic L² vector, differential,
contact-energy origin and Hamiltonian convention are conclusions. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
open scoped InnerProductSpace ComplexConjugate
open MeasureTheory Filter QuantumNLS.Fourier QuantumNLS.Sobolev
  QuantumNLS.Sobolev.PosWeight QuantumNLS.LocalWellPosedness
  QuantumNLS.F04Regularity QuantumNLS.RootEnergyVariation
  QuantumNLS.PhysicalTensor QuantumNLS.ProductEnergyPreparation QuantumNLS.WeakDerivatives
namespace QuantumNLS.RootEnergyVectorField
variable {L : ℝ} [Fact (0 < L)]

/-- Symplectic form with the printed factor two. -/
def omega (h k : L2T L) : ℝ := 2 * (⟪h,k⟫_ℂ).im

/-- The physical vector dictated by X_E=-i∇E. -/
def X (κ : ℝ) (u : h04 L 2) : L2T L := -Complex.I • physical (grad κ u)




lemma weak_pair (u : h04 L 2) :
    HasWeakDeriv (physical (m10 (m21 u))) (physical (Complex.I • D (m21 u))) ∧
    HasWeakDeriv (physical (Complex.I • D (m21 u))) (-physical (lap u)) := by
  have hc (v : h04 L 0) (n : ℤ) : coeff L (physical v) n = v.val n := by
    have h := physical_coeff v n
    rwa [fourierL2_apply] at h
  constructor
  · apply QuantumNLS.WeakDerivatives.hasWeakDeriv_of_coeff
    intro n
    rw [hc, hc]
    change Complex.I * (((freq L n : ℝ) : ℂ) * u.val n) =
      QuantumNLS.WeakDerivatives.ikn L n * u.val n
    simp only [QuantumNLS.WeakDerivatives.ikn]; ring
  · rw [show -physical (lap u) = physical (-(lap u)) from
      (map_neg (physical (L := L)) (lap u)).symm]
    apply QuantumNLS.WeakDerivatives.hasWeakDeriv_of_coeff
    intro n
    rw [hc, hc]
    change -(((freq L n ^ 2 : ℝ) : ℂ) * u.val n) =
      QuantumNLS.WeakDerivatives.ikn L n *
        (Complex.I * (((freq L n : ℝ) : ℂ) * u.val n))
    simp only [QuantumNLS.WeakDerivatives.ikn, Complex.ofReal_pow]
    linear_combination -(freq L n : ℂ)^2 * u.val n * Complex.I_mul_I



lemma cubic (a : h04 L 1) :
    (physical (m10 (Fh (le_refl (1 : ℝ)) a)) : AddCircle L → ℂ) =ᵐ[volume]
      fun x => ((‖physical (m10 a) x‖^2 : ℝ) : ℂ) * physical (m10 a) x := by
  have hm := memLp_of_continuous (continuous_nlRep (L := L) (summable_norm_h1 a))
  have he : physical (m10 (Fh (le_refl (1 : ℝ)) a)) = hm.toLp (nlRep L a.val) := by
    apply (fourierL2 L).injective
    apply Subtype.ext
    funext n
    rw [physical_coeff, fourierL2_toLp]
    rfl
  have hc : (physical (m10 (Fh (le_refl (1 : ℝ)) a)) : AddCircle L → ℂ)
      =ᵐ[volume] nlRep L a.val := by rw [he]; exact hm.coeFn_toLp
  filter_upwards [hc, physical_rep a] with x hx hu
  rw [hx, hu]
  rfl



lemma product_origin (U : L2T L) (hH : OneH1 U) (c : ℝ) (N : ℕ) :
    ∃ Ψ : QuantumNLS.PhysicalEnergy.PhysH1 L N,
      Ψ.val = prodState U N ∧
      QuantumNLS.ContactProductIntegrals.PiSquareFubini Ψ.val ∧
      QuantumNLS.ContactForm.q c Ψ Ψ =
        ((N * (‖U‖ ^ 2) ^ (N-1) * QuantumNLS.ChargeEnergy.kinetic (U : AddCircle L → ℂ) +
          c * N * ((N : ℝ)-1) * (‖U‖ ^ 2) ^ (N-2) *
            QuantumNLS.ChargeEnergy.quartic (U : AddCircle L → ℂ) : ℝ) : ℂ) := by
  obtain ⟨Ψ, hv, _, _, _, hf, _, _, _, hq, _⟩ :=
    QuantumNLS.ContactProductExact.contact_prop_product U hH c N
  exact ⟨Ψ, hv, hf, hq⟩



lemma mass_origin (κ : ℝ) (a : h04 L 1) :
    let U := physical (m10 a)
    (U = 0 ∧ energy κ a = 0) ∨
      ∃ (v : L2T L) (hv : ‖v‖ = 1) (hH : OneH1 v),
        U = (‖U‖ : ℂ) • v ∧
        Tendsto (fun N : ℕ => ‖U‖ ^ 2 *
          (hN (κ * ‖U‖ ^ 2) N (productH1 hv hH N) / N)) atTop
            (nhds (energy κ a)) := by
  let U := physical (m10 a)
  by_cases hU : U = 0
  · left
    refine ⟨hU, ?_⟩
    have hm : m10 a = 0 := by
      apply (physical (L := L)).injective
      calc
        physical (m10 a) = 0 := hU
        _ = physical (0 : h04 L 0) := (map_zero (physical (L := L))).symm
    have ha : a = 0 := by
      apply WSeq.ext
      funext n
      exact congrArg (fun v : h04 L 0 => v.val n) hm
    change energy κ a = 0
    rw [ha]
    simp [energy, kin, quart]
  · right
    have hn : ‖U‖ ≠ 0 := norm_ne_zero_iff.mpr hU
    let b : h04 L 1 := (‖U‖⁻¹ : ℂ) • a
    let v := physical (m10 b)
    have hvlin : v = (‖U‖⁻¹ : ℂ) • U := by
      simp only [v, b, map_smul, U]
    have hv : ‖v‖ = 1 := by
      rw [hvlin, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg U)]
      exact inv_mul_cancel₀ hn
    have hH : OneH1 v := physical_oneH1 b
    have hscale : U = (‖U‖ : ℂ) • v := by
      rw [hvlin, smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hn), one_smul]
    have he : ‖U‖ ^ 2 * QuantumNLS.ChargeEnergy.energyH1 (κ * ‖U‖ ^ 2)
        (v : AddCircle L → ℂ) = energy κ a := by
      have hscaleR : U = ‖U‖ • v := hscale.trans (Complex.coe_smul ‖U‖ v)
      calc
        _ = QuantumNLS.ChargeEnergy.energyH1 κ ((‖U‖ • v : L2T L) : AddCircle L → ℂ) := by
          rw [energyH1_smul]
          unfold QuantumNLS.ChargeEnergy.energyH1
          ring
        _ = QuantumNLS.ChargeEnergy.energyH1 κ (U : AddCircle L → ℂ) := by rw [← hscaleR]
        _ = energy κ a := physical_energy κ a
    refine ⟨v, hv, hH, hscale, ?_⟩
    have ht := ((product_energyPrepared hv hH (κ * ‖U‖ ^ 2)).2.2.2.1).const_mul (‖U‖ ^ 2)
    rw [he] at ht
    exact ht



lemma physical_grad (κ : ℝ) (u : h04 L 2) :
    physical (grad κ u) = -(-physical (lap u)) + ((2 * κ : ℝ) : ℂ) •
      physical (m10 (Fh (le_refl (1 : ℝ)) (m21 u))) := by
  simp only [grad, map_add, map_smul, neg_neg]
/-- Full physical energy vector-field assertion. No differentiability,
integrability, weak-derivative or form-expectation assertion is a premise. -/
theorem root_energy_vector_field (κ : ℝ) (u : h04 L 2) :
    let a := m21 u
    let U := physical (m10 a)
    let Ux := physical (Complex.I • D a)
    let Uxx := -physical (lap u)
    let C := physical (m10 (Fh (le_refl (1 : ℝ)) a))
    (HasWeakDeriv U Ux ∧ HasWeakDeriv Ux Uxx) ∧
    ((C : AddCircle L → ℂ) =ᵐ[volume]
      fun x => ((‖U x‖ ^ 2 : ℝ) : ℂ) * U x) ∧
    energy κ a = QuantumNLS.ChargeEnergy.energyH1 κ (U : AddCircle L → ℂ) ∧
    (∀ (c : ℝ) (N : ℕ), ∃ Ψ : QuantumNLS.PhysicalEnergy.PhysH1 L N,
      Ψ.val = prodState U N ∧
      QuantumNLS.ContactProductIntegrals.PiSquareFubini Ψ.val ∧
      QuantumNLS.ContactForm.q c Ψ Ψ =
        ((N * (‖U‖ ^ 2) ^ (N-1) * QuantumNLS.ChargeEnergy.kinetic (U : AddCircle L → ℂ) +
          c * N * ((N : ℝ)-1) * (‖U‖ ^ 2) ^ (N-2) *
            QuantumNLS.ChargeEnergy.quartic (U : AddCircle L → ℂ) : ℝ) : ℂ)) ∧
    ((U = 0 ∧ energy κ a = 0) ∨
      ∃ (v : L2T L) (hv : ‖v‖ = 1) (hH : OneH1 v),
        U = (‖U‖ : ℂ) • v ∧
        Tendsto (fun N : ℕ => ‖U‖ ^ 2 *
          (hN (κ * ‖U‖ ^ 2) N (productH1 hv hH N) / N)) atTop
            (nhds (energy κ a))) ∧
    HasFDerivAt (energy κ) (differential κ u) a ∧
    (∀ h : h04 L 1,
      differential κ u h = 2 * (⟪-Uxx + ((2 * κ : ℝ) : ℂ) • C,
        physical (m10 h)⟫_ℂ).re ∧
      omega (X κ u) (physical (m10 h)) = differential κ u h) ∧
    Complex.I • X κ u = -Uxx + ((2 * κ : ℝ) : ℂ) • C := by
  change (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  have hg := physical_grad κ u
  refine ⟨weak_pair u, cubic (m21 u), (physical_energy κ (m21 u)).symm,
    fun c N => product_origin (physical (m10 (m21 u))) (physical_oneH1 (m21 u)) c N,
    mass_origin κ (m21 u), energy_fderiv κ u, ?_, ?_⟩
  · intro h
    constructor
    · rw [differential_apply, ← hg, (physical (L := L)).inner_map_map]
    · rw [omega, X, inner_smul_left, differential_apply,
        (physical (L := L)).inner_map_map]
      simp [Complex.mul_im]
  · rw [X, smul_smul]
    simp only [mul_neg, Complex.I_mul_I, neg_neg, one_smul]
    simpa only [neg_neg] using hg

#print axioms root_energy_vector_field
end QuantumNLS.RootEnergyVectorField

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootEnergyVectorField." ||
        n.toString.startsWith "_private.QuantumNLS.RootEnergyVectorField." then
      pending := pending.push n
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
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
