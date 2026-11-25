import QuantumNLS.ContactProductIntegrals

/-! R-242DB77D / contact:prop:product, A01.tex:179–194.
One named theorem, on the original physical carriers and the accepted form.
The only profile premise is membership in H¹; no normalization, nonzero mass,
measurability, integrability, section qualification, or tensor conclusion is assumed.
The stronger all-N statement includes the printed N=1 clause. -/
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ENNReal
open MeasureTheory QuantumNLS.PhysicalEnergy QuantumNLS.PhysicalTensor
  QuantumNLS.ProductEnergyPreparation QuantumNLS.CollisionTrace
  QuantumNLS.CollisionIdentification QuantumNLS.ContactForm QuantumNLS.ChargeEnergy
  QuantumNLS.ContactProductIntegrals QuantumNLS.ProductWeakDerivatives
namespace QuantumNLS.ContactProductExact
variable {L : ℝ} [Fact (0 < L)]

/-- Exact product form energy, including the physical gradient and coordinate-trace
integrals, the repaired GP-14 applications, all masses including zero, and N=1.
At N=2, the ordinary natural power m^(N-2) is definitionally m^0=1. -/
theorem contact_prop_product (u : L2T L) (hH : OneH1 u) (c : ℝ) (N : ℕ) :
    ∃ Ψ : PhysH1 L N,
      Ψ.val = prodState u N ∧
      Ψ ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L N)) ∧
      ‖Ψ.val‖ ^ 2 = (‖u‖ ^ 2) ^ N ∧
      (∫ x, ‖Ψ.val x‖ ^ 2 ∂(torusPiMeasure L N)) = (‖u‖ ^ 2) ^ N ∧
      PiSquareFubini Ψ.val ∧
      (∀ j : Fin N,
        HasWeakPartial j Ψ.val (gradientCLM j Ψ) ∧
        ‖gradientCLM j Ψ‖ ^ 2 = (‖u‖ ^ 2) ^ (N - 1) * kinetic (u : AddCircle L → ℂ) ∧
        (∫ x, ‖gradientCLM j Ψ x‖ ^ 2 ∂(torusPiMeasure L N)) =
          (‖u‖ ^ 2) ^ (N - 1) * kinetic (u : AddCircle L → ℂ) ∧
        PiSquareFubini (gradientCLM j Ψ)) ∧
      (∀ (i j : Fin N) (hij : i ≠ j),
        ‖productTrace i j hij Ψ‖ ^ 2 =
          (‖u‖ ^ 2) ^ (N - 2) * quartic (u : AddCircle L → ℂ) ∧
        (∫ y, ‖productTrace i j hij Ψ y‖ ^ 2 ∂(dyij (L := L) i j)) =
          (‖u‖ ^ 2) ^ (N - 2) * quartic (u : AddCircle L → ℂ) ∧
        (∫ t, ∫ y, ‖productTrace i j hij Ψ (t,y)‖ ^ 2
          ∂(Measure.pi fun _ : Rest N i j => (volume : Measure (AddCircle L)))
          ∂(volume : Measure (AddCircle L))) =
          (‖u‖ ^ 2) ^ (N - 2) * quartic (u : AddCircle L → ℂ) ∧
        SquareFubini (volume : Measure (AddCircle L))
          (Measure.pi fun _ : Rest N i j => (volume : Measure (AddCircle L)))
          (productTrace i j hij Ψ)) ∧
      (q c Ψ Ψ).re =
        (∑ j, ‖gradientCLM j Ψ‖ ^ 2) +
          2 * c * ∑ p : Pair N, ∫ y,
            ‖productTrace p.1.1 p.1.2 (ne_of_lt p.2) Ψ y‖ ^ 2
              ∂(dyij (L := L) p.1.1 p.1.2) ∧
      q c Ψ Ψ = ((N * (‖u‖ ^ 2) ^ (N - 1) * kinetic (u : AddCircle L → ℂ) +
        c * N * ((N : ℝ) - 1) * (‖u‖ ^ 2) ^ (N - 2) *
          quartic (u : AddCircle L → ℂ) : ℝ) : ℂ) ∧
      (N = 1 → q c Ψ Ψ = ((kinetic (u : AddCircle L → ℂ) : ℝ) : ℂ)) := by
  let Ψ := QuantumNLS.ContactProductMass.productH1 hH N
  have hv : Ψ.val = prodState u N := QuantumNLS.ContactProductMass.productH1_val hH N
  have hg : ∀ j : Fin N, ‖gradientCLM j Ψ‖ ^ 2 =
      (‖u‖ ^ 2) ^ (N - 1) * kinetic (u : AddCircle L → ℂ) := fun j => by
    rw [QuantumNLS.PhysicalProductPreparation.norm_gradientCLM]
    exact QuantumNLS.ContactProductMass.norm_sq_Dj_product hH N j
  have ht : ∀ (i j : Fin N) (hij : i ≠ j), ‖productTrace i j hij Ψ‖ ^ 2 =
      (‖u‖ ^ 2) ^ (N - 2) * quartic (u : AddCircle L → ℂ) :=
    fun i j hij => QuantumNLS.ContactProductMass.norm_sq_productTrace hH i j hij
  have hq : q c Ψ Ψ = ((N * (‖u‖ ^ 2) ^ (N - 1) * kinetic (u : AddCircle L → ℂ) +
      c * N * ((N : ℝ) - 1) * (‖u‖ ^ 2) ^ (N - 2) *
        quartic (u : AddCircle L → ℂ) : ℝ) : ℂ) := by
    rw [q_self]
    congr 1
    have hd : ∑ j, ‖Dj j Ψ‖ ^ 2 =
        N * ((‖u‖ ^ 2) ^ (N - 1) * kinetic (u : AddCircle L → ℂ)) :=
      QuantumNLS.ContactProductMass.sum_norm_sq_Dj_product hH N
    have hp : ∑ p : Pair N, ‖Tpair p Ψ‖ ^ 2 =
        Fintype.card (Pair N) * ((‖u‖ ^ 2) ^ (N - 2) * quartic (u : AddCircle L → ℂ)) := by
      have h : ∀ p : Pair N, ‖Tpair p Ψ‖ ^ 2 =
          (‖u‖ ^ 2) ^ (N - 2) * quartic (u : AddCircle L → ℂ) := fun p => by
        rw [Tpair, traceCLM_apply]
        exact QuantumNLS.ContactProductMass.norm_sq_trace_product p.1.1 p.1.2 (ne_of_lt p.2) hH
      simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hd, hp]
    have hc := card_pair_real N
    linear_combination (c * (‖u‖ ^ 2) ^ (N - 2) * quartic (u : AddCircle L → ℂ)) * hc
  refine ⟨Ψ, hv, QuantumNLS.ContactProductMass.productH1_sym hH N, ?_, ?_,
    pi_square_fubini _, ?_, ?_, ?_, hq, ?_⟩
  · rw [hv]; exact QuantumNLS.ContactProductMass.tensor_norm u N
  · have ha : (Ψ.val : (Fin N → AddCircle L) → ℂ) =ᵐ[torusPiMeasure L N]
        prodFun (fun _ : Fin N => u) := by
      rw [hv]
      exact (memLp_prodFun (fun _ : Fin N => u)).coeFn_toLp
    calc
      _ = ∫ x : Fin N → AddCircle L, ‖prodFun (fun _ => u) x‖ ^ 2
          ∂(torusPiMeasure L N) := integral_congr_ae (ha.mono fun x hx => by rw [hx])
      _ = _ := (literal_tensor_integral u N).2
  · intro j
    have hw : HasWeakPartial j Ψ.val (gradientCLM j Ψ) := by
      obtain ⟨G, hG⟩ := QuantumNLS.ProductWeakDerivatives.PhysH1.exists_hasWeakPartial Ψ j
      rw [gradientCLM_eq_of_weak j Ψ G hG]
      exact hG
    refine ⟨hw, hg j, ?_, pi_square_fubini _⟩
    rw [QuantumNLS.ContactFormFamily.integral_norm_sq_eq]
    exact hg j
  · intro i j hij
    have hf := collision_fubini Ψ i j hij
    have he : (∫ y, ‖productTrace i j hij Ψ y‖ ^ 2 ∂(dyij (L := L) i j)) =
        (‖u‖ ^ 2) ^ (N - 2) * quartic (u : AddCircle L → ℂ) := by
      rw [QuantumNLS.ContactFormFamily.integral_norm_sq_eq]
      exact ht i j hij
    refine ⟨ht i j hij, he, ?_, hf⟩
    exact hf.2.2.2.2.2.1.symm.trans he
  · rw [q_self, Complex.ofReal_re]
    congr 1
    · apply Finset.sum_congr rfl
      intro j _
      rw [QuantumNLS.PhysicalProductPreparation.norm_gradientCLM]
    · congr 1
      apply Finset.sum_congr rfl
      intro p _
      rw [QuantumNLS.ContactFormFamily.integral_norm_sq_eq, productTrace_norm]
      rfl
  · intro hN
    simpa only [hN, Nat.cast_one, Nat.sub_self, pow_zero, one_mul,
      sub_self, mul_zero, zero_mul, add_zero] using hq

#print axioms contact_prop_product
end QuantumNLS.ContactProductExact

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.ContactProductExact." ||
        n.toString.startsWith "_private.QuantumNLS.ContactProductExact." then
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
