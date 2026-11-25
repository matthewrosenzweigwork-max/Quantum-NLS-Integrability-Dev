import QuantumNLS.PhysicalProductPreparation

/-! Arbitrary-mass tensor in the physical symmetric H¹ form domain.
R-242DB77D, A01.tex:179–194. Frozen predecessors are consumed read-only. -/
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate InnerProductSpace
open MeasureTheory QuantumNLS.PhysicalEnergy QuantumNLS.PhysicalTensor QuantumNLS.Energy
  QuantumNLS.CollisionTrace QuantumNLS.Fourier QuantumNLS.ContactForm QuantumNLS.ChargeEnergy
  QuantumNLS.ProductEnergyPreparation QuantumNLS.CollisionIdentification
namespace QuantumNLS.ContactProductMass
variable {L : ℝ} [Fact (0 < L)]

theorem mass_sum (u : L2T L) :
    HasSum (fun n : ℤ => ‖fourierL2 L u n‖ ^ 2) (‖u‖ ^ 2) := by
  have h := (QuantumNLS.Energy.summable_sq (fourierL2 L u)).hasSum
  rw [← QuantumNLS.Energy.norm_sq_eq_tsum, norm_fourierL2] at h
  exact h

theorem tensor_norm (u : L2T L) (N : ℕ) :
    ‖prodState u N‖ ^ 2 = (‖u‖ ^ 2) ^ N := by
  rw [norm_prodState, ← pow_mul, Nat.mul_comm N 2, pow_mul]

theorem hasSum_kin_prod {u : L2T L} (hH : OneH1 u) (N : ℕ) (j : Fin N) :
    HasSum (fun w : Mom N => freq L (w j) ^ 2 * ‖(momUnitary L N (prodState u N) : Mom N → ℂ) w‖ ^ 2)
      ((‖u‖ ^ 2) ^ (N - 1) * kinetic (u : AddCircle L → ℂ)) := by
  set g : Fin N → ℤ → ℝ := fun i n => (if i = j then freq L n ^ 2 else 1) * ‖fourierL2 L u n‖ ^ 2
    with hg
  have h0 : ∀ i n, 0 ≤ g i n := fun i n => by simp only [hg]; split_ifs <;> positivity
  have hsum : ∀ i, Summable (g i) := fun i => by
    by_cases hi : i = j
    · simp only [hg, hi, ite_true]; exact (hasSum_kin_a hH).summable
    · simp only [hg, hi, ite_false, one_mul]; exact (mass_sum u).summable
  have h := prod_hasSum N g h0 hsum
  have hval : ∏ i, ∑' n, g i n = (‖u‖ ^ 2) ^ (N - 1) * kinetic (u : AddCircle L → ℂ) := by
    have : ∀ i, ∑' n, g i n = if i = j then kinetic (u : AddCircle L → ℂ) else ‖u‖ ^ 2 := fun i => by
      by_cases hi : i = j
      · simp only [hg, hi, ite_true]; exact (hasSum_kin_a hH).tsum_eq
      · simp only [hg, hi, ite_false, one_mul]; exact (mass_sum u).tsum_eq
    simp_rw [this]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    simp only [ite_true]
    have he : ∏ i ∈ Finset.univ.erase j, (if i = j then kinetic (u : AddCircle L → ℂ) else ‖u‖ ^ 2) =
        (‖u‖ ^ 2) ^ (N - 1) := by
      trans ∏ _i ∈ Finset.univ.erase j, ‖u‖ ^ 2
      · apply Finset.prod_congr rfl
        intro i hi
        rw [ite_eq_right (Finset.ne_of_mem_erase hi)]
      · simp
    rw [he, mul_comm]
  rw [hval] at h
  convert h using 1
  funext w
  rw [coeff_prodState, norm_prod]
  simp only [hg, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.prod_pow]

/-- Total weighted sum on the product state: `Σ_w a_N(w)|Ψ̂(w)|² = m^N + N m^(N-1) K(u)`. -/
theorem hasSum_kinWeight_prod {u : L2T L} (hH : OneH1 u) (N : ℕ) :
    HasSum (fun w : Mom N => kinWeight L N w *
        ‖(momUnitary L N (prodState u N) : Mom N → ℂ) w‖ ^ 2)
      ((‖u‖ ^ 2) ^ N + N * ((‖u‖ ^ 2) ^ (N - 1) * kinetic (u : AddCircle L → ℂ))) := by
  have h1 : HasSum (fun w : Mom N => ‖(momUnitary L N (prodState u N) : Mom N → ℂ) w‖ ^ 2) ((‖u‖ ^ 2) ^ N) := by
    have h := QuantumNLS.Energy.summable_sq (momUnitary L N (prodState u N))
    have e := QuantumNLS.Energy.norm_sq_eq_tsum (momUnitary L N (prodState u N))
    have hn : ‖momUnitary L N (prodState u N)‖ ^ 2 = (‖u‖ ^ 2) ^ N := by
      rw [LinearIsometryEquiv.norm_map, tensor_norm]
    rw [hn] at e
    have := h.hasSum
    rw [← e] at this
    exact this
  have h2 := hasSum_sum (s := Finset.univ) (fun (j : Fin N) _ => hasSum_kin_prod hH N j)
  have h3 := h1.add h2
  convert h3 using 1
  · funext w
    unfold kinWeight
    rw [add_mul, Finset.sum_mul, one_mul]
  · simp

theorem exists_productH1 {u : L2T L} (hH : OneH1 u) (N : ℕ) :
    ∃ x : PhysH1 L N, x.val = prodState u N ∧ x ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L N)) := by
  have hmem : prodState u N ∈ {F : L2TN L N | Summable fun w => kinWeight L N w *
      ‖(momUnitary L N F : Mom N → ℂ) w‖ ^ 2} := (hasSum_kinWeight_prod hH N).summable
  rw [← PhysH1.range_val] at hmem
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x, hx, ?_⟩
  rw [PhysH1.mem_sym_iff, hx]
  rw [isSymm_iff_coeff]
  intro σ w
  rw [coeff_prodState, coeff_prodState]
  exact Equiv.prod_comp σ (fun i => fourierL2 L u (w i))

/-- The product state as an element of `H¹_sym`. -/
def productH1 {u : L2T L} (hH : OneH1 u) (N : ℕ) : PhysH1 L N :=
  Classical.choose (exists_productH1 hH N)

theorem productH1_val {u : L2T L} (hH : OneH1 u) (N : ℕ) :
    (productH1 hH N).val = prodState u N :=
  (Classical.choose_spec (exists_productH1 hH N)).1

theorem productH1_sym {u : L2T L} (hH : OneH1 u) (N : ℕ) :
    productH1 hH N ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L N)) :=
  (Classical.choose_spec (exists_productH1 hH N)).2

theorem coeffFun_productH1 {u : L2T L} (hH : OneH1 u) (N : ℕ) (w : Mom N) :
    coeffFun (productH1 hH N) w = ∏ j, fourierL2 L u (w j) := by
  unfold coeffFun
  rw [productH1_val, coeff_prodState]

/-- `‖∂_jΨ_N‖² = m^(N-1) K(u)` for each coordinate, with arbitrary mass. -/
theorem norm_sq_Dj_product {u : L2T L} (hH : OneH1 u) (N : ℕ) (j : Fin N) :
    ‖Dj j (productH1 hH N)‖ ^ 2 = (‖u‖ ^ 2) ^ (N - 1) * kinetic (u : AddCircle L → ℂ) := by
  rw [norm_sq_Dj]
  have h := hasSum_kin_prod hH N j
  rw [← h.tsum_eq]
  refine tsum_congr fun w => ?_
  unfold coeffFun
  rw [productH1_val]

/-- **Kinetic part of the product state:** `Σ_j ‖∂_jΨ_N‖² = N m^(N-1) K(u)`. -/
theorem sum_norm_sq_Dj_product {u : L2T L} (hH : OneH1 u) (N : ℕ) :
    ∑ j, ‖Dj j (productH1 hH N)‖ ^ 2 = N * ((‖u‖ ^ 2) ^ (N - 1) * kinetic (u : AddCircle L → ℂ)) := by
  simp [norm_sq_Dj_product hH N]


section Trace
variable {N : ℕ} (i j : Fin N) (hij : i ≠ j)
theorem traceCoeff_product {u : L2T L} (hH : OneH1 u) (t : TIdx N i j) :
    traceCoeff L i j hij (coeffFun (productH1 hH N)) t =
      (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * conv u t.1 * ∏ r : Rest N i j, fourierL2 L u (t.2 r) := by
  unfold traceCoeff
  simp_rw [coeffFun_productH1, prod_fib i j hij (fun n => fourierL2 L u n)]
  rw [tsum_mul_right]
  unfold conv
  ring

/-- **The collision trace of `u^{⊗N}` evaluated exactly**: for arbitrary `u ∈ H¹` and any pair `i ≠ j`,
`‖T_ij Ψ_N‖² = m^(N-2) ∫|u|⁴` — computed on the Fourier side from the constructed trace
(`ChargeEnergy.hasSum_quartic`, the Fourier convolution form of the quartic) and the product
sum over the remaining `N−2` factors (each contributing mass m). -/
theorem norm_sq_trace_product {u : L2T L} (hH : OneH1 u) :
    ‖traceMap i j hij (productH1 hH N)‖ ^ 2 = (‖u‖ ^ 2) ^ (N - 2) * quartic (u : AddCircle L → ℂ) := by
  have hq := hasSum_quartic (oneH1_h04 hH)
  have hco : ∀ k, coeff L (u : AddCircle L → ℂ) k = fourierL2 L u k := fun k => (fourierL2_apply L u k).symm
  have hq' : HasSum (fun s : ℤ => ‖(((Real.sqrt L)⁻¹ : ℝ) : ℂ) * conv u s‖ ^ 2) (quartic (u : AddCircle L → ℂ)) := by
    simp only [hco] at hq
    exact hq
  have hB : HasSum (fun m : Rest N i j → ℤ => ∏ r, ‖fourierL2 L u (m r)‖ ^ 2) ((‖u‖ ^ 2) ^ (N - 2)) := by
    have := prod_hasSum_fintype (fun (_ : Rest N i j) (n : ℤ) => ‖fourierL2 L u n‖ ^ 2)
      (fun _ n => by positivity) (fun _ => (mass_sum u).summable)
    have hc : Fintype.card (Rest N i j) = N - 2 := by
      have h := card_DCoord i j hij
      simp only [DCoord, Fintype.card_sum, Fintype.card_unit] at h
      have hN : 2 ≤ N := by
        have := i.isLt; have := j.isLt
        by_contra hn
        have : i = j := Fin.ext (by omega)
        exact hij this
      omega
    simpa [(mass_sum u).tsum_eq, hc] using this
  have hm := Summable.mul_of_nonneg hq'.summable hB.summable
    (fun s => by positivity) (fun m => Finset.prod_nonneg fun r _ => by positivity)
  have hprod := hq'.mul hB hm
  rw [mul_comm] at hprod
  rw [QuantumNLS.Energy.norm_sq_eq_tsum, ← hprod.tsum_eq]
  refine tsum_congr fun t => ?_
  rw [traceMap_apply, traceCoeff_product i j hij hH t, norm_mul, norm_prod, mul_pow,
    Finset.prod_pow]


end Trace

theorem norm_sq_productTrace {u : L2T L} (hH : OneH1 u) {N : ℕ}
    (i j : Fin N) (hij : i ≠ j) :
    ‖productTrace i j hij (productH1 hH N)‖ ^ 2 =
      (‖u‖ ^ 2) ^ (N - 2) * quartic (u : AddCircle L → ℂ) := by
  rw [productTrace_norm, traceCLM_apply]
  exact norm_sq_trace_product i j hij hH

#print axioms mass_sum
#print axioms tensor_norm
#print axioms hasSum_kin_prod
#print axioms hasSum_kinWeight_prod
#print axioms exists_productH1
#print axioms norm_sq_Dj_product
#print axioms norm_sq_productTrace
end QuantumNLS.ContactProductMass

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.ContactProductMass." ||
        n.toString.startsWith "_private.QuantumNLS.ContactProductMass." then
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
