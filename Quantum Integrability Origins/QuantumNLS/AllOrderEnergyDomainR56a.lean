import QuantumNLS.ContactFormTheorem
import QuantumNLS.TerraMultiRound89FormCore

/-! Conservation of the closed contact form under a unitary commuting with
its resolvent. This explains why no Hamiltonian operator-domain hypothesis
is needed for the R-568BCDF8 preparation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
open Filter Topology
open scoped InnerProductSpace LinearPMap
namespace QuantumNLS.AllOrderEnergyDomainR56a
open ContactForm ContactOperator PhysicalEnergy
variable {L : ℝ} [Fact (0 < L)] {N : ℕ} {c : ℝ}

/-- The form norm on the variational resolvent range is the resolvent pairing. -/
theorem formNorm_resolvent (hc : 0 ≤ c) (g : SymL2 L N) :
    formNormSq c (psi c hc g).1 = (⟪Rop c hc g, g⟫_ℂ).re := by
  rw [← re_inner_Mop_self hc, inner_Mop_right, resolvent_eq, ← Rop_eq_valSym_psi]

/-- A unitary preserving the contact resolvent preserves the form domain and
its quadratic expectation. The extension starts on the operator-domain core
and passes to its closure in the form norm. -/
theorem form_evolution_of_commuting_resolvent (hc : 0 ≤ c)
    (U : SymL2 L N ≃ₗᵢ[ℂ] SymL2 L N)
    (hcomm : ∀ g, Rop c hc (U g) = U (Rop c hc g)) (x : VSym L N) :
    ∃ y : VSym L N, valSym y = U (valSym x) ∧ (q c y.1 y.1).re = (q c x.1 x.1).re := by
  have hd := TerraMultiRound89FormCore.psi_dense (L := L) (N := N) hc
  obtain ⟨z, hz, hx⟩ := mem_closure_iff_seq_limit.mp (hd x)
  choose g hg using hz
  have hx' : Tendsto (fun n => psi c hc (g n)) atTop (𝓝 x) := by
    simpa only [hg] using hx
  have hres (g : SymL2 L N) : formNormSq c (psi c hc (U g)).1 = formNormSq c (psi c hc g).1 := by
    rw [formNorm_resolvent, formNorm_resolvent, hcomm, U.inner_map_map]
  let z' : ℕ → VSym L N := fun n => psi c hc (U (g n))
  have hdiff (i j : ℕ) : formNormSq c (z' i - z' j).1 =
      formNormSq c (psi c hc (g i) - psi c hc (g j)).1 := by
    change formNormSq c (((Minv c hc).comp Gop (U (g i)) -
      (Minv c hc).comp Gop (U (g j))) : VSym L N).1 =
        formNormSq c (((Minv c hc).comp Gop (g i) -
          (Minv c hc).comp Gop (g j)) : VSym L N).1
    have h := hres (g i - g j)
    change formNormSq c ((Minv c hc).comp Gop (U (g i - g j))).1 =
      formNormSq c ((Minv c hc).comp Gop (g i - g j)).1 at h
    simpa only [map_sub] using h
  have hC : 0 ≤ 1 + 2 * c * (Fintype.card (Pair N) * (1 + L⁻¹)) := by
    positivity [(Fact.out : 0 < L)]
  let C : ℝ := 1 + 2 * c * (Fintype.card (Pair N) * (1 + L⁻¹))
  have hLip (i j : ℕ) : dist (z' i) (z' j) ≤ Real.sqrt C * dist (psi c hc (g i)) (psi c hc (g j)) := by
    rw [dist_eq_norm, dist_eq_norm]
    apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by positivity)
    rw [mul_pow, Real.sq_sqrt hC]
    exact (H1_le_formNormSq hc _).trans ((hdiff i j).trans_le (formNormSq_le hc _))
  have hzs : CauchySeq z' := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    let δ := ε / (Real.sqrt C + 1)
    have hδ : 0 < δ := div_pos hε (by positivity)
    obtain ⟨n₀, hn⟩ := Metric.cauchySeq_iff.mp hx'.cauchySeq δ hδ
    refine ⟨n₀, fun i hi j hj => (hLip i j).trans_lt ?_⟩
    have hb : Real.sqrt C * δ < ε := by
      calc
        _ < (Real.sqrt C + 1) * δ := by linarith
        _ = ε := by dsimp [δ]; field_simp [(show Real.sqrt C + 1 ≠ 0 by positivity)]
    exact (mul_le_mul_of_nonneg_left (hn i hi j hj).le (Real.sqrt_nonneg _)).trans_lt hb
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hzs
  have hval : valSym y = U (valSym x) := by
    apply tendsto_nhds_unique (valSym.continuous.continuousAt.tendsto.comp hy)
    have h := U.continuous.continuousAt.tendsto.comp (valSym.continuous.continuousAt.tendsto.comp hx')
    simpa only [Function.comp_def, z', ← Rop_eq_valSym_psi, hcomm] using h
  have hcontinuous : Continuous (fun x : VSym L N => formNormSq c x.1) := by
    simp only [← re_inner_Mop_self hc]
    exact Complex.continuous_re.comp (continuous_id.inner (Mop c hc).continuous)
  have hforms : formNormSq c y.1 = formNormSq c x.1 := by
    apply tendsto_nhds_unique (hcontinuous.continuousAt.tendsto.comp hy)
    simpa only [Function.comp_def, z', hres] using hcontinuous.continuousAt.tendsto.comp hx'
  have hnorm : ‖y.1.val‖ = ‖x.1.val‖ := by
    change ‖valSym y‖ = ‖valSym x‖
    rw [hval, U.norm_map]
  unfold formNormSq at hforms
  rw [hnorm] at hforms
  exact ⟨y, hval, add_right_cancel hforms⟩

end QuantumNLS.AllOrderEnergyDomainR56a
set_option maxHeartbeats 15000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := env.constants.toList.filterMap fun (n, _) =>
    if n.toString.startsWith "QuantumNLS.AllOrderEnergyDomainR56a." ||
        n.toString.startsWith "_private.QuantumNLS.AllOrderEnergyDomainR56a." then some n else none
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
