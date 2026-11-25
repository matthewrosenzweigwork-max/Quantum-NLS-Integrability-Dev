import QuantumNLS.RetargetCutoffR48b
import QuantumNLS.RetargetEnergyR48b
import QuantumNLS.TerraMultiRound87Quantum
import QuantumNLS.TerraMultiRound87Rotations
import QuantumNLS.TerraMultiRound88Tensor
import QuantumNLS.TerraMultiRound88Zero

/-! Full-product-torus comparison on a fixed physical H¹ profile class.
The limits are taken by choosing the energy cutoff, then the label cutoff,
then the particle threshold. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false
noncomputable section
open Set Filter Topology
open scoped ENNReal

namespace QuantumNLS.RetargetPropagationR48b
open PhysicalTensor TensorCarrier CountRotations TraceClass HighAngleRotations
open HaarSpectralTail TerraMultiRound87Rotations
open DynSeedInputR47b DynSeedClassicalR47b DynSeedMomentsR47b
open RetargetAnglesR48b RetargetCutoffR48b RetargetEnergyR48b RetargetUniformSeedR48b
open BetheCoefficientTransform

variable {L κ : ℝ} [Fact (0 < L)]

theorem trace_triangle {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B C : H →L[ℂ] H) :
    traceNorm (A - C) ≤ traceNorm (A - B) + traceNorm (B - C) := by
  have h : A - B + (B - C) = A - C := by abel_nf
  rw [← h]
  exact traceNorm_add_le _ _

/-- Uniform removal of arbitrary tail angles on the actual product vectors. -/
theorem quantum_label_cutoff (hκ : 0 < κ) (R : ℝ) (k : ℕ) (hk1 : 1 ≤ k)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ J₀ : ℕ, ∀ J, J₀ ≤ J → ∀ᶠ n in atTop, ∀ hk : k ≤ n+1,
      ∀ u ∈ R52CFCompact.profileClass L R, ∀ θ : AngleTorus,
        let v : HN L (n+1) := HighMomentsOps.wvec (n+1) u
        let b := Def044D1SpectralR51a.basis (L := L) hκ n
        traceNorm (reducedDensityN (n+1) k hk (quantumRotation b θ v).val -
          reducedDensityN (n+1) k hk (quantumRotation b (truncate (labels J) θ) v).val) ≤ ENNReal.ofReal ε := by
  classical
  obtain ⟨C, hC, hprofile⟩ := profile_energy_bound (L := L) hκ R
  let d : ℝ := min (1/2) (ε/32)
  have hd : 0 < d := lt_min (by norm_num) (by positivity)
  have hd1 : d < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hdε : d ≤ ε / 32 := min_le_right _ _
  let E : ℝ := (C+1)/d^2
  have hE : 0 < E := by dsimp [E]; positivity
  have hcE : C / E ≤ d^2 := by
    apply (div_le_iff₀ hE).2
    dsimp [E]
    field_simp
    nlinarith only [hC, sq_nonneg d]
  obtain ⟨NE, η, _, hη, hηlim, htail⟩ :=
    TerraMultiRound87Quantum.inherited_tail_with_projection L hκ hE hk1
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.mp
    (hηlim.eventually (gt_mem_nhds (show 0 < ε / 2 by positivity)))
  refine ⟨J₀, fun J hJ => ?_⟩
  let F := labels J
  have hηJ : η J < ε / 2 := hJ₀ J hJ
  filter_upwards [eventually_ge_atTop NE] with n hnE
  intro hk u hu θ
  let N := n+1
  have hN : 0 < N := Nat.succ_pos _
  let b := bas L hκ hN
  let v : HN L N := HighMomentsOps.wvec N u
  have hv : ‖v‖ = 1 := by
    change ‖(htpow N u : HilbertTensorPower ℂ (L2T L) N)‖ = 1
    simp only [norm_htpow, hu.2.1, one_pow]
  obtain ⟨P, hP, htail'⟩ := htail N (hnE.trans (Nat.le_succ _)) hk
  obtain ⟨huH, huE⟩ := hprofile u hu
  have hcut : ‖v - P v‖ ≤ d :=
    (sq_le_sq₀ (norm_nonneg _) hd.le).mp
      ((product_cutoff hκ hN hE P hP u hu.2.1 huH huE).trans hcE)
  obtain ⟨w, hw, hwP, hwClose⟩ := normalize_mask hκ hN E P hP v hv (hcut.trans_lt hd1)
  let V := quantumRotation b (truncate F θ)
  have hPV : P (V w) = V w := by
    change P (quantumRotation b (truncate F θ) w) = _
    rw [projection_rotation_commute b P _ hP, hwP]
  have hVclose : ‖V v - V w‖ ≤ 2*d := by
    rw [← map_sub, V.norm_map]
    exact hwClose.trans (mul_le_mul_of_nonneg_left hcut zero_le_two)
  have hθ (i : ℤ) (hi : |i| ≤ (J : ℤ)) : tailAngle F θ i = 1 :=
    tailAngle_eq_one F θ i ((mem_labels J i).2 hi)
  have hquant := htail' (V v) (V w)
    (by rw [V.norm_map, hv]) (by rw [V.norm_map, hw]) hPV (2*d) (by positivity) hVclose J
    (tailAngle F θ) hθ
  rw [← quantumRotation_mul b, tailAngle_mul_low] at hquant
  have hquant' : traceNorm (reducedDensityN N k hk (quantumRotation b θ v).val -
      reducedDensityN N k hk (V v).val) ≤ ENNReal.ofReal ε :=
    hquant.trans (ENNReal.ofReal_le_ofReal (by linarith only [hdε, hηJ, hε]))
  exact hquant'


theorem rank_zero_error (hκ : 0 < κ) (n : ℕ) (u : L2T L) (hu : ‖u‖ = 1)
    (θ : AngleTorus) :
    stateError 0 (Nat.zero_le _) (quantumRotation (Def044D1SpectralR51a.basis hκ n) θ
      (HighMomentsOps.wvec (n+1) u)) (physicalAngle hκ θ u) = 0 := by
  let x := quantumRotation (Def044D1SpectralR51a.basis hκ n) θ (HighMomentsOps.wvec (n+1) u)
  have hx : ‖x.val‖ = 1 := by
    change ‖x‖ = 1
    unfold x
    rw [LinearIsometryEquiv.norm_map]
    change ‖(htpow (n+1) u : HilbertTensorPower ℂ (L2T L) (n+1))‖ = 1
    simp only [norm_htpow, hu, one_pow]
  have hzero := TerraMultiRound88Zero.rank_zero_marginal _ x.val hx (physicalAngle hκ θ u)
  change traceNorm (reducedDensityN (n+1) 0 (Nat.zero_le _) x.val -
    Prop025OInputs.tensorProj 0 (physicalAngle hκ θ u)) = 0
  rw [hzero, sub_self]
  exact (traceNorm_eq_zero_iff _).2 rfl

theorem finite_angles (hκ : 0 < κ) (R : ℝ) (k : ℕ) (F : Finset ℤ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ hk : k ≤ n+1, ∀ u ∈ R52CFCompact.profileClass L R, ∀ θ : AngleTorus,
      stateError k hk (quantumRotation (Def044D1SpectralR51a.basis hκ n)
        (truncate F θ) (HighMomentsOps.wvec (n+1) u)) (physicalAngle hκ (truncate F θ) u) ≤
        ENNReal.ofReal ε := by
  obtain ⟨N₀, hf⟩ := (R52CFMain.finite_count_propagation L hκ F R k
    (fun _ => -Real.pi) (fun _ => Real.pi)).1 ε hε
  filter_upwards [eventually_ge_atTop N₀] with n hnF
  intro hk u hu θ
  let N := n+1
  have hN : 0 < N := Nat.succ_pos _
  let v : HN L N := HighMomentsOps.wvec N u
  have hfinite := hf N hN hk (hnF.trans (Nat.le_succ _)) u hu (shortTime F θ)
    (fun i hi => shortTime_zero F θ hi) (fun i _ => shortTime_bound F θ i)
  change traceNorm (reducedDensityN N k hk (R52CFEvol.countEvol L hκ hN F (shortTime F θ) v).val -
    Prop001.coherentProjector k (RF535Final.Tθ hκ (shortTime F θ) u)) ≤ ENNReal.ofReal ε at hfinite
  rw [finite_quantum hκ hN F θ v, finite_classical hκ F θ u] at hfinite
  exact hfinite

theorem classical_projector_cutoff (hκ : 0 < κ) (R : ℝ) (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ J in atTop, ∀ u ∈ R52CFCompact.profileClass L R, ∀ θ : AngleTorus,
      traceNorm (Prop025OInputs.tensorProj k (physicalAngle hκ (truncate (labels J) θ) u) -
        Prop025OInputs.tensorProj k (physicalAngle hκ θ u)) ≤ ENNReal.ofReal ε := by
  let δ : ℝ := ε / (2 * ((k : ℝ) + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδk : 2 * (k : ℝ) * δ ≤ ε := by
    have hden : 0 < 2 * ((k : ℝ) + 1) := by positivity
    have h : δ * (2 * ((k : ℝ) + 1)) = ε := div_mul_cancel₀ _ hden.ne'
    nlinarith only [h, hδ]
  filter_upwards [uniform_classical_cutoff (L := L) hκ R δ hδ] with J hclass
  intro u hu θ
  let vlow := physicalAngle hκ (truncate (labels J) θ) u
  let vfull := physicalAngle hκ θ u
  have hnunit (φ : AngleTorus) : ‖physicalAngle hκ φ u‖ = 1 :=
    (torus_norm hκ (angle_mem_torus hκ u u (fun _ => rfl) φ)).trans hu.2.1
  have hcutClass : ‖vlow - vfull‖ ≤ δ :=
    (by simpa only [dist_eq_norm] using (hclass θ u (subset_closure hu)).le)
  exact (TerraMultiRound88Tensor.tensor_projector_lipschitz k vlow vfull (hnunit _) (hnunit _)).trans
    (ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left hcutClass (by positivity)).trans hδk))

theorem trace_three {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B C D : H →L[ℂ] H) (ε : ℝ) (hε : 0 < ε)
    (hAB : traceNorm (A - B) ≤ ENNReal.ofReal (ε/4))
    (hBC : traceNorm (B - C) ≤ ENNReal.ofReal (ε/4))
    (hCD : traceNorm (C - D) ≤ ENNReal.ofReal (ε/4)) :
    traceNorm (A - D) ≤ ENNReal.ofReal ε := by
  have hquarter : 0 ≤ ε / 4 := by positivity
  refine (trace_triangle A B D).trans ((add_le_add le_rfl (trace_triangle B C D)).trans ?_)
  refine (add_le_add hAB (add_le_add hBC hCD)).trans ?_
  rw [← ENNReal.ofReal_add hquarter hquarter,
    ← ENNReal.ofReal_add hquarter (add_nonneg hquarter hquarter)]
  exact ENNReal.ofReal_le_ofReal (by linarith only [hε])

/-- For positive rank, combine the three comparisons using a single fixed
label cutoff for the class and rank. -/
theorem positive_rank_angles (hκ : 0 < κ) (R : ℝ)
    (k : ℕ) (hk1 : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ hk : k ≤ n+1,
      ∀ u ∈ R52CFCompact.profileClass L R, ∀ θ : AngleTorus,
        stateError k hk (quantumRotation (Def044D1SpectralR51a.basis hκ n) θ
          (HighMomentsOps.wvec (n+1) u)) (physicalAngle hκ θ u) ≤ ENNReal.ofReal ε := by
  have hquarter : 0 < ε / 4 := by positivity
  obtain ⟨J₀, hQ⟩ := quantum_label_cutoff (L := L) hκ R k hk1 (ε/4) hquarter
  obtain ⟨J₁, hC⟩ := eventually_atTop.mp (classical_projector_cutoff (L := L) hκ R k (ε/4) hquarter)
  let J := max J₀ J₁
  let F := labels J
  have hquant := hQ J (le_max_left J₀ J₁)
  have hfin := finite_angles (L := L) hκ R k F (ε/4) hquarter
  refine (hquant.and hfin).mono ?_
  intro n hn hk u hu θ
  let v : HN L (n+1) := HighMomentsOps.wvec (n+1) u
  let b := Def044D1SpectralR51a.basis (L := L) hκ n
  let A := reducedDensityN (n+1) k hk (quantumRotation b θ v).val
  let B := reducedDensityN (n+1) k hk (quantumRotation b (truncate F θ) v).val
  let C := Prop025OInputs.tensorProj k (physicalAngle hκ (truncate F θ) u)
  let D := Prop025OInputs.tensorProj k (physicalAngle hκ θ u)
  have hAB : traceNorm (A - B) ≤ ENNReal.ofReal (ε/4) := hn.1 hk u hu θ
  have hBC : traceNorm (B - C) ≤ ENNReal.ofReal (ε/4) := hn.2 hk u hu θ
  have hCD : traceNorm (C - D) ≤ ENNReal.ofReal (ε/4) :=
    hC J (le_max_right J₀ J₁) u hu θ
  change traceNorm (A - D) ≤ ENNReal.ofReal ε
  exact trace_three A B C D ε hε hAB hBC hCD

theorem uniform_angles (hκ : 0 < κ) (R : ℝ) :
    UniformAngles (L := L) hκ R := by
  intro k ε hε
  cases k with
  | zero =>
    exact Filter.Eventually.of_forall (fun n hk u hu θ => by
      have h : stateError 0 hk (quantumRotation (Def044D1SpectralR51a.basis hκ n) θ
          (HighMomentsOps.wvec (n+1) u)) (physicalAngle hκ θ u) = 0 :=
        rank_zero_error hκ n u hu.2.1 θ
      rw [h]
      exact bot_le)
  | succ k => exact positive_rank_angles hκ R (k+1) (Nat.succ_le_succ (Nat.zero_le k)) ε hε

end QuantumNLS.RetargetPropagationR48b

#print axioms QuantumNLS.RetargetPropagationR48b.uniform_angles

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "QuantumNLS.RetargetPropagationR48b." ||
        name.toString.startsWith "_private.QuantumNLS.RetargetPropagationR48b." then
      pending := pending.push name
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    unless seen.contains name do
      seen := seen.insert name
      if (name.toString.splitOn "HeldGP14Tonelli").length > 1 then
        throwError "Rejected dependency: {name}"
      if let some info := env.find? name then
        match info with
        | .axiomInfo _ =>
          unless name == ``propext || name == ``Classical.choice || name == ``Quot.sound do
            throwError "Nonstandard dependency: {name}"
        | _ => pure ()
        pending := pending ++ info.type.getUsedConstants
        if let some value := info.value? (allowOpaque := true) then
          pending := pending ++ value.getUsedConstants
      else
        throwError "Missing dependency: {name}"
  Lean.logInfo m!"R48b aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only."
