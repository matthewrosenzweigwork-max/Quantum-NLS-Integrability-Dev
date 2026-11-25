import QuantumNLS.AllOrderEnergyPredecessorsR57a
import QuantumNLS.AllOrderEnergyQuantumR56a

/-! The common finite packets satisfy DEF-031 by the intensive energy residual. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Filter Topology
open scoped InnerProductSpace LinearPMap
namespace QuantumNLS.AllOrderEnergyPacketsR57a
open Def033HierarchyR24m PhysicalTensor TensorCarrier PhysicalEnergy EnergyPreparationDef
open BetheCoefficientTransform BetheSpectralCharges BetheLabels BulkResponseActual
open CommonBethePacket ContactOperator ContactForm BethePhysicalTransfer
variable {L κ : ℝ} [Fact (0 < L)]

private theorem norm_sq_combination {N : ℕ} (b : BetheBasis L N) (s : Finset (MArr N))
    (a : MArr N → ℂ) :
    ‖∑ m ∈ s, a m • b m‖ ^ 2 = ∑ m ∈ s, ‖a m‖ ^ 2 := by
  calc
    _ = (⟪∑ m ∈ s, a m • b m, ∑ m ∈ s, a m • b m⟫_ℂ).re := by
      exact norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ = _ := by
      rw [b.orthonormal.inner_sum]
      simp only [Complex.re_sum, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

private theorem packet_multiplier_eq_sum {N : ℕ} (b : BetheBasis L N) (P : Packet b)
    (ev : MArr N → ℝ) (hdom : vector P ∈ (multiplier b ev).domain) :
    multiplier b ev ⟨vector P, hdom⟩ =
      ∑ j ∈ support P, ((ev j : ℂ) * P.coefficients j) • b j := by
  classical
  apply b.repr.injective
  ext m
  simp only [HilbertBasis.repr_apply_apply, multiplier_coord]
  change (ev m : ℂ) * ⟪b m, ∑ j ∈ support P, P.coefficients j • b j⟫_ℂ = _
  by_cases hm : m ∈ support P
  · rw [b.orthonormal.inner_right_sum _ hm, b.orthonormal.inner_right_sum _ hm]
  · have hz (a : MArr N → ℂ) : ⟪b m, ∑ j ∈ support P, a j • b j⟫_ℂ = 0 := by
      rw [inner_sum]
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [inner_smul_right, b.orthonormal.inner_eq_zero (ne_of_mem_of_not_mem hj hm).symm, mul_zero]
    rw [hz, hz, mul_zero]

/-- On a finite packet, a bound on the support of the intensive symbol
bounds the norm of the intensive operator residual. -/
theorem packet_residual {N : ℕ} (b : BetheBasis L N) (P : Packet b)
    (ev : MArr N → ℝ) (I ε : ℝ) (hε : 0 ≤ ε)
    (hb : ∀ m ∈ support P, |ev m - I| ≤ ε) :
    let hdom := AuditWeightedPacketR49a.packet_mem_every_domain b P ev
    ‖multiplier b ev ⟨vector P, hdom⟩ - (I : ℂ) • vector P‖ ≤ ε := by
  classical
  let a := P.coefficients
  let S := support P
  let y := ∑ m ∈ S, ((ev m : ℂ) * a m) • b m
  have hVec : vector P = ∑ m ∈ S, a m • b m := rfl
  have hy := packet_multiplier_eq_sum b P ev (AuditWeightedPacketR49a.packet_mem_every_domain b P ev)
  change ‖multiplier b ev ⟨vector P, _⟩ - (I : ℂ) • vector P‖ ≤ ε
  rw [hy, hVec]
  have hcomb : y - (I : ℂ) • (∑ m ∈ S, a m • b m) =
      ∑ m ∈ S, (((ev m - I : ℝ) : ℂ) * a m) • b m := by
    dsimp only [y]
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_smul, ← sub_smul, Complex.ofReal_sub, sub_mul]
  rw [hcomb]
  apply le_of_pow_le_pow_left₀ (n := 2) (by decide) hε
  rw [norm_sq_combination]
  have hnorm : ∑ m ∈ S, ‖a m‖ ^ 2 = 1 := by
    rw [← norm_sq_combination b S a, ← hVec]
    change ‖synthesis b P.coefficients‖ ^ 2 = 1
    rw [P.normalized, one_pow]
  calc
    (∑ m ∈ S, ‖((ev m - I : ℝ) : ℂ) * a m‖ ^ 2) ≤
        ∑ m ∈ S, ε ^ 2 * ‖a m‖ ^ 2 := by
      refine Finset.sum_le_sum fun m hm => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hb m hm) 2) (sq_nonneg _)
    _ = ε ^ 2 := by rw [← Finset.mul_sum, hnorm, mul_one]

/-- The normalized finite combination is in the physical form domain, and
its actual contact energy equals the expectation of the intensive charge. -/
theorem packet_form (hκ : 0 < κ) (n : ℕ) (P : Packet (physBasis L hκ (n+1))) :
    let b := physBasis L hκ (n+1)
    let ev := fun m => eigenvalue L (n+1) (κ/(n+1 : ℕ)) 2 m / (n+1 : ℕ)
    let hdom := AuditWeightedPacketR49a.packet_mem_every_domain b P ev
    ∃ x : VSym L (n+1), valSym x = symmetricPosition L (n+1) (vector P) ∧
      hN κ (n+1) x.val / (n+1 : ℕ) = (⟪vector P, multiplier b ev ⟨vector P, hdom⟩⟫_ℂ).re := by
  classical
  dsimp only
  let b := physBasis L hκ (n+1)
  let c : ℝ := κ / (n+1 : ℕ)
  let hc : 0 ≤ c := div_nonneg hκ.le (Nat.cast_nonneg _)
  let pos := symmetricPosition L (n+1)
  let e := eigenvalue L (n+1) c 2
  let ev := fun m => e m / (n+1 : ℕ)
  have hb : b = Def044D1SpectralR51a.basis hκ n := by
    simp only [b, physBasis, dite_eq_left (by omega : 1 ≤ n+1)]
  have hB (m) : Rop c hc (((e m + 1 : ℝ) : ℂ) • pos (b m)) = pos (b m) := by
    obtain ⟨hm, he⟩ := AllOrderEnergyQuantumR56a.contact_Hamiltonian_basis (L := L) hκ n m
    rw [hb]
    exact (Rop_eq_valSym_psi hc _).trans (TerraMultiRound89EigenForm.eigen_resolvent_form hc _ hm (e m) he).1
  let g := ∑ m ∈ support P, P.coefficients m • (((e m + 1 : ℝ) : ℂ) • pos (b m))
  have hg : Rop c hc g = pos (vector P) := by
    change Rop c hc g = pos (∑ m ∈ support P, P.coefficients m • b m)
    simp only [g, map_sum, map_smul, hB]
  let x := psi c hc g
  have hx : valSym x = pos (vector P) := (Rop_eq_valSym_psi hc _).symm.trans hg
  refine ⟨x, hx, ?_⟩
  let z := multiplier b ev ⟨vector P, AuditWeightedPacketR49a.packet_mem_every_domain b P ev⟩
  have hz := packet_multiplier_eq_sum b P ev (AuditWeightedPacketR49a.packet_mem_every_domain b P ev)
  change z = _ at hz
  have hsum : g - Rop c hc g = ((n+1 : ℕ) : ℂ) • pos z := by
    rw [hg, hz]
    change (∑ m ∈ support P, P.coefficients m • (((e m + 1 : ℝ) : ℂ) • pos (b m))) -
      pos (∑ m ∈ support P, P.coefficients m • b m) = _
    simp only [map_sum, Finset.smul_sum]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [map_smul, smul_smul, ← sub_smul, Complex.ofReal_add, Complex.ofReal_one]
    congr 1
    have hn : ((n+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    unfold ev
    rw [Complex.ofReal_div, Complex.ofReal_natCast]
    field_simp [hn]
    ring
  have hq := variational_of_domain hc g x
  change q c x.val x.val = _ at hq
  rw [hsum, hx] at hq
  have hinner := inner_smul_right (𝕜 := ℂ) (pos (vector P)) (pos z) ((n+1 : ℕ) : ℂ)
  rw [pos.inner_map_map] at hinner
  rw [hinner] at hq
  have he : hN κ (n+1) x.val = ((n+1 : ℕ) : ℝ) * (⟪vector P, z⟫_ℂ).re := by
    change (q c x.val x.val).re = _
    have h := congrArg Complex.re hq
    simpa [Complex.mul_re] using h
  change hN κ (n+1) x.val / (n+1 : ℕ) = (⟪vector P, z⟫_ℂ).re
  rw [he, mul_comm, mul_div_cancel_right₀ _ (by positivity)]

/-- A positive-sector preparation can be extended at the vacuum by its exact
tensor product, giving the all-N DEF-031 predicate. -/
theorem energy_preparation_of_positive (κ : ℝ) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (ψ : ∀ n : ℕ, HN L (n+1)) (hunit : ∀ n, ‖ψ n‖ = 1)
    (x : ∀ n : ℕ, VSym L (n+1))
    (hx : ∀ n, valSym (x n) = symmetricPosition L (n+1) (ψ n))
    (hclose : Tendsto (fun n => ActualModelCorollaryR53a.preparationError u n (ψ n)) atTop (𝓝 0))
    (hE : limsup (fun n => ((hN κ (n+1) (x n).val / (n+1 : ℕ) : ℝ) : EReal))
      atTop ≤ (I3 κ (physical u) : EReal)) :
    EnergyPreparation κ (physical u) (fun N => Nat.casesOn N (htpow 0 (physical u)) (fun n => (ψ n).val)) := by
  let v := physical u
  have hH := PhysicalProductPreparation.oneH1_smooth u.property
  obtain ⟨⟨hvnorm, _⟩, hvsec, xv, hxv, hxs, _⟩ := product_energyPreparation hu hH κ
  refine ⟨⟨fun N => ?_, ?_⟩, fun N => ?_, ?_⟩
  · cases N with
    | zero => exact hvnorm 0
    | succ n => exact hunit n
  · apply (tendsto_add_atTop_iff_nat 1).mp
    exact hclose
  · cases N with
    | zero => exact hvsec 0
    | succ n => exact (ψ n).property
  · refine ⟨fun N => Nat.casesOn N (xv 0) (fun n => (x n).val), ?_, ?_, ?_⟩
    · intro N
      cases N with
      | zero => exact hxv 0
      | succ n =>
        change (x n).val.val = physUnitary (ψ n).val
        exact congrArg (fun z : SymL2 L (n+1) => z.val) (hx n)
    · intro N
      cases N with
      | zero => exact hxs 0
      | succ n => exact (x n).property
    · refine (EnergyPreparationDef.limsup_le_iff _ _).2 (fun ε hε => ?_)
      obtain ⟨n, hn⟩ := eventually_atTop.1 ((EnergyPreparationDef.limsup_le_iff _ _).1 hE ε hε)
      exact eventually_atTop.2 ⟨n+1, fun N hN => by
        cases N with
        | zero => omega
        | succ n' => exact hn n' (by omega)⟩

/-- One sequence with the printed support guarantees and the physical
DEF-031 and intensive energy limits. -/
def CommonEnergyPackets (hκ : 0 < κ) (u : Smooth L) : Prop :=
    ∃ P : (N : ℕ) → Packet (physBasis L hκ N),
      let ψ (n : ℕ) := vector (P (n+1))
      (∀ r ε, 0 < ε → ∀ᶠ N in atTop, ∀ m ∈ support (P N),
        |eigenvalue L N (κ/N) r m / (N : ℝ) - (ClassicalCharges.charge L κ u.val (r+1)).re| ≤ ε) ∧
      (∀ p : ℝ, 0 ≤ p → ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ m ∈ support (P N),
        AuditWeightedProbabilityR49a.error hκ (physical u) p N m ≤ ε) ∧
      EnergyPreparation κ (physical u) (fun N => Nat.casesOn N (htpow 0 (physical u)) (fun n => (ψ n).val)) ∧
      ∃ x : ∀ n, VSym L (n+1), (∀ n, valSym (x n) = symmetricPosition L (n+1) (ψ n)) ∧
        Tendsto (fun n => hN κ (n+1) (x n).val / (n+1 : ℕ)) atTop (𝓝 (I3 κ (physical u)))

/-- The very same common sequence from R-115CAA16 is norm-close and DEF-031
prepared at positive particle number, with its intensive energy converging. -/
theorem common_packets_prepared (hκ : 0 < κ)
    (WeightedR115CAA16Input : AllOrderEnergyPredecessorsR57a.WeightedR115CAA16Input (L := L) hκ)
    (u : Smooth L) (hu : ‖physical u‖ = 1) :
    CommonEnergyPackets hκ u := by
  obtain ⟨_, _, P, hP, hcharge, hweight⟩ :=
    WeightedR115CAA16Input (HierarchyInputR25m.scalar_moments hκ)
      (AllOrderEnergyPredecessorsR57a.concentrationAndBias hκ) u.val u.property hu
  let ψ (n : ℕ) := vector (P (n+1))
  have hunit (n) : ‖ψ n‖ = 1 := (P (n+1)).normalized
  have hclose : Tendsto (fun n => ActualModelCorollaryR53a.preparationError u n (ψ n)) atTop (𝓝 0) :=
    hP.comp (tendsto_add_atTop_nat 1)
  choose x hx hE using fun n => packet_form hκ n (P (n+1))
  have hlim : Tendsto (fun n => hN κ (n+1) (x n).val / (n+1 : ℕ)) atTop (𝓝 (I3 κ (physical u))) := by
    apply Metric.tendsto_nhds.2
    intro ε hε
    have hh := (tendsto_add_atTop_nat 1).eventually (hcharge 2 (ε/2) (half_pos hε))
    rw [charge_three_eq_I3 κ u.property, Complex.ofReal_re] at hh
    filter_upwards [hh] with n hn
    let b := physBasis L hκ (n+1)
    let ev := fun m => eigenvalue L (n+1) (κ/(n+1 : ℕ)) 2 m / (n+1 : ℕ)
    let I := I3 κ (physical u)
    have hr := packet_residual b (P (n+1)) ev I (ε/2) (half_pos hε).le hn
    have hc := AllOrderEnergyInputsR55a.packet_energy_error (ψ n)
      (multiplier b ev ⟨ψ n, AuditWeightedPacketR49a.packet_mem_every_domain b (P (n+1)) ev⟩) (hunit n) I
    rw [Real.dist_eq, hE n]
    exact ((hc.trans hr).trans_lt (half_lt_self hε))
  have hUpper : limsup (fun n => ((hN κ (n+1) (x n).val / (n+1 : ℕ) : ℝ) : EReal))
      atTop ≤ (I3 κ (physical u) : EReal) := by
    refine (EnergyPreparationDef.limsup_le_iff _ _).2 fun ε hε => ?_
    filter_upwards [hlim.eventually (gt_mem_nhds (show I3 κ (physical u) < I3 κ (physical u) + ε by linarith))]
      with n hn
    exact hn.le
  exact ⟨P, hcharge, hweight, energy_preparation_of_positive κ u hu ψ hunit x hx hclose hUpper, x, hx, hlim⟩

end QuantumNLS.AllOrderEnergyPacketsR57a
