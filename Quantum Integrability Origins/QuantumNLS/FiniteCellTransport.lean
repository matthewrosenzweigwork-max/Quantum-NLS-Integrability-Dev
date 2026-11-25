import QuantumNLS.FiniteCellIncidence
import Mathlib.Algebra.Order.Chebyshev

/-! R-D8BB052C E2 prerequisites: actual target phases and operator residuals.
All arrays are complete occupation arrays. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped InnerProductSpace ComplexConjugate Classical
namespace QuantumNLS.FiniteCellTransport
open Occupation OccupationHilbert FullOccupationAffinity FiniteCellSupport
  FiniteCellPartition FiniteCellPaths FiniteCellGauge
variable {N : ℕ}

/-- The factorized target phase with the source's integer exponents. -/
def targetPhase (I : Finset ℤ) (t : ℤ → Phase) (m n : Arr N) : ℂ :=
  ∏ a ∈ I, (t a).1 ^ ((m.1 a : ℤ) - (n.1 a : ℤ))

theorem targetPhase_unit (I : Finset ℤ) (t : ℤ → Phase) (m n : Arr N) :
    ‖targetPhase I t m n‖ = 1 := by
  simp [targetPhase, norm_prod, norm_zpow, (t _).2]

theorem targetPhase_self (I : Finset ℤ) (t : ℤ → Phase) (m : Arr N) :
    targetPhase I t m m = 1 := by simp [targetPhase]

theorem targetPhase_trans (I : Finset ℤ) (t : ℤ → Phase) (m n p : Arr N) :
    targetPhase I t m n * targetPhase I t n p = targetPhase I t m p := by
  rw [targetPhase, targetPhase, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro a _
  have hz : (t a).1 ≠ 0 := by intro h; have := (t a).2; simp [h] at this
  rw [← zpow_add₀ hz]
  congr 1
  ring

theorem targetPhase_active (I : Finset ℤ) (K ell : ℕ) (t : ℤ → Phase)
    (m n : Arr N) (hc : SameCell I K ell m n) :
    targetPhase I t m n = targetPhase (active I K m) t m n := by
  symm
  apply Finset.prod_subset (Finset.filter_subset _ _)
  intro a ha hn
  rw [hc.2.2.1 a ha hn]
  simp

theorem phase_inv (z : Phase) : z.1⁻¹ = conj z.1 := by
  have hz : z.1 ≠ 0 := by intro h; have := z.2; simp [h] at this
  apply (mul_left_cancel₀ hz)
  rw [mul_inv_cancel₀ hz, mul_comm, phase_conj_mul]

/-- One actual donor step gives precisely t_a conjugate(t_b), in this orientation. -/
theorem targetPhase_shift (I : Finset ℤ) (t : ℤ → Phase) (a b : ℤ)
    (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b) (m : Arr N) (hd : DonorOK a m.1) :
    targetPhase I t m (shiftArr a b m hd) = (t a).1 * conj (t b).1 := by
  have hh : ∀ c ∈ I,
      (t c).1 ^ ((m.1 c : ℤ) - ((shiftArr a b m hd).1 c : ℤ)) =
        (if c = a then (t a).1 else 1) * (if c = b then conj (t b).1 else 1) := by
    intro c _
    by_cases hca : c = a
    · subst c
      have he : (m.1 a : ℤ) - ((shiftArr a b m hd).1 a : ℤ) = 1 := by
        change (m.1 a : ℤ) - (shift a b m.1 a : ℤ) = 1
        rw [shift_apply_donor m.1 hab]
        unfold DonorOK at hd
        omega
      simp [he, hab]
    · by_cases hcb : c = b
      · subst c
        have he : (m.1 b : ℤ) - ((shiftArr a b m hd).1 b : ℤ) = -1 := by
          change (m.1 b : ℤ) - (shift a b m.1 b : ℤ) = -1
          rw [shift_apply_receiver m.1 hab]
          omega
        simp [he, hca, phase_inv]
      · have he : (shiftArr a b m hd).1 c = m.1 c := shift_apply_exterior m.1 hca hcb
        simp [he, hca, hcb]
  rw [targetPhase, Finset.prod_congr rfl hh, Finset.prod_mul_distrib]
  simp [ha, hb]

theorem targetPhase_step (I : Finset ℤ) (t : ℤ → Phase) (a b : ℤ)
    (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b) (m n : Arr N) (hd : DonorOK a m.1) :
    targetPhase I t m n =
      ((t a).1 * conj (t b).1) * targetPhase I t (shiftArr a b m hd) n := by
  rw [← targetPhase_trans I t m (shiftArr a b m hd) n,
    targetPhase_shift I t a b ha hb hab m hd]

theorem targetPhase_next (I : Finset ℤ) (K ell : ℕ) (t : ℤ → Phase)
    (m n : Arr N) (hc : SameCell I K ell m n) (hne : m ≠ n) :
    targetPhase I t m n =
      ((t (firstAbove I K ell m n hc hne)).1 *
        conj (t (firstBelow I K ell m n hc hne)).1) *
      targetPhase I t (next I K ell m n hc hne) n :=
  targetPhase_step I t _ _ (firstAbove_spec I K ell m n hc hne).1
    (firstBelow_spec I K ell m n hc hne).1
    (next_labels_ne I K ell m n hc hne) m n _

/-- The residual is the actual completed FOA1 operator, before any restriction. -/
def residual (c : OrderedSeeds N) (t : ℤ → Phase) (a b : ℤ) (hab : a ≠ b)
    (g : H N) : H N :=
  seedTransfer c a b hab g - ((t a).1 * conj (t b).1) • g

theorem residual_destination (c : OrderedSeeds N) (t : ℤ → Phase) (a b : ℤ)
    (hab : a ≠ b) (g : H N) (m : Donor N a) :
    residual c t a b hab g (destination N a b m) =
      (seedPhase c a b hab m).1 * g m.1 -
        ((t a).1 * conj (t b).1) * g (destination N a b m) := by
  change transfer a b (seedPhase c a b hab) g (destination N a b m) - _ = _
  rw [transfer_at_destination]
  rfl

/-- Square energies of every actual Hilbert vector are summable. -/
theorem summable_energy (v : H N) : Summable (fun m : Arr N => ‖v m‖ ^ 2) := by
  simpa using (lp.memℓp v).summable (show (0 : ℝ) < (2 : ENNReal).toReal by norm_num)

theorem tsum_energy (v : H N) : (∑' m : Arr N, ‖v m‖ ^ 2) = ‖v‖ ^ 2 := by
  simpa using (lp.norm_rpow_eq_tsum (show (0 : ℝ) < (2 : ENNReal).toReal by norm_num) v).symm

/-- Donor edge energies are an injective restriction of the actual residual. -/
theorem residual_edge_energy (c : OrderedSeeds N) (t : ℤ → Phase) (a b : ℤ)
    (hab : a ≠ b) (g : H N) :
    Summable (fun m : Donor N a =>
      ‖(seedPhase c a b hab m).1 * g m.1 -
        ((t a).1 * conj (t b).1) * g (destination N a b m)‖ ^ 2) ∧
    (∑' m : Donor N a,
      ‖(seedPhase c a b hab m).1 * g m.1 -
        ((t a).1 * conj (t b).1) * g (destination N a b m)‖ ^ 2) ≤
      ‖residual c t a b hab g‖ ^ 2 := by
  simp_rw [← residual_destination]
  have hs := (summable_energy (residual c t a b hab g)).comp_injective (destination_injective N a b)
  refine ⟨hs, ?_⟩
  rw [← tsum_energy]
  exact hs.tsum_le_tsum_of_inj (destination N a b) (destination_injective N a b)
    (fun _ _ => sq_nonneg _) (fun _ => le_rfl) (summable_energy _)

/-- Actual complex edge residuals along the prescribed seed walk. -/
def walkErrors (c : OrderedSeeds N) (t : ℤ → Phase) (I : Finset ℤ) (K ell : ℕ)
    (g : H N) : ℕ → (m n : Arr N) → SameCell I K ell m n → List ℂ
  | 0, _, _, _ => []
  | fuel + 1, m, n, hc =>
      if he : m = n then []
      else residual c t (firstAbove I K ell m n hc he) (firstBelow I K ell m n hc he)
        (next_labels_ne I K ell m n hc he) g (next I K ell m n hc he) ::
        walkErrors c t I K ell g fuel (next I K ell m n hc he) n
          (next_sameCell I K ell m n hc he)

theorem walkErrors_length (c : OrderedSeeds N) (t : ℤ → Phase) (I : Finset ℤ)
    (K ell fuel : ℕ) (g : H N) (m n : Arr N) (hc : SameCell I K ell m n) :
    (walkErrors c t I K ell g fuel m n hc).length ≤ distance I n m := by
  induction fuel generalizing m with
  | zero => simp [walkErrors]
  | succ fuel ih =>
    rw [walkErrors]
    split_ifs with he
    · simp
    · have hd := distance_next I K ell m n hc he
      have hh := ih _ (next_sameCell I K ell m n hc he)
      simp only [List.length_cons]
      omega

/-- Telescoping uses completed seed coefficients and the factorized target,
with no energy estimate supplied as a premise. -/
theorem walk_defect_le (c : OrderedSeeds N) (t : ℤ → Phase) (I : Finset ℤ)
    (K ell fuel : ℕ) (g : H N) (m n : Arr N) (hc : SameCell I K ell m n)
    (hf : distance I n m ≤ fuel) :
    ‖(walkPhase c I K ell fuel m n hc).1 * g m - targetPhase I t m n * g n‖ ≤
      ((walkErrors c t I K ell g fuel m n hc).map (fun z => ‖z‖)).sum := by
  induction fuel generalizing m with
  | zero =>
    have he := (distance_zero_iff I K ell hc).mp (by omega)
    subst m
    simp [walkPhase, phaseOne, targetPhase_self, walkErrors]
  | succ fuel ih =>
    by_cases he : m = n
    · subst m
      simp [walkPhase, phaseOne, targetPhase_self, walkErrors]
    · let a := firstAbove I K ell m n hc he
      let b := firstBelow I K ell m n hc he
      let y := next I K ell m n hc he
      let hy := next_sameCell I K ell m n hc he
      let qy := walkPhase c I K ell fuel y n hy
      let zeta := (t a).1 * conj (t b).1
      have hz : ‖zeta‖ = 1 := by
        dsimp [zeta]
        rw [norm_mul, Complex.norm_conj, (t a).2, (t b).2, one_mul]
      have hd := distance_next I K ell m n hc he
      have hi := ih y hy (by change distance I n (next I K ell m n hc he) ≤ fuel; omega)
      have hdon : DonorOK a m.1 := by
        have h := (firstAbove_spec I K ell m n hc he).2
        change 0 < m.1 (firstAbove I K ell m n hc he)
        omega
      have hr := residual_destination c t a b (next_labels_ne I K ell m n hc he) g ⟨m, hdon⟩
      change residual c t a b (next_labels_ne I K ell m n hc he) g y =
        (stepPhase c I K ell m n hc he).1 * g m - zeta * g y at hr
      have ht := targetPhase_next I K ell t m n hc he
      change targetPhase I t m n = zeta * targetPhase I t y n at ht
      have hs : (walkPhase c I K ell (fuel + 1) m n hc).1 * g m -
          targetPhase I t m n * g n =
          qy.1 * residual c t a b (next_labels_ne I K ell m n hc he) g y +
          zeta * (qy.1 * g y - targetPhase I t y n * g n) := by
        rw [hr, ht]
        rw [walkPhase]
        split_ifs
        change ((stepPhase c I K ell m n hc he).1 * qy.1) * g m - _ = _
        ring
      rw [hs]
      calc
        _ ≤ ‖qy.1 * residual c t a b (next_labels_ne I K ell m n hc he) g y‖ +
            ‖zeta * (qy.1 * g y - targetPhase I t y n * g n)‖ := norm_add_le _ _
        _ = ‖residual c t a b (next_labels_ne I K ell m n hc he) g y‖ +
            ‖qy.1 * g y - targetPhase I t y n * g n‖ := by
              rw [norm_mul, norm_mul, qy.2, hz, one_mul, one_mul]
        _ ≤ ‖residual c t a b (next_labels_ne I K ell m n hc he) g y‖ +
            ((walkErrors c t I K ell g fuel y n hy).map (fun z => ‖z‖)).sum :=
              add_le_add le_rfl hi
        _ = _ := by simp only [walkErrors, dite_eq_right he, List.map_cons, List.sum_cons]; rfl

theorem list_norm_sum_sq (v : List ℂ) :
    ((v.map (fun z => ‖z‖)).sum) ^ 2 ≤
      (v.length : ℝ) * ((v.map (fun z => ‖z‖ ^ 2)).sum) := by
  simpa [List.map_map, Function.comp_def] using
    (Multiset.sq_sum_le_card_mul_sum_sq (v.map (fun z => ‖z‖) : Multiset ℝ))

/-- Exact pathwise square estimate against actual residual coefficients. -/
theorem walk_defect_sq_le (c : OrderedSeeds N) (t : ℤ → Phase) (I : Finset ℤ)
    (K ell fuel : ℕ) (hell : 0 < ell) (g : H N) (m n : Arr N)
    (hc : SameCell I K ell m n) (hf : distance I n m ≤ fuel) :
    ‖(walkPhase c I K ell fuel m n hc).1 * g m - targetPhase I t m n * g n‖ ^ 2 ≤
      ((I.card * ell : ℕ) : ℝ) *
        ((walkErrors c t I K ell g fuel m n hc).map (fun z => ‖z‖ ^ 2)).sum := by
  let v := walkErrors c t I K ell g fuel m n hc
  have h := walk_defect_le c t I K ell fuel g m n hc hf
  have hl : v.length ≤ I.card * ell :=
    (walkErrors_length c t I K ell fuel g m n hc).trans (distance_le I K ell hell hc)
  have hn : 0 ≤ (v.map (fun z => ‖z‖ ^ 2)).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hx
    exact sq_nonneg _
  calc
    _ ≤ ((v.map (fun z => ‖z‖)).sum) ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) h 2
    _ ≤ (v.length : ℝ) * (v.map (fun z => ‖z‖ ^ 2)).sum := list_norm_sum_sq v
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hl) hn

end QuantumNLS.FiniteCellTransport

-- BEGIN COMPLETE DECLARATION AUDIT
#print axioms QuantumNLS.FiniteCellTransport.targetPhase
#print axioms QuantumNLS.FiniteCellTransport.targetPhase_unit
#print axioms QuantumNLS.FiniteCellTransport.targetPhase_self
#print axioms QuantumNLS.FiniteCellTransport.targetPhase_trans
#print axioms QuantumNLS.FiniteCellTransport.targetPhase_active
#print axioms QuantumNLS.FiniteCellTransport.phase_inv
#print axioms QuantumNLS.FiniteCellTransport.targetPhase_shift
#print axioms QuantumNLS.FiniteCellTransport.targetPhase_step
#print axioms QuantumNLS.FiniteCellTransport.targetPhase_next
#print axioms QuantumNLS.FiniteCellTransport.residual
#print axioms QuantumNLS.FiniteCellTransport.residual_destination
#print axioms QuantumNLS.FiniteCellTransport.summable_energy
#print axioms QuantumNLS.FiniteCellTransport.tsum_energy
#print axioms QuantumNLS.FiniteCellTransport.residual_edge_energy
#print axioms QuantumNLS.FiniteCellTransport.walkErrors
#print axioms QuantumNLS.FiniteCellTransport.walkErrors_length
#print axioms QuantumNLS.FiniteCellTransport.walk_defect_le
#print axioms QuantumNLS.FiniteCellTransport.list_norm_sum_sq
#print axioms QuantumNLS.FiniteCellTransport.walk_defect_sq_le

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.FiniteCellTransport.targetPhase,
    ``QuantumNLS.FiniteCellTransport.targetPhase_unit,
    ``QuantumNLS.FiniteCellTransport.targetPhase_self,
    ``QuantumNLS.FiniteCellTransport.targetPhase_trans,
    ``QuantumNLS.FiniteCellTransport.targetPhase_active,
    ``QuantumNLS.FiniteCellTransport.phase_inv,
    ``QuantumNLS.FiniteCellTransport.targetPhase_shift,
    ``QuantumNLS.FiniteCellTransport.targetPhase_step,
    ``QuantumNLS.FiniteCellTransport.targetPhase_next,
    ``QuantumNLS.FiniteCellTransport.residual,
    ``QuantumNLS.FiniteCellTransport.residual_destination,
    ``QuantumNLS.FiniteCellTransport.summable_energy,
    ``QuantumNLS.FiniteCellTransport.tsum_energy,
    ``QuantumNLS.FiniteCellTransport.residual_edge_energy,
    ``QuantumNLS.FiniteCellTransport.walkErrors,
    ``QuantumNLS.FiniteCellTransport.walkErrors_length,
    ``QuantumNLS.FiniteCellTransport.walk_defect_le,
    ``QuantumNLS.FiniteCellTransport.list_norm_sum_sq,
    ``QuantumNLS.FiniteCellTransport.walk_defect_sq_le]
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if n.toString == "QuantumNLS.BetheConditionalBasis.AbstractContinuity" then
        throwError "Abstract finite-cell proof reached EXT-001: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"FiniteCellTransport aggregate audit PASS: {seen.size} transitive constants. All declarations independent of EXT-001."
