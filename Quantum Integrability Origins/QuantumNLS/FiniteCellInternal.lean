import QuantumNLS.FiniteCellEstimate

/-! R-D8BB052C internal-edge estimate, for the same preselected scalar gauge. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open scoped InnerProductSpace ComplexConjugate Classical
namespace QuantumNLS.FiniteCellInternal
open Occupation OccupationHilbert FullOccupationAffinity FiniteCellSupport
  FiniteCellPartition FiniteCellPaths FiniteCellGauge FiniteCellTransport FiniteCellEstimate
variable {N : ℕ}

/-- Actual W residual coefficients agree in norm with the gauged difference. -/
theorem W_residual_coefficient (Q : Arr N → Phase) (t : ℤ → Phase) (a b : ℤ)
    (g : H N) (m : Donor N a) :
    ‖(FiniteCellGauge.W Q a b g - ((t a).1 * conj (t b).1) • g)
      (destination N a b m)‖ =
      ‖(Q m.1).1 * g m.1 - ((t a).1 * conj (t b).1) *
        (Q (destination N a b m)).1 * g (destination N a b m)‖ := by
  let y := destination N a b m
  let zeta := (t a).1 * conj (t b).1
  have hr : (FiniteCellGauge.W Q a b g - zeta • g) y =
      (ratio Q m.1 y).1 * g m.1 - zeta * g y := by
    change transfer a b (edgePhase Q a b) g y - zeta * g y = _
    rw [transfer_at_destination a b (edgePhase Q a b) g m]
    rfl
  have hu : (Q y).1 * conj (Q y).1 = 1 := by rw [mul_comm, phase_conj_mul]
  have he : (Q y).1 * ((FiniteCellGauge.W Q a b g - zeta • g) y) =
      (Q m.1).1 * g m.1 - zeta * (Q y).1 * g y := by
    rw [hr]
    change (Q y).1 * ((Q m.1).1 * conj (Q y).1 * g m.1 - zeta * g y) = _
    calc
      _ = ((Q y).1 * conj (Q y).1) * ((Q m.1).1 * g m.1) - zeta * (Q y).1 * g y := by ring
      _ = _ := by rw [hu]; ring
  have hn := congrArg norm he
  rw [norm_mul, (Q y).2, one_mul] at hn
  exact hn

/-- Donors whose full source and destination lie in one good cell. -/
abbrev Internal (I G : Finset ℤ) (K ell : ℕ) (a b : ℤ) :=
  {m : Donor N a // SameCell I K ell m.1 (destination N a b m) ∧ active I K m.1 ⊆ G}

theorem internal_source_injective (I G : Finset ℤ) (K ell : ℕ) (a b : ℤ) :
    Function.Injective (fun m : Internal (N := N) I G K ell a b => m.1.1) := by
  intro m n he
  exact Subtype.ext (Subtype.ext he)

theorem internal_target_injective (I G : Finset ℤ) (K ell : ℕ) (a b : ℤ) :
    Function.Injective (fun m : Internal (N := N) I G K ell a b => destination N a b m.1) :=
  (destination_injective N a b).comp Subtype.val_injective

/-- Pointwise good-cell estimate with the exact same q and target phases. -/
theorem internal_coefficient_sq (c : OrderedSeeds N) (t : ℤ → Phase) (I G : Finset ℤ)
    (K ell : ℕ) (a b : ℤ) (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b)
    (g : H N) (m : Internal (N := N) I G K ell a b) :
    ‖(FiniteCellGauge.W (q c I K ell) a b g - ((t a).1 * conj (t b).1) • g)
      (destination N a b m.1)‖ ^ 2 ≤
      2 * pathDefect c t I G K ell g m.1.1 +
      2 * pathDefect c t I G K ell g (destination N a b m.1) := by
  let x := m.1.1
  let y := destination N a b m.1
  let zeta := (t a).1 * conj (t b).1
  let rx := (root I K ell x).1
  let ry := (root I K ell y).1
  let u := (q c I K ell x).1 * g x - targetPhase I t x rx * g rx
  let v := (q c I K ell y).1 * g y - targetPhase I t y ry * g ry
  have hz : ‖zeta‖ = 1 := by
    dsimp [zeta]
    rw [norm_mul, Complex.norm_conj, (t a).2, (t b).2, one_mul]
  have hr : rx = ry := root_eq_of_sameCell I K ell m.2.1
  have ht : targetPhase I t x rx = zeta * targetPhase I t y ry := by
    rw [← hr]
    exact targetPhase_step I t a b ha hb hab x rx m.1.2
  have he : (q c I K ell x).1 * g x - zeta * (q c I K ell y).1 * g y = u - zeta * v := by
    dsimp only [u, v]
    rw [ht, hr]
    ring
  have hgy : active I K y ⊆ G := by
    rw [← m.2.1.2.1]
    exact m.2.2
  have hDx : pathDefect c t I G K ell g x = ‖u‖ ^ 2 := by
    rw [pathDefect, ite_eq_left m.2.2]
  have hDy : pathDefect c t I G K ell g y = ‖v‖ ^ 2 := by
    rw [pathDefect, ite_eq_left hgy]
  rw [W_residual_coefficient, he, hDx, hDy]
  have hn : ‖u - zeta * v‖ ≤ ‖u‖ + ‖v‖ := by
    simpa only [norm_mul, hz, one_mul] using norm_sub_le u (zeta * v)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hn 2
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

/-- Nonnegative good-cell energies, with both source and target injective. -/
theorem internal_energy_bound (c : OrderedSeeds N) (t : ℤ → Phase) (I G : Finset ℤ)
    (K ell : ℕ) (hell : 0 < ell) (hI : 0 < I.card) (a b : ℤ)
    (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b) (g : H N) (eta : ℝ)
    (hres : (∑ p : Pairs G, ‖pairResidual c t G g p‖ ^ 2) ≤ eta ^ 2) :
    Summable (fun m : Internal (N := N) I G K ell a b =>
      ‖(FiniteCellGauge.W (q c I K ell) a b g - ((t a).1 * conj (t b).1) • g)
        (destination N a b m.1)‖ ^ 2) ∧
    (∑' m : Internal (N := N) I G K ell a b,
      ‖(FiniteCellGauge.W (q c I K ell) a b g - ((t a).1 * conj (t b).1) • g)
        (destination N a b m.1)‖ ^ 2) ≤
      4 * (I.card : ℝ) * (ell : ℝ) ^ I.card * eta ^ 2 := by
  let D := pathDefect c t I G K ell g
  have hD := pathDefect_summable_bound c t I G K ell hell hI g eta hres
  have hs : Summable (fun m : Internal (N := N) I G K ell a b => D m.1.1) :=
    hD.1.comp_injective (internal_source_injective (N := N) I G K ell a b)
  have ht : Summable (fun m : Internal (N := N) I G K ell a b => D (destination N a b m.1)) :=
    hD.1.comp_injective (internal_target_injective (N := N) I G K ell a b)
  let v := FiniteCellGauge.W (q c I K ell) a b g - ((t a).1 * conj (t b).1) • g
  have he := (summable_energy v).comp_injective (internal_target_injective (N := N) I G K ell a b)
  have hsource : (∑' m : Internal (N := N) I G K ell a b, D m.1.1) ≤ ∑' x, D x :=
    hs.tsum_le_tsum_of_inj _ (internal_source_injective (N := N) I G K ell a b)
      (fun x _ => pathDefect_nonneg _ _ _ _ _ _ _ x) (fun _ => le_rfl) hD.1
  have htarget : (∑' m : Internal (N := N) I G K ell a b, D (destination N a b m.1)) ≤ ∑' x, D x :=
    ht.tsum_le_tsum_of_inj _ (internal_target_injective (N := N) I G K ell a b)
      (fun x _ => pathDefect_nonneg _ _ _ _ _ _ _ x) (fun _ => le_rfl) hD.1
  refine ⟨he, ?_⟩
  calc
    _ ≤ ∑' m : Internal (N := N) I G K ell a b,
        (2 * D m.1.1 + 2 * D (destination N a b m.1)) :=
      he.tsum_le_tsum (internal_coefficient_sq c t I G K ell a b ha hb hab g)
        ((hs.mul_left 2).add (ht.mul_left 2))
    _ = 2 * (∑' m : Internal (N := N) I G K ell a b, D m.1.1) +
        2 * (∑' m : Internal (N := N) I G K ell a b, D (destination N a b m.1)) := by
      rw [Summable.tsum_add (hs.mul_left 2) (ht.mul_left 2), tsum_mul_left, tsum_mul_left]
    _ ≤ 4 * ∑' x, D x := by linarith
    _ ≤ _ := by linarith [hD.2]

/-- The real-power coefficient in the printed internal bound. -/
theorem internal_energy_norm_bound (c : OrderedSeeds N) (t : ℤ → Phase) (I G : Finset ℤ)
    (K ell : ℕ) (hell : 0 < ell) (hI : 0 < I.card) (a b : ℤ)
    (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b) (g : H N) (eta : ℝ) (heta : 0 ≤ eta)
    (hres : (∑ p : Pairs G, ‖pairResidual c t G g p‖ ^ 2) ≤ eta ^ 2) :
    Summable (fun m : Internal (N := N) I G K ell a b =>
      ‖(FiniteCellGauge.W (q c I K ell) a b g - ((t a).1 * conj (t b).1) • g)
        (destination N a b m.1)‖ ^ 2) ∧
    Real.sqrt (∑' m : Internal (N := N) I G K ell a b,
      ‖(FiniteCellGauge.W (q c I K ell) a b g - ((t a).1 * conj (t b).1) • g)
        (destination N a b m.1)‖ ^ 2) ≤
      2 * Real.sqrt (I.card : ℝ) * (ell : ℝ) ^ ((I.card : ℝ) / 2) * eta := by
  have h := internal_energy_bound c t I G K ell hell hI a b ha hb hab g eta hres
  refine ⟨h.1, ?_⟩
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hp : ((ell : ℝ) ^ ((I.card : ℝ) / 2)) ^ 2 = (ell : ℝ) ^ I.card := by
    have he : ((I.card : ℝ) / 2) * ((2 : ℕ) : ℝ) = (I.card : ℝ) := by norm_num
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg ell), he, Real.rpow_natCast]
  have hr : Real.sqrt (I.card : ℝ) ^ 2 = (I.card : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  calc
    _ ≤ 4 * (I.card : ℝ) * (ell : ℝ) ^ I.card * eta ^ 2 := h.2
    _ = _ := by rw [mul_pow, mul_pow, mul_pow, hr, hp]; ring

/-- Printed internal bound for q_N and the actual nested operator-residual hypothesis. -/
theorem finite_cell_internal (I G : Finset ℤ) (ell : ℕ) (hI : 2 ≤ I.card) (hell : 2 ≤ ell)
    (c : SelectedSeeds I N) (t : ℤ → Phase) (g : H N) (eta : ℝ) (heta : 0 ≤ eta)
    (hres : (∑ a : ↥G, ∑ b : ↥(G.erase a.1),
      ‖seedTransfer (extendSeeds I c) a.1 b.1 (Finset.mem_erase.mp b.2).1.symm g -
        ((t a.1).1 * conj (t b.1).1) • g‖ ^ 2) ≤ eta ^ 2)
    (a b : ℤ) (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b) :
    Summable (fun m : Internal (N := N) I G (threshold N ell) ell a b =>
      ‖(FiniteCellGauge.W (q_N I ell c) a b g - ((t a).1 * conj (t b).1) • g)
        (destination N a b m.1)‖ ^ 2) ∧
    Real.sqrt (∑' m : Internal (N := N) I G (threshold N ell) ell a b,
      ‖(FiniteCellGauge.W (q_N I ell c) a b g - ((t a).1 * conj (t b).1) • g)
        (destination N a b m.1)‖ ^ 2) ≤
      2 * Real.sqrt (I.card : ℝ) * (ell : ℝ) ^ ((I.card : ℝ) / 2) * eta := by
  have hactual : (∑ p : Pairs G, ‖pairResidual (extendSeeds I c) t G g p‖ ^ 2) ≤ eta ^ 2 := by
    simp only [pairResidual]
    rw [sum_pairs G (fun a b hab => ‖residual (extendSeeds I c) t a b hab g‖ ^ 2)]
    exact hres
  exact internal_energy_norm_bound (extendSeeds I c) t I G (threshold N ell) ell
    (by omega) (by omega) a b ha hb hab g eta heta hactual

end QuantumNLS.FiniteCellInternal

-- BEGIN COMPLETE DECLARATION AUDIT
#print axioms QuantumNLS.FiniteCellInternal.W_residual_coefficient
#print axioms QuantumNLS.FiniteCellInternal.Internal
#print axioms QuantumNLS.FiniteCellInternal.internal_source_injective
#print axioms QuantumNLS.FiniteCellInternal.internal_target_injective
#print axioms QuantumNLS.FiniteCellInternal.internal_coefficient_sq
#print axioms QuantumNLS.FiniteCellInternal.internal_energy_bound
#print axioms QuantumNLS.FiniteCellInternal.internal_energy_norm_bound
#print axioms QuantumNLS.FiniteCellInternal.finite_cell_internal

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.FiniteCellInternal.W_residual_coefficient,
    ``QuantumNLS.FiniteCellInternal.Internal,
    ``QuantumNLS.FiniteCellInternal.internal_source_injective,
    ``QuantumNLS.FiniteCellInternal.internal_target_injective,
    ``QuantumNLS.FiniteCellInternal.internal_coefficient_sq,
    ``QuantumNLS.FiniteCellInternal.internal_energy_bound,
    ``QuantumNLS.FiniteCellInternal.internal_energy_norm_bound,
    ``QuantumNLS.FiniteCellInternal.finite_cell_internal]
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
  Lean.logInfo m!"FiniteCellInternal aggregate audit PASS: {seen.size} transitive constants. All declarations independent of EXT-001."
