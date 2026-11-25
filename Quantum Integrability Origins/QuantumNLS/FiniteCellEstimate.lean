import QuantumNLS.FiniteCellTransport
import QuantumNLS.FiniteCellSummation

/-! R-D8BB052C E2: good-cell path defects from actual operator residuals. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open scoped InnerProductSpace ComplexConjugate Classical
namespace QuantumNLS.FiniteCellEstimate
open Occupation OccupationHilbert FullOccupationAffinity FiniteCellSupport
  FiniteCellPartition FiniteCellPaths FiniteCellGauge FiniteCellTransport FiniteCellSummation
variable {N : ℕ}

/-- The actual directed-pair residual energy, extended by zero off its donor set. -/
def sourceEnergy (c : OrderedSeeds N) (t : ℤ → Phase) (a b : ℤ) (hab : a ≠ b)
    (g : H N) (m : Arr N) : ℝ :=
  if hd : DonorOK a m.1 then ‖residual c t a b hab g (destination N a b ⟨m, hd⟩)‖ ^ 2 else 0

theorem sourceEnergy_nonneg (c : OrderedSeeds N) (t : ℤ → Phase) (a b : ℤ)
    (hab : a ≠ b) (g : H N) (m : Arr N) : 0 ≤ sourceEnergy c t a b hab g m := by
  unfold sourceEnergy
  split_ifs <;> positivity

theorem sourceEnergy_summable (c : OrderedSeeds N) (t : ℤ → Phase) (a b : ℤ)
    (hab : a ≠ b) (g : H N) :
    Summable (sourceEnergy c t a b hab g) ∧
      (∑' m, sourceEnergy c t a b hab g m) ≤ ‖residual c t a b hab g‖ ^ 2 := by
  let E := sourceEnergy c t a b hab g
  have heval (m : Donor N a) : E m.1 =
      ‖residual c t a b hab g (destination N a b m)‖ ^ 2 := by
    simp only [E, sourceEnergy, dite_eq_left m.2]
  have hd : Summable (fun m : Donor N a => E m.1) := by
    exact ((summable_energy (residual c t a b hab g)).comp_injective
      (destination_injective N a b)).congr (fun m => (heval m).symm)
  have hi : Set.indicator {m : Arr N | DonorOK a m.1} E = E := by
    funext m
    by_cases hm : DonorOK a m.1
    · simp [Set.indicator, hm]
    · simp [Set.indicator, hm, E, sourceEnergy]
  have hs : Summable E := by
    have h := (summable_subtype_iff_indicator (s := {m : Arr N | DonorOK a m.1}) (f := E)).mp hd
    rwa [hi] at h
  refine ⟨hs, ?_⟩
  have he := tsum_subtype {m : Arr N | DonorOK a m.1} E
  rw [hi] at he
  rw [← he]
  have h := (residual_edge_energy c t a b hab g).2
  simp_rw [← residual_destination] at h
  change (∑' m : Donor N a, E m.1) ≤ ‖residual c t a b hab g‖ ^ 2
  calc
    _ = ∑' m : Donor N a, ‖residual c t a b hab g (destination N a b m)‖ ^ 2 :=
      tsum_congr heval
    _ ≤ _ := h

/-- All tested ordered distinct pairs, with proofs intrinsic to the finite set. -/
abbrev Pairs (G : Finset ℤ) := ↥G.offDiag

def pairResidual (c : OrderedSeeds N) (t : ℤ → Phase) (G : Finset ℤ)
    (g : H N) (p : Pairs G) : H N :=
  residual c t p.1.1 p.1.2 (Finset.mem_offDiag.mp p.2).2.2 g

def totalEnergy (c : OrderedSeeds N) (t : ℤ → Phase) (G : Finset ℤ)
    (g : H N) (m : Arr N) : ℝ :=
  ∑ p : Pairs G,
    sourceEnergy c t p.1.1 p.1.2 (Finset.mem_offDiag.mp p.2).2.2 g m

theorem totalEnergy_nonneg (c : OrderedSeeds N) (t : ℤ → Phase) (G : Finset ℤ)
    (g : H N) (m : Arr N) : 0 ≤ totalEnergy c t G g m :=
  Finset.sum_nonneg (fun _ _ => sourceEnergy_nonneg _ _ _ _ _ _ _)

theorem totalEnergy_summable (c : OrderedSeeds N) (t : ℤ → Phase) (G : Finset ℤ)
    (g : H N) : Summable (totalEnergy c t G g) ∧
      (∑' m, totalEnergy c t G g m) ≤ ∑ p : Pairs G, ‖pairResidual c t G g p‖ ^ 2 := by
  have hs : ∀ p : Pairs G, Summable
      (sourceEnergy c t p.1.1 p.1.2 (Finset.mem_offDiag.mp p.2).2.2 g) :=
    fun p => (sourceEnergy_summable _ _ _ _ _ _).1
  refine ⟨summable_sum (fun p _ => hs p), ?_⟩
  change (∑' m, ∑ p : Pairs G,
    sourceEnergy c t p.1.1 p.1.2 (Finset.mem_offDiag.mp p.2).2.2 g m) ≤ _
  rw [Summable.tsum_finsetSum (fun p _ => hs p)]
  exact Finset.sum_le_sum (fun p _ => (sourceEnergy_summable c t _ _ _ g).2)

theorem sourceEnergy_le_total (c : OrderedSeeds N) (t : ℤ → Phase) (G : Finset ℤ)
    (g : H N) (a b : ℤ) (ha : a ∈ G) (hb : b ∈ G) (hab : a ≠ b) (m : Arr N) :
    sourceEnergy c t a b hab g m ≤ totalEnergy c t G g m := by
  let p : Pairs G := ⟨(a,b), Finset.mem_offDiag.mpr ⟨ha,hb,hab⟩⟩
  have h := Finset.single_le_sum
    (f := fun p : Pairs G => sourceEnergy c t p.1.1 p.1.2 (Finset.mem_offDiag.mp p.2).2.2 g m)
    (fun p _ => sourceEnergy_nonneg c t p.1.1 p.1.2 _ g m) (Finset.mem_univ p)
  exact h

/-- Every path edge uses two active labels, hence two actual tested residuals. -/
theorem walkErrors_energy_le (c : OrderedSeeds N) (t : ℤ → Phase) (I G : Finset ℤ)
    (K ell fuel : ℕ) (g : H N) (m n : Arr N) (hc : SameCell I K ell m n)
    (hgood : active I K m ⊆ G) :
    ((walkErrors c t I K ell g fuel m n hc).map (fun z => ‖z‖ ^ 2)).sum ≤
      ∑ x ∈ (walk I K ell fuel m n hc).toFinset, totalEnergy c t G g x := by
  induction fuel generalizing m with
  | zero => simp [walkErrors, walk, totalEnergy_nonneg]
  | succ fuel ih =>
    by_cases he : m = n
    · simp [walkErrors, walk, he, totalEnergy_nonneg]
    · let a := firstAbove I K ell m n hc he
      let b := firstBelow I K ell m n hc he
      let y := next I K ell m n hc he
      let hy := next_sameCell I K ell m n hc he
      have ha := firstAbove_spec I K ell m n hc he
      have hb := firstBelow_spec I K ell m n hc he
      have haS : a ∈ active I K m := by
        by_contra hn
        have hh := hc.2.2.1 a ha.1 hn
        have hh' : n.1 a < m.1 a := ha.2
        omega
      have hbS : b ∈ active I K m := by
        by_contra hn
        have hh := hc.2.2.1 b hb.1 hn
        have hh' : m.1 b < n.1 b := hb.2
        omega
      have hdon : DonorOK a m.1 := by
        have hh : n.1 a < m.1 a := ha.2
        change 0 < m.1 a
        omega
      have hr := sourceEnergy_le_total c t G g a b (hgood haS) (hgood hbS)
        (next_labels_ne I K ell m n hc he) m
      rw [sourceEnergy, dite_eq_left hdon] at hr
      change ‖residual c t a b (next_labels_ne I K ell m n hc he) g y‖ ^ 2 ≤
        totalEnergy c t G g m at hr
      have hgy : active I K y ⊆ G := by
        rw [hy.2.1, ← hc.2.1]
        exact hgood
      have hi := ih y hy hgy
      have hn := FiniteCellIncidence.walk_nodup I K ell (fuel + 1) m n hc
      rw [walk, dite_eq_right he] at hn
      have hnot : m ∉ (walk I K ell fuel y n hy).toFinset := by
        simpa only [List.mem_toFinset] using (List.nodup_cons.mp hn).1
      rw [walkErrors, dite_eq_right he, List.map_cons, List.sum_cons,
        walk, dite_eq_right he, List.toFinset_cons, Finset.sum_insert hnot]
      exact add_le_add hr hi

/-- Exactly the good-cell squared defects; no normalization or tolerance premise. -/
def pathDefect (c : OrderedSeeds N) (t : ℤ → Phase) (I G : Finset ℤ)
    (K ell : ℕ) (g : H N) (m : Arr N) : ℝ :=
  if active I K m ⊆ G then
    ‖(q c I K ell m).1 * g m -
      targetPhase I t m (root I K ell m).1 * g (root I K ell m).1‖ ^ 2 else 0

theorem pathDefect_nonneg (c : OrderedSeeds N) (t : ℤ → Phase) (I G : Finset ℤ)
    (K ell : ℕ) (g : H N) (m : Arr N) : 0 ≤ pathDefect c t I G K ell g m := by
  unfold pathDefect
  split_ifs <;> positivity

theorem pathDefect_le (c : OrderedSeeds N) (t : ℤ → Phase) (I G : Finset ℤ)
    (K ell : ℕ) (hell : 0 < ell) (g : H N) (m : Arr N) :
    pathDefect c t I G K ell g m ≤ ((I.card * ell : ℕ) : ℝ) *
      ∑ x ∈ (path I K ell m).toFinset, totalEnergy c t G g x := by
  unfold pathDefect
  split_ifs with hg
  · exact (walk_defect_sq_le c t I K ell _ hell g m (root I K ell m).1
      (root I K ell m).2 le_rfl).trans
        (mul_le_mul_of_nonneg_left (walkErrors_energy_le c t I G K ell _ g m _
          (root I K ell m).2 hg) (Nat.cast_nonneg _))
  · exact mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun x _ => totalEnergy_nonneg _ _ _ _ _))

/-- E2 as a conjunction: countable summability and its exact total bound.
Only the actual operator residual sum is assumed; normalization is unnecessary. -/
theorem pathDefect_summable_bound (c : OrderedSeeds N) (t : ℤ → Phase) (I G : Finset ℤ)
    (K ell : ℕ) (hell : 0 < ell) (hI : 0 < I.card) (g : H N) (eta : ℝ)
    (hres : (∑ p : Pairs G, ‖pairResidual c t G g p‖ ^ 2) ≤ eta ^ 2) :
    Summable (pathDefect c t I G K ell g) ∧
      (∑' m, pathDefect c t I G K ell g m) ≤
        (I.card : ℝ) * (ell : ℝ) ^ I.card * eta ^ 2 := by
  let E := totalEnergy c t G g
  let P := fun m => ∑ x ∈ (path I K ell m).toFinset, E x
  have hE := totalEnergy_summable c t G g
  have hP := path_energy_summable I K ell hell E (totalEnergy_nonneg c t G g) hE.1
  have hdom := fun m => pathDefect_le c t I G K ell hell g m
  have hs : Summable (pathDefect c t I G K ell g) :=
    Summable.of_nonneg_of_le (pathDefect_nonneg c t I G K ell g) hdom
      (hP.1.mul_left ((I.card * ell : ℕ) : ℝ))
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' m, ((I.card * ell : ℕ) : ℝ) * P m :=
      hs.tsum_le_tsum hdom (hP.1.mul_left _)
    _ = ((I.card * ell : ℕ) : ℝ) * ∑' m, P m := tsum_mul_left
    _ ≤ ((I.card * ell : ℕ) : ℝ) * ((ell ^ (I.card - 1) : ℕ) * ∑' x, E x) :=
      mul_le_mul_of_nonneg_left hP.2 (Nat.cast_nonneg _)
    _ ≤ ((I.card * ell : ℕ) : ℝ) * ((ell ^ (I.card - 1) : ℕ) * eta ^ 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hE.2.trans hres) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    _ = _ := by
      have he : I.card - 1 + 1 = I.card := by omega
      have hp : (ell : ℝ) * (ell : ℝ) ^ (I.card - 1) = (ell : ℝ) ^ I.card := by
        rw [← pow_succ', he]
      push_cast
      calc
        _ = (I.card : ℝ) * ((ell : ℝ) * (ell : ℝ) ^ (I.card - 1)) * eta ^ 2 := by ring
        _ = _ := by rw [hp]

/-- Directed distinct pairs are exactly the printed nested erase-indexed sum. -/
def pairEquiv (G : Finset ℤ) : Pairs G ≃ Σ a : ↥G, ↥(G.erase a.1) where
  toFun p := ⟨⟨p.1.1, (Finset.mem_offDiag.mp p.2).1⟩,
    ⟨p.1.2, Finset.mem_erase.mpr ⟨(Finset.mem_offDiag.mp p.2).2.2.symm,
      (Finset.mem_offDiag.mp p.2).2.1⟩⟩⟩
  invFun p := ⟨(p.1.1, p.2.1), Finset.mem_offDiag.mpr
    ⟨p.1.2, (Finset.mem_erase.mp p.2.2).2, (Finset.mem_erase.mp p.2.2).1.symm⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem sum_pairs (G : Finset ℤ) (F : (a b : ℤ) → a ≠ b → ℝ) :
    (∑ p : Pairs G, F p.1.1 p.1.2 (Finset.mem_offDiag.mp p.2).2.2) =
      ∑ a : ↥G, ∑ b : ↥(G.erase a.1), F a.1 b.1 (Finset.mem_erase.mp b.2).1.symm := by
  calc
    _ = ∑ p : (Σ a : ↥G, ↥(G.erase a.1)),
        F p.1.1 p.2.1 (Finset.mem_erase.mp p.2.2).1.symm :=
      Fintype.sum_equiv (pairEquiv G) _ _ (fun _ => rfl)
    _ = _ := Fintype.sum_sigma _

/-- E2 in the source notation, from only the actual completed operator residuals.
The conjunction explicitly includes summability. Nonnegative eta is recorded
as the source tolerance convention, though this squared estimate is stronger. -/
theorem finite_cell_E2 (I G : Finset ℤ) (ell : ℕ) (hI : 2 ≤ I.card) (hell : 2 ≤ ell)
    (c : SelectedSeeds I N) (t : ℤ → Phase) (g : H N) (eta : ℝ) (heta : 0 ≤ eta)
    (hres : (∑ a : ↥G, ∑ b : ↥(G.erase a.1),
      ‖seedTransfer (extendSeeds I c) a.1 b.1 (Finset.mem_erase.mp b.2).1.symm g -
        ((t a.1).1 * conj (t b.1).1) • g‖ ^ 2) ≤ eta ^ 2) :
    Summable (fun m : Arr N =>
      if active I (threshold N ell) m ⊆ G then
        ‖(q_N I ell c m).1 * g m -
          targetPhase I t m (root I (threshold N ell) ell m).1 *
            g (root I (threshold N ell) ell m).1‖ ^ 2 else 0) ∧
    (∑' m : Arr N,
      if active I (threshold N ell) m ⊆ G then
        ‖(q_N I ell c m).1 * g m -
          targetPhase I t m (root I (threshold N ell) ell m).1 *
            g (root I (threshold N ell) ell m).1‖ ^ 2 else 0) ≤
        (I.card : ℝ) * (ell : ℝ) ^ I.card * eta ^ 2 := by
  have hactual : (∑ p : Pairs G, ‖pairResidual (extendSeeds I c) t G g p‖ ^ 2) ≤ eta ^ 2 := by
    simp only [pairResidual]
    rw [sum_pairs G (fun a b hab => ‖residual (extendSeeds I c) t a b hab g‖ ^ 2)]
    exact hres
  have hbound := pathDefect_summable_bound (extendSeeds I c) t I G (threshold N ell) ell
    (by omega) (by omega) g |eta| (by simpa only [abs_of_nonneg heta] using hactual)
  rw [abs_of_nonneg heta] at hbound
  exact hbound

end QuantumNLS.FiniteCellEstimate

-- BEGIN COMPLETE DECLARATION AUDIT
#print axioms QuantumNLS.FiniteCellEstimate.sourceEnergy
#print axioms QuantumNLS.FiniteCellEstimate.sourceEnergy_nonneg
#print axioms QuantumNLS.FiniteCellEstimate.sourceEnergy_summable
#print axioms QuantumNLS.FiniteCellEstimate.Pairs
#print axioms QuantumNLS.FiniteCellEstimate.pairResidual
#print axioms QuantumNLS.FiniteCellEstimate.totalEnergy
#print axioms QuantumNLS.FiniteCellEstimate.totalEnergy_nonneg
#print axioms QuantumNLS.FiniteCellEstimate.totalEnergy_summable
#print axioms QuantumNLS.FiniteCellEstimate.sourceEnergy_le_total
#print axioms QuantumNLS.FiniteCellEstimate.walkErrors_energy_le
#print axioms QuantumNLS.FiniteCellEstimate.pathDefect
#print axioms QuantumNLS.FiniteCellEstimate.pathDefect_nonneg
#print axioms QuantumNLS.FiniteCellEstimate.pathDefect_le
#print axioms QuantumNLS.FiniteCellEstimate.pathDefect_summable_bound
#print axioms QuantumNLS.FiniteCellEstimate.pairEquiv
#print axioms QuantumNLS.FiniteCellEstimate.sum_pairs
#print axioms QuantumNLS.FiniteCellEstimate.finite_cell_E2

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.FiniteCellEstimate.sourceEnergy,
    ``QuantumNLS.FiniteCellEstimate.sourceEnergy_nonneg,
    ``QuantumNLS.FiniteCellEstimate.sourceEnergy_summable,
    ``QuantumNLS.FiniteCellEstimate.Pairs,
    ``QuantumNLS.FiniteCellEstimate.pairResidual,
    ``QuantumNLS.FiniteCellEstimate.totalEnergy,
    ``QuantumNLS.FiniteCellEstimate.totalEnergy_nonneg,
    ``QuantumNLS.FiniteCellEstimate.totalEnergy_summable,
    ``QuantumNLS.FiniteCellEstimate.sourceEnergy_le_total,
    ``QuantumNLS.FiniteCellEstimate.walkErrors_energy_le,
    ``QuantumNLS.FiniteCellEstimate.pathDefect,
    ``QuantumNLS.FiniteCellEstimate.pathDefect_nonneg,
    ``QuantumNLS.FiniteCellEstimate.pathDefect_le,
    ``QuantumNLS.FiniteCellEstimate.pathDefect_summable_bound,
    ``QuantumNLS.FiniteCellEstimate.pairEquiv,
    ``QuantumNLS.FiniteCellEstimate.sum_pairs,
    ``QuantumNLS.FiniteCellEstimate.finite_cell_E2]
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
  Lean.logInfo m!"FiniteCellEstimate aggregate audit PASS: {seen.size} transitive constants. All declarations independent of EXT-001."
