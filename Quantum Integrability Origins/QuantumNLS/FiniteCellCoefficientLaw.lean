import QuantumNLS.FiniteCellEstimate

/-! R-D8BB052C F: actual coefficient probability laws and full fiber sums. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open scoped Classical
namespace QuantumNLS.FiniteCellCoefficientLaw
open Occupation OccupationHilbert FiniteCellTransport FullOccupationAffinity FiniteCellSupport
variable {N : ℕ}

/-- The actual law of full coefficients, before choosing a selected-coordinate map. -/
def law (g : H N) (m : Arr N) : ℝ := ‖g m‖ ^ 2

theorem law_nonneg (g : H N) (m : Arr N) : 0 ≤ law g m := sq_nonneg _

theorem law_summable (g : H N) : Summable (law g) := summable_energy g

theorem law_total (g : H N) : (∑' m, law g m) = ‖g‖ ^ 2 := tsum_energy g

/-- Every exterior is retained in the fiber sum of an arbitrary actual map. -/
def pushLaw {X : Type*} (f : Arr N → X) (g : H N) (x : X) : ℝ :=
  ∑' m : f ⁻¹' {x}, law g m.1

theorem pushLaw_hasSum {X : Type*} (f : Arr N → X) (g : H N) :
    HasSum (pushLaw f g) (‖g‖ ^ 2) := by
  have h := (law_summable g).hasSum
  rw [law_total] at h
  exact h.tsum_fiberwise f

theorem pushLaw_nonneg {X : Type*} (f : Arr N → X) (g : H N) (x : X) :
    0 ≤ pushLaw f g x := tsum_nonneg (fun m => law_nonneg g m.1)

theorem pushLaw_normalized {X : Type*} (f : Arr N → X) (g : H N) (hg : ‖g‖ = 1) :
    Summable (pushLaw f g) ∧ (∑' x, pushLaw f g x) = 1 := by
  have h := pushLaw_hasSum f g
  refine ⟨h.summable, ?_⟩
  simpa only [hg, one_pow] using h.tsum_eq

/-- Selected counts are integer arrays, so their law has the printed zero extension. -/
def selected (I : Finset ℤ) (m : Arr N) : ↥I → ℤ := fun a => (m.1 a.1 : ℤ)

/-- Full exterior data, encoded without a finite exterior list. -/
def exterior (I : Finset ℤ) (m : Arr N) : ℤ → ℕ :=
  fun a => if a ∈ I then 0 else m.1 a

theorem selected_exterior_injective (I : Finset ℤ) :
    Function.Injective (fun m : Arr N => (selected (N := N) I m, exterior I m)) := by
  intro m n h
  apply Subtype.ext
  ext a
  by_cases ha : a ∈ I
  · have hs := congrFun (congrArg Prod.fst h) ⟨a,ha⟩
    change (m.1 a : ℤ) = (n.1 a : ℤ) at hs
    exact_mod_cast hs
  · have he := congrFun (congrArg Prod.snd h) a
    simpa only [exterior, ite_eq_right ha] using he

/-- The selected probability law is derived from the normalized actual vector. -/
theorem selectedLaw_normalized (I : Finset ℤ) (g : H N) (hg : ‖g‖ = 1) :
    (∀ x, 0 ≤ pushLaw (selected (N := N) I) g x) ∧
    Summable (pushLaw (selected (N := N) I) g) ∧ (∑' x, pushLaw (selected (N := N) I) g x) = 1 :=
  ⟨pushLaw_nonneg _ _, pushLaw_normalized _ _ hg⟩

/-- The actual full fiber restriction of an arbitrary square-summable vector. -/
def fiberVector {A X : Type*} (f : A → X) (v : L2 A) (x : X) : L2 (f ⁻¹' {x}) :=
  restrictL2 Subtype.val Subtype.val_injective v

def fiberMass {A X : Type*} (f : A → X) (v : L2 A) (x : X) : ℝ :=
  ∑' i : f ⁻¹' {x}, ‖v i.1‖ ^ 2

theorem fiberMass_hasSum {A X : Type*} (f : A → X) (v : L2 A) :
    HasSum (fiberMass f v) (‖v‖ ^ 2) := by
  have h : HasSum (fun i : A => ‖v i‖ ^ 2) (‖v‖ ^ 2) := by
    simpa using lp.hasSum_norm (show (0 : ℝ) < (2 : ENNReal).toReal by norm_num) v
  exact h.tsum_fiberwise f

theorem fiberMass_eq_norm {A X : Type*} (f : A → X) (v : L2 A) (x : X) :
    fiberMass f v x = ‖fiberVector f v x‖ ^ 2 := by
  have h := (lp.hasSum_norm (show (0 : ℝ) < (2 : ENNReal).toReal by norm_num)
    (fiberVector f v x)).tsum_eq
  simpa [fiberMass, fiberVector, restrictL2_apply] using h

def groupedTerm {A X : Type*} (f : A → X) (u v : L2 A) (x : X) : ℝ :=
  ‖fiberVector f u x‖ * ‖fiberVector f v x‖

theorem groupedTerm_summable {A X : Type*} (f : A → X) (u v : L2 A) :
    Summable (groupedTerm f u v) := by
  have hle : ∀ x, groupedTerm f u v x ≤ fiberMass f u x + fiberMass f v x := by
    intro x
    rw [fiberMass_eq_norm, fiberMass_eq_norm]
    unfold groupedTerm
    nlinarith [sq_nonneg (‖fiberVector f u x‖ - ‖fiberVector f v x‖)]
  exact Summable.of_nonneg_of_le (fun x => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    hle ((fiberMass_hasSum f u).summable.add (fiberMass_hasSum f v).summable)

theorem fiber_Cauchy {A X : Type*} (f : A → X) (u v : L2 A) (x : X) :
    (∑' i : f ⁻¹' {x}, ‖u i.1‖ * ‖v i.1‖) ≤ groupedTerm f u v x := by
  have hp : (2 : ENNReal).toReal.HolderConjugate (2 : ENNReal).toReal := by
    rw [Real.holderConjugate_iff]
    norm_num
  have h := lp.tsum_mul_le_mul_norm' hp (fiberVector f u x) (fiberVector f v x)
  simpa only [groupedTerm, fiberVector, restrictL2_apply] using h

/-- Cauchy--Schwarz is applied to FOA1's FULL donor affinity, retaining all
actual fibers. Identification with translated selected probabilities is separate. -/
theorem full_affinity_grouped {X : Type*} (a b : ℤ) (g : H N) (f : Donor N a → X) :
    Summable (groupedTerm f (sourceCoefficients a g) (targetCoefficients a b g)) ∧
    FullOccupationAffinity.affinity a b g ≤
      ∑' x, groupedTerm f (sourceCoefficients a g) (targetCoefficients a b g) x := by
  have h := (summable_affinityTerm a b g).hasSum.tsum_fiberwise f
  refine ⟨groupedTerm_summable _ _ _, ?_⟩
  change (∑' m : Donor N a, affinityTerm a b g m) ≤ _
  rw [← h.tsum_eq]
  apply h.summable.tsum_le_tsum _ (groupedTerm_summable _ _ _)
  intro x
  have hc := fiber_Cauchy f (sourceCoefficients a g) (targetCoefficients a b g) x
  simpa only [affinityTerm, sourceCoefficients, targetCoefficients, restrictL2_apply] using hc

/-- Actual selected translation by -e_a+e_b, on all integer count arrays. -/
def selectedStep (I : Finset ℤ) (a b : ℤ) (k : ↥I → ℤ) : ↥I → ℤ :=
  fun c => k c - (if c.1 = a then 1 else 0) + (if c.1 = b then 1 else 0)

def selectedStepEquiv (I : Finset ℤ) (a b : ℤ) : (↥I → ℤ) ≃ (↥I → ℤ) where
  toFun := selectedStep I a b
  invFun := selectedStep I b a
  left_inv k := by ext c; simp only [selectedStep]; ring
  right_inv k := by ext c; simp only [selectedStep]; ring

theorem selected_destination (I : Finset ℤ) (a b : ℤ) (hab : a ≠ b) (m : Donor N a) :
    selected (N := N) I (destination N a b m) = selectedStep I a b (selected (N := N) I m.1) := by
  ext c
  change (shift a b m.1.1 c.1 : ℤ) = (m.1.1 c.1 : ℤ) -
    (if c.1 = a then 1 else 0) + (if c.1 = b then 1 else 0)
  by_cases hca : c.1 = a
  · have hd : 0 < m.1.1 a := m.2
    simp only [hca]
    rw [shift_apply_donor m.1.1 hab]
    simp [hab, Nat.cast_sub (by omega : 1 ≤ m.1.1 a)]
  · by_cases hcb : c.1 = b
    · simp only [hcb]
      rw [shift_apply_receiver m.1.1 hab]
      simp [hab.symm]
    · rw [shift_apply_exterior m.1.1 hca hcb]
      simp only [ite_eq_right hca, ite_eq_right hcb, sub_zero, add_zero]

def selectedDonor (I : Finset ℤ) (a : ℤ) (m : Donor N a) : ↥I → ℤ := selected (N := N) I m.1

theorem source_fiberMass_le (I : Finset ℤ) (a : ℤ) (g : H N) (k : ↥I → ℤ) :
    fiberMass (selectedDonor (N := N) I a) (sourceCoefficients a g) k ≤ pushLaw (selected (N := N) I) g k := by
  let j : (selectedDonor (N := N) I a) ⁻¹' {k} → (selected (N := N) I) ⁻¹' {k} := fun d => ⟨d.1.1, d.2⟩
  have hj : Function.Injective j := by
    intro d e h
    exact Subtype.ext (Subtype.ext (congrArg (fun m : (selected (N := N) I) ⁻¹' {k} => m.1) h))
  have ht : Summable (fun m : (selected (N := N) I) ⁻¹' {k} => law g m.1) :=
    (law_summable g).comp_injective Subtype.val_injective
  have hs := ht.comp_injective hj
  have h := hs.tsum_le_tsum_of_inj j hj (fun m _ => law_nonneg g m.1) (fun _ => le_rfl) ht
  simpa only [Function.comp_def, j, law, fiberMass, sourceCoefficients, restrictL2_apply, pushLaw] using h

theorem target_fiberMass_le (I : Finset ℤ) (a b : ℤ) (hab : a ≠ b)
    (g : H N) (k : ↥I → ℤ) :
    fiberMass (selectedDonor (N := N) I a) (targetCoefficients a b g) k ≤
      pushLaw (selected (N := N) I) g (selectedStep I a b k) := by
  let j : (selectedDonor (N := N) I a) ⁻¹' {k} → (selected (N := N) I) ⁻¹' {selectedStep I a b k} := fun d =>
    ⟨destination N a b d.1, by
      change selected (N := N) I (destination N a b d.1) = selectedStep I a b k
      rw [selected_destination I a b hab d.1]
      have hd : selected (N := N) I d.1.1 = k := d.2
      rw [hd]⟩
  have hj : Function.Injective j := by
    intro d e h
    apply Subtype.ext
    apply destination_injective N a b
    exact congrArg (fun m : (selected (N := N) I) ⁻¹' {selectedStep I a b k} => m.1) h
  have ht : Summable (fun m : (selected (N := N) I) ⁻¹' {selectedStep I a b k} => law g m.1) :=
    (law_summable g).comp_injective Subtype.val_injective
  have hs := ht.comp_injective hj
  have h := hs.tsum_le_tsum_of_inj j hj (fun m _ => law_nonneg g m.1) (fun _ => le_rfl) ht
  simpa only [Function.comp_def, j, law, fiberMass, targetCoefficients, restrictL2_apply, pushLaw] using h

def selectedAffinityTerm (I : Finset ℤ) (a b : ℤ) (g : H N) (k : ↥I → ℤ) : ℝ :=
  Real.sqrt (pushLaw (selected (N := N) I) g k) * Real.sqrt (pushLaw (selected (N := N) I) g (selectedStep I a b k))

theorem selectedAffinityTerm_summable (I : Finset ℤ) (a b : ℤ) (g : H N) :
    Summable (selectedAffinityTerm I a b g) := by
  have hs := (pushLaw_hasSum (selected (N := N) I) g).summable
  have ht := hs.comp_injective (selectedStepEquiv I a b).injective
  have hle : ∀ k, selectedAffinityTerm I a b g k ≤
      pushLaw (selected (N := N) I) g k + pushLaw (selected (N := N) I) g (selectedStep I a b k) := by
    intro k
    have hp := Real.sq_sqrt (pushLaw_nonneg (selected (N := N) I) g k)
    have hq := Real.sq_sqrt (pushLaw_nonneg (selected (N := N) I) g (selectedStep I a b k))
    unfold selectedAffinityTerm
    nlinarith [sq_nonneg (Real.sqrt (pushLaw (selected (N := N) I) g k) -
      Real.sqrt (pushLaw (selected (N := N) I) g (selectedStep I a b k)))]
  exact Summable.of_nonneg_of_le (fun k => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    hle (hs.add ht)

/-- Full-to-selected affinity, for the actual probability pushforward and translation. -/
theorem full_affinity_le_selected (I : Finset ℤ) (a b : ℤ) (hab : a ≠ b) (g : H N) :
    Summable (selectedAffinityTerm I a b g) ∧
      FullOccupationAffinity.affinity a b g ≤ ∑' k, selectedAffinityTerm I a b g k := by
  have hgroup := full_affinity_grouped a b g (selectedDonor (N := N) I a)
  have hs := selectedAffinityTerm_summable I a b g
  refine ⟨hs, hgroup.2.trans (hgroup.1.tsum_le_tsum ?_ hs)⟩
  intro k
  have hp := Real.sqrt_le_sqrt (source_fiberMass_le I a g k)
  have hq := Real.sqrt_le_sqrt (target_fiberMass_le I a b hab g k)
  rw [fiberMass_eq_norm, Real.sqrt_sq (norm_nonneg _)] at hp
  rw [fiberMass_eq_norm, Real.sqrt_sq (norm_nonneg _)] at hq
  exact mul_le_mul hp hq (norm_nonneg _) (Real.sqrt_nonneg _)

end QuantumNLS.FiniteCellCoefficientLaw

-- BEGIN COMPLETE DECLARATION AUDIT
#print axioms QuantumNLS.FiniteCellCoefficientLaw.law
#print axioms QuantumNLS.FiniteCellCoefficientLaw.law_nonneg
#print axioms QuantumNLS.FiniteCellCoefficientLaw.law_summable
#print axioms QuantumNLS.FiniteCellCoefficientLaw.law_total
#print axioms QuantumNLS.FiniteCellCoefficientLaw.pushLaw
#print axioms QuantumNLS.FiniteCellCoefficientLaw.pushLaw_hasSum
#print axioms QuantumNLS.FiniteCellCoefficientLaw.pushLaw_nonneg
#print axioms QuantumNLS.FiniteCellCoefficientLaw.pushLaw_normalized
#print axioms QuantumNLS.FiniteCellCoefficientLaw.selected
#print axioms QuantumNLS.FiniteCellCoefficientLaw.exterior
#print axioms QuantumNLS.FiniteCellCoefficientLaw.selected_exterior_injective
#print axioms QuantumNLS.FiniteCellCoefficientLaw.selectedLaw_normalized
#print axioms QuantumNLS.FiniteCellCoefficientLaw.fiberVector
#print axioms QuantumNLS.FiniteCellCoefficientLaw.fiberMass
#print axioms QuantumNLS.FiniteCellCoefficientLaw.fiberMass_hasSum
#print axioms QuantumNLS.FiniteCellCoefficientLaw.fiberMass_eq_norm
#print axioms QuantumNLS.FiniteCellCoefficientLaw.groupedTerm
#print axioms QuantumNLS.FiniteCellCoefficientLaw.groupedTerm_summable
#print axioms QuantumNLS.FiniteCellCoefficientLaw.fiber_Cauchy
#print axioms QuantumNLS.FiniteCellCoefficientLaw.full_affinity_grouped
#print axioms QuantumNLS.FiniteCellCoefficientLaw.selectedStep
#print axioms QuantumNLS.FiniteCellCoefficientLaw.selectedStepEquiv
#print axioms QuantumNLS.FiniteCellCoefficientLaw.selected_destination
#print axioms QuantumNLS.FiniteCellCoefficientLaw.selectedDonor
#print axioms QuantumNLS.FiniteCellCoefficientLaw.source_fiberMass_le
#print axioms QuantumNLS.FiniteCellCoefficientLaw.target_fiberMass_le
#print axioms QuantumNLS.FiniteCellCoefficientLaw.selectedAffinityTerm
#print axioms QuantumNLS.FiniteCellCoefficientLaw.selectedAffinityTerm_summable
#print axioms QuantumNLS.FiniteCellCoefficientLaw.full_affinity_le_selected

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.FiniteCellCoefficientLaw.law,
    ``QuantumNLS.FiniteCellCoefficientLaw.law_nonneg,
    ``QuantumNLS.FiniteCellCoefficientLaw.law_summable,
    ``QuantumNLS.FiniteCellCoefficientLaw.law_total,
    ``QuantumNLS.FiniteCellCoefficientLaw.pushLaw,
    ``QuantumNLS.FiniteCellCoefficientLaw.pushLaw_hasSum,
    ``QuantumNLS.FiniteCellCoefficientLaw.pushLaw_nonneg,
    ``QuantumNLS.FiniteCellCoefficientLaw.pushLaw_normalized,
    ``QuantumNLS.FiniteCellCoefficientLaw.selected,
    ``QuantumNLS.FiniteCellCoefficientLaw.exterior,
    ``QuantumNLS.FiniteCellCoefficientLaw.selected_exterior_injective,
    ``QuantumNLS.FiniteCellCoefficientLaw.selectedLaw_normalized,
    ``QuantumNLS.FiniteCellCoefficientLaw.fiberVector,
    ``QuantumNLS.FiniteCellCoefficientLaw.fiberMass,
    ``QuantumNLS.FiniteCellCoefficientLaw.fiberMass_hasSum,
    ``QuantumNLS.FiniteCellCoefficientLaw.fiberMass_eq_norm,
    ``QuantumNLS.FiniteCellCoefficientLaw.groupedTerm,
    ``QuantumNLS.FiniteCellCoefficientLaw.groupedTerm_summable,
    ``QuantumNLS.FiniteCellCoefficientLaw.fiber_Cauchy,
    ``QuantumNLS.FiniteCellCoefficientLaw.full_affinity_grouped,
    ``QuantumNLS.FiniteCellCoefficientLaw.selectedStep,
    ``QuantumNLS.FiniteCellCoefficientLaw.selectedStepEquiv,
    ``QuantumNLS.FiniteCellCoefficientLaw.selected_destination,
    ``QuantumNLS.FiniteCellCoefficientLaw.selectedDonor,
    ``QuantumNLS.FiniteCellCoefficientLaw.source_fiberMass_le,
    ``QuantumNLS.FiniteCellCoefficientLaw.target_fiberMass_le,
    ``QuantumNLS.FiniteCellCoefficientLaw.selectedAffinityTerm,
    ``QuantumNLS.FiniteCellCoefficientLaw.selectedAffinityTerm_summable,
    ``QuantumNLS.FiniteCellCoefficientLaw.full_affinity_le_selected]
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
  Lean.logInfo m!"FiniteCellCoefficientLaw aggregate audit PASS: {seen.size} transitive constants. All declarations independent of EXT-001."
