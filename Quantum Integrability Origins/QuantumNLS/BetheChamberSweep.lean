import QuantumNLS.BetheFaceEnumeration

/-! A complete one-coordinate sweep across any number of spectators. Every
adjacent chamber seam is evaluated once, including coincident cuts. This is
an actual source integral; assembling higher-dimensional placement faces
across transfer degrees remains a separate obligation. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
set_option maxHeartbeats 4000000
namespace QuantumNLS.BetheChamberSweep
open BetheExtension BetheInternalFaces BetheCrossDegreeFaces

def insertionPermutation {N : ℕ} (k : Fin (N+1)) : Equiv.Perm (Fin (N+1)) :=
  (finSuccEquiv' k).trans (finSuccEquiv N).symm

theorem insertNth_eq_comp {N : ℕ} (s : Fin N → ℝ) (k : Fin (N+1)) (t : ℝ) :
    Fin.insertNth (α := fun _ => ℝ) k t s = Fin.cons (α := fun _ => ℝ) t s ∘ insertionPermutation k := by
  ext i
  refine Fin.succAboveCases k ?_ (fun j => ?_) i
  · simp [insertionPermutation]
  · simp [insertionPermutation]

theorem source_insertNth {N : ℕ} (L c : ℝ) (n : Fin (N+1) → ℤ)
    (s : Fin N → ℝ) (k : Fin (N+1)) (t : ℝ) :
    symmetricExtension L c n (Fin.insertNth (α := fun _ => ℝ) k t s) =
      symmetricExtension L c n (Fin.cons (α := fun _ => ℝ) t s) := by
  rw [insertNth_eq_comp, symmetricExtension_permute]

theorem antitone_insertNth {N : ℕ} (s : Fin N → ℝ) (hs : Antitone s)
    (k : Fin (N+1)) (t : ℝ)
    (hl : ∀ i : Fin N, i.castSucc < k → t ≤ s i)
    (hr : ∀ i : Fin N, k ≤ i.castSucc → s i ≤ t) :
    Antitone (Fin.insertNth (α := fun _ => ℝ) k t s) := by
  intro i j
  refine Fin.succAboveCases k ?_ (fun a => ?_) i <;>
    refine Fin.succAboveCases k ?_ (fun b => ?_) j <;> intro hij
  · exact le_rfl
  · simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    exact hr b ((Fin.lt_succAbove_iff_le_castSucc k b).mp
      (lt_of_le_of_ne hij (k.succAbove_ne b).symm))
  · simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    exact hl a ((Fin.succAbove_lt_iff_castSucc_lt k a).mp
      (lt_of_le_of_ne hij (k.succAbove_ne a)))
  · simp only [Fin.insertNth_apply_succAbove]
    exact hs ((Fin.succAboveOrderEmb k).le_iff_le.mp hij)

/-- Decreasing cuts hi,s_0,...,s_(N-1),lo. No distinctness of s is needed. -/
def cuts {N : ℕ} (hi lo : ℝ) (s : Fin N → ℝ) : Fin (N+2) → ℝ :=
  Fin.cons (α := fun _ => ℝ) hi (Fin.snoc (α := fun _ => ℝ) s lo)

theorem cuts_seam {N : ℕ} (hi lo : ℝ) (s : Fin N → ℝ) (j : Fin N) :
    cuts hi lo s j.castSucc.succ = s j := by
  simp [cuts]

theorem insert_segment_antitone {N : ℕ} (hi lo : ℝ) (s : Fin N → ℝ)
    (hs : Antitone s)
    (k : Fin (N+1)) {t : ℝ}
    (ht : t ∈ Icc (cuts hi lo s k.succ) (cuts hi lo s k.castSucc)) :
    Antitone (Fin.insertNth (α := fun _ => ℝ) k t s) := by
  apply antitone_insertNth s hs k t
  · intro i hik
    revert hik ht
    refine Fin.cases ?_ (fun j => ?_) k
    · intro _ hik
      exact False.elim (Fin.not_lt_zero i.castSucc hik)
    · intro ht hik
      have hij : i ≤ j := by exact_mod_cast (show i.val ≤ j.val by simpa using hik)
      have ht' : t ≤ s j := by simpa [cuts] using ht.2
      exact ht'.trans (hs hij)
  · intro i hki
    revert hki ht
    refine Fin.lastCases ?_ (fun j => ?_) k
    · intro _ hki
      have hv := Fin.le_iff_val_le_val.mp hki
      simp at hv
      omega
    · intro ht hki
      have hji : j ≤ i := by simpa using hki
      have ht' : s j ≤ t := by simpa [cuts] using ht.1
      exact (hs hji).trans ht'

theorem cuts_antitone {N : ℕ} (hi lo : ℝ) (hlh : lo ≤ hi)
    (s : Fin N → ℝ) (hs : Antitone s) (hb : ∀ i, s i ∈ Icc lo hi) :
    Antitone (cuts hi lo s) := by
  cases N with
  | zero =>
    apply Fin.antitone_iff_succ_le.mpr
    intro k
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    simpa [cuts, Fin.snoc_zero] using hlh
  | succ N =>
    apply Fin.antitone_iff_succ_le.mpr
    intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · simpa [cuts] using (hb 0).2
    · refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [cuts, Fin.castSucc_succ, Fin.cons_succ, Fin.snoc_castSucc]
        rw [show Fin.snoc (α := fun _ => ℝ) s lo (Fin.last N).succ = lo from Fin.snoc_last (n := N+1) (α := fun _ => ℝ) lo s]
        exact (hb (Fin.last N)).1
      · simp only [cuts, Fin.castSucc_succ, Fin.cons_succ, Fin.snoc_castSucc]
        rw [← Fin.castSucc_succ i, Fin.snoc_castSucc]
        exact hs i.castSucc_le_succ

/-- The two consecutive closed charts have literally the same collision
tuple. Multiple equal spectators create zero-length segments, not gaps. -/
theorem insert_collision {N : ℕ} (s : Fin N → ℝ) (hs : Antitone s) (j : Fin N) :
    Fin.insertNth (α := fun _ => ℝ) j.castSucc (s j) s = Fin.insertNth (α := fun _ => ℝ) j.succ (s j) s := by
  have ha : Antitone (Fin.insertNth (α := fun _ => ℝ) j.castSucc (s j) s) := by
    apply antitone_insertNth s hs
    · intro i hij
      exact hs (le_of_lt (by simpa using hij))
    · intro i hji
      exact hs (by simpa using hji)
  have hb : Antitone (Fin.insertNth (α := fun _ => ℝ) j.succ (s j) s) := by
    apply antitone_insertNth s hs
    · intro i hij
      exact hs (by exact_mod_cast (show i.val ≤ j.val by simpa using hij))
    · intro i hji
      exact hs (by exact_mod_cast (show j.val ≤ i.val by have := Fin.le_iff_val_le_val.mp hji; simp at this; omega))
  simp only [insertNth_eq_comp] at ha hb ⊢
  exact Tuple.unique_antitone ha hb

theorem collision_coordinates {N : ℕ} (s : Fin N → ℝ) (j : Fin N) :
    (Fin.insertNth (α := fun _ => ℝ) j.castSucc (s j) s) j.castSucc =
      (Fin.insertNth (α := fun _ => ℝ) j.castSucc (s j) s) j.succ := by
  rw [Fin.insertNth_apply_same, ← Fin.succAbove_castSucc_self j,
    Fin.insertNth_apply_succAbove]

/-- Pure endpoint accounting: two external ends, and each internal seam
exactly once with its right-minus-left orientation. -/
theorem sum_endpoint_differences {N : ℕ} (U V : Fin (N+1) → ℂ) :
    (∑ k, (U k - V k)) = U 0 - V (Fin.last N) +
      ∑ j : Fin N, (U j.succ - V j.castSucc) := by
  rw [Finset.sum_sub_distrib, Fin.sum_univ_succ U, Fin.sum_univ_castSucc V,
    Finset.sum_sub_distrib]
  ring

theorem sum_integral_cuts {K : ℕ} (a : Fin (K+1) → ℝ)
    (f : ℝ → ℂ) (hf : Continuous f) :
    (∑ k : Fin K, ∫ t in a k.succ..a k.castSucc, f t) =
      ∫ t in a (Fin.last K)..a 0, f t := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Fin.sum_univ_succ]
    have ht := ih (fun i => a i.succ)
    change (∫ t in a (0 : Fin (K+1)).succ..a (0 : Fin (K+1)).castSucc, f t) +
      (∑ k : Fin K, ∫ t in a k.succ.succ..a k.castSucc.succ, f t) = _
    rw [ht, add_comm, intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]
    rfl

def endpoint {N : ℕ} (c : ℝ) (q : Fin (N+1) → ℝ) (z : ℂ)
    (s : Fin N → ℝ) (u : ℝ) (k : Fin (N+1)) (t : ℝ) : ℂ :=
  Complex.exp (Complex.I*z*(u-t)) *
    primitive c q (Fin.insertNth (α := fun _ => ℝ) k t s) z {k}

theorem integral_source_sweep_segment {N : ℕ} {L c : ℝ}
    (s : Fin N → ℝ) (hs : Antitone s) (hi lo : ℝ) (hlh : lo ≤ hi)
    (hb : ∀ i, s i ∈ Icc lo hi) (n : Fin (N+1) → ℤ) (z : ℂ)
    (hz : ∀ i, z ≠ (BetheSmooth.sourceRoots L n c i : ℂ)) (u : ℝ) (k : Fin (N+1)) :
    (∫ t in cuts hi lo s k.succ..cuts hi lo s k.castSucc,
      Complex.exp (Complex.I*z*(u-t)) * symmetricExtension L c n (Fin.cons (α := fun _ => ℝ) t s)) =
      endpoint c (BetheSmooth.sourceRoots L n c) z s u k (cuts hi lo s k.castSucc) -
        endpoint c (BetheSmooth.sourceRoots L n c) z s u k (cuts hi lo s k.succ) := by
  have hle := cuts_antitone hi lo hlh s hs hb k.castSucc_le_succ
  have ha := insert_segment_antitone hi lo s hs k (t := cuts hi lo s k.succ) ⟨le_rfl,hle⟩
  have hb' := insert_segment_antitone hi lo s hs k (t := cuts hi lo s k.castSucc) ⟨hle,le_rfl⟩
  have h := integral_source_segment
    (Fin.insertNth (α := fun _ => ℝ) k (cuts hi lo s k.castSucc) s) k n z hz u
    (cuts hi lo s k.succ) (cuts hi lo s k.castSucc) hle
    (by simpa only [Fin.update_insertNth] using ha)
    (by simpa only [Fin.update_insertNth] using hb')
  simpa only [Fin.update_insertNth, source_insertNth, endpoint] using h

/-- Each seam is exactly BIF1's adjacent primitive recurrence. Its two
charts, orientation, phase, and multiplicity one are explicit. -/
theorem source_sweep_seam {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n)
    (s : Fin N → ℝ) (hs : Antitone s) (hi lo u : ℝ) (z : ℂ)
    (hz : ∀ i, z ≠ (BetheSmooth.sourceRoots L n c i : ℂ)) (j : Fin N) :
    endpoint c (BetheSmooth.sourceRoots L n c) z s u j.succ (cuts hi lo s j.succ.castSucc) -
      endpoint c (BetheSmooth.sourceRoots L n c) z s u j.castSucc (cuts hi lo s j.castSucc.succ) =
      (c : ℂ) * Complex.exp (Complex.I*z*(u-s j)) *
        primitive c (BetheSmooth.sourceRoots L n c)
          (Fin.insertNth (α := fun _ => ℝ) j.castSucc (s j) s) z {j.castSucc,j.succ} := by
  classical
  simp only [Fin.castSucc_succ, cuts_seam, endpoint]
  rw [← insert_collision s hs j, ← mul_sub]
  have h := source_primitive_internal_face hL hc hn
    (Fin.insertNth (α := fun _ => ℝ) j.castSucc (s j) s) z hz ∅
    (a := j.castSucc) (b := j.succ) (by simp)
    (Finset.notMem_empty _) (Finset.notMem_empty _) (collision_coordinates s j)
  simp only [Finset.insert_empty] at h
  rw [h]
  ring

/-- Actual ordinary integral across ALL N spectators. There are N+1
segments, exactly N internal faces, and the two displayed external ends.
No remaining endpoint term is set to zero. -/
theorem integral_source_sweep {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n)
    (s : Fin N → ℝ) (hs : Antitone s) (hi lo : ℝ) (hlh : lo ≤ hi)
    (hb : ∀ i, s i ∈ Icc lo hi) (u : ℝ) (z : ℂ)
    (hz : ∀ i, z ≠ (BetheSmooth.sourceRoots L n c i : ℂ)) :
    (∫ t in lo..hi, Complex.exp (Complex.I*z*(u-t)) *
      symmetricExtension L c n (Fin.cons (α := fun _ => ℝ) t s)) =
      endpoint c (BetheSmooth.sourceRoots L n c) z s u 0 hi -
        endpoint c (BetheSmooth.sourceRoots L n c) z s u (Fin.last N) lo +
      ∑ j : Fin N, (c : ℂ) * Complex.exp (Complex.I*z*(u-s j)) *
        primitive c (BetheSmooth.sourceRoots L n c)
          (Fin.insertNth (α := fun _ => ℝ) j.castSucc (s j) s) z {j.castSucc,j.succ} := by
  have hcont : Continuous (fun t : ℝ => Complex.exp (Complex.I*z*(u-t)) *
      symmetricExtension L c n (Fin.cons (α := fun _ => ℝ) t s)) := by
    apply Continuous.mul
    · fun_prop
    · exact (continuous_symmetricExtension L c n).comp (by fun_prop)
  have hsum := sum_integral_cuts (cuts hi lo s)
    (fun t => Complex.exp (Complex.I*z*(u-t)) * symmetricExtension L c n (Fin.cons (α := fun _ => ℝ) t s)) hcont
  have hends : cuts hi lo s 0 = hi ∧ cuts hi lo s (Fin.last (N+1)) = lo := by
    change cuts hi lo s 0 = hi ∧ cuts hi lo s (Fin.last N).succ = lo
    simp [cuts]
  rw [hends.1,hends.2] at hsum
  rw [← hsum]
  simp_rw [integral_source_sweep_segment s hs hi lo hlh hb n z hz u]
  rw [sum_endpoint_differences]
  simp only [show (Fin.last N).succ = Fin.last (N+1) from rfl,
    hends.2, source_sweep_seam hL hc hn s hs hi lo u z hz]
  rfl

/-- The fixed physical spectators, sorted with their full multiplicities. -/
def sortedSpectators {N : ℕ} (y : Fin (N+1) → ℝ) (a : Fin (N+1)) : Fin N → ℝ :=
  decreasing (Fin.removeNth a y)

theorem source_update_sortedSpectators {N : ℕ} (L c : ℝ) (n : Fin (N+1) → ℤ)
    (y : Fin (N+1) → ℝ) (a : Fin (N+1)) (t : ℝ) :
    symmetricExtension L c n (Function.update y a t) =
      symmetricExtension L c n (Fin.cons (α := fun _ => ℝ) t (sortedSpectators y a)) := by
  have hu : Function.update y a t =
      Fin.insertNth (α := fun _ => ℝ) a t (Fin.removeNth a y) := by
    apply Fin.eq_insertNth_iff.mpr
    constructor
    · simp
    · ext i
      simp [Fin.removeNth]
  rw [hu, source_insertNth]
  exact (symmetricExtension_cons_permute L c n t (Fin.removeNth a y)
    (Tuple.sort (α := ℝᵒᵈ) (Fin.removeNth a y))).symm

theorem sortedSpectators_bounds {N : ℕ} (y : Fin (N+1) → ℝ) (a : Fin (N+1))
    (hi lo : ℝ) (hy : ∀ i, i ≠ a → y i ∈ Icc lo hi) :
    ∀ i, sortedSpectators y a i ∈ Icc lo hi := by
  intro i
  exact hy _ (a.succAbove_ne _)

/-- A whole conditional integration coordinate of an arbitrary selected
block, with its actual summed phase and every other coordinate fixed. The
spectators may initially be in any order. All spectator seams are explicit;
this does not identify iterated multivariable boundary contributions. -/
theorem integral_source_selected_sweep {N m : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n)
    (ι : Fin m ↪ Fin (N+1)) (X : Fin m → ℝ) (y : Fin (N+1) → ℝ)
    (j : Fin m) (hi lo : ℝ) (hlh : lo ≤ hi)
    (hy : ∀ i, i ≠ ι j → y i ∈ Icc lo hi) (z : ℂ)
    (hz : ∀ i, z ≠ (BetheSmooth.sourceRoots L n c i : ℂ)) :
    let s := sortedSpectators y (ι j)
    let u := BetheHigherCancellation.selectedDisplacement ι X y + y (ι j)
    (∫ t in lo..hi,
      Complex.exp (Complex.I*z*BetheHigherCancellation.selectedDisplacement ι X
        (Function.update y (ι j) t)) * symmetricExtension L c n (Function.update y (ι j) t)) =
      endpoint c (BetheSmooth.sourceRoots L n c) z s u 0 hi -
        endpoint c (BetheSmooth.sourceRoots L n c) z s u (Fin.last N) lo +
      ∑ k : Fin N, (c : ℂ) * Complex.exp (Complex.I*z*(u-s k)) *
        primitive c (BetheSmooth.sourceRoots L n c)
          (Fin.insertNth (α := fun _ => ℝ) k.castSucc (s k) s) z {k.castSucc,k.succ} := by
  dsimp only
  simp_rw [BetheSourceCrossing.selectedDisplacement_update, source_update_sortedSpectators]
  convert
    integral_source_sweep hL hc hn _ (decreasing_antitone _) hi lo hlh
      (sortedSpectators_bounds y (ι j) hi lo hy)
      (BetheHigherCancellation.selectedDisplacement ι X y + y (ι j)) z hz using 1 <;>
      simp only [Complex.ofReal_sub, sortedSpectators]

end QuantumNLS.BetheChamberSweep

#print axioms QuantumNLS.BetheChamberSweep.insertionPermutation
#print axioms QuantumNLS.BetheChamberSweep.insertNth_eq_comp
#print axioms QuantumNLS.BetheChamberSweep.source_insertNth
#print axioms QuantumNLS.BetheChamberSweep.antitone_insertNth
#print axioms QuantumNLS.BetheChamberSweep.cuts
#print axioms QuantumNLS.BetheChamberSweep.cuts_seam
#print axioms QuantumNLS.BetheChamberSweep.insert_segment_antitone
#print axioms QuantumNLS.BetheChamberSweep.cuts_antitone
#print axioms QuantumNLS.BetheChamberSweep.insert_collision
#print axioms QuantumNLS.BetheChamberSweep.collision_coordinates
#print axioms QuantumNLS.BetheChamberSweep.sum_endpoint_differences
#print axioms QuantumNLS.BetheChamberSweep.sum_integral_cuts
#print axioms QuantumNLS.BetheChamberSweep.endpoint
#print axioms QuantumNLS.BetheChamberSweep.integral_source_sweep_segment
#print axioms QuantumNLS.BetheChamberSweep.source_sweep_seam
#print axioms QuantumNLS.BetheChamberSweep.integral_source_sweep
#print axioms QuantumNLS.BetheChamberSweep.sortedSpectators
#print axioms QuantumNLS.BetheChamberSweep.source_update_sortedSpectators
#print axioms QuantumNLS.BetheChamberSweep.sortedSpectators_bounds
#print axioms QuantumNLS.BetheChamberSweep.integral_source_selected_sweep

#check QuantumNLS.BetheFaceEnumeration.exists_unique_mergeChart
#check QuantumNLS.BetheFaceEnumeration.sum_permutation_faces
#check QuantumNLS.BetheFaceEnumeration.physical_orderedFiber_coefficient
#check QuantumNLS.BetheChamberSweep.integral_source_sweep
#check QuantumNLS.BetheChamberSweep.integral_source_selected_sweep

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.BetheFaceEnumeration.exists_unique_mergeChart,
    ``QuantumNLS.BetheFaceEnumeration.sum_permutation_faces,
    ``QuantumNLS.BetheFaceEnumeration.chamber_interior_or_face,
    ``QuantumNLS.BetheFaceEnumeration.internal_membership_cases,
    ``QuantumNLS.BetheFaceEnumeration.physical_orderedFiber_coefficient,
    ``QuantumNLS.BetheFaceEnumeration.sum_spectator_labels,
    ``QuantumNLS.BetheChamberSweep.integral_source_selected_sweep]
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  for n in #[``QuantumNLS.TensorPlacements.placementFiberEquiv,
      ``QuantumNLS.TensorPlacements.card_placementFiber,
      ``QuantumNLS.BetheFaceEnumeration.mergePermutation,
      ``QuantumNLS.BetheFaceEnumeration.mergePermutation_unique,
      ``QuantumNLS.BetheFaceEnumeration.orderedFiberEquiv,
      ``QuantumNLS.BetheFaceEnumeration.card_orderedFiber,
      ``QuantumNLS.BetheFaceEnumeration.spectatorDeletion,
      ``QuantumNLS.BetheFaceEnumeration.spectatorDeletion_label,
      ``QuantumNLS.BetheHigherPlacement.coefficient_normalization,
      ``Nat.factorial_mul_descFactorial,
      ``QuantumNLS.BetheChamberSweep.insertNth_eq_comp,
      ``QuantumNLS.BetheChamberSweep.antitone_insertNth,
      ``QuantumNLS.BetheChamberSweep.cuts_antitone,
      ``QuantumNLS.BetheChamberSweep.insert_collision,
      ``QuantumNLS.BetheChamberSweep.sum_endpoint_differences,
      ``QuantumNLS.BetheChamberSweep.sum_integral_cuts,
      ``QuantumNLS.BetheChamberSweep.integral_source_sweep_segment,
      ``QuantumNLS.BetheChamberSweep.source_sweep_seam,
      ``QuantumNLS.BetheChamberSweep.integral_source_sweep,
      ``QuantumNLS.BetheChamberSweep.source_update_sortedSpectators,
      ``QuantumNLS.BetheSourceCrossing.selectedDisplacement_update,
      ``QuantumNLS.BetheCrossDegreeFaces.integral_source_segment,
      ``QuantumNLS.BetheInternalFaces.source_primitive_internal_face,
      ``QuantumNLS.BetheInternalFaces.primitive_internal_face,
      ``QuantumNLS.BetheWavefunctions.coefficient,
      ``QuantumNLS.BetheContact.coefficient_contact,
      ``QuantumNLS.BetheSmooth.sourceRoots_strictAnti,
      ``QuantumNLS.BetheExtension.symmetricExtension_permute,
      ``QuantumNLS.BetheExtension.continuous_symmetricExtension] do
    unless seen.contains n do
      throwError "Enumeration/sweep route missing ingredient: {n}"
  for n in seen do
    if n.toString.startsWith "QuantumNLS.BetheOneParticleAction." ||
        n.toString.startsWith "QuantumNLS.BetheTwoParticle" then
      throwError "Enumeration/sweep route used special-particle action: {n}"
  Lean.logInfo m!"Enumeration/sweep route PASS: {seen.size} transitive constants; unique ordered merge charts, full and ordered permutation fibers, exact physical factorial coefficient, labelled spectator deletion, actual source integral over every spectator seam and arbitrary selected phase. Alternating rectangle boundary enumeration, cross-degree face matching, full cancellation and allN eigenrelation/basis OPEN."
