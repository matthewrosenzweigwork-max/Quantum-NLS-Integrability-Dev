import QuantumNLS.BetheGeneralSliceEndpoints

/-! Higher-degree outer-face cancellation of the actual on-shell source.
Every selected coordinate and every unselected spectator is retained. This
proves the physical outer pair; internal/cross-degree terms remain separate. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ComplexConjugate
set_option maxHeartbeats 4000000
namespace QuantumNLS.BetheHigherCancellation
open BetheExtension BetheTransferKernelAdjoint

/-- The phase length of an arbitrary selected block of physical coordinates. -/
def selectedDisplacement {M m : ℕ} (ι : Fin m ↪ Fin M)
    (x : Fin m → ℝ) (y : Fin M → ℝ) : ℝ :=
  ∑ j, (x j - y (ι j))

theorem selectedDisplacement_face {M m : ℕ} (ι : Fin m ↪ Fin M)
    (x : Fin m → ℝ) (y : Fin M → ℝ) (j : Fin m) (L : ℝ) :
    selectedDisplacement ι x (Function.update y (ι j) L) =
      selectedDisplacement ι x (Function.update y (ι j) 0) - L := by
  classical
  have he : (∑ k : Fin m, (Function.update y (ι j) L (ι k) -
      Function.update y (ι j) 0 (ι k))) = L := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hkj
      have hne : ι k ≠ ι j := fun h => hkj (ι.injective h)
      simp [Function.update_of_ne hne]
    · simp
  calc
    _ = selectedDisplacement ι x (Function.update y (ι j) 0) -
        ∑ k : Fin m, (Function.update y (ι j) L (ι k) - Function.update y (ι j) 0 (ι k)) := by
      simp only [selectedDisplacement]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [he]

/-- The lower branch is exactly the same displacement phase multiplied by
exp(izL), for every degree and every complex parameter. -/
theorem lower_phase (L : ℝ) (z : ℂ) {m : ℕ} (x y : Fin m → ℝ) :
    Complex.exp (Complex.I*z*L - Complex.I*z*(∑ j, (y j-x j) : ℝ)) =
      Complex.exp (Complex.I*z*L) * Complex.exp (Complex.I*z*displacement x y) := by
  rw [← Complex.exp_add]
  congr 1
  have h := displacement_swap x y
  change (∑ j, (y j-x j)) = -(∑ j, (x j-y j)) at h
  unfold displacement
  rw [h]
  push_cast
  ring

variable (L : ℝ) [Fact (0 < L)]

/-- Exact source-root cancellation for the full degree-m exponential, at any
selected integration coordinate, with all remaining coordinates arbitrary in
the closed cube. No on-shell transfer or cancellation premise is supplied. -/
theorem source_selected_outer_cancel {N m : ℕ} {c : ℝ} (hc : 0 < c)
    {n : Fin (N+1) → ℤ} (hn : Antitone n) (ι : Fin m ↪ Fin (N+1))
    (x : Fin m → ℝ) (y : Fin (N+1) → ℝ) (hy : ∀ k, y k ∈ Icc 0 L)
    (j : Fin m) (z : ℂ) :
    Complex.exp (Complex.I*z*L) *
        Complex.exp (Complex.I*z*selectedDisplacement ι x (Function.update y (ι j) L)) *
        symmetricExtension L c n (Function.update y (ι j) L) -
      Complex.exp (Complex.I*z*selectedDisplacement ι x (Function.update y (ι j) 0)) *
        symmetricExtension L c n (Function.update y (ι j) 0) = 0 := by
  rw [symmetricExtension_update_faces (Fact.out : 0 < L) hc hn y hy (ι j),
    selectedDisplacement_face,← Complex.exp_add]
  have he (d : ℝ) : Complex.I*z*(L : ℂ) + Complex.I*z*((d-L : ℝ) : ℂ) = Complex.I*z*d := by
    push_cast
    ring
  rw [he,sub_self]

/-- The arbitrary selection theorem includes precisely the first block of a
placement, including arbitrarily many unchanged spectators. -/
theorem selectedDisplacement_firstBlock (m q : ℕ) (x : Fin m → ℝ)
    (t : Fin m → ℝ) (s : Fin q → ℝ) :
    selectedDisplacement (Fin.castAddEmb q) x (Fin.append t s) = displacement x t := by
  simp only [selectedDisplacement,displacement,Fin.castAddEmb_apply,Fin.append_left]

/-- The two actual outer integration faces differ by the cyclic relocation
of the endpoint within the acted-on block. Every spectator stays fixed. -/
theorem source_cyclic_block_faces (r q : ℕ) {c : ℝ} (hc : 0 < c)
    {n : Fin (q+(r+1)) → ℤ} (hn : Antitone n)
    (s : Fin q → ℝ) (hs : ∀ j, s j ∈ Icc 0 L)
    (t : Fin r → ℝ) (ht : ∀ j, t j ∈ Icc 0 L) :
    symmetricExtension L c n (Fin.append s (Fin.cons L t)) =
      symmetricExtension L c n (Fin.append s (Fin.snoc t 0)) := by
  classical
  let y := Fin.append s (Fin.cons 0 t)
  let i : Fin (q+(r+1)) := Fin.natAdd q 0
  have hy : ∀ j, y j ∈ Icc 0 L := by
    intro j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simpa [y] using hs k
    · refine Fin.cases ?_ (fun k => ?_) k
      · simp [y,(Fact.out : 0 < L).le]
      · simpa [y] using ht k
  have hup (a : ℝ) : Function.update y i a = Fin.append s (Fin.cons a t) := by
    ext j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · have hne : Fin.castAdd (r+1) k ≠ i := by
        intro h
        have hv := congrArg Fin.val h
        change k.val = q + 0 at hv
        omega
      simp [y,Function.update_of_ne hne]
    · refine Fin.cases ?_ (fun k => ?_) k
      · simp [y,i]
      · have hne : Fin.natAdd q k.succ ≠ i := by
          intro h
          have hv := congrArg Fin.val h
          change q + (k.val+1) = q + 0 at hv
          omega
        simp [y,Function.update_of_ne hne]
  have hp := symmetricExtension_update_faces (Fact.out : 0 < L) hc hn y hy i
  rw [hup,hup] at hp
  have he : Fin.append s (Fin.snoc t 0) =
      Fin.append s (Fin.cons 0 t) ∘
        TensorPlacements.blockPerm (1 : Equiv.Perm (Fin q)) (finRotate (r+1)) := by
    ext j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simp
    · simp only [Function.comp_apply,TensorPlacements.blockPerm_natAdd,Fin.append_right,
        Fin.snoc_eq_cons_rotate]
  rw [he,symmetricExtension_permute]
  exact hp

/-- At degree r+1 the minus face y₁=L and plus face y_(r+1)=0 cancel
with the original full e^(izL) phase. The remaining r integration variables
and all q spectators are arbitrary in the closed cube. -/
theorem source_cyclic_block_outer_cancel (r q : ℕ) {c : ℝ} (hc : 0 < c)
    {n : Fin (q+(r+1)) → ℤ} (hn : Antitone n)
    (x : Fin (r+1) → ℝ) (s : Fin q → ℝ) (hs : ∀ j, s j ∈ Icc 0 L)
    (t : Fin r → ℝ) (ht : ∀ j, t j ∈ Icc 0 L) (z : ℂ) :
    Complex.exp (Complex.I*z*L) * Complex.exp (Complex.I*z*displacement x (Fin.cons L t)) *
        symmetricExtension L c n (Fin.append s (Fin.cons L t)) -
      Complex.exp (Complex.I*z*displacement x (Fin.snoc t 0)) *
        symmetricExtension L c n (Fin.append s (Fin.snoc t 0)) = 0 := by
  have hd : displacement x (Fin.cons L t) = displacement x (Fin.snoc t 0) - L := by
    have hc : (∑ j : Fin (r+1), Fin.cons L t j) = L + ∑ j, t j := by
      rw [Fin.sum_univ_succ]
      simp
    have ht : (∑ j : Fin (r+1), Fin.snoc t 0 j) = ∑ j, t j := by
      rw [Fin.sum_univ_castSucc]
      simp
    simp only [displacement,Finset.sum_sub_distrib]
    rw [hc,ht]
    ring
  rw [source_cyclic_block_faces L r q hc hn s hs t ht,hd,← Complex.exp_add]
  have he (d : ℝ) : Complex.I*z*(L : ℂ) + Complex.I*z*((d-L : ℝ) : ℂ) = Complex.I*z*d := by
    push_cast
    ring
  rw [he,sub_self]

/-- Common remaining domain of the minus face y₁=L and plus face y_(r+1)=0:
the r literal intervals [x_(j+1),x_j], with ordinary Lebesgue measure. -/
def outerFaceMeasure {r : ℕ} (x : Fin (r+1) → ℝ) : Measure (Fin r → ℝ) :=
  Measure.pi (fun j => volume.restrict (Icc (x j.succ) (x j.castSucc)))

theorem outerFaceMeasure_eq_open {r : ℕ} (x : Fin (r+1) → ℝ) :
    outerFaceMeasure x =
      Measure.pi (fun j => volume.restrict (Ioo (x j.succ) (x j.castSucc))) := by
  unfold outerFaceMeasure
  congr 1
  funext j
  exact restrict_Ioo_eq_restrict_Icc.symm

/-- The entire paired outer-face contribution integrates to zero on its
actual common alternating domain, with arbitrary spectators. -/
theorem integral_source_cyclic_outer_cancel (r q : ℕ) {c : ℝ} (hc : 0 < c)
    {n : Fin (q+(r+1)) → ℤ} (hn : Antitone n)
    (x : Fin (r+1) → ℝ) (hx : ∀ j, x j ∈ Icc 0 L)
    (s : Fin q → ℝ) (hs : ∀ j, s j ∈ Icc 0 L) (z : ℂ) :
    (∫ t, Complex.exp (Complex.I*z*L) * Complex.exp (Complex.I*z*displacement x (Fin.cons L t)) *
        symmetricExtension L c n (Fin.append s (Fin.cons L t)) -
      Complex.exp (Complex.I*z*displacement x (Fin.snoc t 0)) *
        symmetricExtension L c n (Fin.append s (Fin.snoc t 0)) ∂outerFaceMeasure x) = 0 := by
  have hmem : ∀ᵐ t ∂outerFaceMeasure x, ∀ j : Fin r,
      t j ∈ Icc (x j.succ) (x j.castSucc) := by
    rw [ae_all_iff]
    intro j
    exact (Measure.quasiMeasurePreserving_eval
      (fun k : Fin r => volume.restrict (Icc (x k.succ) (x k.castSucc))) j).ae
        (ae_restrict_mem measurableSet_Icc)
  calc
    _ = ∫ _t, (0 : ℂ) ∂outerFaceMeasure x := by
      apply integral_congr_ae
      filter_upwards [hmem] with t ht
      exact source_cyclic_block_outer_cancel L r q hc hn x s hs t
        (fun j => ⟨(hx j.succ).1.trans (ht j).1,(ht j).2.trans (hx j.castSucc).2⟩) z
    _ = 0 := integral_zero _ _

end QuantumNLS.BetheHigherCancellation

#print axioms QuantumNLS.BetheHigherCancellation.selectedDisplacement
#print axioms QuantumNLS.BetheHigherCancellation.selectedDisplacement_face
#print axioms QuantumNLS.BetheHigherCancellation.lower_phase
#print axioms QuantumNLS.BetheHigherCancellation.source_selected_outer_cancel
#print axioms QuantumNLS.BetheHigherCancellation.selectedDisplacement_firstBlock
#print axioms QuantumNLS.BetheHigherCancellation.source_cyclic_block_faces
#print axioms QuantumNLS.BetheHigherCancellation.source_cyclic_block_outer_cancel
#print axioms QuantumNLS.BetheHigherCancellation.outerFaceMeasure
#print axioms QuantumNLS.BetheHigherCancellation.outerFaceMeasure_eq_open
#print axioms QuantumNLS.BetheHigherCancellation.integral_source_cyclic_outer_cancel
