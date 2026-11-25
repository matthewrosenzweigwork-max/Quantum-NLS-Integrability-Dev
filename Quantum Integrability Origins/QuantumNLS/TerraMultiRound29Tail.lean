import QuantumNLS.TerraMultiRound28PlaneSecond

/-! A uniform quadratic-tail obstruction for the actual indexed actions.
This is a constituent, not the full analyticity theorem. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound29Tail
open QuantumNLS.Fourier (modeLp)
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.TerraMultiRound28PlaneSecond
variable {L κ : ℝ} [Fact (0 < L)]

/-- At every positive radius and beyond any finite collection of labels, the
actual mass has one coordinate equal to the squared norm of the field. -/
theorem actual_mass_tail_witness (hκ : 0 < κ) (S : Finset ℤ) {a : ℝ} (ha : 0 < a) :
    ∃ (u : L2T L) (n : ℤ), n ∉ S ∧ ‖u‖ = a ∧
      (RootIndexedMasses.masses hκ u).1 n = ‖u‖ ^ 2 := by
  obtain ⟨n, hn⟩ := S.finite_toSet.exists_notMem
  refine ⟨(a : ℂ) • modeLp L n, n, hn, ?_, ?_⟩
  · rw [norm_smul, OneParticleBorn.norm_modeLp]
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  · have hu : ‖(a : ℂ) • modeLp L n‖ = a := by
      rw [norm_smul, OneParticleBorn.norm_modeLp]
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    rw [hu, RootMassPlane.masses_plane]
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]

/-- A uniform quadratic bound on all discarded physical coordinates cannot
have coefficient strictly below one, even on an arbitrarily small ball. -/
theorem no_small_quadratic_tail_bound (hκ : 0 < κ) (S : Finset ℤ)
    {δ C : ℝ} (hδ : 0 < δ) (hC : C < 1) :
    ¬ ∀ (u : L2T L), ‖u‖ < δ → ∀ n : ℤ, n ∉ S →
      (RootIndexedMasses.masses hκ u).1 n ≤ C * ‖u‖ ^ 2 := by
  intro h
  obtain ⟨u, n, hn, hu, hm⟩ := actual_mass_tail_witness (L := L) hκ S (half_pos hδ)
  have hball : ‖u‖ < δ := by rw [hu]; linarith
  have hb := h u hball n hn
  rw [hm, hu] at hb
  have hp : 0 < (δ / 2) ^ 2 := sq_pos_of_pos (half_pos hδ)
  nlinarith

/-- Every finite cutoff misses a unit physical direction whose actual scalar
second derivative is exactly two. -/
theorem unit_direction_second_tail (hκ : 0 < κ) (S : Finset ℤ) :
    ∃ k : ℤ, k ∉ S ∧ ‖modeLp L k‖ = 1 ∧
      deriv (deriv (planeAction (L := L) hκ k k)) 0 = 2 := by
  obtain ⟨k, hk, hd⟩ := planeAction_second_outside (L := L) hκ S
  exact ⟨k, hk, OneParticleBorn.norm_modeLp k, hd.deriv⟩

/-- If bounded bilinear forms represent the scalar second derivatives on
physical mode directions, their discarded coordinate norms are bounded below
by two. This conditional bridge does not assert existence of a Hessian. -/
theorem represented_hessian_tail_lower_bound (hκ : 0 < κ) (S : Finset ℤ)
    (B : ℤ → L2T L →L[ℝ] L2T L →L[ℝ] ℝ)
    (hB : ∀ k : ℤ, B k (modeLp L k) (modeLp L k) =
      deriv (deriv (planeAction (L := L) hκ k k)) 0) :
    ∃ k : ℤ, k ∉ S ∧ 2 ≤ ‖B k‖ := by
  obtain ⟨k, hk, hn, hd⟩ := unit_direction_second_tail (L := L) hκ S
  have hv : B k (modeLp L k) (modeLp L k) = 2 := by rw [hB k, hd]
  have h₁ := (B k (modeLp L k)).le_opNorm (modeLp L k)
  have h₂ := (B k).le_opNorm (modeLp L k)
  rw [hv, hn] at h₁
  rw [hn] at h₂
  norm_num at h₁ h₂
  exact ⟨k, hk, le_trans h₁ h₂⟩

/-- Any sequence-valued bounded bilinear tail operator with the actual
plane-wave second derivatives as its discarded coordinates has norm at least
two. The representation premise is explicit and still needs to be proved for
the actual sequence Hessian. -/
theorem represented_sequence_hessian_tail_lower_bound (hκ : 0 < κ) (S : Finset ℤ)
    (T : L2T L →L[ℝ] L2T L →L[ℝ] lp (fun _ : ℤ => ℝ) 1)
    (hT : ∀ k : ℤ, k ∉ S → T (modeLp L k) (modeLp L k) k =
      deriv (deriv (planeAction (L := L) hκ k k)) 0) :
    2 ≤ ‖T‖ := by
  obtain ⟨k, hk, hn, hd⟩ := unit_direction_second_tail (L := L) hκ S
  have hv : T (modeLp L k) (modeLp L k) k = 2 := by rw [hT k hk, hd]
  have h₀ := lp.norm_apply_le_norm (by norm_num : (1 : ENNReal) ≠ 0)
    (T (modeLp L k) (modeLp L k)) k
  have h₁ := (T (modeLp L k)).le_opNorm (modeLp L k)
  have h₂ := T.le_opNorm (modeLp L k)
  rw [hv] at h₀
  rw [hn] at h₁ h₂
  norm_num at h₀ h₁ h₂
  exact le_trans h₀ (le_trans h₁ h₂)

end QuantumNLS.TerraMultiRound29Tail
#print axioms QuantumNLS.TerraMultiRound29Tail.actual_mass_tail_witness
#print axioms QuantumNLS.TerraMultiRound29Tail.no_small_quadratic_tail_bound
#print axioms QuantumNLS.TerraMultiRound29Tail.unit_direction_second_tail
#print axioms QuantumNLS.TerraMultiRound29Tail.represented_hessian_tail_lower_bound
#print axioms QuantumNLS.TerraMultiRound29Tail.represented_sequence_hessian_tail_lower_bound
