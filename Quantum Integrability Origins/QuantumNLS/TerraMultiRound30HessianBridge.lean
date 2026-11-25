import QuantumNLS.TerraMultiRound29Tail

/-! Chain-rule bridge for the actual indexed actions. This does not establish
existence of the first or second Fréchet derivatives. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound30HessianBridge
open QuantumNLS.Fourier (modeLp)
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.TerraMultiRound28PlaneSecond
open QuantumNLS.TerraMultiRound29Tail

variable {L κ : ℝ} [Fact (0 < L)]
abbrev Actions (hκ : 0 < κ) (u : L2T L) : lp (fun _ : ℤ => ℝ) 1 :=
  (RootIndexedMasses.masses hκ u).1

/-- The diagonal values of a differentiable derivative field are forced by
 the exact physical plane-wave restrictions. The differentiability premises
 are explicit and are not proved by this lemma. -/
theorem hessian_diagonal_of_derivative_field (hκ : 0 < κ)
    (D : L2T L → L2T L →L[ℝ] lp (fun _ : ℤ => ℝ) 1)
    (H : L2T L →L[ℝ] L2T L →L[ℝ] lp (fun _ : ℤ => ℝ) 1)
    (hD : ∀ u, HasFDerivAt (Actions hκ) (D u) u)
    (hH : HasFDerivAt D H 0) (k n : ℤ) :
    H (modeLp L k) (modeLp L k) n = if n = k then 2 else 0 := by
  let v : L2T L := modeLp L k
  let e : lp (fun _ : ℤ => ℝ) 1 →L[ℝ] ℝ := lp.evalCLM ℝ (fun _ : ℤ => ℝ) 1 n
  have hline (s : ℝ) : HasDerivAt (fun t : ℝ => t • v) v s := by
    simpa using (hasDerivAt_id s).smul_const v
  have hd (s : ℝ) : deriv (planeAction (L := L) hκ k n) s = e (D (s • v) v) := by
    have hh := e.hasFDerivAt.comp_hasDerivAt s ((hD (s • v)).comp_hasDerivAt s (hline s))
    have heq : (fun t : ℝ => e (Actions hκ (t • v))) = planeAction (L := L) hκ k n := by
      funext t
      simp [e, lp.evalCLM, Actions, planeAction, v, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    change HasDerivAt (fun t : ℝ => e (Actions hκ (t • v))) _ s at hh
    rw [heq] at hh
    simpa using hh.deriv
  have hf : deriv (planeAction (L := L) hκ k n) = fun s : ℝ => e (D (s • v) v) := by
    funext s
    exact hd s
  have hh := (ContinuousLinearMap.apply ℝ (lp (fun _ : ℤ => ℝ) 1) v).hasFDerivAt.comp 0 hH
  have hh' := e.hasFDerivAt.comp 0 hh
  have hc := hh'.comp_hasDerivAt_of_eq 0 (hline 0) (by simp)
  have hc' : HasDerivAt (deriv (planeAction (L := L) hκ k n)) (H v v n) 0 := by
    rw [hf]
    simpa [e, lp.evalCLM, Function.comp_def] using hc
  exact hc'.unique (planeAction_second (L := L) hκ k n 0)

/-- Any tail of the Hessian of the actual actions has norm at least two,
once the derivative field exists. The equality states the tail action on
coordinates outside the finite cutoff. -/
theorem hessian_tail_lower_bound_of_derivative_field (hκ : 0 < κ)
    (D : L2T L → L2T L →L[ℝ] lp (fun _ : ℤ => ℝ) 1)
    (H T : L2T L →L[ℝ] L2T L →L[ℝ] lp (fun _ : ℤ => ℝ) 1)
    (hD : ∀ u, HasFDerivAt (Actions hκ) (D u) u)
    (hH : HasFDerivAt D H 0) (S : Finset ℤ)
    (hT : ∀ k, k ∉ S → T (modeLp L k) (modeLp L k) k =
      H (modeLp L k) (modeLp L k) k) :
    2 ≤ ‖T‖ := by
  apply represented_sequence_hessian_tail_lower_bound hκ S T
  intro k hk
  rw [hT k hk, hessian_diagonal_of_derivative_field hκ D H hD hH]
  simpa using (planeAction_second (L := L) hκ k k 0).deriv.symm

end QuantumNLS.TerraMultiRound30HessianBridge
#print axioms QuantumNLS.TerraMultiRound30HessianBridge.hessian_diagonal_of_derivative_field
#print axioms QuantumNLS.TerraMultiRound30HessianBridge.hessian_tail_lower_bound_of_derivative_field
