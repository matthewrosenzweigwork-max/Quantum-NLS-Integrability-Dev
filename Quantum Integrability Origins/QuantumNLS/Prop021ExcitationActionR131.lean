import QuantumNLS.Prop021ExcitationFockR130
import QuantumNLS.Prop022OFormIdentity

/-! The excitation Hamiltonian is precisely the number-preserving
quadratic operator at the complementary condensate projection. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
open scoped InnerProductSpace
namespace QuantumNLS.Prop021ExcitationActionR131

open PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Prop021ExcitationR130 Prop021ExcitationFockR130
open Ext005QuadraticEnergyR108 Ext005Moments Ext005FormCutoffR109 Ext005MomentEnergyR108
open Ext005FormScaleR109 Ext005PhysicalNumberFormR114
open Prop022StrongOperatorR125 Prop022OQuadraticKet Prop022OWeakIdentity
open Prop022PrintedCoefficientsR124 Ext006KernelHilbertSchmidt Ext006PhysFockCoord
variable {L : ℝ} [Fact (0 < L)]

/-- The two independently defined sector operators coincide term-for-term. -/
theorem excitation_eq_numberBlock (u : L2T L) (n : ℕ) :
    excitation u n = numberBlock (q u) n := by
  unfold excitation average numberBlock
  by_cases h : 1 ≤ n
  · simp only [dite_eq_left h]
    congr 1
    exact (PlacementConsistency.physicalU_N_r_eq_genericU_N_r L n 1 h (q u)).symm
  · simp only [dite_eq_right h]
    apply ContinuousLinearMap.ext
    intro z
    change (n : ℂ) • (0 : HN L n) = 0
    exact smul_zero (n : ℂ)

private lemma lower_pair_zero (j : ℕ) (hj : 1 ≤ j) :
    lower (L := L) j hj (0 : HN L 2) = 0 := by
  simpa only [sub_self] using lower_sub j hj (0 : HN L 2) 0

/-- The literal number-preserving quadratic action with zero pair term. -/
theorem Qp_eq_number (a : HN L 1 →L[ℂ] HN L 1) (x : Fock L) :
    Qp a 0 x = numberCoordinates a (rootLift 2 x) := by
  simp [Qp, strongCoordinates, lower_pair_zero]

private lemma Qp_excitation_sector (u : L2T L) (x : Fock L)
    (hx : x ∈ momentDomain (L := L) 2) (n : ℕ) :
    Qp (q u) 0 x n = excitation u n (x n) := by
  have he : embedding 2 (rootLift 2 x) = x := by
    rw [rootLift_eq 2 x hx]
    exact embedding_root 2 ⟨x,hx⟩
  rw [Qp_eq_number, numberCoordinates_two, excitation_eq_numberBlock]
  exact congrArg (fun y : Fock L => numberBlock (q u) n (y n)) he

/-- The constructed physical excitation block acts on the entire second
number-moment domain, including all smooth vectors. -/
theorem moment_mem_D (u : L2T L) (x : Fock L) (hx : x ∈ momentDomain (L := L) 2) :
    x ∈ (Prop021ExcitationFockR130.D u).domain := by
  change Memℓp (fun n => excitation u n (x n)) 2
  simpa only [← Qp_excitation_sector u x hx] using lp.memℓp (Qp (q u) 0 x)

/-- Exact action equality on that domain, with the same Fock vector in
both descriptions. -/
theorem D_eq_Qp (u : L2T L) (x : Fock L) (hx : x ∈ momentDomain (L := L) 2) :
    Prop021ExcitationFockR130.D u ⟨x,moment_mem_D u x hx⟩ = Qp (q u) 0 x := by
  apply lp.ext
  funext n
  show excitation u n (x n) = _
  exact (Qp_excitation_sector u x hx n).symm

/-- The unbounded action has linear sector growth and preserves the
intersection of all number-moment domains. -/
theorem D_preserves_moments (u : L2T L) (hu : ‖u‖ = 1) (x : Fock L)
    (hx : ∀ j, x ∈ momentDomain (L := L) j) (j : ℕ) :
    Prop021ExcitationFockR130.D u ⟨x,moment_mem_D u x (hx 2)⟩ ∈ momentDomain (L := L) j := by
  rw [momentDomain_iff]
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (momentWeight_nonneg _ _) (sq_nonneg _))
    _ ((momentDomain_iff _ _).mp (hx (j+2)))
  intro n
  change momentWeight j n * ‖excitation u n (x n)‖^2 ≤ momentWeight (j+2) n * ‖x n‖^2
  have hnorm : ‖excitation u n (x n)‖ ≤ ((n : ℝ)+1) * ‖x n‖ := by
    rw [excitation, smul_apply, norm_smul, Complex.norm_natCast]
    have hb := (ContinuousLinearMap.le_opNorm (average u n) (x n)).trans
      (mul_le_mul_of_nonneg_right (average_norm u hu n) (norm_nonneg _))
    rw [one_mul] at hb
    exact (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  have he := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm 2)
    (momentWeight_nonneg j n)
  exact he.trans_eq (by simp only [momentWeight, pow_add, mul_pow]; ring)

/-- The actual one-particle generator annihilates the condensate. -/
theorem aOp_q_condensate (u : L2T L) (hu : ‖u‖ = 1) :
    aOp (q u) u = 0 := by
  have eq : oneEmbedding u = condensate u :=
    oneEmbedding_apply u
  simp [aOp, eq, q_condensate u hu]

/-- The maximal Fock root norm equals the literal excitation expectation
on the operator domain, whenever the vector also lies in the root domain. -/
theorem root_inner_eq (u : L2T L) (hu : ‖u‖ = 1) (x : Fock L)
    (hD : x ∈ (Prop021ExcitationFockR130.D u).domain)
    (hR : x ∈ (root u).domain) :
    ⟪x, Prop021ExcitationFockR130.D u ⟨x,hD⟩⟫_ℂ =
      (‖root u ⟨x,hR⟩‖ : ℂ)^2 := by
  let z := root u ⟨x,hR⟩
  have hz : ⟪z,z⟫_ℂ = (‖z‖ : ℂ)^2 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) z
  change ⟪x, Prop021ExcitationFockR130.D u ⟨x,hD⟩⟫_ℂ = (‖z‖ : ℂ)^2
  rw [← hz, lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  change ⟪x n,excitation u n (x n)⟫_ℂ =
    ⟪excitationRoot u n (x n),excitationRoot u n (x n)⟫_ℂ
  have he := congrArg (fun A : HN L n →L[ℂ] HN L n => A (x n))
    (excitationRoot_sq u hu n)
  calc
    _ = ⟪x n,excitationRoot u n (excitationRoot u n (x n))⟫_ℂ :=
      congrArg (fun y : HN L n => ⟪x n,y⟫_ℂ) he.symm
    _ = _ := by
      have h := ContinuousLinearMap.adjoint_inner_right (excitationRoot u n) (x n)
        (excitationRoot u n (x n))
      rwa [(excitationRoot_positive u n).isSelfAdjoint.adjoint_eq] at h

end QuantumNLS.Prop021ExcitationActionR131

#print axioms QuantumNLS.Prop021ExcitationActionR131.D_eq_Qp
#print axioms QuantumNLS.Prop021ExcitationActionR131.D_preserves_moments
#print axioms QuantumNLS.Prop021ExcitationActionR131.root_inner_eq

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if ["Prop021ExcitationActionR131"].any
        (fun m => n.toString.startsWith ("QuantumNLS." ++ m ++ ".") ||
          n.toString.startsWith ("_private.QuantumNLS." ++ m ++ ".")) then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").contains "HeldGP14Tonelli" ||
          (n.toString.splitOn ".").contains "RegularCut" then
        throwError "Forbidden held dependency: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"R131 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
