import QuantumNLS.HighAngleLinearEvolution
import QuantumNLS.HighAngleSpectralBridge
import QuantumNLS.HighAngleRotations
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! Literal count phases, common diagonal evolution, and the factor-two
marginal comparison on the actual energy subspace. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Complex Filter Topology Set
open scoped BigOperators InnerProductSpace
namespace QuantumNLS.HighAngleEvolutionBridge
open TensorCarrier PhysicalTensor KernelDefinition LinearTailGenerator LinearTailPhysicalEvolution
open HaarSpectralTail HaarNonlinearTail HaarNonlinearAbstract HighAngleReconstruction
open HighAngleLinearEvolution CountRotations HighAngleRotations

/-- Representatives in [-pi,pi], normalized to the unit angle bound. -/
def unitAngle (θ : AngleTorus) (n : ℤ) : ℝ := (θ n : ℂ).arg / Real.pi

lemma unitAngle_le (θ : AngleTorus) (n : ℤ) : |unitAngle θ n| ≤ 1 := by
  rw [unitAngle, abs_div, abs_of_pos Real.pi_pos, div_le_one Real.pi_pos]
  exact abs_le.mpr ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩

lemma unitAngle_zero (θ : AngleTorus) (n : ℤ) (hn : θ n = 1) : unitAngle θ n = 0 := by
  simp [unitAngle, hn]

lemma countPhase_exp {N : ℕ} (a : Finset ℤ) (θ : AngleTorus) (m : BetheLabels.MArr N) :
    (countPhase (truncate a θ) m : ℂ) =
      exp (-((Real.pi * countEigen a (unitAngle θ) m : ℝ) : ℂ) * I) := by
  classical
  let f : ℤ → ℂ := fun n => ((truncate a θ n : Circle) : ℂ)⁻¹ ^ m.val n
  have h1 : (countPhase (truncate a θ) m : ℂ) = ∏ n ∈ m.val.support, f n := by
    change Circle.coeHom (∏ n ∈ m.val.support, (truncate a θ n)⁻¹ ^ m.val n) = _
    rw [map_prod]
    rfl
  have h2 : (∏ n ∈ m.val.support, f n) = ∏ n ∈ m.val.support ∪ a, f n := by
    apply Finset.prod_subset Finset.subset_union_left (fun n hn hnot => ?_)
    simp only [f, Finsupp.notMem_support_iff.mp hnot, pow_zero]
  have h3 : (∏ n ∈ a, f n) = ∏ n ∈ m.val.support ∪ a, f n := by
    apply Finset.prod_subset Finset.subset_union_right (fun n hn hnot => ?_)
    simp only [f, truncate, ite_eq_right hnot, Circle.coe_one, inv_one, one_pow]
  rw [h1, h2, ← h3]
  have hp (n : ℤ) (hn : n ∈ a) :
      f n = exp (-((Real.pi * (unitAngle θ n * (m.val n : ℝ)) : ℝ) : ℂ) * I) := by
    have he : ((θ n : Circle) : ℂ) = exp (((θ n : ℂ).arg : ℂ) * I) := by
      exact congrArg (fun z : Circle => (z : ℂ)) (Circle.exp_arg (θ n)).symm
    dsimp only [f]
    rw [truncate, ite_eq_left hn]
    rw [he, ← Complex.exp_neg, ← Complex.exp_nat_mul]
    congr 1
    unfold unitAngle
    push_cast
    field_simp
  simp_rw [Finset.prod_congr rfl hp]
  rw [← Complex.exp_sum]
  congr 1
  unfold countEigen
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Finset.sum_mul]

section Generic
variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma diagonal_real (b : HilbertBasis ι ℂ H) (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (μ : ι → ℂ) (hμ : ∀ i, A (b i) = μ i • b i) (i : ι) : (μ i : ℂ) = ((μ i).re : ℂ) := by
  have hd := diagC_of_apply hμ
  have hh := hd.adjoint i (b i)
  have ha : ContinuousLinearMap.adjoint A = A := hA
  rw [ha, hd, inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one] at hh
  norm_num at hh
  exact (Complex.conj_eq_iff_re.mp hh.symm).symm

/-- Uniform scalar comparison becomes a vector comparison of the actual
bounded evolutions. No evolution estimate is supplied as an assumption. -/
lemma diagonal_evolution_comparison (b : HilbertBasis ι ℂ H)
    (U : H ≃ₗᵢ[ℂ] H) (A B : H →L[ℂ] H) (x y z : ι → ℝ) (s : ℝ)
    (hU : ∀ i, U (b i) = exp (-(s : ℂ) * (x i : ℂ) * I) • b i)
    (hA : ∀ i, A (b i) = (y i : ℂ) • b i)
    (hB : ∀ i, B (b i) = (z i : ℂ) • b i)
    (S : Set ι) {δ : ℝ} (hδ : 0 ≤ δ) (hb : ∀ i ∈ S, |x i - y i - z i| ≤ δ)
    (ψ : H) (hψ : Supp b S ψ) :
    ‖U ψ - evolution B s (evolution A s ψ)‖ ≤ (|s| * δ) * ‖ψ‖ := by
  let D := U.toContinuousLinearEquiv.toContinuousLinearMap - evolution B s * evolution A s
  have he (i : ι) : D (b i) =
      (exp (-((s * x i : ℝ) : ℂ) * I) - exp (-((s * (y i + z i) : ℝ) : ℂ) * I)) • b i := by
    change U (b i) - evolution B s (evolution A s (b i)) = _
    rw [hU, evolution_eigen A (hA i), map_smul, evolution_eigen B (hB i), smul_smul,
      ← Complex.exp_add, ← sub_smul]
    congr 3 <;> push_cast <;> ring
  exact Prop020Vector.diag_apply_le b D _ he S (mul_nonneg (abs_nonneg _) hδ)
    (fun i hi => (Prop020Vector.norm_exp_sub_le _ _).trans (by
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left (by convert hb i hi using 1; congr 1; ring)
        (abs_nonneg s))) ψ hψ
end Generic

open PeriodReconstructionCore PeriodTwoTerm HaarSummableReconstruction

/-- Exact source decomposition with every contour hypothesis discharged. -/
theorem actual_remainder_identity (L : ℝ) [Fact (0 < L)] {κ E : ℝ}
    (hκ : 0 < κ) (hE : 0 < E) :
    ∃ NE : ℕ, ∃ RE : ℝ, 0 < NE ∧ 2 ≤ RE ∧
      ∀ (N : ℕ) (hN : 0 < N), NE ≤ N →
        ∀ m : BetheLabels.MArr N, m ∈ adm L κ N E →
          ∀ R : ℝ, RE ≤ R → ∀ a : Finset ℤ, (∀ n ∈ a, R < |(n : ℝ)|) →
            ∀ t : ℤ → ℝ,
              (rEig L hκ hN E a t m).re = leadingEigen L κ a t m -
                (N : ℝ) * (LinearTailCommute.genEigen L κ hκ N hN a t m).re := by
  have hL : 0 < L := Fact.out
  obtain ⟨NE, RE, C, hNE, hRE, _, hmain⟩ := haar_summable_reconstruction hL hκ hE
  refine ⟨NE, RE, hNE, hRE, ?_⟩
  intro N hN hNN m hm R hR a ha t
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hact := HaarSpectralTail.sourceRoots_actual hL (div_pos hκ hNr)
    (NormalityBridge.label m).property
  have hen : (N : ℝ)⁻¹ * ∑ j, roots L κ m j ^ 2 ≤ E := by
    have he : ∑ j, roots L κ m j ^ 2 = EnergyProjection.energyEig L κ N (NormalityBridge.label m) := by
      unfold roots EnergyProjection.energyEig
      exact HaarSpectralTail.sum_rev
        (fun j => BetheSmooth.sourceRoots L (NormalityBridge.label m).val (κ / N) j ^ 2)
    rw [he, inv_mul_le_iff₀ hNr]
    exact hm
  obtain ⟨hpt, -, -, -⟩ := hmain N ((NormalityBridge.label m).val ∘ Fin.rev)
    (roots L κ m) hNN hact hen
  have hpoint (n : ℤ) (hn : n ∈ a) (w : ℂ) (hw : w ∈ OffgridBessel.Gamma0 L) :=
    hpt n (hR.trans_lt (ha n hn)) (OffgridCommutator.zpt L w n)
      (Gam_subset_Γ hL n (HaarSpectralTail.zpt_mem hw n))
  have hne : ∀ n ∈ a, ∀ w ∈ OffgridBessel.Gamma0 L,
      ∀ j, OffgridCommutator.zpt L w n ≠ (roots L κ m j : ℂ) := by
    intro n hn w hw j
    apply sub_ne_zero.mp
    apply norm_pos_iff.mp
    exact lt_trans (by positivity : (0 : ℝ) < 2 * |κ / (N : ℝ)|) ((hpoint n hn w hw).1 j)
  have hc : ∀ n ∈ a, ∀ w ∈ OffgridBessel.Gamma0 L,
      ContinuousAt (fun w => log (aNf L κ (κ / N) G0 (roots L κ m)
        (OffgridCommutator.zpt L w n))) w := by
    intro n hn w hw
    obtain ⟨-, -, hnorm, hdiff, -, -, -⟩ := hpoint n hn w hw
    have hre := Complex.abs_re_le_norm
      (aNf L κ (κ / N) G0 (roots L κ m) (OffgridCommutator.zpt L w n) - 1)
    simp only [sub_re, one_re] at hre
    have hp : 0 < (aNf L κ (κ / N) G0 (roots L κ m) (OffgridCommutator.zpt L w n)).re := by
      have hneg := neg_abs_le
        ((aNf L κ (κ / N) G0 (roots L κ m) (OffgridCommutator.zpt L w n)).re - 1)
      linarith
    have hzcont : ContinuousAt (fun v => OffgridCommutator.zpt L v n) w := by
      unfold OffgridCommutator.zpt
      fun_prop
    have hinner : ContinuousAt (fun v : ℂ => aNf L κ (κ / N) G0 (roots L κ m)
        (OffgridCommutator.zpt L v n)) w :=
      ContinuousAt.comp (f := fun v : ℂ => OffgridCommutator.zpt L v n)
        (g := aNf L κ (κ / N) G0 (roots L κ m)) (x := w) hdiff.continuousAt hzcont
    exact ContinuousAt.comp (f := fun v : ℂ => aNf L κ (κ / N) G0 (roots L κ m)
      (OffgridCommutator.zpt L v n)) (g := log) (x := w) (continuousAt_clog (Or.inl hp)) hinner
  exact HighAngleSpectralBridge.remainder_identity L hκ hN E m hm a t hne hc

/-- The bounded leading operator on the energy subspace is exactly the sum
of the actual linear generator and the constructed nonlinear remainder. -/
lemma leading_operator_on_cutoff (L : ℝ) [Fact (0 < L)] {κ E : ℝ}
    (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (a : Finset ℤ) (t : ℤ → ℝ)
    (B : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N)
    (hB : ∀ m, B (bas L hκ hN m) = rEig L hκ hN E a t m • bas L hκ hN m)
    (hid : ∀ m ∈ adm L κ N E, (rEig L hκ hN E a t m).re =
      leadingEigen L κ a t m - N * (LinearTailCommute.genEigen L κ hκ N hN a t m).re)
    (m : BetheLabels.MArr N) (hm : m ∈ adm L κ N E) :
    (((N : ℂ) • genSum L κ N a t) + B) (bas L hκ hN m) =
      (leadingEigen L κ a t m : ℂ) • bas L hκ hN m := by
  let A := (N : ℂ) • genSum L κ N a t
  let μ := fun j => (N : ℂ) * LinearTailCommute.genEigen L κ hκ N hN a t j
  have hA (j : BetheLabels.MArr N) : A (bas L hκ hN j) = μ j • bas L hκ hN j := by
    simp only [A, μ, smul_apply, LinearTailCommute.genSum_meanField, smul_smul]
  have hsa : IsSelfAdjoint A :=
    (show IsSelfAdjoint (N : ℂ) from by simp [isSelfAdjoint_iff]).smul
      (show IsSelfAdjoint (genSum L κ N a t) from by
        simpa only [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint] using
          LinearTailSelfadjoint.genSum_selfadjoint L κ N a t)
  have hreal := diagonal_real (bas L hκ hN) A hsa μ hA m
  change (A + B) _ = _
  rw [add_apply, hA, hB, hreal, ← add_smul]
  congr 1
  apply Complex.ext
  · simp only [Complex.add_re, ofReal_re, μ, Complex.mul_re, natCast_re, natCast_im,
      zero_mul, sub_zero]
    linarith [hid m hm]
  · simp only [rEig, ite_eq_left hm, Complex.add_im, Complex.ofReal_im, add_zero]

/-- The exact bounded-operator comparison, with no decomposition hypothesis. -/
theorem actual_operator_decomposition (L : ℝ) [Fact (0 < L)] {κ E : ℝ}
    (hκ : 0 < κ) (hE : 0 < E) :
    ∃ NE : ℕ, ∃ RE : ℝ, 0 < NE ∧ 2 ≤ RE ∧
      ∀ (N : ℕ) (hN : 0 < N), NE ≤ N → ∀ R : ℝ, RE ≤ R →
        ∀ a : Finset ℤ, (∀ n ∈ a, R < |(n : ℝ)|) → ∀ t : ℤ → ℝ,
          ∀ B : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N,
            (∀ m, B (bas L hκ hN m) = rEig L hκ hN E a t m • bas L hκ hN m) →
            ∀ m ∈ adm L κ N E,
              (((N : ℂ) • genSum L κ N a t) + B) (bas L hκ hN m) =
                (leadingEigen L κ a t m : ℂ) • bas L hκ hN m := by
  obtain ⟨NE, RE, hNE, hRE, hid⟩ := actual_remainder_identity L hκ hE
  refine ⟨NE, RE, hNE, hRE, ?_⟩
  intro N hN hNN R hR a ha t B hB m hm
  exact leading_operator_on_cutoff L hκ hN a t B hB
    (fun j hj => hid N hN hNN j hj R hR a ha t) m hm

end QuantumNLS.HighAngleEvolutionBridge

#print axioms QuantumNLS.HighAngleEvolutionBridge.unitAngle
#print axioms QuantumNLS.HighAngleEvolutionBridge.unitAngle_le
#print axioms QuantumNLS.HighAngleEvolutionBridge.unitAngle_zero
#print axioms QuantumNLS.HighAngleEvolutionBridge.countPhase_exp
#print axioms QuantumNLS.HighAngleEvolutionBridge.diagonal_real
#print axioms QuantumNLS.HighAngleEvolutionBridge.diagonal_evolution_comparison
#print axioms QuantumNLS.HighAngleEvolutionBridge.actual_remainder_identity
#print axioms QuantumNLS.HighAngleEvolutionBridge.leading_operator_on_cutoff

#print axioms QuantumNLS.HighAngleEvolutionBridge.actual_operator_decomposition

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.HighAngleEvolutionBridge." then
      pending := pending.push n
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
