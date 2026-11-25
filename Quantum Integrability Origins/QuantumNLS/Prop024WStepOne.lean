import QuantumNLS.Prop024AssemblyR58
import QuantumNLS.Prop021RemainderInputR131
import QuantumNLS.MixedCommutator
import QuantumNLS.Prop024WSeries

/-! PROP-024 step (1): the operator-level Wick expansion of the pulled-back interaction (Prop024WStepOne).

`stepOne_core`: for a factorial kernel family `B`, a unit profile `u`, `N ≥ 256 e A Q` and a smooth vector `x` with the printed polynomial number-moment bounds `‖(N+j)^{j/2} x‖ ≤ (32 Q j)^{j/2}`, the translated vector `W(√N u) x` belongs to the maximal domain of the actual physical interaction `interaction N B` (the source's own argument: the Hilbert-norm convergent cell series has the interaction's sector components) and
`W(√N u)⁻¹ H_N W(√N u) x = constScalar • x + linVec + quadVec + remVec`,
the sums over all interaction orders of the Wick cells `N^{1-(a+b)/2} C(m,a) C(m,b) 𝒲_{a,b}(contractedKernel m a b)` of total degree 0, 1, 2 and ≥ 3.  `stepOneIdentification` / `stepOneIdentification_explicit` are this statement in exactly the form of `hStepOneIdentificationInput` of `Prop024AssemblyR58.prop024_intermediate_scaffold`; `translatedDomain_of_moments` discharges its `hTranslatedDomainInput`. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
open scoped InnerProductSpace ComplexConjugate Topology
open Filter
namespace QuantumNLS.Prop024WStepOne
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors Ext006PhysFockCoord
open Prop024WWeylPhysical Prop022TensorCompressionR115 Ext006NumberPhase
open Prop024WBlock Prop024WSector Prop024WWords Prop024WOrder Prop024WNorms Prop024WSeries
open Prop024ContractionsR54 Prop024PhysicalHamiltonianR54 Prop024WickCellsR54
open Prop022FactorialCoefficientsR115 Prop024HilbertConjugationR58 Prop022OVacuum
variable {L : ℝ} [Fact (0 < L)]

lemma fallingScale_mul (N m k : ℕ) :
    (((N : ℝ) / (N : ℝ) ^ m : ℝ) * wickCoeff m m k) = (N : ℝ) * fallingScale N (m + k) m := by
  unfold fallingScale
  rw [wickCoeff_balanced]
  have hk : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hb : ((m+k).factorial : ℝ) = (k.factorial : ℝ) * (((m+k).descFactorial m : ℕ) : ℝ) := by
    have := Nat.factorial_mul_descFactorial (show m ≤ m + k by omega)
    rw [Nat.add_sub_cancel_left] at this
    exact_mod_cast this.symm
  rw [hb]
  field_simp

lemma orderVec_sector_ge (N m : ℕ) (Bm : HN L m →L[ℂ] HN L m) {z : Fock L} (hz : MomentFinite z)
    (n : ℕ) (hmn : m ≤ n) :
    (orderVec N m Bm z) n =
      (N : ℂ) • ((fallingScale N n m : ℝ) : ℂ) •
        (PhysicalPlacements.physicalQ_N_p L n m hmn Bm) (z n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  unfold orderVec
  change (((N : ℝ) / (N : ℝ) ^ m : ℝ) : ℂ) • (wickFock m m Bm z) (m + k) = _
  rw [wickFock_sector m m Bm hz k, wickBlock_balanced, smul_smul]
  have h1 : PhysicalPlacements.physicalQ_N_p L (m + k) m hmn Bm = KernelDefinition.U_N_r (r := m) (q := k) Bm := by
    change KernelDefinition.physicalU_N_r L (m + k) m hmn Bm = _
    rw [PlacementConsistency.physicalU_N_r_eq_genericU_N_r, QuantumNLS.MixedCommutator.genericU_add_eq]
  rw [h1, smul_smul]
  congr 1
  have := fallingScale_mul N m k
  have := congrArg (fun r : ℝ => (r : ℂ)) this
  simpa using this

lemma orderVec_sector_lt (N m : ℕ) (Bm : HN L m →L[ℂ] HN L m) {z : Fock L} (hz : MomentFinite z)
    (n : ℕ) (hn : n < m) : (orderVec N m Bm z) n = 0 := by
  unfold orderVec
  change (((N : ℝ) / (N : ℝ) ^ m : ℝ) : ℂ) • (wickFock m m Bm z) n = 0
  rw [wickFock_sector_lt m m Bm hz n hn, smul_zero]


lemma interactionSector_eq_orders (N n : ℕ) (B : ∀ m, HN L m →L[ℂ] HN L m) {z : Fock L}
    (hz : MomentFinite z) :
    interactionSector N n B (z n) = ∑ m ∈ Finset.range n, (orderVec N (m + 1) (B (m + 1)) z) n := by
  unfold interactionSector
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, Finset.smul_sum]
  rw [← Fin.sum_univ_eq_sum_range (fun m => (orderVec N (m + 1) (B (m + 1)) z) n) n]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hmn : i.val + 1 ≤ n := Nat.succ_le_of_lt i.isLt
  rw [orderVec_sector_ge N (i.val + 1) (B (i.val + 1)) hz n hmn]
  rfl

/-- **The pulled-back interaction is the sum of the Wick cells.**  Let `B` be a factorial family,
`u` a unit profile, `N ≥ 256 e A Q`, and `x` a smooth vector with the printed polynomial number-moment
bounds.  Then the translated vector `W(√N u) x` lies in the maximal domain of the physical interaction
and `W(√N u)⁻¹ H_N W(√N u) x = constScalar • x + linVec + quadVec + remVec`. -/
theorem stepOne_core (N : ℕ) (hN : 0 < N) (B : ∀ r, HN L r →L[ℂ] HN L r) (M A Q : ℝ)
    (hM : 0 ≤ M) (hA : 0 < A) (hQ : 1 ≤ Q) (hNQ : 256 * Real.exp 1 * A * Q ≤ N)
    (hB : FactorialBound B M A) (u : L2T L) (hu : ‖u‖ = 1) (x : physSmooth L)
    (hMom : PolyMoments Q x.1) :
    ∃ hz : physicalWeyl N u x.1 ∈ (interaction N B).domain,
      pulledInteraction N u B x.1 hz =
        constScalar N B u • x.1 + linVec N B u x.1 + quadVec N B u x.1 + remVec N B u x.1 := by
  set Y := constScalar N B u • x.1 + linVec N B u x.1 + quadVec N B u x.1 + remVec N B u x.1 with hY
  have hsum := hasSum_cellSum N hN B M A Q hM hA hQ hNQ hB u hu x hMom
  set v : L2T L := ((Real.sqrt (N : ℝ) : ℝ) : ℂ) • u with hv
  have hW : ∀ w : Fock L, physicalWeyl N u w = Prop022OVacuum.printedWeyl v w :=
    fun w => Prop024WeylConventionR55.physicalWeyl_eq_printedWeyl N u w
  have hzmem : physicalWeyl N u x.1 ∈ physSmooth L := (physicalWeyl_mem_physSmooth_iff N u x.1).mpr x.2
  set z : physSmooth L := ⟨physicalWeyl N u x.1, hzmem⟩ with hzdef
  have hzfin : MomentFinite z.1 := momentFinite_of_mem z
  -- apply the unitary
  let Wc : Fock L →L[ℂ] Fock L :=
    (Prop022OVacuum.printedWeyl v).toContinuousLinearEquiv.toContinuousLinearMap
  have hord : ∀ m : ℕ, 0 < m + 1 → Wc (cellSum N (m + 1) (B (m + 1)) u x.1) =
      orderVec N (m + 1) (B (m + 1)) z.1 := by
    intro m _
    have h := perOrder N (m + 1) hN u x (B (m + 1))
    unfold lhsOrder at h
    have h2 := congrArg (Prop022OVacuum.printedWeyl v) h
    rw [LinearIsometryEquiv.apply_symm_apply] at h2
    change Prop022OVacuum.printedWeyl v (cellSum N (m + 1) (B (m + 1)) u x.1) = _
    rw [← h2]
    exact congrArg (orderVec N (m + 1) (B (m + 1))) (hW x.1).symm
  have hWsum : HasSum (fun m : ℕ => orderVec N (m + 1) (B (m + 1)) z.1) (Wc Y) := by
    have h1 := Wc.hasSum hsum
    have hfun : (fun m : ℕ => Wc (cellSum N (m + 1) (B (m + 1)) u x.1)) =
        fun m : ℕ => orderVec N (m + 1) (B (m + 1)) z.1 := funext fun m => hord m (by omega)
    rw [hfun] at h1
    exact h1
  have hsec : ∀ n : ℕ, (Wc Y : Fock L) n = interactionSector N n B (z.1 n) := by
    intro n
    have h1 : HasSum (fun m : ℕ => (orderVec N (m + 1) (B (m + 1)) z.1 : Fock L) n) ((Wc Y : Fock L) n) :=
      (lp.evalCLM ℂ (fun N => HN L N) 2 n).hasSum hWsum
    have h2 : HasSum (fun m : ℕ => (orderVec N (m + 1) (B (m + 1)) z.1 : Fock L) n)
        (∑ m ∈ Finset.range n, (orderVec N (m + 1) (B (m + 1)) z.1 : Fock L) n) :=
      hasSum_sum_of_ne_finset_zero (fun m hm => by
        simp only [Finset.mem_range, not_lt] at hm
        exact orderVec_sector_lt N (m + 1) _ hzfin n (by omega))
    rw [h1.unique h2, interactionSector_eq_orders N n B hzfin]
  have hmem : Memℓp (fun n => interactionSector N n B (z.1 n)) 2 := by
    have heq : (fun n => interactionSector N n B (z.1 n)) = (Wc Y : ∀ n, HN L n) :=
      funext fun n => (hsec n).symm
    rw [heq]
    exact (Wc Y).2
  have hz : physicalWeyl N u x.1 ∈ (interaction N B).domain :=
    (interaction_mem_domain_iff N B (physicalWeyl N u x.1)).mpr hmem
  refine ⟨hz, ?_⟩
  have hint : interaction N B ⟨physicalWeyl N u x.1, hz⟩ = Wc Y := by
    apply lp.ext
    funext n
    rw [interaction_apply_sector]
    exact (hsec n).symm
  unfold pulledInteraction
  rw [hint]
  have hWY : Wc Y = physicalWeyl N u Y := (hW Y).symm
  rw [hWY, LinearIsometryEquiv.symm_apply_apply]


/-- Polynomial moment bounds give the common smooth domain. -/
lemma mem_physSmooth_of_polyMoments (Q : ℝ) (x : Fock L) (hm : PolyMoments Q x) : x ∈ physSmooth L := by
  rw [mem_physSmooth_iff_moments]
  intro j
  rw [Ext005Moments.momentDomain_iff]
  cases j with
  | zero =>
      have h := (lp.hasSum_norm (p := 2) (by norm_num) x).summable
      simpa only [Ext005Moments.momentWeight, pow_zero, one_mul, ENNReal.toReal_ofNat, Real.rpow_two] using h
  | succ j =>
      obtain ⟨hdom, _⟩ := hm (j+1) (by omega)
      have hs := (hasSum_polyRoot (j+1) ⟨x, hdom⟩).summable
      refine Summable.of_nonneg_of_le (fun n => mul_nonneg (Ext005Moments.momentWeight_nonneg _ _) (sq_nonneg _)) ?_ hs
      intro n
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      unfold Ext005Moments.momentWeight
      exact pow_le_pow_left₀ (by positivity) (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) j]) _

lemma polyMoments_of_numberMoments (Q : ℝ) (x : Fock L)
    (h : Prop021RemainderInputR131.NumberMoments Q x) : PolyMoments Q x := h.2


/-- **PROP-024 step (1): the translated domain, from the printed moment bounds.**  The
`hTranslatedDomainInput` of `Prop024AssemblyR58.prop024_intermediate_scaffold` holds for every `t`
for which the propagated vacuum `V(t,0) Ω` has the printed polynomial number-moment bounds. -/
theorem translatedDomain_of_moments
    (N : ℕ) (K : ∀ n, HN L (n+1) →L[ℂ] HN L (n+1)) (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A)
    (hK : ∀ n, ‖K n‖ ≤ M * A ^ (n+1) / Real.sqrt ((2*(n+1)).factorial : ℝ))
    (hsK : ∀ n, (K n).adjoint = K n) (u₀ : Prop001.Sphere (L2T L)) (T Q : ℝ) (hQ : 1 ≤ Q)
    (hN : 0 < N) (hNQ : 256 * Real.exp 1 * A * Q ≤ N)
    (hMoments :
      let B := Prop022PositiveDataR126.positiveExtension K
      let hB := Prop022PositiveDataR126.positiveExtension_bound K M A hK
      let hsa := Prop022PositiveDataR126.positiveExtension_selfAdjoint K hsK
      let u := Prop022ActualProfileR117.profile B M A hA.le hB hsa u₀
      let V := fun t s : ℝ => Prop022FockPropagatorR122.propagator B M A
        (by linarith) hA.le hB hsa u₀ s t
      ∀ t : ℝ, |t| ≤ T → PolyMoments Q (V t 0 vac)) :
    let B := Prop022PositiveDataR126.positiveExtension K
    let hB := Prop022PositiveDataR126.positiveExtension_bound K M A hK
    let hsa := Prop022PositiveDataR126.positiveExtension_selfAdjoint K hsK
    let u := Prop022ActualProfileR117.profile B M A hA.le hB hsa u₀
    let V := fun t s : ℝ => Prop022FockPropagatorR122.propagator B M A
      (by linarith) hA.le hB hsa u₀ s t
    ∀ t : ℝ, |t| ≤ T → physicalWeyl N (u t) (V t 0 vac) ∈ (interaction N B).domain := by
  intro B hB hsa u V t ht
  have hmom : PolyMoments Q (V t 0 vac) := hMoments t ht
  have hu : ‖u t‖ = 1 := (Prop022ActualProfileR117.profile_spec B M A hA.le hB hsa u₀).2.2.1 t
  have hsm : V t 0 vac ∈ physSmooth L := mem_physSmooth_of_polyMoments Q _ hmom
  obtain ⟨hz, _⟩ := stepOne_core N hN B M A Q (by linarith) hA hQ hNQ hB (u t) hu ⟨_, hsm⟩ hmom
  exact hz

/-- **PROP-024 step (1), the identification of the pulled-back interaction.**  This is exactly the
`hStepOneIdentificationInput` of `Prop024AssemblyR58.prop024_intermediate_scaffold`, with
`constantTerm t = constScalar N B (u t)`, `linearTerm t = linVec N B (u t) (V t 0 vac)`,
`quadraticTerm t = quadVec N B (u t) (V t 0 vac)`, `remainderTerm t = remVec N B (u t) (V t 0 vac)`:
the constant, linear, quadratic and entire Wick-remainder vectors, defined as the sums over all
interaction orders `m` of the cells `N^{1-(a+b)/2} C(m,a) C(m,b) 𝒲_{a,b}(contractedKernel m a b)`
of total degree `0`, `1`, `2`, `≥ 3`.  The hypothesis `hMoments` is the printed number-moment bound
of `Q7B:eq:mgf` (`Prop021RemainderInputR131.NumberMoments.2`, supplied by luna's `actual_moments`). -/
theorem stepOneIdentification
    (N : ℕ) (K : ∀ n, HN L (n+1) →L[ℂ] HN L (n+1)) (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A)
    (hK : ∀ n, ‖K n‖ ≤ M * A ^ (n+1) / Real.sqrt ((2*(n+1)).factorial : ℝ))
    (hsK : ∀ n, (K n).adjoint = K n) (u₀ : Prop001.Sphere (L2T L)) (T Q : ℝ) (hQ : 1 ≤ Q)
    (hN : 0 < N) (hNQ : 256 * Real.exp 1 * A * Q ≤ N)
    (hMoments :
      let B := Prop022PositiveDataR126.positiveExtension K
      let hB := Prop022PositiveDataR126.positiveExtension_bound K M A hK
      let hsa := Prop022PositiveDataR126.positiveExtension_selfAdjoint K hsK
      let u := Prop022ActualProfileR117.profile B M A hA.le hB hsa u₀
      let V := fun t s : ℝ => Prop022FockPropagatorR122.propagator B M A
        (by linarith) hA.le hB hsa u₀ s t
      ∀ t : ℝ, |t| ≤ T → PolyMoments Q (V t 0 vac))
    (constantTerm : ℝ → ℂ) (linearTerm quadraticTerm remainderTerm : ℝ → Fock L)
    (hTranslatedDomainInput :
      let B := Prop022PositiveDataR126.positiveExtension K
      let hB := Prop022PositiveDataR126.positiveExtension_bound K M A hK
      let hsa := Prop022PositiveDataR126.positiveExtension_selfAdjoint K hsK
      let u := Prop022ActualProfileR117.profile B M A hA.le hB hsa u₀
      let V := fun t s : ℝ => Prop022FockPropagatorR122.propagator B M A
        (by linarith) hA.le hB hsa u₀ s t
      ∀ t : ℝ, |t| ≤ T → physicalWeyl N (u t) (V t 0 vac) ∈ (interaction N B).domain)
    (hconst :
      let B := Prop022PositiveDataR126.positiveExtension K
      let hB := Prop022PositiveDataR126.positiveExtension_bound K M A hK
      let hsa := Prop022PositiveDataR126.positiveExtension_selfAdjoint K hsK
      let u := Prop022ActualProfileR117.profile B M A hA.le hB hsa u₀
      ∀ t : ℝ, constantTerm t = constScalar N B (u t))
    (hlin :
      let B := Prop022PositiveDataR126.positiveExtension K
      let hB := Prop022PositiveDataR126.positiveExtension_bound K M A hK
      let hsa := Prop022PositiveDataR126.positiveExtension_selfAdjoint K hsK
      let u := Prop022ActualProfileR117.profile B M A hA.le hB hsa u₀
      let V := fun t s : ℝ => Prop022FockPropagatorR122.propagator B M A
        (by linarith) hA.le hB hsa u₀ s t
      ∀ t : ℝ, linearTerm t = linVec N B (u t) (V t 0 vac))
    (hquad :
      let B := Prop022PositiveDataR126.positiveExtension K
      let hB := Prop022PositiveDataR126.positiveExtension_bound K M A hK
      let hsa := Prop022PositiveDataR126.positiveExtension_selfAdjoint K hsK
      let u := Prop022ActualProfileR117.profile B M A hA.le hB hsa u₀
      let V := fun t s : ℝ => Prop022FockPropagatorR122.propagator B M A
        (by linarith) hA.le hB hsa u₀ s t
      ∀ t : ℝ, quadraticTerm t = quadVec N B (u t) (V t 0 vac))
    (hrem :
      let B := Prop022PositiveDataR126.positiveExtension K
      let hB := Prop022PositiveDataR126.positiveExtension_bound K M A hK
      let hsa := Prop022PositiveDataR126.positiveExtension_selfAdjoint K hsK
      let u := Prop022ActualProfileR117.profile B M A hA.le hB hsa u₀
      let V := fun t s : ℝ => Prop022FockPropagatorR122.propagator B M A
        (by linarith) hA.le hB hsa u₀ s t
      ∀ t : ℝ, remainderTerm t = remVec N B (u t) (V t 0 vac)) :
    let B := Prop022PositiveDataR126.positiveExtension K
    let hB := Prop022PositiveDataR126.positiveExtension_bound K M A hK
    let hsa := Prop022PositiveDataR126.positiveExtension_selfAdjoint K hsK
    let u := Prop022ActualProfileR117.profile B M A hA.le hB hsa u₀
    let V := fun t s : ℝ => Prop022FockPropagatorR122.propagator B M A
      (by linarith) hA.le hB hsa u₀ s t
    ∀ t : ℝ, ∀ ht : |t| ≤ T,
      pulledInteraction N (u t) B (V t 0 vac) (hTranslatedDomainInput t ht) =
        constantTerm t • (V t 0 vac) + linearTerm t +
          quadraticTerm t + remainderTerm t := by
  intro B hB hsa u V t ht
  have hmom : PolyMoments Q (V t 0 vac) := hMoments t ht
  have hu : ‖u t‖ = 1 := (Prop022ActualProfileR117.profile_spec B M A hA.le hB hsa u₀).2.2.1 t
  have hsm : V t 0 vac ∈ physSmooth L := mem_physSmooth_of_polyMoments Q _ hmom
  obtain ⟨hz, hid⟩ := stepOne_core N hN B M A Q (by linarith) hA hQ hNQ hB (u t) hu ⟨_, hsm⟩ hmom
  have h1 : pulledInteraction N (u t) B (V t 0 vac) (hTranslatedDomainInput t ht) =
      pulledInteraction N (u t) B (V t 0 vac) hz := rfl
  rw [h1, hid, hconst t, hlin t, hquad t, hrem t]


/-- The same identification with the four terms written out (no term-function hypotheses):
the explicit instance of `hStepOneIdentificationInput` for
`constantTerm t = constScalar N B (u t)`, `linearTerm t = linVec N B (u t) (V t 0 vac)`,
`quadraticTerm t = quadVec N B (u t) (V t 0 vac)`, `remainderTerm t = remVec N B (u t) (V t 0 vac)`. -/
theorem stepOneIdentification_explicit
    (N : ℕ) (K : ∀ n, HN L (n+1) →L[ℂ] HN L (n+1)) (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A)
    (hK : ∀ n, ‖K n‖ ≤ M * A ^ (n+1) / Real.sqrt ((2*(n+1)).factorial : ℝ))
    (hsK : ∀ n, (K n).adjoint = K n) (u₀ : Prop001.Sphere (L2T L)) (T Q : ℝ) (hQ : 1 ≤ Q)
    (hN : 0 < N) (hNQ : 256 * Real.exp 1 * A * Q ≤ N)
    (hMoments :
      let B := Prop022PositiveDataR126.positiveExtension K
      let hB := Prop022PositiveDataR126.positiveExtension_bound K M A hK
      let hsa := Prop022PositiveDataR126.positiveExtension_selfAdjoint K hsK
      let u := Prop022ActualProfileR117.profile B M A hA.le hB hsa u₀
      let V := fun t s : ℝ => Prop022FockPropagatorR122.propagator B M A
        (by linarith) hA.le hB hsa u₀ s t
      ∀ t : ℝ, |t| ≤ T → PolyMoments Q (V t 0 vac))
    (hTranslatedDomainInput :
      let B := Prop022PositiveDataR126.positiveExtension K
      let hB := Prop022PositiveDataR126.positiveExtension_bound K M A hK
      let hsa := Prop022PositiveDataR126.positiveExtension_selfAdjoint K hsK
      let u := Prop022ActualProfileR117.profile B M A hA.le hB hsa u₀
      let V := fun t s : ℝ => Prop022FockPropagatorR122.propagator B M A
        (by linarith) hA.le hB hsa u₀ s t
      ∀ t : ℝ, |t| ≤ T → physicalWeyl N (u t) (V t 0 vac) ∈ (interaction N B).domain) :
    let B := Prop022PositiveDataR126.positiveExtension K
    let hB := Prop022PositiveDataR126.positiveExtension_bound K M A hK
    let hsa := Prop022PositiveDataR126.positiveExtension_selfAdjoint K hsK
    let u := Prop022ActualProfileR117.profile B M A hA.le hB hsa u₀
    let V := fun t s : ℝ => Prop022FockPropagatorR122.propagator B M A
      (by linarith) hA.le hB hsa u₀ s t
    ∀ t : ℝ, ∀ ht : |t| ≤ T,
      pulledInteraction N (u t) B (V t 0 vac) (hTranslatedDomainInput t ht) =
        constScalar N B (u t) • (V t 0 vac) + linVec N B (u t) (V t 0 vac) +
          quadVec N B (u t) (V t 0 vac) + remVec N B (u t) (V t 0 vac) := by
  intro B hB hsa u V t ht
  have hmom : PolyMoments Q (V t 0 vac) := hMoments t ht
  have hu : ‖u t‖ = 1 := (Prop022ActualProfileR117.profile_spec B M A hA.le hB hsa u₀).2.2.1 t
  have hsm : V t 0 vac ∈ physSmooth L := mem_physSmooth_of_polyMoments Q _ hmom
  obtain ⟨hz, hid⟩ := stepOne_core N hN B M A Q (by linarith) hA hQ hNQ hB (u t) hu ⟨_, hsm⟩ hmom
  exact hid

end QuantumNLS.Prop024WStepOne

#print axioms QuantumNLS.Prop024WStepOne.orderVec_sector_ge
#print axioms QuantumNLS.Prop024WStepOne.interactionSector_eq_orders
#print axioms QuantumNLS.Prop024WStepOne.stepOne_core
#print axioms QuantumNLS.Prop024WStepOne.translatedDomain_of_moments
#print axioms QuantumNLS.Prop024WStepOne.stepOneIdentification
#print axioms QuantumNLS.Prop024WStepOne.stepOneIdentification_explicit
#print axioms QuantumNLS.Prop024WStepOne.mem_physSmooth_of_polyMoments

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop024WStepOne." ||
        n.toString.startsWith "_private.QuantumNLS.Prop024WStepOne." then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").any (fun s => s == "HeldGP14Tonelli" || s == "RegularCut") then
        throwError "Held identifier in dependency closure: {n}"
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
  Lean.logInfo m!"Prop024WStepOne aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard axioms only."
