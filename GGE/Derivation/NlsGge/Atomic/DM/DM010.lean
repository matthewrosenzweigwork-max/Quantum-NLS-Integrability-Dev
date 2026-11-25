import NlsGge.Atomic.Support.DMResolventLattice
import NlsGge.Atomic.KST.KST005
import NlsGge.Atomic.LIB.LIB031
import NlsGge.Atomic.LIB.LIB033
import NlsGge.Atomic.LIB.LIB036
import NlsGge.Atomic.LIB.LIB037
import NlsGge.Atomic.DM.DM001
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
noncomputable section
open Set
open scoped BigOperators
namespace NlsGge.Atomic.DM010
open NlsGge.Schur NlsGge.Atomic.Interval NlsGge.Atomic.LIB031 NlsGge.Atomic.LIB036

/-- The distinct free frequencies appearing in the paper's parity resolvent sum. -/
def dmFrequencySet : ZSBoundaryCondition → Set ℤ
  | .periodic => {k | k % 2 = 0}
  | .antiperiodic => {k | k % 2 = 1}
  | _ => ∅

/-- One scalar index per distinct spectral frequency; the two physical channels are grouped later. -/
abbrev DMFrequency (bc : ZSBoundaryCondition) := {k : ℤ // k ∈ dmFrequencySet bc}

/-- The source-frequency set obtained from the repository's actual free basis labels. -/
def dmSourceFrequencySet (bc : ZSBoundaryCondition) : Set ℂ :=
  Set.range (fun i : FreeIndex bc => (freeFrequency bc i : ℂ))

/-- Source parameter `n+x+it`; `n` is signed and zero is permitted. -/
def dmLambda (n : ℤ) (x t : ℝ) : ℂ := (n : ℂ) + (x : ℂ) + Complex.I * (t : ℂ)

/-- One distinct-frequency summand in the source scalar resolvent sum. -/
def dmLatticeTerm (bc : ZSBoundaryCondition) («λ» : ℂ) (k : DMFrequency bc) : ℝ :=
  1 / ‖«λ» - (k.val : ℂ)‖ ^ 2

/-- Source scalar resolvent sum, defined only after its summability is proved at its uses. -/
def dmLatticeSum (bc : ZSBoundaryCondition) («λ» : ℂ) : ℝ :=
  ∑' k : DMFrequency bc, dmLatticeTerm bc «λ» k

/-- The real-coordinate form of one full-lattice resolvent weight. -/
def dmRealLatticeTerm (x t : ℝ) (d : ℤ) : ℝ :=
  1 / ((x - (d : ℝ)) ^ 2 + t ^ 2)

/-- Totalized finite branch for the paper's `min(1,1/|t|)` tail profile. -/
def dmTailProfile (t : ℝ) : ℝ := if 1 ≤ |t| then |t|⁻¹ else 1

/-- The three full-integer nearby denominators in (1.142). -/
def dmNearbySum (x t : ℝ) : ℝ :=
  ∑ τ ∈ Finset.Icc (-1 : ℤ) 1, 1 / ((x - (τ : ℝ)) ^ 2 + t ^ 2)

/-- The source frequency set has one frequency for each sector value, not one per channel. -/
theorem dm_sourceFrequencySet_eq_parityFrequencySet
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic) :
    dmSourceFrequencySet bc = Set.range (fun k : DMFrequency bc => (k.val : ℂ)) := by
  rcases hbc with hbc | hbc
  · subst bc
    ext z
    constructor
    · rintro ⟨⟨b, k⟩, rfl⟩
      exact ⟨⟨k.val, by simpa [dmFrequencySet] using k.property⟩, rfl⟩
    · rintro ⟨⟨k, hk⟩, rfl⟩
      refine ⟨(true, ⟨k, ?_⟩), ?_⟩
      · simpa [dmFrequencySet] using hk
      · simp [freeFrequency]
  · subst bc
    ext z
    constructor
    · rintro ⟨⟨b, k⟩, rfl⟩
      exact ⟨⟨k.val, by simpa [dmFrequencySet] using k.property⟩, rfl⟩
    · rintro ⟨⟨k, hk⟩, rfl⟩
      refine ⟨(true, ⟨k, ?_⟩), ?_⟩
      · simpa [dmFrequencySet] using hk
      · simp [freeFrequency]

/-- Source pole exclusion transfers to the actual project eigenvalue range at parameter `πλ`. -/
theorem dm_scaled_parameter_not_freeEigenvalue
    (bc : ZSBoundaryCondition)
    (n : ℤ) (x t : ℝ)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc) :
    (Real.pi : ℂ) * dmLambda n x t ∉
      Set.range (fun i : FreeIndex bc => freeEigenvalue bc i) := by
  rintro ⟨i, hi⟩
  apply «hλ»
  refine ⟨i, ?_⟩
  have hmul : (Real.pi : ℂ) * dmLambda n x t =
      (Real.pi : ℂ) * (freeFrequency bc i : ℂ) := by
    calc
      _ = freeEigenvalue bc i := hi.symm
      _ = _ := by simp [freeEigenvalue, mul_comm]
  exact (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) hmul).symm

/-- Every actual Per± basis label is represented once in the distinct scalar frequency set. -/
theorem dm_frequency_of_index
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (i : FreeIndex bc) :
    ∃ k : DMFrequency bc, (k.val : ℂ) = (freeFrequency bc i : ℂ) := by
  have hi : (freeFrequency bc i : ℂ) ∈ dmSourceFrequencySet bc := ⟨i, rfl⟩
  rw [dm_sourceFrequencySet_eq_parityFrequencySet bc hbc] at hi
  exact hi

/-- The scaled denominator used by the actual unit-interval free realization. -/
def dmScaledDenominator (bc : ZSBoundaryCondition) (n : ℤ) (x t : ℝ)
    (i : FreeIndex bc) : ℂ :=
  (Real.pi : ℂ) * dmLambda n x t - freeEigenvalue bc i

def dmScaledCoefficient (bc : ZSBoundaryCondition) (n : ℤ) (x t : ℝ)
    (i : FreeIndex bc) : ℂ := (dmScaledDenominator bc n x t i)⁻¹

theorem dm_scaled_denominator_ne_zero
    (bc : ZSBoundaryCondition) (n : ℤ) (x t : ℝ)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (i : FreeIndex bc) : dmScaledDenominator bc n x t i ≠ 0 := by
  intro hz
  apply dm_scaled_parameter_not_freeEigenvalue bc n x t «hλ»
  exact ⟨i, (sub_eq_zero.mp (by simpa [dmScaledDenominator] using hz)).symm⟩

/-- The complex denominator is the Euclidean real/imaginary denominator in the source. -/
theorem dmLambda_sub_frequency_norm_sq (n k : ℤ) (x t : ℝ) :
    ‖dmLambda n x t - (k : ℂ)‖ ^ 2 = (x - ((k - n : ℤ) : ℝ)) ^ 2 + t ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [dmLambda, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  ring

theorem dm_latticeTerm_nonneg (bc : ZSBoundaryCondition) («λ» : ℂ)
    (k : DMFrequency bc) : 0 ≤ dmLatticeTerm bc «λ» k := by
  unfold dmLatticeTerm
  exact div_nonneg (by norm_num) (sq_nonneg _)

private theorem dm_scaled_coefficient_norm_le
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (hsum : Summable (dmLatticeTerm bc (dmLambda n x t)))
    (i : FreeIndex bc) :
    ‖dmScaledCoefficient bc n x t i‖ ≤
      Real.sqrt (dmLatticeSum bc (dmLambda n x t)) / Real.pi := by
  obtain ⟨k, hfreq⟩ := dm_frequency_of_index bc hbc i
  let q : ℝ := ‖dmLambda n x t - (k.val : ℂ)‖
  have hdiff : dmLambda n x t - (k.val : ℂ) ≠ 0 := by
    intro hz
    apply «hλ»
    refine ⟨i, ?_⟩
    exact ((sub_eq_zero.mp hz).trans hfreq).symm
  have hqpos : 0 < q := by
    dsimp [q]
    exact norm_pos_iff.mpr hdiff
  have ha : 0 ≤ dmLatticeSum bc (dmLambda n x t) := by
    unfold dmLatticeSum
    exact tsum_nonneg (fun j => dm_latticeTerm_nonneg bc _ j)
  have hterm : 1 / q ^ 2 ≤ dmLatticeSum bc (dmLambda n x t) := by
    have h := hsum.le_tsum k (fun j _ => dm_latticeTerm_nonneg bc _ j)
    simpa [dmLatticeSum, dmLatticeTerm, q] using h
  have hqinv_sq : (q⁻¹) ^ 2 ≤ dmLatticeSum bc (dmLambda n x t) := by
    have hrewrite : (q⁻¹) ^ 2 = 1 / q ^ 2 := by rw [one_div, inv_pow]
    rw [hrewrite]
    exact hterm
  have hqinv_le : q⁻¹ ≤ Real.sqrt (dmLatticeSum bc (dmLambda n x t)) :=
    (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp <| by
      simpa [Real.sq_sqrt ha] using hqinv_sq
  have hden : dmScaledDenominator bc n x t i =
      (Real.pi : ℂ) * (dmLambda n x t - (k.val : ℂ)) := by
    simp only [dmScaledDenominator, freeEigenvalue]
    rw [show (freeFrequency bc i : ℂ) * Real.pi =
      (Real.pi : ℂ) * (freeFrequency bc i : ℂ) by ring, ← mul_sub, ← hfreq]
  have hnormden : ‖dmScaledDenominator bc n x t i‖ = Real.pi * q := by
    rw [hden, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hfrac : (Real.pi * q)⁻¹ = q⁻¹ / Real.pi := by
    field_simp [Real.pi_ne_zero, hqpos.ne']
  rw [dmScaledCoefficient, norm_inv, hnormden, hfrac]
  exact div_le_div_of_nonneg_right hqinv_le Real.pi_pos.le

private theorem dm_scaled_weighted_coefficient_norm_le
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (hsum : Summable (dmLatticeTerm bc (dmLambda n x t)))
    (i : FreeIndex bc) :
    ‖freeEigenvalue bc i * dmScaledCoefficient bc n x t i‖ ≤
      ‖dmLambda n x t‖ * Real.sqrt (dmLatticeSum bc (dmLambda n x t)) + 1 := by
  have hden : dmScaledDenominator bc n x t i ≠ 0 :=
    dm_scaled_denominator_ne_zero bc n x t «hλ» i
  have hsplit : freeEigenvalue bc i * dmScaledCoefficient bc n x t i =
      ((Real.pi : ℂ) * dmLambda n x t) * dmScaledCoefficient bc n x t i - 1 := by
    calc
      _ = (((Real.pi : ℂ) * dmLambda n x t - dmScaledDenominator bc n x t i) *
          dmScaledCoefficient bc n x t i) := by
            congr 1
            dsimp [dmScaledDenominator]
            ring
      _ = ((Real.pi : ℂ) * dmLambda n x t) * dmScaledCoefficient bc n x t i -
          dmScaledDenominator bc n x t i * dmScaledCoefficient bc n x t i := by rw [sub_mul]
      _ = _ := by simp [dmScaledCoefficient, hden]
  calc
    _ = ‖((Real.pi : ℂ) * dmLambda n x t) * dmScaledCoefficient bc n x t i - 1‖ := by
      rw [hsplit]
    _ ≤ ‖(Real.pi : ℂ) * dmLambda n x t‖ *
        ‖dmScaledCoefficient bc n x t i‖ + ‖(1 : ℂ)‖ := by
          calc
            _ ≤ ‖((Real.pi : ℂ) * dmLambda n x t) *
                dmScaledCoefficient bc n x t i‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
            _ = _ := by rw [norm_mul]
    _ = ‖(Real.pi : ℂ) * dmLambda n x t‖ *
        ‖dmScaledCoefficient bc n x t i‖ + 1 := by simp
    _ ≤ (Real.pi * ‖dmLambda n x t‖) *
        (Real.sqrt (dmLatticeSum bc (dmLambda n x t)) / Real.pi) + 1 := by
          have hc := dm_scaled_coefficient_norm_le bc hbc n x t «hλ» hsum i
          have «hλnonneg» : 0 ≤ ‖dmLambda n x t‖ := norm_nonneg _
          have hpnonneg : 0 ≤ Real.pi * ‖dmLambda n x t‖ :=
            mul_nonneg Real.pi_pos.le «hλnonneg»
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
          exact add_le_add (mul_le_mul_of_nonneg_left hc hpnonneg) le_rfl
    _ = ‖dmLambda n x t‖ *
        Real.sqrt (dmLatticeSum bc (dmLambda n x t)) + 1 := by
          field_simp [Real.pi_ne_zero]

private noncomputable def dmResolventDiagonal
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (hsum : Summable (dmLatticeTerm bc (dmLambda n x t))) :
    NlsGge.Atomic.LIB037.FreeSquare bc →L[ℂ] NlsGge.Atomic.LIB037.FreeSquare bc :=
  lp.mapCLM 2 (fun i => dmScaledCoefficient bc n x t i • ContinuousLinearMap.id ℂ ℂ)
    (div_nonneg (Real.sqrt_nonneg _) Real.pi_pos.le) (fun i => by
      simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one] using
        dm_scaled_coefficient_norm_le bc hbc n x t «hλ» hsum i)

private noncomputable def dmWeightedResolventDiagonal
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (hsum : Summable (dmLatticeTerm bc (dmLambda n x t))) :
    NlsGge.Atomic.LIB037.FreeSquare bc →L[ℂ] NlsGge.Atomic.LIB037.FreeSquare bc :=
  lp.mapCLM 2 (fun i =>
      (freeEigenvalue bc i * dmScaledCoefficient bc n x t i) • ContinuousLinearMap.id ℂ ℂ)
    (show 0 ≤ ‖dmLambda n x t‖ *
        Real.sqrt (dmLatticeSum bc (dmLambda n x t)) + 1 by positivity)
    (fun i => by
      simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one] using
        dm_scaled_weighted_coefficient_norm_le bc hbc n x t «hλ» hsum i)

private noncomputable def dmFreeResolvent
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (hsum : Summable (dmLatticeTerm bc (dmLambda n x t))) :
    SourcePairL2 →L[ℂ] SourcePairL2 :=
  (freeZSBasis bc).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((dmResolventDiagonal bc hbc n x t «hλ» hsum).comp
      (freeZSBasis bc).repr.toContinuousLinearEquiv.toContinuousLinearMap)

private noncomputable def dmFreeActionImage
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (hsum : Summable (dmLatticeTerm bc (dmLambda n x t))) :
    SourcePairL2 →L[ℂ] SourcePairL2 :=
  (freeZSBasis bc).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((dmWeightedResolventDiagonal bc hbc n x t «hλ» hsum).comp
      (freeZSBasis bc).repr.toContinuousLinearEquiv.toContinuousLinearMap)

private lemma dmFreeResolvent_repr
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (hsum : Summable (dmLatticeTerm bc (dmLambda n x t)))
    (f : SourcePairL2) (i : FreeIndex bc) :
    (freeZSBasis bc).repr (dmFreeResolvent bc hbc n x t «hλ» hsum f) i =
      dmScaledCoefficient bc n x t i * (freeZSBasis bc).repr f i := by
  change (freeZSBasis bc).repr ((freeZSBasis bc).repr.symm
      (dmResolventDiagonal bc hbc n x t «hλ» hsum ((freeZSBasis bc).repr f))) i = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

private lemma dmFreeActionImage_repr
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (hsum : Summable (dmLatticeTerm bc (dmLambda n x t)))
    (f : SourcePairL2) (i : FreeIndex bc) :
    (freeZSBasis bc).repr (dmFreeActionImage bc hbc n x t «hλ» hsum f) i =
      (freeEigenvalue bc i * dmScaledCoefficient bc n x t i) *
        (freeZSBasis bc).repr f i := by
  change (freeZSBasis bc).repr ((freeZSBasis bc).repr.symm
      (dmWeightedResolventDiagonal bc hbc n x t «hλ» hsum ((freeZSBasis bc).repr f))) i = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

private lemma dm_free_resolvent_domain_pairing
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (hsum : Summable (dmLatticeTerm bc (dmLambda n x t)))
    (f : SourcePairL2) (u : (NlsGge.Atomic.LIB033.zsRealization 0 bc).domain) :
    inner ℂ (NlsGge.Atomic.LIB033.zsRealization 0 bc u)
        (dmFreeResolvent bc hbc n x t «hλ» hsum f) =
      inner ℂ (u : SourcePairL2)
        (dmFreeActionImage bc hbc n x t «hλ» hsum f) := by
  rw [← (freeZSBasis bc).repr.inner_map_map, ← (freeZSBasis bc).repr.inner_map_map]
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  rw [NlsGge.Atomic.LIB037.free_action_repr, dmFreeResolvent_repr,
    dmFreeActionImage_repr]
  simp only [RCLike.inner_apply, map_mul, starRingEnd_apply,
    NlsGge.Atomic.LIB037.star_freeEigenvalue]
  ring

private lemma dm_free_resolvent_adjoint_pairing
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (hsum : Summable (dmLatticeTerm bc (dmLambda n x t)))
    (f : SourcePairL2) (u : (NlsGge.Atomic.LIB033.zsRealization 0 bc).domain) :
    inner ℂ (dmFreeActionImage bc hbc n x t «hλ» hsum f) (u : SourcePairL2) =
      inner ℂ (dmFreeResolvent bc hbc n x t «hλ» hsum f)
        (NlsGge.Atomic.LIB033.zsRealization 0 bc u) := by
  have h := congrArg (starRingEnd ℂ)
    (dm_free_resolvent_domain_pairing bc hbc n x t «hλ» hsum f u).symm
  simpa only [inner_conj_symm] using h

private lemma dm_free_operator_adjoint_eq (bc : ZSBoundaryCondition) :
    (NlsGge.Atomic.LIB033.zsRealization 0 bc).adjoint =
      NlsGge.Atomic.LIB033.zsRealization 0 bc :=
  NlsGge.Atomic.LIB037.free_operator_adjoint_eq bc

private lemma dmFreeResolvent_mem_adjoint
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (hsum : Summable (dmLatticeTerm bc (dmLambda n x t)))
    (f : SourcePairL2) :
    dmFreeResolvent bc hbc n x t «hλ» hsum f ∈
      (NlsGge.Atomic.LIB033.zsRealization 0 bc).adjoint.domain :=
  LinearPMap.mem_adjoint_domain_of_exists _
    ⟨dmFreeActionImage bc hbc n x t «hλ» hsum f,
      dm_free_resolvent_adjoint_pairing bc hbc n x t «hλ» hsum f⟩

private lemma dmFreeResolvent_mem_domain
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (hsum : Summable (dmLatticeTerm bc (dmLambda n x t)))
    (f : SourcePairL2) :
    dmFreeResolvent bc hbc n x t «hλ» hsum f ∈
      (NlsGge.Atomic.LIB033.zsRealization 0 bc).domain := by
  have h := dmFreeResolvent_mem_adjoint bc hbc n x t «hλ» hsum f
  rwa [dm_free_operator_adjoint_eq] at h

set_option backward.isDefEq.respectTransparency false in
private lemma dmFreeResolvent_action
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (hsum : Summable (dmLatticeTerm bc (dmLambda n x t)))
    (f : SourcePairL2) :
    NlsGge.Atomic.LIB033.zsRealization 0 bc
      ⟨dmFreeResolvent bc hbc n x t «hλ» hsum f,
        dmFreeResolvent_mem_domain bc hbc n x t «hλ» hsum f⟩ =
      dmFreeActionImage bc hbc n x t «hλ» hsum f := by
  have h := (NlsGge.Atomic.LIB033.zsRealization 0 bc).adjoint_apply_eq
    (NlsGge.Atomic.LIB033.zsRealization_dense 0 bc)
    ⟨dmFreeResolvent bc hbc n x t «hλ» hsum f,
      dmFreeResolvent_mem_adjoint bc hbc n x t «hλ» hsum f⟩
    (dm_free_resolvent_adjoint_pairing bc hbc n x t «hλ» hsum f)
  obtain ⟨hdom, happly⟩ := LinearPMap.dExt_iff.mp (dm_free_operator_adjoint_eq bc)
  have he := happly
    (x := ⟨dmFreeResolvent bc hbc n x t «hλ» hsum f,
      dmFreeResolvent_mem_adjoint bc hbc n x t «hλ» hsum f⟩)
    (y := ⟨dmFreeResolvent bc hbc n x t «hλ» hsum f,
      dmFreeResolvent_mem_domain bc hbc n x t «hλ» hsum f⟩) rfl
  exact he.symm.trans h

private lemma dmFreeActionImage_eq
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (hsum : Summable (dmLatticeTerm bc (dmLambda n x t)))
    (f : SourcePairL2) :
    dmFreeActionImage bc hbc n x t «hλ» hsum f =
      ((Real.pi : ℂ) * dmLambda n x t) • dmFreeResolvent bc hbc n x t «hλ» hsum f - f := by
  apply (freeZSBasis bc).repr.injective
  apply lp.ext
  funext i
  simp only [map_sub, map_smul, lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul, dmFreeActionImage_repr, dmFreeResolvent_repr]
  have hd := dm_scaled_denominator_ne_zero bc n x t «hλ» i
  have hscalar : freeEigenvalue bc i * dmScaledCoefficient bc n x t i =
      (Real.pi : ℂ) * dmLambda n x t * dmScaledCoefficient bc n x t i - 1 := by
    calc
      _ = (((Real.pi : ℂ) * dmLambda n x t - dmScaledDenominator bc n x t i) *
          dmScaledCoefficient bc n x t i) := by
            congr 1
            dsimp [dmScaledDenominator]
            ring
      _ = _ := by
            rw [sub_mul, dmScaledCoefficient, mul_inv_cancel₀ hd]
  rw [hscalar]
  ring

private theorem dmFreeResolvent_right_inverse
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (hsum : Summable (dmLatticeTerm bc (dmLambda n x t)))
    (f : SourcePairL2) :
    ((Real.pi : ℂ) * dmLambda n x t) • dmFreeResolvent bc hbc n x t «hλ» hsum f -
      NlsGge.Atomic.LIB033.zsRealization 0 bc
        ⟨dmFreeResolvent bc hbc n x t «hλ» hsum f,
          dmFreeResolvent_mem_domain bc hbc n x t «hλ» hsum f⟩ = f := by
  rw [dmFreeResolvent_action, dmFreeActionImage_eq]
  abel

private theorem dmFreeResolvent_left_inverse
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (hsum : Summable (dmLatticeTerm bc (dmLambda n x t)))
    (u : (NlsGge.Atomic.LIB033.zsRealization 0 bc).domain) :
    dmFreeResolvent bc hbc n x t «hλ» hsum
      (((Real.pi : ℂ) * dmLambda n x t) • (u : SourcePairL2) -
        NlsGge.Atomic.LIB033.zsRealization 0 bc u) = u := by
  apply (freeZSBasis bc).repr.injective
  apply lp.ext
  funext i
  rw [dmFreeResolvent_repr]
  simp only [map_sub, map_smul, lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul, NlsGge.Atomic.LIB037.free_action_repr]
  have hd := dm_scaled_denominator_ne_zero bc n x t «hλ» i
  change dmScaledCoefficient bc n x t i *
      (((Real.pi : ℂ) * dmLambda n x t) *
        (freeZSBasis bc).repr (u : SourcePairL2) i -
        freeEigenvalue bc i * (freeZSBasis bc).repr (u : SourcePairL2) i) = _
  rw [← sub_mul]
  change dmScaledCoefficient bc n x t i *
      (dmScaledDenominator bc n x t i * (freeZSBasis bc).repr (u : SourcePairL2) i) = _
  rw [dmScaledCoefficient, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]

private noncomputable def dmFreeResolventH1
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (hsum : Summable (dmLatticeTerm bc (dmLambda n x t)))
    (f : SourcePairL2) : NlsGge.Atomic.Interval.H1Pair :=
  NlsGge.Atomic.LIB033.domainLift
    ⟨dmFreeResolvent bc hbc n x t «hλ» hsum f,
      dmFreeResolvent_mem_domain bc hbc n x t «hλ» hsum f⟩

private lemma dmFreeResolventH1_value
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (hsum : Summable (dmLatticeTerm bc (dmLambda n x t)))
    (f : SourcePairL2) :
    NlsGge.Atomic.Interval.h1PairValue
      (dmFreeResolventH1 bc hbc n x t «hλ» hsum f) =
        dmFreeResolvent bc hbc n x t «hλ» hsum f :=
  NlsGge.Atomic.LIB033.domainLift_value _

private lemma dmFreeResolventH1_add
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (hsum : Summable (dmLatticeTerm bc (dmLambda n x t)))
    (f g : SourcePairL2) :
    dmFreeResolventH1 bc hbc n x t «hλ» hsum (f + g) =
      NlsGge.Atomic.LIB033.h1PairAdd
        (dmFreeResolventH1 bc hbc n x t «hλ» hsum f)
        (dmFreeResolventH1 bc hbc n x t «hλ» hsum g) := by
  apply NlsGge.Atomic.LIB033.h1PairValue_injective
  rw [NlsGge.Atomic.LIB033.h1PairValue_add,
    dmFreeResolventH1_value, dmFreeResolventH1_value,
    dmFreeResolventH1_value, map_add]

private lemma dmFreeResolventH1_smul
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (hsum : Summable (dmLatticeTerm bc (dmLambda n x t)))
    (c : ℂ) (f : SourcePairL2) :
    dmFreeResolventH1 bc hbc n x t «hλ» hsum (c • f) =
      NlsGge.Atomic.LIB033.h1PairSmul c
        (dmFreeResolventH1 bc hbc n x t «hλ» hsum f) := by
  apply NlsGge.Atomic.LIB033.h1PairValue_injective
  rw [NlsGge.Atomic.LIB033.h1PairValue_smul,
    dmFreeResolventH1_value, dmFreeResolventH1_value, map_smul]

private def dmFreeResolventToSupLinear
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (hsum : Summable (dmLatticeTerm bc (dmLambda n x t))) :
    SourcePairL2 →ₗ[ℂ]
      C(Icc (0 : ℝ) 1, NlsGge.Atomic.LIB031.PointPair) where
  toFun f := NlsGge.Atomic.LIB031.pairRepresentative
    (dmFreeResolventH1 bc hbc n x t «hλ» hsum f)
  map_add' f g := by
    rw [dmFreeResolventH1_add, NlsGge.Atomic.LIB037.pairRepresentative_add]
  map_smul' c f := by
    rw [dmFreeResolventH1_smul, NlsGge.Atomic.LIB037.pairRepresentative_smul]
    simp

private lemma dm_nat_shift_square_summable :
    Summable (fun m : ℕ => (16 : ℝ) / ((m : ℝ) + 1) ^ 2) := by
  have h := (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
  have hs := h.comp_injective Nat.succ_injective
  convert hs.mul_left (16 : ℝ) using 1 <;> simp [div_eq_mul_inv]

/-- The real full-lattice row is summable; the finitely many possible small denominators
are totalized real divisions, while both tails are dominated by a shifted p-series. -/
private theorem dm_real_lattice_summable (x t : ℝ) :
    Summable (dmRealLatticeTerm x t) := by
  change Summable (NlsGge.Atomic.DMResolventLattice.dmRealLatticeTerm x t)
  exact NlsGge.Atomic.DMResolventLattice.dm_full_lattice_summable x t

/-- The actual parity-indexed row is summable before its real `tsum` is used. -/
theorem dm_resolvent_lattice_summable
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ) (hx : -1 ≤ x ∧ x ≤ 1)
    («hλ» : dmLambda n x t ∉ Set.range (fun k : DMFrequency bc => (k.val : ℂ))) :
    Summable (dmLatticeTerm bc (dmLambda n x t)) := by
  have hfull := (dm_real_lattice_summable x t).comp_injective
    (show Function.Injective (fun k : DMFrequency bc => k.val - n) from by
      intro a b hab
      apply Subtype.ext
      have hcancel := congrArg (fun z : ℤ => z + n) hab
      simpa using hcancel)
  apply hfull.congr
  intro k
  simp [dmLatticeTerm, dmRealLatticeTerm, dmLambda_sub_frequency_norm_sq]

/-- Source strip bound for the actual distinct Per± frequencies. -/
theorem dm_resolvent_lattice_sum_le
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ) (hx : -1 ≤ x ∧ x ≤ 1)
    («hλ» : dmLambda n x t ∉ Set.range (fun k : DMFrequency bc => (k.val : ℂ))) :
    dmLatticeSum bc (dmLambda n x t) ≤ dmNearbySum x t + 6 * dmTailProfile t := by
  let φ : DMFrequency bc → ℤ := fun k => k.val - n
  have hφ : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    change a.val - n = b.val - n at hab
    have hcancel := congrArg (fun z : ℤ => z + n) hab
    simpa using hcancel
  have hterm (k : DMFrequency bc) :
      dmLatticeTerm bc (dmLambda n x t) k =
        NlsGge.Atomic.DMResolventLattice.dmRealLatticeTerm x t (φ k) := by
    simp [φ, dmLatticeTerm, dmLambda_sub_frequency_norm_sq,
      NlsGge.Atomic.DMResolventLattice.dmRealLatticeTerm]
  have hsum_eq :
      dmLatticeSum bc (dmLambda n x t) =
        ∑' k : DMFrequency bc,
          NlsGge.Atomic.DMResolventLattice.dmRealLatticeTerm x t (φ k) := by
    unfold dmLatticeSum
    exact tsum_congr hterm
  have hsub :
      (∑' k : DMFrequency bc,
        NlsGge.Atomic.DMResolventLattice.dmRealLatticeTerm x t (φ k)) ≤
        NlsGge.Atomic.DMResolventLattice.dmFullLatticeSum x t := by
    unfold NlsGge.Atomic.DMResolventLattice.dmFullLatticeSum
    exact tsum_comp_le_tsum_of_inj
      (NlsGge.Atomic.DMResolventLattice.dm_full_lattice_summable x t)
      (by
        intro d
        unfold NlsGge.Atomic.DMResolventLattice.dmRealLatticeTerm
        positivity)
      hφ
  rw [hsum_eq]
  calc
    (∑' k : DMFrequency bc,
      NlsGge.Atomic.DMResolventLattice.dmRealLatticeTerm x t (φ k)) ≤
        NlsGge.Atomic.DMResolventLattice.dmFullLatticeSum x t := hsub
    _ ≤ NlsGge.Atomic.DMResolventLattice.dmNearbySum x t +
        6 * NlsGge.Atomic.DMResolventLattice.dmTailProfile t :=
      NlsGge.Atomic.DMResolventLattice.dm_full_lattice_sum_le x t hx
    _ = dmNearbySum x t + 6 * dmTailProfile t := by
      rfl

/-! The actual Per± resolvent energy is kept on one `Sector` row.  These
private carriers are only bookkeeping for the proof below; the public source
commands above remain unchanged. -/

private def dmSectorType : ZSBoundaryCondition → Type
  | .periodic => Sector 0
  | .antiperiodic => Sector 1
  | _ => Empty

private def dmSectorFrequencyEquiv (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic) :
    dmSectorType bc ≃ DMFrequency bc := by
  cases bc with
  | dirichlet =>
      have hfalse : False := by
        rcases hbc with h | h
        · cases h
        · cases h
      exact False.elim hfalse
  | neumann =>
      have hfalse : False := by
        rcases hbc with h | h
        · cases h
        · cases h
      exact False.elim hfalse
  | periodic =>
      refine
        { toFun := fun m => ⟨m.val, ?_⟩
          invFun := fun k => ⟨k.val, ?_⟩
          left_inv := ?_
          right_inv := ?_ }
      · simpa [dmSectorType, DMFrequency, dmFrequencySet] using m.property
      · simpa [dmSectorType, DMFrequency, dmFrequencySet] using k.property
      · intro m
        apply Subtype.ext
        rfl
      · intro k
        apply Subtype.ext
        rfl
  | antiperiodic =>
      refine
        { toFun := fun m => ⟨m.val, ?_⟩
          invFun := fun k => ⟨k.val, ?_⟩
          left_inv := ?_
          right_inv := ?_ }
      · simpa [dmSectorType, DMFrequency, dmFrequencySet] using m.property
      · simpa [dmSectorType, DMFrequency, dmFrequencySet] using k.property
      · intro m
        apply Subtype.ext
        rfl
      · intro k
        apply Subtype.ext
        rfl

private def dmSectorIndex (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic) (b : Bool) :
    dmSectorType bc → FreeIndex bc := by
  cases bc with
  | dirichlet =>
      have hfalse : False := by
        rcases hbc with h | h
        · cases h
        · cases h
      exact False.elim hfalse
  | neumann =>
      have hfalse : False := by
        rcases hbc with h | h
        · cases h
        · cases h
      exact False.elim hfalse
  | periodic => exact fun m => (b, m)
  | antiperiodic => exact fun m => (b, m)

private theorem dmSectorIndex_injective (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic) (b : Bool) :
    Function.Injective (dmSectorIndex bc hbc b) := by
  cases bc with
  | dirichlet => rcases hbc with h | h <;> cases h
  | neumann => rcases hbc with h | h <;> cases h
  | periodic =>
      intro m m' h
      change (b, m) = (b, m') at h
      exact congrArg Prod.snd h
  | antiperiodic =>
      intro m m' h
      change (b, m) = (b, m') at h
      exact congrArg Prod.snd h

private theorem dmSectorIndex_frequency (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic) (b : Bool)
    (m : dmSectorType bc) :
    (freeFrequency bc (dmSectorIndex bc hbc b m) : ℂ) =
      ((dmSectorFrequencyEquiv bc hbc m).val : ℂ) := by
  cases bc with
  | dirichlet => rcases hbc with h | h <;> cases h
  | neumann => rcases hbc with h | h <;> cases h
  | periodic => rfl
  | antiperiodic => rfl

private def dmResolventCoefficientEnergyRow (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ) («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (b : Bool) (m : dmSectorType bc) : ℝ :=
  ‖dmScaledCoefficient bc n x t (dmSectorIndex bc hbc b m)‖ ^ 2

private def dmResolventCoefficientEnergy (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ) («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc) : ℝ :=
  ∑' m : dmSectorType bc,
    dmResolventCoefficientEnergyRow bc hbc n x t «hλ» true m

private theorem dm_resolvent_coefficient_energy_term
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (b : Bool) (m : dmSectorType bc) :
    dmResolventCoefficientEnergyRow bc hbc n x t «hλ» b m =
      dmLatticeTerm bc (dmLambda n x t) (dmSectorFrequencyEquiv bc hbc m) /
        Real.pi ^ 2 := by
  let i := dmSectorIndex bc hbc b m
  let k := dmSectorFrequencyEquiv bc hbc m
  have hfreq : (freeFrequency bc i : ℂ) = (k.val : ℂ) :=
    dmSectorIndex_frequency bc hbc b m
  have hden : dmScaledDenominator bc n x t i =
      (Real.pi : ℂ) * (dmLambda n x t - (k.val : ℂ)) := by
    simp only [dmScaledDenominator, freeEigenvalue]
    rw [hfreq]
    ring
  have hden_ne : dmScaledDenominator bc n x t i ≠ 0 :=
    dm_scaled_denominator_ne_zero bc n x t «hλ» i
  have hdiff : dmLambda n x t - (k.val : ℂ) ≠ 0 := by
    intro hz
    apply hden_ne
    rw [hden, hz]
    simp
  have hnorm : ‖dmScaledCoefficient bc n x t i‖ ^ 2 =
      1 / ((Real.pi * ‖dmLambda n x t - (k.val : ℂ)‖) ^ 2) := by
    rw [dmScaledCoefficient, hden, norm_inv, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [inv_pow, one_div]
  change ‖dmScaledCoefficient bc n x t i‖ ^ 2 = _
  rw [hnorm, dmLatticeTerm]
  have hnorm_ne : ‖dmLambda n x t - (k.val : ℂ)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hdiff
  dsimp [k]
  field_simp [Real.pi_ne_zero, hnorm_ne]

private theorem dm_resolvent_coefficient_energy_row_summable
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ) (hx : -1 ≤ x ∧ x ≤ 1)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (b : Bool) :
    Summable (dmResolventCoefficientEnergyRow bc hbc n x t «hλ» b) := by
  have «hλ'» : dmLambda n x t ∉
      Set.range (fun k : DMFrequency bc => (k.val : ℂ)) := by
    intro hh
    apply «hλ»
    rw [dm_sourceFrequencySet_eq_parityFrequencySet bc hbc]
    exact hh
  have hscalar := dm_resolvent_lattice_summable bc hbc n x t hx «hλ'»
  let e := dmSectorFrequencyEquiv bc hbc
  have hsub : Summable (fun m : dmSectorType bc =>
      dmLatticeTerm bc (dmLambda n x t) (e m)) :=
    hscalar.comp_injective e.injective
  have hscaled : Summable (fun m : dmSectorType bc =>
      dmLatticeTerm bc (dmLambda n x t) (e m) * (Real.pi ^ 2)⁻¹) :=
    hsub.mul_right ((Real.pi ^ 2)⁻¹)
  apply hscaled.congr
  intro m
  rw [dm_resolvent_coefficient_energy_term]
  dsimp [e]
  simp [div_eq_mul_inv, mul_comm]

private theorem dm_resolvent_coefficient_energy_eq
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ) (hx : -1 ≤ x ∧ x ≤ 1)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc) :
    dmResolventCoefficientEnergy bc hbc n x t «hλ» =
      dmLatticeSum bc (dmLambda n x t) / Real.pi ^ 2 := by
  have «hλ'» : dmLambda n x t ∉
      Set.range (fun k : DMFrequency bc => (k.val : ℂ)) := by
    intro hh
    apply «hλ»
    rw [dm_sourceFrequencySet_eq_parityFrequencySet bc hbc]
    exact hh
  let e := dmSectorFrequencyEquiv bc hbc
  have hscalar := dm_resolvent_lattice_summable bc hbc n x t hx «hλ'»
  have hsub : Summable (fun m : dmSectorType bc =>
      dmLatticeTerm bc (dmLambda n x t) (e m)) := hscalar.comp_injective e.injective
  have _hrow := dm_resolvent_coefficient_energy_row_summable
    bc hbc n x t hx «hλ» true
  calc
    dmResolventCoefficientEnergy bc hbc n x t «hλ» =
        ∑' m : dmSectorType bc,
          dmLatticeTerm bc (dmLambda n x t) (e m) * (Real.pi ^ 2)⁻¹ := by
      unfold dmResolventCoefficientEnergy
      apply tsum_congr
      intro m
      rw [dm_resolvent_coefficient_energy_term]
      simp [e, div_eq_mul_inv]
    _ = (∑' m : dmSectorType bc,
          dmLatticeTerm bc (dmLambda n x t) (e m)) * (Real.pi ^ 2)⁻¹ :=
      hsub.tsum_mul_right ((Real.pi ^ 2)⁻¹)
    _ = dmLatticeSum bc (dmLambda n x t) / Real.pi ^ 2 := by
      rw [dmLatticeSum, div_eq_mul_inv]
      rw [← e.tsum_eq (fun k : DMFrequency bc => dmLatticeTerm bc (dmLambda n x t) k)]

private def dmInputCoefficientEnergy (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (f : SourcePairL2) (b : Bool) : ℝ :=
  ∑' m : dmSectorType bc,
    ‖(freeZSBasis bc).repr f (dmSectorIndex bc hbc b m)‖ ^ 2

private theorem dm_input_coefficient_energy_row_summable
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (f : SourcePairL2) (b : Bool) :
    Summable (fun m : dmSectorType bc =>
      ‖(freeZSBasis bc).repr f (dmSectorIndex bc hbc b m)‖ ^ 2) := by
  have hfull : Summable (fun i : FreeIndex bc =>
      ‖(freeZSBasis bc).repr f i‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.memℓp ((freeZSBasis bc).repr f)).summable
        (by norm_num : 0 < (2 : ENNReal).toReal)
  exact hfull.comp_injective (dmSectorIndex_injective bc hbc b)

private theorem dm_input_coefficient_energies_sum
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (f : SourcePairL2) :
    dmInputCoefficientEnergy bc hbc f true +
      dmInputCoefficientEnergy bc hbc f false = ‖f‖ ^ 2 := by
  rcases hbc with hbc | hbc
  · subst bc
    have _hrow_true := dm_input_coefficient_energy_row_summable .periodic (Or.inl rfl) f true
    have _hrow_false := dm_input_coefficient_energy_row_summable .periodic (Or.inl rfl) f false
    have hnorm := lp.hasSum_norm (p := (2 : ENNReal))
      (by norm_num : 0 < (2 : ENNReal).toReal)
      ((freeZSBasis .periodic).repr f)
    have hprod := hnorm.summable.tsum_prod
    have hbool : dmInputCoefficientEnergy .periodic (Or.inl rfl) f true +
        dmInputCoefficientEnergy .periodic (Or.inl rfl) f false =
        ∑' b : Bool, ∑' m : Sector 0,
          ‖(freeZSBasis .periodic).repr f (b, m)‖ ^ 2 := by
      simp [dmInputCoefficientEnergy, dmSectorIndex, dmSectorType]
    calc
      _ = ∑' b : Bool, ∑' m : Sector 0,
          ‖(freeZSBasis .periodic).repr f (b, m)‖ ^ 2 := hbool
      _ = ∑' i : Bool × Sector 0,
          ‖(freeZSBasis .periodic).repr f i‖ ^ 2 := by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hprod.symm
      _ = ‖(freeZSBasis .periodic).repr f‖ ^ 2 := by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two, FreeIndex] using hnorm.tsum_eq
      _ = ‖f‖ ^ 2 := by rw [(freeZSBasis .periodic).repr.norm_map]
  · subst bc
    have _hrow_true := dm_input_coefficient_energy_row_summable .antiperiodic (Or.inr rfl) f true
    have _hrow_false := dm_input_coefficient_energy_row_summable .antiperiodic (Or.inr rfl) f false
    have hnorm := lp.hasSum_norm (p := (2 : ENNReal))
      (by norm_num : 0 < (2 : ENNReal).toReal)
      ((freeZSBasis .antiperiodic).repr f)
    have hprod := hnorm.summable.tsum_prod
    have hbool : dmInputCoefficientEnergy .antiperiodic (Or.inr rfl) f true +
        dmInputCoefficientEnergy .antiperiodic (Or.inr rfl) f false =
        ∑' b : Bool, ∑' m : Sector 1,
          ‖(freeZSBasis .antiperiodic).repr f (b, m)‖ ^ 2 := by
      simp [dmInputCoefficientEnergy, dmSectorIndex, dmSectorType]
    calc
      _ = ∑' b : Bool, ∑' m : Sector 1,
          ‖(freeZSBasis .antiperiodic).repr f (b, m)‖ ^ 2 := hbool
      _ = ∑' i : Bool × Sector 1,
          ‖(freeZSBasis .antiperiodic).repr f i‖ ^ 2 := by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hprod.symm
      _ = ‖(freeZSBasis .antiperiodic).repr f‖ ^ 2 := by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two, FreeIndex] using hnorm.tsum_eq
      _ = ‖f‖ ^ 2 := by rw [(freeZSBasis .antiperiodic).repr.norm_map]

private abbrev dmIntervalMeasure : MeasureTheory.Measure ℝ :=
  MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)

private theorem dmIntervalMeasure_isFinite :
    MeasureTheory.IsFiniteMeasure dmIntervalMeasure := by
  refine ⟨?_⟩
  change (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) Set.univ < ⊤
  rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Ioc]
  simp only [sub_zero]
  exact ENNReal.ofReal_lt_top

private theorem dmIntervalMeasure_mass :
    MeasureTheory.measureUnivNNReal dmIntervalMeasure = 1 := by
  unfold MeasureTheory.measureUnivNNReal dmIntervalMeasure
  rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Ioc]
  norm_num

/-- Extend a continuous interval function by the actual closed-interval projection. -/
private def dmIccExtendBoundedFunction
    (G : C(Icc (0 : ℝ) 1, ℂ)) : BoundedContinuousFunction ℝ ℂ where
  toFun := Set.IccExtend zero_le_one G
  continuous_toFun := G.continuous.Icc_extend'
  map_bounded' := by
    refine ⟨2 * ‖G‖, ?_⟩
    intro x y
    have hx : ‖Set.IccExtend zero_le_one G x‖ ≤ ‖G‖ := by
      rw [Set.IccExtend_apply]
      exact G.norm_coe_le_norm _
    have hy : ‖Set.IccExtend zero_le_one G y‖ ≤ ‖G‖ := by
      rw [Set.IccExtend_apply]
      exact G.norm_coe_le_norm _
    rw [dist_eq_norm]
    calc
      ‖Set.IccExtend zero_le_one G x - Set.IccExtend zero_le_one G y‖ ≤
          ‖Set.IccExtend zero_le_one G x‖ + ‖Set.IccExtend zero_le_one G y‖ :=
        norm_sub_le _ _
      _ ≤ ‖G‖ + ‖G‖ := add_le_add hx hy
      _ = 2 * ‖G‖ := by ring

private def dmIccExtendBoundedFunctionLinear :
    C(Icc (0 : ℝ) 1, ℂ) →ₗ[ℂ] BoundedContinuousFunction ℝ ℂ where
  toFun := dmIccExtendBoundedFunction
  map_add' G H := by
    ext x
    simp [dmIccExtendBoundedFunction, Set.IccExtend]
  map_smul' c G := by
    ext x
    simp [dmIccExtendBoundedFunction, Set.IccExtend]

private theorem dmIccExtendBoundedFunction_norm_le
    (G : C(Icc (0 : ℝ) 1, ℂ)) :
    ‖dmIccExtendBoundedFunction G‖ ≤ ‖G‖ := by
  apply (BoundedContinuousFunction.norm_le_of_nonempty
    (f := dmIccExtendBoundedFunction G) (M := ‖G‖)).2
  intro x
  change ‖Set.IccExtend zero_le_one G x‖ ≤ ‖G‖
  rw [Set.IccExtend_apply]
  exact G.norm_coe_le_norm _

private noncomputable def dmIccExtendBoundedFunctionCLM :
    C(Icc (0 : ℝ) 1, ℂ) →L[ℂ] BoundedContinuousFunction ℝ ℂ :=
  dmIccExtendBoundedFunctionLinear.mkContinuous 1 (by
    intro G
    change ‖dmIccExtendBoundedFunction G‖ ≤ 1 * ‖G‖
    rw [one_mul]
    exact dmIccExtendBoundedFunction_norm_le G)

private noncomputable def dmIccExtendSourceIntervalL2CLM :
    C(Icc (0 : ℝ) 1, ℂ) →L[ℂ] SourceIntervalL2 := by
  letI : MeasureTheory.IsFiniteMeasure dmIntervalMeasure := dmIntervalMeasure_isFinite
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  exact (BoundedContinuousFunction.toLp (2 : ENNReal) dmIntervalMeasure ℂ).comp
    dmIccExtendBoundedFunctionCLM

private theorem dmIccExtendSourceIntervalL2_ae
    (G : C(Icc (0 : ℝ) 1, ℂ)) :
    (dmIccExtendSourceIntervalL2CLM G : ℝ → ℂ) =ᵐ[dmIntervalMeasure]
      Set.IccExtend zero_le_one G := by
  letI : MeasureTheory.IsFiniteMeasure dmIntervalMeasure := dmIntervalMeasure_isFinite
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  change ((BoundedContinuousFunction.toLp (2 : ENNReal) dmIntervalMeasure ℂ)
      (dmIccExtendBoundedFunction G) : ℝ → ℂ) =ᵐ[dmIntervalMeasure]
    Set.IccExtend zero_le_one G
  simpa [dmIccExtendBoundedFunction] using
    (BoundedContinuousFunction.coeFn_toLp (2 : ENNReal) dmIntervalMeasure ℂ
      (dmIccExtendBoundedFunction G))

private theorem dmIccExtendSourceIntervalL2_norm_le
    (G : C(Icc (0 : ℝ) 1, ℂ)) :
    ‖dmIccExtendSourceIntervalL2CLM G‖ ≤ ‖G‖ := by
  letI : MeasureTheory.IsFiniteMeasure dmIntervalMeasure := dmIntervalMeasure_isFinite
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  let T : BoundedContinuousFunction ℝ ℂ →L[ℂ] SourceIntervalL2 :=
    BoundedContinuousFunction.toLp (2 : ENNReal) dmIntervalMeasure ℂ
  have hT :
      ‖T‖ ≤ 1 := by
    calc
      _ ≤ (MeasureTheory.measureUnivNNReal dmIntervalMeasure : ℝ) ^
          ((2 : ENNReal).toReal)⁻¹ :=
        by
          change ‖(BoundedContinuousFunction.toLp (2 : ENNReal) dmIntervalMeasure ℂ :
            BoundedContinuousFunction ℝ ℂ →L[ℂ] SourceIntervalL2)‖ ≤ _
          exact BoundedContinuousFunction.toLp_norm_le dmIntervalMeasure
      _ = 1 := by rw [dmIntervalMeasure_mass]; norm_num
  change ‖T (dmIccExtendBoundedFunctionCLM G)‖ ≤ ‖G‖
  calc
    _ ≤ ‖T‖ * ‖dmIccExtendBoundedFunctionCLM G‖ := T.le_opNorm _
    _ ≤ 1 * ‖dmIccExtendBoundedFunctionCLM G‖ :=
      mul_le_mul_of_nonneg_right hT (norm_nonneg _)
    _ = ‖dmIccExtendBoundedFunctionCLM G‖ := by rw [one_mul]
    _ ≤ ‖G‖ := dmIccExtendBoundedFunction_norm_le G

private theorem dmIccExtendSourceIntervalL2_freeZSBasis_component
    (bc : ZSBoundaryCondition) (i : FreeIndex bc) (b : Bool) :
    dmIccExtendSourceIntervalL2CLM
        (NlsGge.Atomic.LIB026.representative (freeZSH1 bc i b)) =
      (freeZSBasis bc i) b := by
  have hcomponent : (freeZSH1 bc i b).value = (freeZSBasis bc i) b := by
    simpa [NlsGge.Atomic.Interval.h1PairValue] using
      congrArg (fun z : SourcePairL2 => z b) (freeZSH1_value bc i)
  have hcomponentFun :
      ((freeZSH1 bc i b).value : ℝ → ℂ) = (freeZSBasis bc i b : ℝ → ℂ) :=
    congrArg (fun z : SourceIntervalL2 => (z : ℝ → ℂ)) hcomponent
  have hcomponent_ae :
      (freeZSH1 bc i b).value =ᵐ[dmIntervalMeasure] (freeZSBasis bc i) b :=
    Filter.Eventually.of_forall (fun x => congrFun hcomponentFun x)
  apply MeasureTheory.Lp.ext
  exact (dmIccExtendSourceIntervalL2_ae
      (NlsGge.Atomic.LIB026.representative (freeZSH1 bc i b))).trans
    ((NlsGge.Atomic.LIB026.representative_ae (freeZSH1 bc i b)).trans hcomponent_ae)

/-! Private stage 1: genuine component and Hilbert-series norm summability.
These helpers retain the two actual complex components separately and derive
absolute norm summability from their Hölder product rows. -/

private def dmComponentResolventSeriesTerm
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ)
    (f : SourcePairL2) (b : Bool) (m : dmSectorType bc) :
    C(Icc (0 : ℝ) 1, ℂ) :=
  let i := dmSectorIndex bc hbc b m
  (dmScaledCoefficient bc n x t i * (freeZSBasis bc).repr f i) •
    NlsGge.Atomic.LIB026.representative (freeZSH1 bc i b)

private theorem dm_component_resolvent_series_term_norm_le
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ)
    (f : SourcePairL2) (b : Bool) (m : dmSectorType bc) :
    ‖dmComponentResolventSeriesTerm bc hbc n x t f b m‖ ≤
      ‖dmScaledCoefficient bc n x t (dmSectorIndex bc hbc b m)‖ *
        ‖(freeZSBasis bc).repr f (dmSectorIndex bc hbc b m)‖ := by
  let i := dmSectorIndex bc hbc b m
  rw [ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  intro y
  have hpair :
      ‖NlsGge.Atomic.LIB031.pairRepresentative (freeZSH1 bc i) y‖ ≤ 1 := by
    calc
      ‖NlsGge.Atomic.LIB031.pairRepresentative (freeZSH1 bc i) y‖ ≤
          ‖NlsGge.Atomic.LIB031.pairRepresentative (freeZSH1 bc i)‖ :=
        (NlsGge.Atomic.LIB031.pairRepresentative (freeZSH1 bc i)).norm_coe_le_norm y
      _ ≤ 1 := NlsGge.Atomic.LIB036.free_zs_sup_le_one bc i
  have hpair0 :
      0 ≤ ‖NlsGge.Atomic.LIB031.pairRepresentative (freeZSH1 bc i) y‖ :=
    norm_nonneg _
  have hpairSq := NlsGge.Atomic.LIB031.pairRepresentative_norm_sq
    (freeZSH1 bc i) y
  have hcomponent :
      ‖NlsGge.Atomic.LIB026.representative (freeZSH1 bc i b) y‖ ≤ 1 := by
    cases b with
    | false =>
        have htarget :
            0 ≤ ‖NlsGge.Atomic.LIB026.representative (freeZSH1 bc i false) y‖ :=
          norm_nonneg _
        have hother :
            0 ≤ ‖NlsGge.Atomic.LIB026.representative (freeZSH1 bc i true) y‖ :=
          norm_nonneg _
        have hpairSq_le :
            ‖NlsGge.Atomic.LIB031.pairRepresentative (freeZSH1 bc i) y‖ ^ 2 ≤ 1 := by
          have hsquare := (sq_le_sq₀ hpair0 (by norm_num : 0 ≤ (1 : ℝ))).2 hpair
          simpa using hsquare
        have htargetSq :
            ‖NlsGge.Atomic.LIB026.representative (freeZSH1 bc i false) y‖ ^ 2 ≤ 1 := by
          nlinarith [hpairSq, hpairSq_le, sq_nonneg
            (‖NlsGge.Atomic.LIB026.representative (freeZSH1 bc i true) y‖)]
        exact (sq_le_sq₀ htarget (by norm_num : 0 ≤ (1 : ℝ))).mp
          (by simpa using htargetSq)
    | true =>
        have htarget :
            0 ≤ ‖NlsGge.Atomic.LIB026.representative (freeZSH1 bc i true) y‖ :=
          norm_nonneg _
        have hother :
            0 ≤ ‖NlsGge.Atomic.LIB026.representative (freeZSH1 bc i false) y‖ :=
          norm_nonneg _
        have hpairSq_le :
            ‖NlsGge.Atomic.LIB031.pairRepresentative (freeZSH1 bc i) y‖ ^ 2 ≤ 1 := by
          have hsquare := (sq_le_sq₀ hpair0 (by norm_num : 0 ≤ (1 : ℝ))).2 hpair
          simpa using hsquare
        have htargetSq :
            ‖NlsGge.Atomic.LIB026.representative (freeZSH1 bc i true) y‖ ^ 2 ≤ 1 := by
          nlinarith [hpairSq, hpairSq_le, sq_nonneg
            (‖NlsGge.Atomic.LIB026.representative (freeZSH1 bc i false) y‖)]
        exact (sq_le_sq₀ htarget (by norm_num : 0 ≤ (1 : ℝ))).mp
          (by simpa using htargetSq)
  change ‖(dmScaledCoefficient bc n x t i *
      (freeZSBasis bc).repr f i) •
        NlsGge.Atomic.LIB026.representative (freeZSH1 bc i b) y‖ ≤ _
  calc
    _ = ‖dmScaledCoefficient bc n x t i *
          (freeZSBasis bc).repr f i‖ *
          ‖NlsGge.Atomic.LIB026.representative (freeZSH1 bc i b) y‖ := norm_smul ..
    _ ≤ ‖dmScaledCoefficient bc n x t i *
          (freeZSBasis bc).repr f i‖ := by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hcomponent
            (norm_nonneg (dmScaledCoefficient bc n x t i *
              (freeZSBasis bc).repr f i)))
    _ = ‖dmScaledCoefficient bc n x t i‖ *
          ‖(freeZSBasis bc).repr f i‖ := norm_mul ..

private theorem dm_component_resolvent_product_summable
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ) (hx : -1 ≤ x ∧ x ≤ 1)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (f : SourcePairL2) (b : Bool) :
    Summable (fun m : dmSectorType bc =>
      ‖dmScaledCoefficient bc n x t (dmSectorIndex bc hbc b m)‖ *
        ‖(freeZSBasis bc).repr f (dmSectorIndex bc hbc b m)‖) := by
  have hA := dm_resolvent_coefficient_energy_row_summable
    bc hbc n x t hx «hλ» b
  have hA' : Summable (fun m : dmSectorType bc =>
      ‖dmScaledCoefficient bc n x t (dmSectorIndex bc hbc b m)‖ ^ 2) :=
    hA.congr (fun m => by rfl)
  have hC := dm_input_coefficient_energy_row_summable
    bc hbc f b
  let A : lp (fun _ : dmSectorType bc => ℂ) 2 :=
    ⟨fun m => dmScaledCoefficient bc n x t (dmSectorIndex bc hbc b m),
      memℓp_gen (by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hA')⟩
  let C : lp (fun _ : dmSectorType bc => ℂ) 2 :=
    ⟨fun m => (freeZSBasis bc).repr f (dmSectorIndex bc hbc b m),
      memℓp_gen (by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hC)⟩
  have hpq : (2 : ENNReal).toReal.HolderConjugate (2 : ENNReal).toReal := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hHolder := lp.tsum_mul_le_mul_norm hpq A C
  simpa [A, C] using hHolder.1

private theorem dm_component_resolvent_series_summable
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ) (hx : -1 ≤ x ∧ x ≤ 1)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (f : SourcePairL2) (b : Bool) :
    Summable (fun m : dmSectorType bc =>
      dmComponentResolventSeriesTerm bc hbc n x t f b m) := by
  apply Summable.of_norm_bounded
    (dm_component_resolvent_product_summable bc hbc n x t hx «hλ» f b)
  intro m
  exact dm_component_resolvent_series_term_norm_le
    bc hbc n x t f b m

private theorem dm_component_resolvent_series_norm_summable
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ) (hx : -1 ≤ x ∧ x ≤ 1)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (f : SourcePairL2) (b : Bool) :
    Summable (fun m : dmSectorType bc =>
      ‖dmComponentResolventSeriesTerm bc hbc n x t f b m‖) := by
  apply Summable.of_nonneg_of_le
    (fun m => norm_nonneg _)
    (fun m => dm_component_resolvent_series_term_norm_le
      bc hbc n x t f b m)
  exact dm_component_resolvent_product_summable bc hbc n x t hx «hλ» f b

private def dmResolventHilbertSeriesTerm
    (bc : ZSBoundaryCondition)
    (n : ℤ) (x t : ℝ)
    (f : SourcePairL2) (i : FreeIndex bc) : SourcePairL2 :=
  (dmScaledCoefficient bc n x t i * (freeZSBasis bc).repr f i) •
    freeZSBasis bc i

private theorem dm_resolvent_hilbert_series_term_norm
    (bc : ZSBoundaryCondition)
    (n : ℤ) (x t : ℝ) (f : SourcePairL2) (i : FreeIndex bc) :
    ‖dmResolventHilbertSeriesTerm bc n x t f i‖ =
      ‖dmScaledCoefficient bc n x t i‖ *
        ‖(freeZSBasis bc).repr f i‖ := by
  rw [dmResolventHilbertSeriesTerm, norm_smul,
    NlsGge.Atomic.LIB036.free_zs_normalized, mul_one, norm_mul]

private theorem dm_resolvent_hilbert_series_norm_summable
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ) (hx : -1 ≤ x ∧ x ≤ 1)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (f : SourcePairL2) :
    Summable (fun i : FreeIndex bc =>
      ‖dmResolventHilbertSeriesTerm bc n x t f i‖) := by
  rcases hbc with hbc | hbc
  · subst bc
    have hrow (b : Bool) : Summable (fun m : Sector 0 =>
        ‖dmScaledCoefficient .periodic n x t (b, m)‖ *
          ‖(freeZSBasis .periodic).repr f (b, m)‖) := by
      simpa [dmSectorIndex, dmSectorType] using
        (dm_component_resolvent_product_summable .periodic (Or.inl rfl)
          n x t hx «hλ» f b)
    have hnonneg (p : Bool × Sector 0) :
        0 ≤ ‖dmScaledCoefficient .periodic n x t p‖ *
          ‖(freeZSBasis .periodic).repr f p‖ := by
      positivity
    have houter : Summable (fun b : Bool =>
        ∑' m : Sector 0,
          ‖dmScaledCoefficient .periodic n x t (b, m)‖ *
            ‖(freeZSBasis .periodic).repr f (b, m)‖) :=
      (hasSum_fintype (fun b : Bool =>
        ∑' m : Sector 0,
          ‖dmScaledCoefficient .periodic n x t (b, m)‖ *
            ‖(freeZSBasis .periodic).repr f (b, m)‖)).summable
    have hprod : Summable (fun p : Bool × Sector 0 =>
        ‖dmScaledCoefficient .periodic n x t p‖ *
          ‖(freeZSBasis .periodic).repr f p‖) := by
      rw [summable_prod_of_nonneg hnonneg]
      exact ⟨hrow, houter⟩
    change Summable (fun i : Bool × Sector 0 =>
      ‖dmResolventHilbertSeriesTerm .periodic n x t f i‖)
    apply hprod.congr
    intro i
    exact (dm_resolvent_hilbert_series_term_norm
      .periodic n x t f i).symm
  · subst bc
    have hrow (b : Bool) : Summable (fun m : Sector 1 =>
        ‖dmScaledCoefficient .antiperiodic n x t (b, m)‖ *
          ‖(freeZSBasis .antiperiodic).repr f (b, m)‖) := by
      simpa [dmSectorIndex, dmSectorType] using
        (dm_component_resolvent_product_summable .antiperiodic (Or.inr rfl)
          n x t hx «hλ» f b)
    have hnonneg (p : Bool × Sector 1) :
        0 ≤ ‖dmScaledCoefficient .antiperiodic n x t p‖ *
          ‖(freeZSBasis .antiperiodic).repr f p‖ := by
      positivity
    have houter : Summable (fun b : Bool =>
        ∑' m : Sector 1,
          ‖dmScaledCoefficient .antiperiodic n x t (b, m)‖ *
            ‖(freeZSBasis .antiperiodic).repr f (b, m)‖) :=
      (hasSum_fintype (fun b : Bool =>
        ∑' m : Sector 1,
          ‖dmScaledCoefficient .antiperiodic n x t (b, m)‖ *
            ‖(freeZSBasis .antiperiodic).repr f (b, m)‖)).summable
    have hprod : Summable (fun p : Bool × Sector 1 =>
        ‖dmScaledCoefficient .antiperiodic n x t p‖ *
          ‖(freeZSBasis .antiperiodic).repr f p‖) := by
      rw [summable_prod_of_nonneg hnonneg]
      exact ⟨hrow, houter⟩
    change Summable (fun i : Bool × Sector 1 =>
      ‖dmResolventHilbertSeriesTerm .antiperiodic n x t f i‖)
    apply hprod.congr
    intro i
    exact (dm_resolvent_hilbert_series_term_norm
      .antiperiodic n x t f i).symm

/-! Private stage 2: actual product projection and same-witness representative. -/

private def dmComponentResolventSeriesSum
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ) (f : SourcePairL2) (b : Bool) :
    C(Icc (0 : ℝ) 1, ℂ) :=
  ∑' m : dmSectorType bc,
    dmComponentResolventSeriesTerm bc hbc n x t f b m

private def dmResolventComponentProjection (b : Bool) :
    SourcePairL2 →L[ℂ] SourceIntervalL2 :=
  PiLp.proj (𝕜 := ℂ) 2 (fun _ : Bool => SourceIntervalL2) b

private theorem dm_resolvent_hilbert_series_hasSum
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (hsum : Summable (dmLatticeTerm bc (dmLambda n x t)))
    (f : SourcePairL2) :
    HasSum (fun i : FreeIndex bc =>
      dmResolventHilbertSeriesTerm bc n x t f i)
      (dmFreeResolvent bc hbc n x t «hλ» hsum f) := by
  simpa only [dmResolventHilbertSeriesTerm, dmFreeResolvent_repr] using
    (freeZSBasis bc).hasSum_repr
      (dmFreeResolvent bc hbc n x t «hλ» hsum f)

private theorem dm_parity_off_channel_representative_zero
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (c b : Bool) (m : dmSectorType bc) (hcb : c ≠ b) :
    NlsGge.Atomic.LIB026.representative
      (freeZSH1 bc (dmSectorIndex bc hbc c m) b) = 0 := by
  rcases hbc with hbc | hbc
  · subst bc
    apply ContinuousMap.ext
    intro y
    change NlsGge.Atomic.LIB026.representative
      (NlsGge.Atomic.LIB036.parityH1 0 (c, m) b) y = 0
    rw [NlsGge.Atomic.LIB036.parity_representative_formula]
    simp [NlsGge.Atomic.LIB036.unitAmplitude, Ne.symm hcb]
  · subst bc
    apply ContinuousMap.ext
    intro y
    change NlsGge.Atomic.LIB026.representative
      (NlsGge.Atomic.LIB036.parityH1 1 (c, m) b) y = 0
    rw [NlsGge.Atomic.LIB036.parity_representative_formula]
    simp [NlsGge.Atomic.LIB036.unitAmplitude, Ne.symm hcb]

private theorem dm_resolvent_projection_term_eq
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ) (f : SourcePairL2)
    (c b : Bool) (m : dmSectorType bc) :
    dmResolventComponentProjection b
        (dmResolventHilbertSeriesTerm bc n x t f
          (dmSectorIndex bc hbc c m)) =
      if c = b then
        dmIccExtendSourceIntervalL2CLM
          (dmComponentResolventSeriesTerm bc hbc n x t f b m)
      else 0 := by
  by_cases hcb : c = b
  · subst c
    simp [dmResolventComponentProjection, dmResolventHilbertSeriesTerm,
      dmComponentResolventSeriesTerm]
    rw [dmIccExtendSourceIntervalL2_freeZSBasis_component]
  · have hrep := dm_parity_off_channel_representative_zero
      bc hbc c b m hcb
    have hcomponent :
        (freeZSBasis bc (dmSectorIndex bc hbc c m)) b = 0 := by
      calc
        _ = dmIccExtendSourceIntervalL2CLM
            (NlsGge.Atomic.LIB026.representative
              (freeZSH1 bc (dmSectorIndex bc hbc c m) b)) :=
          (dmIccExtendSourceIntervalL2_freeZSBasis_component
            bc (dmSectorIndex bc hbc c m) b).symm
        _ = 0 := by rw [hrep]; simp
    simp [hcb, dmResolventComponentProjection,
      dmResolventHilbertSeriesTerm, dmComponentResolventSeriesTerm, hcomponent]

private theorem dm_component_resolvent_toLp_hasSum
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ) (hx : -1 ≤ x ∧ x ≤ 1)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (f : SourcePairL2) (b : Bool) :
    HasSum (fun m : dmSectorType bc =>
      dmIccExtendSourceIntervalL2CLM
        (dmComponentResolventSeriesTerm bc hbc n x t f b m))
      (dmIccExtendSourceIntervalL2CLM
        (dmComponentResolventSeriesSum bc hbc n x t f b)) := by
  exact ((dm_component_resolvent_series_summable
    bc hbc n x t hx «hλ» f b).hasSum).mapL dmIccExtendSourceIntervalL2CLM

private theorem dm_resolvent_component_l2_equals_continuous_series
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (hsum : Summable (dmLatticeTerm bc (dmLambda n x t)))
    (hx : -1 ≤ x ∧ x ≤ 1) (f : SourcePairL2) (b : Bool) :
    dmIccExtendSourceIntervalL2CLM
        (dmComponentResolventSeriesSum bc hbc n x t f b) =
      (dmFreeResolvent bc hbc n x t «hλ» hsum f) b := by
  rcases hbc with hbc | hbc
  · subst bc
    let P := dmResolventComponentProjection b
    have hseries : HasSum
        (fun i : Bool × Sector 0 =>
          dmResolventHilbertSeriesTerm .periodic n x t f i)
        (dmFreeResolvent .periodic (Or.inl rfl) n x t «hλ» hsum f) := by
      simpa only [FreeIndex] using
        (dm_resolvent_hilbert_series_hasSum .periodic (Or.inl rfl)
          n x t «hλ» hsum f)
    have hproj : HasSum
        (fun i : Bool × Sector 0 => P
          (dmResolventHilbertSeriesTerm .periodic n x t f i))
        (P (dmFreeResolvent .periodic (Or.inl rfl) n x t «hλ» hsum f)) :=
      hseries.mapL P
    have hrows (c : Bool) : HasSum
        (fun m : Sector 0 => P
          (dmResolventHilbertSeriesTerm .periodic n x t f (c, m)))
        (if c = b then
          dmIccExtendSourceIntervalL2CLM
            (dmComponentResolventSeriesSum .periodic (Or.inl rfl)
              n x t f b)
        else 0) := by
      by_cases hcb : c = b
      · subst c
        simp only [if_pos rfl]
        apply HasSum.congr_fun
          (dm_component_resolvent_toLp_hasSum .periodic (Or.inl rfl)
            n x t hx «hλ» f b)
        intro m
        simpa [P, dmSectorIndex] using
          (dm_resolvent_projection_term_eq .periodic (Or.inl rfl)
            n x t f b b m)
      · have hzero : ∀ m : Sector 0,
            P (dmResolventHilbertSeriesTerm .periodic n x t f (c, m)) = 0 := by
          intro m
          simpa [hcb, P, dmSectorIndex] using
            (dm_resolvent_projection_term_eq .periodic (Or.inl rfl)
              n x t f c b m)
        simpa [hcb, hzero] using
          (hasSum_zero : HasSum (fun _ : Sector 0 =>
            (0 : SourceIntervalL2)) 0)
    have hrowsTsum (c : Bool) : HasSum
        (fun m : Sector 0 => P
          (dmResolventHilbertSeriesTerm .periodic n x t f (c, m)))
        (∑' m : Sector 0, P
          (dmResolventHilbertSeriesTerm .periodic n x t f (c, m))) :=
      (hrows c).summable.hasSum
    have hfib : HasSum
        (fun c : Bool => ∑' m : Sector 0,
          P (dmResolventHilbertSeriesTerm .periodic n x t f (c, m)))
        (P (dmFreeResolvent .periodic (Or.inl rfl) n x t «hλ» hsum f)) :=
      HasSum.prod_fiberwise hproj hrowsTsum
    have hsumBool := hfib.tsum_eq
    simp only [tsum_fintype, Fintype.sum_bool] at hsumBool
    rw [(hrows true).tsum_eq, (hrows false).tsum_eq] at hsumBool
    cases b <;> simpa [P, dmResolventComponentProjection] using hsumBool
  · subst bc
    let P := dmResolventComponentProjection b
    have hseries : HasSum
        (fun i : Bool × Sector 1 =>
          dmResolventHilbertSeriesTerm .antiperiodic n x t f i)
        (dmFreeResolvent .antiperiodic (Or.inr rfl) n x t «hλ» hsum f) := by
      simpa only [FreeIndex] using
        (dm_resolvent_hilbert_series_hasSum .antiperiodic (Or.inr rfl)
          n x t «hλ» hsum f)
    have hproj : HasSum
        (fun i : Bool × Sector 1 => P
          (dmResolventHilbertSeriesTerm .antiperiodic n x t f i))
        (P (dmFreeResolvent .antiperiodic (Or.inr rfl) n x t «hλ» hsum f)) :=
      hseries.mapL P
    have hrows (c : Bool) : HasSum
        (fun m : Sector 1 => P
          (dmResolventHilbertSeriesTerm .antiperiodic n x t f (c, m)))
        (if c = b then
          dmIccExtendSourceIntervalL2CLM
            (dmComponentResolventSeriesSum .antiperiodic (Or.inr rfl)
              n x t f b)
        else 0) := by
      by_cases hcb : c = b
      · subst c
        simp only [if_pos rfl]
        apply HasSum.congr_fun
          (dm_component_resolvent_toLp_hasSum .antiperiodic (Or.inr rfl)
            n x t hx «hλ» f b)
        intro m
        simpa [P, dmSectorIndex] using
          (dm_resolvent_projection_term_eq .antiperiodic (Or.inr rfl)
            n x t f b b m)
      · have hzero : ∀ m : Sector 1,
            P (dmResolventHilbertSeriesTerm .antiperiodic n x t f (c, m)) = 0 := by
          intro m
          simpa [hcb, P, dmSectorIndex] using
            (dm_resolvent_projection_term_eq .antiperiodic (Or.inr rfl)
              n x t f c b m)
        simpa [hcb, hzero] using
          (hasSum_zero : HasSum (fun _ : Sector 1 =>
            (0 : SourceIntervalL2)) 0)
    have hrowsTsum (c : Bool) : HasSum
        (fun m : Sector 1 => P
          (dmResolventHilbertSeriesTerm .antiperiodic n x t f (c, m)))
        (∑' m : Sector 1, P
          (dmResolventHilbertSeriesTerm .antiperiodic n x t f (c, m))) :=
      (hrows c).summable.hasSum
    have hfib : HasSum
        (fun c : Bool => ∑' m : Sector 1,
          P (dmResolventHilbertSeriesTerm .antiperiodic n x t f (c, m)))
        (P (dmFreeResolvent .antiperiodic (Or.inr rfl) n x t «hλ» hsum f)) :=
      HasSum.prod_fiberwise hproj hrowsTsum
    have hsumBool := hfib.tsum_eq
    simp only [tsum_fintype, Fintype.sum_bool] at hsumBool
    rw [(hrows true).tsum_eq, (hrows false).tsum_eq] at hsumBool
    cases b <;> simpa [P, dmResolventComponentProjection] using hsumBool

private theorem dm_component_series_eq_actual_representative
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (hsum : Summable (dmLatticeTerm bc (dmLambda n x t)))
    (hx : -1 ≤ x ∧ x ≤ 1) (f : SourcePairL2) (b : Bool) :
    dmComponentResolventSeriesSum bc hbc n x t f b =
      NlsGge.Atomic.LIB026.representative
        (dmFreeResolventH1 bc hbc n x t «hλ» hsum f b) := by
  let G := dmComponentResolventSeriesSum bc hbc n x t f b
  have hLp := dm_resolvent_component_l2_equals_continuous_series
    bc hbc n x t «hλ» hsum hx f b
  have hvalue := dmFreeResolventH1_value bc hbc n x t «hλ» hsum f
  have hcomponent :
      (dmFreeResolventH1 bc hbc n x t «hλ» hsum f b).value =
        (dmFreeResolvent bc hbc n x t «hλ» hsum f) b := by
    simpa only [NlsGge.Atomic.Interval.h1PairValue] using
      congrArg (fun z : SourcePairL2 => z b) hvalue
  have hLp_ae :
      (dmIccExtendSourceIntervalL2CLM G : ℝ → ℂ) =ᵐ[dmIntervalMeasure]
        ((dmFreeResolvent bc hbc n x t «hλ» hsum f) b : ℝ → ℂ) :=
    MeasureTheory.Lp.ext_iff.mp hLp
  have hcomponent_ae :
      ((dmFreeResolvent bc hbc n x t «hλ» hsum f) b : ℝ → ℂ) =ᵐ[dmIntervalMeasure]
        (dmFreeResolventH1 bc hbc n x t «hλ» hsum f b).value :=
    (MeasureTheory.Lp.ext_iff.mp hcomponent).symm
  have hGae : Set.IccExtend zero_le_one G =ᵐ[dmIntervalMeasure]
      (dmFreeResolventH1 bc hbc n x t «hλ» hsum f b).value := by
    exact (dmIccExtendSourceIntervalL2_ae G).symm.trans
      (hLp_ae.trans hcomponent_ae)
  exact NlsGge.Atomic.LIB026.representative_eq_of_ae
    (dmFreeResolventH1 bc hbc n x t «hλ» hsum f b) G hGae



/-! Private Stage 3: the sharp continuous representative bound. -/

private theorem dm_component_resolvent_series_norm_le
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ) (hx : -1 ≤ x ∧ x ≤ 1)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (f : SourcePairL2) (b : Bool) :
    ‖dmComponentResolventSeriesSum bc hbc n x t f b‖ ≤
      Real.sqrt (dmResolventCoefficientEnergy bc hbc n x t «hλ») *
        Real.sqrt (dmInputCoefficientEnergy bc hbc f b) := by
  have hA := dm_resolvent_coefficient_energy_row_summable
    bc hbc n x t hx «hλ» b
  have hA' : Summable (fun m : dmSectorType bc =>
      ‖dmScaledCoefficient bc n x t (dmSectorIndex bc hbc b m)‖ ^ 2) :=
    hA.congr (fun m => by rfl)
  have hC := dm_input_coefficient_energy_row_summable bc hbc f b
  let A : lp (fun _ : dmSectorType bc => ℂ) (2 : ENNReal) :=
    ⟨fun m => dmScaledCoefficient bc n x t (dmSectorIndex bc hbc b m),
      memℓp_gen (by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hA')⟩
  let C : lp (fun _ : dmSectorType bc => ℂ) (2 : ENNReal) :=
    ⟨fun m => (freeZSBasis bc).repr f (dmSectorIndex bc hbc b m),
      memℓp_gen (by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hC)⟩
  have hpq : (2 : ENNReal).toReal.HolderConjugate
      (2 : ENNReal).toReal := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hproducts := lp.tsum_mul_le_mul_norm hpq A C
  have hnorms : Summable (fun m : dmSectorType bc =>
      ‖dmComponentResolventSeriesTerm bc hbc n x t f b m‖) :=
    Summable.of_nonneg_of_le
      (fun m => norm_nonneg _)
      (fun m => dm_component_resolvent_series_term_norm_le
        bc hbc n x t f b m)
      hproducts.1
  have hcontinuous_norm :
      ‖dmComponentResolventSeriesSum bc hbc n x t f b‖ ≤
        ‖A‖ * ‖C‖ := by
    calc
      ‖dmComponentResolventSeriesSum bc hbc n x t f b‖ ≤
          ∑' m : dmSectorType bc,
            ‖dmComponentResolventSeriesTerm bc hbc n x t f b m‖ :=
        norm_tsum_le_tsum_norm hnorms
      _ ≤ ∑' m : dmSectorType bc,
          ‖dmScaledCoefficient bc n x t (dmSectorIndex bc hbc b m)‖ *
            ‖(freeZSBasis bc).repr f (dmSectorIndex bc hbc b m)‖ :=
        hnorms.tsum_le_tsum
          (fun m => dm_component_resolvent_series_term_norm_le
            bc hbc n x t f b m) hproducts.1
      _ ≤ ‖A‖ * ‖C‖ := hproducts.2
  have hrow_eq (m : dmSectorType bc) :
      dmResolventCoefficientEnergyRow bc hbc n x t «hλ» true m =
        dmResolventCoefficientEnergyRow bc hbc n x t «hλ» b m := by
    calc
      _ = dmLatticeTerm bc (dmLambda n x t)
            (dmSectorFrequencyEquiv bc hbc m) / Real.pi ^ 2 :=
        dm_resolvent_coefficient_energy_term
          bc hbc n x t «hλ» true m
      _ = _ := (dm_resolvent_coefficient_energy_term
        bc hbc n x t «hλ» b m).symm
  have henergy_row :
      dmResolventCoefficientEnergy bc hbc n x t «hλ» =
        ∑' m : dmSectorType bc,
          dmResolventCoefficientEnergyRow bc hbc n x t «hλ» b m := by
    unfold dmResolventCoefficientEnergy
    exact tsum_congr hrow_eq
  have hA_sq : ‖A‖ ^ 2 =
      dmResolventCoefficientEnergy bc hbc n x t «hλ» := by
    calc
      ‖A‖ ^ 2 = ∑' m : dmSectorType bc, ‖A m‖ ^ 2 := by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
          (lp.norm_rpow_eq_tsum
            (by norm_num : 0 < (2 : ENNReal).toReal) A)
      _ = ∑' m : dmSectorType bc,
          dmResolventCoefficientEnergyRow bc hbc n x t «hλ» b m := by rfl
      _ = dmResolventCoefficientEnergy bc hbc n x t «hλ» :=
        henergy_row.symm
  have hC_sq : ‖C‖ ^ 2 = dmInputCoefficientEnergy bc hbc f b := by
    calc
      ‖C‖ ^ 2 = ∑' m : dmSectorType bc, ‖C m‖ ^ 2 := by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
          (lp.norm_rpow_eq_tsum
            (by norm_num : 0 < (2 : ENNReal).toReal) C)
      _ = dmInputCoefficientEnergy bc hbc f b := by rfl
  have hA0 : 0 ≤ dmResolventCoefficientEnergy bc hbc n x t «hλ» := by
    unfold dmResolventCoefficientEnergy dmResolventCoefficientEnergyRow
    exact tsum_nonneg (fun _ => sq_nonneg _)
  have hE0 : 0 ≤ dmInputCoefficientEnergy bc hbc f b := by
    unfold dmInputCoefficientEnergy
    exact tsum_nonneg (fun _ => sq_nonneg _)
  have hAnorm : ‖A‖ =
      Real.sqrt (dmResolventCoefficientEnergy bc hbc n x t «hλ») := by
    calc
      ‖A‖ = Real.sqrt (‖A‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      _ = _ := by rw [hA_sq]
  have hCnorm : ‖C‖ =
      Real.sqrt (dmInputCoefficientEnergy bc hbc f b) := by
    calc
      ‖C‖ = Real.sqrt (‖C‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      _ = _ := by rw [hC_sq]
  calc
    ‖dmComponentResolventSeriesSum bc hbc n x t f b‖ ≤
        ‖A‖ * ‖C‖ := hcontinuous_norm
    _ = Real.sqrt (dmResolventCoefficientEnergy bc hbc n x t «hλ») *
        Real.sqrt (dmInputCoefficientEnergy bc hbc f b) := by
      rw [hAnorm, hCnorm]

private theorem dm_component_representative_norm_sq_le
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ) (hx : -1 ≤ x ∧ x ≤ 1)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (hsum : Summable (dmLatticeTerm bc (dmLambda n x t)))
    (f : SourcePairL2) (b : Bool) (y : Icc (0 : ℝ) 1) :
    ‖NlsGge.Atomic.LIB026.representative
        (dmFreeResolventH1 bc hbc n x t «hλ» hsum f b) y‖ ^ 2 ≤
      dmResolventCoefficientEnergy bc hbc n x t «hλ» *
        dmInputCoefficientEnergy bc hbc f b := by
  have hG := dm_component_resolvent_series_norm_le
    bc hbc n x t hx «hλ» f b
  have hrep := dm_component_series_eq_actual_representative
    bc hbc n x t «hλ» hsum hx f b
  have hpoint :
      ‖NlsGge.Atomic.LIB026.representative
          (dmFreeResolventH1 bc hbc n x t «hλ» hsum f b) y‖ ≤
        ‖dmComponentResolventSeriesSum bc hbc n x t f b‖ := by
    rw [← DFunLike.congr_fun hrep y]
    exact (dmComponentResolventSeriesSum bc hbc n x t f b).norm_coe_le_norm y
  have hA0 : 0 ≤ dmResolventCoefficientEnergy bc hbc n x t «hλ» := by
    unfold dmResolventCoefficientEnergy dmResolventCoefficientEnergyRow
    exact tsum_nonneg (fun _ => sq_nonneg _)
  have hE0 : 0 ≤ dmInputCoefficientEnergy bc hbc f b := by
    unfold dmInputCoefficientEnergy
    exact tsum_nonneg (fun _ => sq_nonneg _)
  have hsqprod :
      (Real.sqrt (dmResolventCoefficientEnergy bc hbc n x t «hλ») *
        Real.sqrt (dmInputCoefficientEnergy bc hbc f b)) ^ 2 =
      dmResolventCoefficientEnergy bc hbc n x t «hλ» *
        dmInputCoefficientEnergy bc hbc f b := by
    rw [mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hE0]
  calc
    _ ≤ (Real.sqrt (dmResolventCoefficientEnergy bc hbc n x t «hλ») *
          Real.sqrt (dmInputCoefficientEnergy bc hbc f b)) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr (hpoint.trans hG)
    _ = dmResolventCoefficientEnergy bc hbc n x t «hλ» *
          dmInputCoefficientEnergy bc hbc f b := hsqprod

private theorem dm_free_resolvent_pair_norm_sq_le
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ) (hx : -1 ≤ x ∧ x ≤ 1)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (hsum : Summable (dmLatticeTerm bc (dmLambda n x t)))
    (f : SourcePairL2) (y : Icc (0 : ℝ) 1) :
    ‖NlsGge.Atomic.LIB031.pairRepresentative
        (dmFreeResolventH1 bc hbc n x t «hλ» hsum f) y‖ ^ 2 ≤
      dmResolventCoefficientEnergy bc hbc n x t «hλ» * ‖f‖ ^ 2 := by
  rw [NlsGge.Atomic.LIB031.pairRepresentative_norm_sq]
  calc
    _ ≤ dmResolventCoefficientEnergy bc hbc n x t «hλ» *
          dmInputCoefficientEnergy bc hbc f true +
        dmResolventCoefficientEnergy bc hbc n x t «hλ» *
          dmInputCoefficientEnergy bc hbc f false :=
      add_le_add
        (dm_component_representative_norm_sq_le
          bc hbc n x t hx «hλ» hsum f true y)
        (dm_component_representative_norm_sq_le
          bc hbc n x t hx «hλ» hsum f false y)
    _ = dmResolventCoefficientEnergy bc hbc n x t «hλ» *
          (dmInputCoefficientEnergy bc hbc f true +
            dmInputCoefficientEnergy bc hbc f false) := by ring
    _ = dmResolventCoefficientEnergy bc hbc n x t «hλ» * ‖f‖ ^ 2 := by
      rw [dm_input_coefficient_energies_sum bc hbc f]

private theorem dm_free_resolvent_pair_pointwise_le
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ) (hx : -1 ≤ x ∧ x ≤ 1)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (hsum : Summable (dmLatticeTerm bc (dmLambda n x t)))
    (f : SourcePairL2) (y : Icc (0 : ℝ) 1) :
    ‖NlsGge.Atomic.LIB031.pairRepresentative
        (dmFreeResolventH1 bc hbc n x t «hλ» hsum f) y‖ ≤
      (Real.sqrt (dmLatticeSum bc (dmLambda n x t)) / Real.pi) * ‖f‖ := by
  have hL0 : 0 ≤ dmLatticeSum bc (dmLambda n x t) := by
    unfold dmLatticeSum
    exact tsum_nonneg (fun k => dm_latticeTerm_nonneg bc (dmLambda n x t) k)
  have hK0 : 0 ≤ Real.sqrt (dmLatticeSum bc (dmLambda n x t)) / Real.pi :=
    div_nonneg (Real.sqrt_nonneg _) Real.pi_pos.le
  have hKsq :
      (Real.sqrt (dmLatticeSum bc (dmLambda n x t)) / Real.pi) ^ 2 =
        dmLatticeSum bc (dmLambda n x t) / Real.pi ^ 2 := by
    rw [div_pow, Real.sq_sqrt hL0]
  have hpairSq := dm_free_resolvent_pair_norm_sq_le
    bc hbc n x t hx «hλ» hsum f y
  have hpairSqSource :
      ‖NlsGge.Atomic.LIB031.pairRepresentative
          (dmFreeResolventH1 bc hbc n x t «hλ» hsum f) y‖ ^ 2 ≤
        (dmLatticeSum bc (dmLambda n x t) / Real.pi ^ 2) * ‖f‖ ^ 2 := by
    calc
      _ ≤ dmResolventCoefficientEnergy bc hbc n x t «hλ» * ‖f‖ ^ 2 := hpairSq
      _ = (dmLatticeSum bc (dmLambda n x t) / Real.pi ^ 2) * ‖f‖ ^ 2 := by
        rw [dm_resolvent_coefficient_energy_eq bc hbc n x t hx «hλ»]
  have hpair0 : 0 ≤ ‖NlsGge.Atomic.LIB031.pairRepresentative
      (dmFreeResolventH1 bc hbc n x t «hλ» hsum f) y‖ := norm_nonneg _
  have hKf0 : 0 ≤
      (Real.sqrt (dmLatticeSum bc (dmLambda n x t)) / Real.pi) * ‖f‖ :=
    mul_nonneg hK0 (norm_nonneg _)
  apply (sq_le_sq₀ hpair0 hKf0).mp
  calc
    ‖NlsGge.Atomic.LIB031.pairRepresentative
        (dmFreeResolventH1 bc hbc n x t «hλ» hsum f) y‖ ^ 2 ≤
        (dmLatticeSum bc (dmLambda n x t) / Real.pi ^ 2) * ‖f‖ ^ 2 := hpairSqSource
    _ = ((Real.sqrt (dmLatticeSum bc (dmLambda n x t)) / Real.pi) *
          ‖f‖) ^ 2 := by rw [mul_pow, hKsq]

private theorem dm_free_resolvent_to_sup_linear_bound
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ) (hx : -1 ≤ x ∧ x ≤ 1)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (hsum : Summable (dmLatticeTerm bc (dmLambda n x t)))
    (f : SourcePairL2) :
    ‖dmFreeResolventToSupLinear bc hbc n x t «hλ» hsum f‖ ≤
      (Real.sqrt (dmLatticeSum bc (dmLambda n x t)) / Real.pi) * ‖f‖ := by
  have hL0 : 0 ≤ dmLatticeSum bc (dmLambda n x t) := by
    unfold dmLatticeSum
    exact tsum_nonneg (fun k => dm_latticeTerm_nonneg bc (dmLambda n x t) k)
  have hK0 : 0 ≤ Real.sqrt (dmLatticeSum bc (dmLambda n x t)) / Real.pi :=
    div_nonneg (Real.sqrt_nonneg _) Real.pi_pos.le
  apply (ContinuousMap.norm_le _ (mul_nonneg hK0 (norm_nonneg _))).2
  intro y
  exact dm_free_resolvent_pair_pointwise_le
    bc hbc n x t hx «hλ» hsum f y

private noncomputable def dmFreeResolventToSupCLM
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ) (hx : -1 ≤ x ∧ x ≤ 1)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (hsum : Summable (dmLatticeTerm bc (dmLambda n x t))) :
    SourcePairL2 →L[ℂ] C(Icc (0 : ℝ) 1, NlsGge.Atomic.LIB031.PointPair) :=
  (dmFreeResolventToSupLinear bc hbc n x t «hλ» hsum).mkContinuous
    (Real.sqrt (dmLatticeSum bc (dmLambda n x t)) / Real.pi)
    (dm_free_resolvent_to_sup_linear_bound
      bc hbc n x t hx «hλ» hsum)

private theorem dm_free_resolvent_to_sup_clm_norm_le
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ) (hx : -1 ≤ x ∧ x ≤ 1)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc)
    (hsum : Summable (dmLatticeTerm bc (dmLambda n x t))) :
    ‖dmFreeResolventToSupCLM bc hbc n x t hx «hλ» hsum‖ ≤
      Real.sqrt (dmLatticeSum bc (dmLambda n x t)) / Real.pi := by
  change ‖(dmFreeResolventToSupLinear bc hbc n x t «hλ» hsum).mkContinuous
      (Real.sqrt (dmLatticeSum bc (dmLambda n x t)) / Real.pi)
      (dm_free_resolvent_to_sup_linear_bound
        bc hbc n x t hx «hλ» hsum)‖ ≤ _
  exact LinearMap.mkContinuous_norm_le
    (dmFreeResolventToSupLinear bc hbc n x t «hλ» hsum)
    (div_nonneg (Real.sqrt_nonneg _) Real.pi_pos.le)
    (dm_free_resolvent_to_sup_linear_bound
      bc hbc n x t hx «hλ» hsum)

/-- The actual free Dirac resolvent on the Per± source strip, together with its
canonical continuous representative and the source's sharp lattice bound. -/
theorem dm_free_resolvent_realization
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ) (hx : -1 ≤ x ∧ x ≤ 1)
    («hλ» : dmLambda n x t ∉ dmSourceFrequencySet bc) :
    ∃ (R : SourcePairL2 →L[ℂ] SourcePairL2),
      ∃ (T : SourcePairL2 →L[ℂ] C(Icc (0 : ℝ) 1, PointPair)),
        ∃ (hR : ∀ f : SourcePairL2,
          R f ∈ (NlsGge.Atomic.LIB033.zsRealization 0 bc).domain),
        (∀ f : SourcePairL2, ∀ i : FreeIndex bc,
          (freeZSBasis bc).repr (R f) i =
            (((Real.pi : ℂ) * dmLambda n x t - freeEigenvalue bc i)⁻¹) *
              (freeZSBasis bc).repr f i) ∧
        (∀ f : SourcePairL2, ∀ i : FreeIndex bc,
          (freeZSBasis bc).repr
            (NlsGge.Atomic.LIB033.zsRealization 0 bc
              ⟨R f, hR f⟩) i =
            (freeEigenvalue bc i *
              (((Real.pi : ℂ) * dmLambda n x t - freeEigenvalue bc i)⁻¹)) *
              (freeZSBasis bc).repr f i) ∧
        (∀ f : SourcePairL2,
          ((Real.pi : ℂ) * dmLambda n x t) • R f -
            NlsGge.Atomic.LIB033.zsRealization 0 bc
              ⟨R f, hR f⟩ = f) ∧
        (∀ u : (NlsGge.Atomic.LIB033.zsRealization 0 bc).domain,
          R (((Real.pi : ℂ) * dmLambda n x t) • (u : SourcePairL2) -
            NlsGge.Atomic.LIB033.zsRealization 0 bc u) = u) ∧
        (∀ f : SourcePairL2,
          T f = NlsGge.Atomic.LIB031.pairRepresentative
            (NlsGge.Atomic.LIB033.domainLift
              (⟨R f, hR f⟩ : NlsGge.Atomic.LIB033.zsDomain bc))) ∧
        ‖T‖ ≤ Real.sqrt (dmLatticeSum bc (dmLambda n x t)) / Real.pi := by
  have hscalar : dmLambda n x t ∉
      Set.range (fun k : DMFrequency bc => (k.val : ℂ)) := by
    rw [← dm_sourceFrequencySet_eq_parityFrequencySet bc hbc]
    exact «hλ»
  have hsum : Summable (dmLatticeTerm bc (dmLambda n x t)) :=
    dm_resolvent_lattice_summable bc hbc n x t hx hscalar
  let R : SourcePairL2 →L[ℂ] SourcePairL2 :=
    dmFreeResolvent bc hbc n x t «hλ» hsum
  let T : SourcePairL2 →L[ℂ] C(Icc (0 : ℝ) 1, PointPair) :=
    dmFreeResolventToSupCLM bc hbc n x t hx «hλ» hsum
  let hR : ∀ f : SourcePairL2,
      R f ∈ (NlsGge.Atomic.LIB033.zsRealization 0 bc).domain := by
    intro f
    exact dmFreeResolvent_mem_domain bc hbc n x t «hλ» hsum f
  refine ⟨R, T, hR, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f i
    simpa [R, dmScaledCoefficient, dmScaledDenominator] using
      (dmFreeResolvent_repr bc hbc n x t «hλ» hsum f i)
  · intro f i
    have hact := dmFreeResolvent_action bc hbc n x t «hλ» hsum f
    change (freeZSBasis bc).repr
      (NlsGge.Atomic.LIB033.zsRealization 0 bc
        ⟨dmFreeResolvent bc hbc n x t «hλ» hsum f,
          dmFreeResolvent_mem_domain bc hbc n x t «hλ» hsum f⟩) i = _
    rw [hact, dmFreeActionImage_repr]
    simp [dmScaledCoefficient, dmScaledDenominator]
  · intro f
    simpa [R, hR] using
      (dmFreeResolvent_right_inverse bc hbc n x t «hλ» hsum f)
  · intro u
    simpa [R] using
      (dmFreeResolvent_left_inverse bc hbc n x t «hλ» hsum u)
  · intro f
    rfl
  · simpa [T] using
      (dm_free_resolvent_to_sup_clm_norm_le bc hbc n x t hx «hλ» hsum)

end NlsGge.Atomic.DM010
