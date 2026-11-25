import Mathlib
import NlsGge.ThirdConsultation.M.MRound11Host
import NlsGge.ThirdConsultation.M.MRound11Paths
import NlsGge.Atomic.KST.KST012
import NlsGge.Atomic.KST.KST016

   
                                                                                            

                                                                                                                     
                                                                                                                    
                                                                                                                    
                                                                                                                 
                                                                                                                
                                                                                                           
  

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.MTwoModeW

open scoped InnerProduct InnerProductSpace
open NlsGge.Atomic.KST003 NlsGge.Atomic.KST004
open NlsGge.ThirdConsultation.MTwoMode NlsGge.ThirdConsultation.MTwoModeSupp

/-! ### Generic Neumann series from absolute summability of the powers -/

theorem neumann_unit {R : Type*} [NormedRing R] [CompleteSpace R] (S : R)
    (hS : Summable fun j : ℕ => ‖S ^ j‖) :
    ∃ u : Rˣ, (u : R) = 1 - S ∧ ((u⁻¹ : Rˣ) : R) = ∑' j : ℕ, S ^ j ∧
      HasSum (fun j : ℕ => S ^ j) (∑' j : ℕ, S ^ j) := by
  have hsum : HasSum (fun j : ℕ => S ^ j) (∑' j : ℕ, S ^ j) := hS.of_norm.hasSum
  obtain ⟨σ, hσ⟩ : ∃ σ : R, σ = ∑' j : ℕ, S ^ j := ⟨_, rfl⟩
  rw [← hσ] at hsum
  have hshift : HasSum (fun j : ℕ => S ^ (j + 1)) (σ - 1) := by
    have h := (hasSum_nat_add_iff' 1).2 hsum
    simpa using h
  have htel : HasSum (fun j : ℕ => S ^ j - S ^ (j + 1)) 1 := by
    have h := hsum.sub hshift
    simpa using h
  have hR : (1 - S) * σ = 1 := by
    have h1 : HasSum (fun j : ℕ => (1 - S) * S ^ j) ((1 - S) * σ) := hsum.mul_left (1 - S)
    have e : (fun j : ℕ => (1 - S) * S ^ j) = fun j : ℕ => S ^ j - S ^ (j + 1) := by
      funext j
      rw [sub_mul, one_mul, ← pow_succ']
    rw [e] at h1
    exact h1.unique htel
  have hL : σ * (1 - S) = 1 := by
    have h1 : HasSum (fun j : ℕ => S ^ j * (1 - S)) (σ * (1 - S)) := hsum.mul_right (1 - S)
    have e : (fun j : ℕ => S ^ j * (1 - S)) = fun j : ℕ => S ^ j - S ^ (j + 1) := by
      funext j
      rw [mul_sub, mul_one, ← pow_succ]
    rw [e] at h1
    exact h1.unique htel
  exact ⟨⟨1 - S, σ, hR, hL⟩, rfl, hσ, by rw [← hσ]; exact hsum⟩

/-- Norm-free version of `hasSum_geom_series_inverse` (+ unit). -/
theorem hasSum_geom_inverse_of_summable {R : Type*} [NormedRing R] [CompleteSpace R] (S : R)
    (hS : Summable fun j : ℕ => ‖S ^ j‖) :
    IsUnit (1 - S) ∧ HasSum (fun j : ℕ => S ^ j) (Ring.inverse (1 - S)) := by
  obtain ⟨u, hu, hui, hsum⟩ := neumann_unit S hS
  have hinv : Ring.inverse (1 - S) = ∑' j : ℕ, S ^ j := by
    rw [← hu, Ring.inverse_unit]
    exact hui
  exact ⟨⟨u, hu⟩, by rw [hinv]; exact hsum⟩

/-- Norm-free version of `KST012.inverse_one_sub_of_sq_norm_lt`. -/
theorem inverse_one_sub_of_sq_summable {R : Type*} [NormedRing R] [CompleteSpace R] (T : R)
    (h : Summable fun j : ℕ => ‖(T ^ 2) ^ j‖) :
    IsUnit (1 - T) ∧
      Ring.inverse (1 - T) = (1 + T) * Ring.inverse (1 - T ^ 2) ∧
      (1 - T) * ((1 + T) * Ring.inverse (1 - T ^ 2)) = 1 ∧
      ((1 + T) * Ring.inverse (1 - T ^ 2)) * (1 - T) = 1 := by
  obtain ⟨u, hu, hui, _⟩ := neumann_unit (T ^ 2) h
  have hpoly : (1 - T) * (1 + T) = (u : R) := by
    rw [hu]
    noncomm_ring
  have hcomm : Commute (1 - T) (1 + T) := by
    change (1 - T) * (1 + T) = (1 + T) * (1 - T)
    noncomm_ring
  let U : Rˣ := Units.leftOfMul u (1 - T) (1 + T) hpoly hcomm
  have hunit : IsUnit (1 - T) := ⟨U, rfl⟩
  have hinvT2 : Ring.inverse (1 - T ^ 2) = ((u⁻¹ : Rˣ) : R) := by
    rw [← hu]
    exact Ring.inverse_unit u
  have hinverse : Ring.inverse (1 - T) = (1 + T) * Ring.inverse (1 - T ^ 2) := by
    rw [hinvT2]
    change Ring.inverse (U : R) = _
    rw [Ring.inverse_unit]
    rfl
  refine ⟨hunit, hinverse, ?_, ?_⟩
  · rw [← hinverse]
    exact Ring.mul_inverse_cancel (1 - T) hunit
  · rw [← hinverse]
    exact Ring.inverse_mul_cancel (1 - T) hunit

/-- Norm-free version of `KST016.inverse_series_of_square_small`. -/
theorem inverse_series_of_sq_summable {R : Type*} [NormedRing R] [CompleteSpace R] (T : R)
    (hT : Summable fun j : ℕ => ‖(T ^ 2) ^ j‖) :
    Summable (fun m : ℕ => ‖T ^ m‖) ∧
      HasSum (fun m : ℕ => T ^ m) (Ring.inverse (1 - T)) := by
  have hS : HasSum (fun k : ℕ => (T ^ 2) ^ k) (Ring.inverse (1 - T ^ 2)) :=
    (hasSum_geom_inverse_of_summable (T ^ 2) hT).2
  obtain ⟨_, hinv, _, _⟩ := inverse_one_sub_of_sq_summable T hT
  constructor
  · have he : Summable (fun k : ℕ => ‖T ^ (2 * k)‖) := by
      simpa only [pow_mul] using hT
    have ho : Summable (fun k : ℕ => ‖T ^ (2 * k + 1)‖) := by
      refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) (hT.mul_left ‖T‖)
      rw [pow_succ' T (2 * k), pow_mul]
      exact norm_mul_le _ _
    exact Summable.even_add_odd he ho
  · have hev : HasSum (fun k : ℕ => T ^ (2 * k)) (Ring.inverse (1 - T ^ 2)) := by
      simpa only [pow_mul] using hS
    have hod : HasSum (fun k : ℕ => T ^ (2 * k + 1)) (T * Ring.inverse (1 - T ^ 2)) := by
      have h := hS.mul_left T
      have e : (fun k : ℕ => T * (T ^ 2) ^ k) = fun k : ℕ => T ^ (2 * k + 1) := by
        funext k
        rw [pow_succ' T (2 * k), pow_mul]
      rw [e] at h
      exact h
    have h := hev.even_add_odd hod
    have e2 : Ring.inverse (1 - T ^ 2) + T * Ring.inverse (1 - T ^ 2) =
        Ring.inverse (1 - T) := by
      rw [hinv, add_mul, one_mul]
    rw [e2] at h
    exact h

/-! ### Operator-level path series (norm-free versions of `MRound11Paths`) -/

theorem hasSum_even_op_w (T : EndH) (hT : Summable fun j : ℕ => ‖(T ^ 2) ^ j‖) :
    HasSum (fun k : ℕ => T ^ (2 * k + 2)) (T ^ 2 * Ring.inverse (1 - T ^ 2)) := by
  have h := (hasSum_geom_inverse_of_summable (T ^ 2) hT).2.mul_left (T ^ 2)
  have e : (fun k : ℕ => T ^ (2 * k + 2)) = fun k : ℕ => T ^ 2 * (T ^ 2) ^ k :=
    funext (pow_two_mul_add_two T)
  rw [e]
  exact h

theorem hasSum_odd_op_w (T : EndH) (hT : Summable fun j : ℕ => ‖(T ^ 2) ^ j‖) :
    HasSum (fun k : ℕ => T ^ (2 * k + 1)) (T * Ring.inverse (1 - T ^ 2)) := by
  have h := (hasSum_geom_inverse_of_summable (T ^ 2) hT).2.mul_left T
  have e : (fun k : ℕ => T ^ (2 * k + 1)) = fun k : ℕ => T * (T ^ 2) ^ k :=
    funext (pow_two_mul_add_one T)
  rw [e]
  exact h

theorem hasSum_even_vec_w (T : EndH) (hT : Summable fun j : ℕ => ‖(T ^ 2) ^ j‖)
    (e x : KSTPairL2) :
    HasSum (fun k : ℕ => inner ℂ e ((T ^ (2 * k + 2)) x))
      (inner ℂ e ((T ^ 2) ((Ring.inverse (1 - T ^ 2) : EndH) x))) := by
  have h := ((innerSL ℂ e).comp (ContinuousLinearMap.apply ℂ KSTPairL2 x)).hasSum
    (hasSum_even_op_w T hT)
  simpa using h

theorem hasSum_odd_vec_w (T : EndH) (hT : Summable fun j : ℕ => ‖(T ^ 2) ^ j‖)
    (e x : KSTPairL2) :
    HasSum (fun k : ℕ => inner ℂ e ((T ^ (2 * k + 1)) x))
      (inner ℂ e (T ((Ring.inverse (1 - T ^ 2) : EndH) x))) := by
  have h := ((innerSL ℂ e).comp (ContinuousLinearMap.apply ℂ KSTPairL2 x)).hasSum
    (hasSum_odd_op_w T hT)
  simpa using h

theorem hasSum_even_paths_w (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hT : Summable fun j : ℕ => ‖(ambientT φ n lam hlam ^ 2) ^ j‖) (i j : Bool) :
    HasSum (fun k : ℕ => schurPathTerm φ n lam hlam (2 * k + 2) i j)
      (inner ℂ (schurFrame n i : KSTPairL2)
        ((ambientT φ n lam hlam ^ 2)
          ((Ring.inverse (1 - ambientT φ n lam hlam ^ 2) : EndH)
            (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
              (schurFrame n j : KSTPairL2))))) :=
  hasSum_even_vec_w (ambientT φ n lam hlam) hT _ _

theorem hasSum_odd_paths_w (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hT : Summable fun j : ℕ => ‖(ambientT φ n lam hlam ^ 2) ^ j‖) (i j : Bool) :
    HasSum (fun k : ℕ => schurPathTerm φ n lam hlam (2 * k + 1) i j)
      (inner ℂ (schurFrame n i : KSTPairL2)
        (ambientT φ n lam hlam
          ((Ring.inverse (1 - ambientT φ n lam hlam ^ 2) : EndH)
            (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
              (schurFrame n j : KSTPairL2))))) :=
  hasSum_odd_vec_w (ambientT φ n lam hlam) hT _ _

theorem hasSum_all_paths_w (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hT : Summable fun j : ℕ => ‖(ambientT φ n lam hlam ^ 2) ^ j‖) (i j : Bool) :
    HasSum (fun m : ℕ => schurPathTerm φ n lam hlam m i j)
      (inner ℂ (schurFrame n i : KSTPairL2)
        ((Ring.inverse (1 - ambientT φ n lam hlam) : EndH)
          (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
            (schurFrame n j : KSTPairL2)))) :=
  (pathFunctional φ n i j).hasSum (inverse_series_of_sq_summable (ambientT φ n lam hlam) hT).2

/-- Norm-free version of `KST016.pathTerm_norm_summable`. -/
theorem pathTerm_norm_summable_w (φ : NlsGge.Atomic.KST016.Potential) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n)
    (hT : Summable fun j : ℕ => ‖(NlsGge.Atomic.KST006.qOperator φ n z hz ^ 2) ^ j‖)
    (i j : Bool) :
    Summable (fun m : ℕ => ‖NlsGge.Atomic.KST016.pathTerm φ n z hz m i j‖) := by
  have hs := (inverse_series_of_sq_summable _ hT).1
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
    (hs.mul_right ‖NlsGge.Atomic.KST012.potentialOnPn φ n
      (NlsGge.Atomic.KST016.frame n j : NlsGge.Atomic.KST016.H)‖)
  calc ‖NlsGge.Atomic.KST016.pathTerm φ n z hz m i j‖
      ≤ ‖(NlsGge.Atomic.KST016.frame n i : NlsGge.Atomic.KST016.H)‖ *
          ‖(NlsGge.Atomic.KST006.qOperator φ n z hz ^ m)
            (NlsGge.Atomic.KST012.potentialOnPn φ n
              (NlsGge.Atomic.KST016.frame n j : NlsGge.Atomic.KST016.H))‖ :=
        norm_inner_le_norm _ _
    _ ≤ 1 * (‖NlsGge.Atomic.KST006.qOperator φ n z hz ^ m‖ *
          ‖NlsGge.Atomic.KST012.potentialOnPn φ n
            (NlsGge.Atomic.KST016.frame n j : NlsGge.Atomic.KST016.H)‖) := by
        rw [NlsGge.Atomic.KST016.frame_norm]
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖NlsGge.Atomic.KST006.qOperator φ n z hz ^ m‖ *
          ‖NlsGge.Atomic.KST012.potentialOnPn φ n
            (NlsGge.Atomic.KST016.frame n j : NlsGge.Atomic.KST016.H)‖ := one_mul _

theorem pathTerm_norm_summable_amb (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hT : Summable fun j : ℕ => ‖(ambientT φ n lam hlam ^ 2) ^ j‖) (i j : Bool) :
    Summable (fun m : ℕ => ‖schurPathTerm φ n lam hlam m i j‖) :=
  pathTerm_norm_summable_w (schurPhysicalPair φ) n lam hlam hT i j

/-- Norm-free version of `MRound11Paths.schurDiagonal_eq_odd`. -/
theorem schurDiagonal_eq_odd_w (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hT : Summable fun j : ℕ => ‖(ambientT φ n lam hlam ^ 2) ^ j‖) (i : Bool) :
    ((lam - (n : ℂ) * (Real.pi : ℂ)) - schurEntry φ n lam hlam i i) =
      ∑' j : ℕ, schurPathTerm φ n lam hlam (2 * j + 1) i i := by
  rw [schurDiagonal_eq, ← (hasSum_all_paths_w φ n lam hlam hT i i).tsum_eq]
  exact tsum_all_eq_tsum_odd _ (pathTerm_norm_summable_amb φ n lam hlam hT i i)
    (fun j => even_diagonal_path_zero φ n lam hlam i j)

/-- Norm-free version of `KST016.reducedBC_fourier_remainders`. -/
theorem reducedBC_fourier_remainders_w (φ : NlsGge.Atomic.KST016.Potential) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n)
    (hT : Summable fun j : ℕ => ‖(NlsGge.Atomic.KST006.qOperator φ n z hz ^ 2) ^ j‖) :
    Summable (fun j : ℕ => ‖NlsGge.Atomic.KST016.pathTerm φ n z hz (2 * j + 2) false true‖) ∧
    Summable (fun j : ℕ => ‖NlsGge.Atomic.KST016.pathTerm φ n z hz (2 * j + 2) true false‖) ∧
    NlsGge.Atomic.KST016.reducedB φ n z hz =
      NlsGge.Atomic.KST016.coveredCoeff φ false (2 * n) +
        NlsGge.Atomic.KST016.remainderB φ n z hz ∧
    NlsGge.Atomic.KST016.reducedC φ n z hz =
      NlsGge.Atomic.KST016.coveredCoeff φ true (-2 * n) +
        NlsGge.Atomic.KST016.remainderC φ n z hz := by
  have hseries := (inverse_series_of_sq_summable _ hT).2
  have hhas : ∀ i j : Bool, HasSum (fun m : ℕ => NlsGge.Atomic.KST016.pathTerm φ n z hz m i j)
      (inner ℂ (NlsGge.Atomic.KST016.frame n i : NlsGge.Atomic.KST016.H)
        (Ring.inverse (1 - NlsGge.Atomic.KST006.qOperator φ n z hz)
          (NlsGge.Atomic.KST012.potentialOnPn φ n
            (NlsGge.Atomic.KST016.frame n j : NlsGge.Atomic.KST016.H)))) := by
    intro i j
    let L : NlsGge.Atomic.KST016.EndH →L[ℂ] ℂ :=
      (innerSL ℂ (NlsGge.Atomic.KST016.frame n i : NlsGge.Atomic.KST016.H)).comp
        (ContinuousLinearMap.apply ℂ NlsGge.Atomic.KST016.H
          (NlsGge.Atomic.KST012.potentialOnPn φ n
            (NlsGge.Atomic.KST016.frame n j : NlsGge.Atomic.KST016.H)))
    exact hseries.mapL L
  have hcorr : ∀ i j : Bool,
      inner ℂ (NlsGge.Atomic.KST016.frame n i : NlsGge.Atomic.KST016.H)
        (NlsGge.Atomic.KST016.correction φ n z hz
          (NlsGge.Atomic.KST016.frame n j : NlsGge.Atomic.KST016.H)) =
      inner ℂ (NlsGge.Atomic.KST016.frame n i : NlsGge.Atomic.KST016.H)
        (Ring.inverse (1 - NlsGge.Atomic.KST006.qOperator φ n z hz)
          (NlsGge.Atomic.KST012.potentialOnPn φ n
            (NlsGge.Atomic.KST016.frame n j : NlsGge.Atomic.KST016.H))) := by
    intro i j
    change inner ℂ (NlsGge.Atomic.KST016.frame n i : NlsGge.Atomic.KST016.H) (spectralPn n
      (Ring.inverse (1 - NlsGge.Atomic.KST006.qOperator φ n z hz)
        (NlsGge.Atomic.KST012.potentialOnPn φ n
          (NlsGge.Atomic.KST016.frame n j : NlsGge.Atomic.KST016.H)))) = _
    rw [NlsGge.Atomic.KST016.frame_coe, NlsGge.Atomic.KST016.inner_frame_Pn,
      ← NlsGge.Atomic.KST016.frame_coe]
  have hsm := pathTerm_norm_summable_w φ n z hz hT
  have hent := NlsGge.Atomic.KST016.entries_correction φ n z hz
  have hodd := NlsGge.Atomic.KST016.odd_offDiagonal_path_zero φ n z hz
  have hzero := NlsGge.Atomic.KST016.zeroth_offDiagonal_path φ n z hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hsm false true).comp_injective (i := fun j : ℕ => 2 * j + 2)
      (fun a b h => by simp at h; omega)
  · exact (hsm true false).comp_injective (i := fun j : ℕ => 2 * j + 2)
      (fun a b h => by simp at h; omega)
  · rw [hent.2.1, hcorr, ← (hhas false true).tsum_eq,
      NlsGge.Atomic.KST016.tsum_even_split _ (hsm false true) (fun j => (hodd j).1), hzero.1]
    rfl
  · rw [hent.2.2, hcorr, ← (hhas true false).tsum_eq,
      NlsGge.Atomic.KST016.tsum_even_split _ (hsm true false) (fun j => (hodd j).2), hzero.2]
    rfl

end NlsGge.ThirdConsultation.MTwoModeW

end
