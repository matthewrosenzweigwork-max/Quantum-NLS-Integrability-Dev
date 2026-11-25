import Mathlib
import NlsGge.ThirdConsultation.M.MRound11Host
import NlsGge.Atomic.KST.KST012
import NlsGge.Atomic.KST.KST016

   
                                                                                 

                                                                                    
                                                                                                     
                                                                               
  

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.MTwoModeSupp

open scoped InnerProduct InnerProductSpace
open NlsGge.Atomic.KST003 NlsGge.Atomic.KST004
open NlsGge.ThirdConsultation.MTwoMode

abbrev EndH : Type := KSTPairL2 →L[ℂ] KSTPairL2

/-- The ambient small-square hypothesis gives the strict contraction used internally. -/
theorem sq_norm_lt_one (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hsmall : ‖ambientT φ n lam hlam ^ 2‖ ≤ (1 / 2 : ℝ)) :
    ‖ambientT φ n lam hlam ^ 2‖ < 1 :=
  lt_of_le_of_lt hsmall (by norm_num)

theorem pow_two_mul_add_two {M : Type*} [Monoid M] (T : M) (k : ℕ) :
    T ^ (2 * k + 2) = T ^ 2 * (T ^ 2) ^ k := by
  rw [← pow_succ', ← pow_mul, mul_add, mul_one]

theorem pow_two_mul_add_one {M : Type*} [Monoid M] (T : M) (k : ℕ) :
    T ^ (2 * k + 1) = T * (T ^ 2) ^ k := by
  rw [pow_succ' T (2 * k), pow_mul]

theorem hasSum_even_op (T : EndH) (hT : ‖T ^ 2‖ < 1) :
    HasSum (fun k : ℕ => T ^ (2 * k + 2)) (T ^ 2 * Ring.inverse (1 - T ^ 2)) := by
  have h := (hasSum_geom_series_inverse (T ^ 2) hT).mul_left (T ^ 2)
  have e : (fun k : ℕ => T ^ (2 * k + 2)) = fun k : ℕ => T ^ 2 * (T ^ 2) ^ k :=
    funext (pow_two_mul_add_two T)
  rw [e]
  exact h

theorem hasSum_odd_op (T : EndH) (hT : ‖T ^ 2‖ < 1) :
    HasSum (fun k : ℕ => T ^ (2 * k + 1)) (T * Ring.inverse (1 - T ^ 2)) := by
  have h := (hasSum_geom_series_inverse (T ^ 2) hT).mul_left T
  have e : (fun k : ℕ => T ^ (2 * k + 1)) = fun k : ℕ => T * (T ^ 2) ^ k :=
    funext (pow_two_mul_add_one T)
  rw [e]
  exact h

theorem hasSum_even_vec (T : EndH) (hT : ‖T ^ 2‖ < 1) (e x : KSTPairL2) :
    HasSum (fun k : ℕ => inner ℂ e ((T ^ (2 * k + 2)) x))
      (inner ℂ e ((T ^ 2) ((Ring.inverse (1 - T ^ 2) : EndH) x))) :=
  by
  have h := ((innerSL ℂ e).comp (ContinuousLinearMap.apply ℂ KSTPairL2 x)).hasSum
    (hasSum_even_op T hT)
  simpa using h

theorem hasSum_odd_vec (T : EndH) (hT : ‖T ^ 2‖ < 1) (e x : KSTPairL2) :
    HasSum (fun k : ℕ => inner ℂ e ((T ^ (2 * k + 1)) x))
      (inner ℂ e (T ((Ring.inverse (1 - T ^ 2) : EndH) x))) :=
  by
  have h := ((innerSL ℂ e).comp (ContinuousLinearMap.apply ℂ KSTPairL2 x)).hasSum
    (hasSum_odd_op T hT)
  simpa using h

/-- The evaluation functional `X ↦ ⟨e_i, X (V e_j)⟩`. -/
def pathFunctional (φ : NlsGge.GK38.PotPair) (n : ℤ) (i j : Bool) :
    EndH →L[ℂ] ℂ :=
  (innerSL ℂ (schurFrame n i : KSTPairL2)).comp
    (ContinuousLinearMap.apply ℂ KSTPairL2
      (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
        (schurFrame n j : KSTPairL2)))

theorem pathFunctional_apply (φ : NlsGge.GK38.PotPair) (n : ℤ) (i j : Bool)
    (X : EndH) :
    pathFunctional φ n i j X =
      inner ℂ (schurFrame n i : KSTPairL2)
        (X (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
          (schurFrame n j : KSTPairL2))) := rfl

theorem schurPathTerm_eq_functional (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n) (r : ℕ) (i j : Bool) :
    schurPathTerm φ n lam hlam r i j =
      pathFunctional φ n i j (ambientT φ n lam hlam ^ r) := rfl

theorem schurFrame_eq_kst016 (n : ℤ) (b : Bool) :
    schurFrame n b = NlsGge.Atomic.KST016.frame n b := rfl

theorem schurFrame_coe (n : ℤ) (b : Bool) :
    (schurFrame n b : KSTPairL2) = kstPnFrame n b := by
  cases b <;> rfl

theorem schurPathTerm_eq_kst016 (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n) (r : ℕ) (i j : Bool) :
    schurPathTerm φ n lam hlam r i j =
      NlsGge.Atomic.KST016.pathTerm (schurPhysicalPair φ) n lam hlam r i j := rfl

/-- Even path series: `∑_k ⟨e_i, T^(2k+2) V e_j⟩ = ⟨e_i, T² (I-T²)⁻¹ V e_j⟩`. -/
theorem hasSum_even_paths (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hT : ‖ambientT φ n lam hlam ^ 2‖ < 1) (i j : Bool) :
    HasSum (fun k : ℕ => schurPathTerm φ n lam hlam (2 * k + 2) i j)
      (inner ℂ (schurFrame n i : KSTPairL2)
        ((ambientT φ n lam hlam ^ 2)
          ((Ring.inverse (1 - ambientT φ n lam hlam ^ 2) : EndH)
            (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
              (schurFrame n j : KSTPairL2))))) :=
  hasSum_even_vec (ambientT φ n lam hlam) hT _ _

/-- Odd path series: `∑_k ⟨e_i, T^(2k+1) V e_j⟩ = ⟨e_i, T (I-T²)⁻¹ V e_j⟩`. -/
theorem hasSum_odd_paths (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hT : ‖ambientT φ n lam hlam ^ 2‖ < 1) (i j : Bool) :
    HasSum (fun k : ℕ => schurPathTerm φ n lam hlam (2 * k + 1) i j)
      (inner ℂ (schurFrame n i : KSTPairL2)
        (ambientT φ n lam hlam
          ((Ring.inverse (1 - ambientT φ n lam hlam ^ 2) : EndH)
            (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
              (schurFrame n j : KSTPairL2))))) :=
  hasSum_odd_vec (ambientT φ n lam hlam) hT _ _

/-- Full path series: `∑_m ⟨e_i, T^m V e_j⟩ = ⟨e_i, (I-T)⁻¹ V e_j⟩`. -/
theorem hasSum_all_paths (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hT : ‖ambientT φ n lam hlam ^ 2‖ < 1) (i j : Bool) :
    HasSum (fun m : ℕ => schurPathTerm φ n lam hlam m i j)
      (inner ℂ (schurFrame n i : KSTPairL2)
        ((Ring.inverse (1 - ambientT φ n lam hlam) : EndH)
          (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
            (schurFrame n j : KSTPairL2)))) :=
  (pathFunctional φ n i j).hasSum
    (NlsGge.Atomic.KST016.inverse_series_of_square_small (ambientT φ n lam hlam) hT).2

theorem pathTerm_norm_summable (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hT : ‖ambientT φ n lam hlam ^ 2‖ < 1) (i j : Bool) :
    Summable (fun m : ℕ => ‖schurPathTerm φ n lam hlam m i j‖) :=
  NlsGge.Atomic.KST016.pathTerm_norm_summable (schurPhysicalPair φ) n lam hlam hT i j

theorem schurFrame_inner (n : ℤ) (i j : Bool) :
    inner ℂ (schurFrame n i : KSTPairL2) (schurFrame n j : KSTPairL2) =
      if i = j then (1 : ℂ) else 0 :=
  NlsGge.Atomic.KST016.frame_inner n i j

/-- The reduced entry in terms of the full inverse. -/
theorem schurEntry_eq (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n) (i j : Bool) :
    schurEntry φ n lam hlam i j =
      (lam - (n : ℂ) * (Real.pi : ℂ)) *
          inner ℂ (schurFrame n i : KSTPairL2) (schurFrame n j : KSTPairL2) -
        inner ℂ (schurFrame n i : KSTPairL2)
          ((Ring.inverse (1 - ambientT φ n lam hlam) : EndH)
            (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
              (schurFrame n j : KSTPairL2))) := by
  have h := NlsGge.Atomic.KST016.entry_eq (schurPhysicalPair φ) n lam hlam i j
  have hc : inner ℂ (NlsGge.Atomic.KST016.frame n i : KSTPairL2)
      (NlsGge.Atomic.KST016.correction (schurPhysicalPair φ) n lam hlam
        (NlsGge.Atomic.KST016.frame n j : KSTPairL2)) =
      inner ℂ (schurFrame n i : KSTPairL2)
        ((Ring.inverse (1 - ambientT φ n lam hlam) : EndH)
          (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
            (schurFrame n j : KSTPairL2))) := by
    change inner ℂ (NlsGge.Atomic.KST016.frame n i : KSTPairL2) (spectralPn n
      (Ring.inverse (1 - NlsGge.Atomic.KST006.qOperator (schurPhysicalPair φ) n lam hlam)
        (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
          (NlsGge.Atomic.KST016.frame n j : KSTPairL2)))) = _
    rw [NlsGge.Atomic.KST016.frame_coe, NlsGge.Atomic.KST016.inner_frame_Pn,
      ← NlsGge.Atomic.KST016.frame_coe]
    rfl
  exact h.trans (by rw [hc]; rfl)

theorem schurDiagonal_eq (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n) (i : Bool) :
    ((lam - (n : ℂ) * (Real.pi : ℂ)) - schurEntry φ n lam hlam i i) =
      inner ℂ (schurFrame n i : KSTPairL2)
        ((Ring.inverse (1 - ambientT φ n lam hlam) : EndH)
          (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
            (schurFrame n i : KSTPairL2))) := by
  have hi : inner ℂ (schurFrame n i : KSTPairL2) (schurFrame n i : KSTPairL2) = 1 := by
    rw [schurFrame_inner]
    simp
  rw [schurEntry_eq, hi, mul_one]
  ring

/-- Even-index diagonal path terms vanish (channel parity: `V e_i` lies in channel `!i`,
`T^(2k)` preserves it, and `e_i` pairs to zero with channel `!i`). -/
theorem even_diagonal_path_zero (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n) (i : Bool) (k : ℕ) :
    schurPathTerm φ n lam hlam (2 * k) i i = 0 := by
  have h1 := NlsGge.Atomic.KST016.potentialOnPn_flips (schurPhysicalPair φ) n i
    (NlsGge.Atomic.KST016.frame n i : KSTPairL2) (NlsGge.Atomic.KST016.frame_inChannel n i)
  have h2 := NlsGge.Atomic.KST016.qOperator_pow_even (schurPhysicalPair φ) n lam hlam k (!i) _ h1
  exact NlsGge.Atomic.KST016.inner_frame_of_channel n i _ h2

/-- The odd split of the full diagonal series, after summability. -/
theorem tsum_all_eq_tsum_odd (f : ℕ → ℂ) (hs : Summable (fun m => ‖f m‖))
    (heven : ∀ j : ℕ, f (2 * j) = 0) :
    ∑' m, f m = ∑' j : ℕ, f (2 * j + 1) := by
  have hf : Summable f := hs.of_norm
  have he : Summable (fun k : ℕ => f (2 * k)) :=
    hf.comp_injective (i := fun k : ℕ => 2 * k) (fun a b h => by simp at h; omega)
  have ho : Summable (fun k : ℕ => f (2 * k + 1)) :=
    hf.comp_injective (i := fun k : ℕ => 2 * k + 1) (fun a b h => by simp at h; omega)
  rw [← tsum_even_add_odd he ho]
  have he0 : ∑' k : ℕ, f (2 * k) = 0 := by simp [heven]
  rw [he0, zero_add]

/-- `schurDiagonal` is the sum of the odd diagonal path series. -/
theorem schurDiagonal_eq_odd (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hT : ‖ambientT φ n lam hlam ^ 2‖ < 1) (i : Bool) :
    ((lam - (n : ℂ) * (Real.pi : ℂ)) - schurEntry φ n lam hlam i i) =
      ∑' j : ℕ, schurPathTerm φ n lam hlam (2 * j + 1) i i := by
  rw [schurDiagonal_eq, ← (hasSum_all_paths φ n lam hlam hT i i).tsum_eq]
  exact tsum_all_eq_tsum_odd _ (pathTerm_norm_summable φ n lam hlam hT i i)
    (fun j => even_diagonal_path_zero φ n lam hlam i j)

end NlsGge.ThirdConsultation.MTwoModeSupp

end
