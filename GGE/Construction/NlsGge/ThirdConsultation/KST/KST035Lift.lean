import Mathlib
import NlsGge.Atomic.DM.DM048
import NlsGge.Atomic.KST.KST002
import NlsGge.Atomic.KST.KST027
import NlsGge.Sobolev.PeriodicBridge
import NlsGge.Sobolev.WeightedHilbert
import NlsGge.ThirdConsultation.KST.KST034Host
import NlsGge.ThirdConsultation.KST.KST035Host

                                                                                                                          
                                                                                                                  
                                                                                                                   
                                                                                                                       
                                                                                                
                                                                                  
set_option autoImplicit false
open scoped ENNReal
open NlsGge.Atomic.KST002 NlsGge.Pilot

namespace NlsGge.ThirdConsultation.KST
noncomputable section
attribute [local instance] Classical.propDecidable

namespace KST035L

theorem summable_of_rawEnergy (ω : ℤ → ℝ) (r : RawPair) (h : rawEnergy ω r ≠ ⊤) (ch : Bool) :
    Summable (fun m : ℤ => ω (2 * m) ^ 2 * ‖r ch m‖ ^ 2) := by
  have hle : ∀ m : ℤ, ENNReal.ofReal (ω (2 * m) ^ 2 * ‖r ch m‖ ^ 2) ≤
      ENNReal.ofReal (ω (2 * m) ^ 2 * (‖r true m‖ ^ 2 + ‖r false m‖ ^ 2)) := by
    intro m
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
    cases ch
    · exact le_add_of_nonneg_left (sq_nonneg _)
    · exact le_add_of_nonneg_right (sq_nonneg _)
  have hfin : ∑' m : ℤ, ENNReal.ofReal (ω (2 * m) ^ 2 * ‖r ch m‖ ^ 2) ≠ ⊤ :=
    ne_top_of_le_ne_top h (ENNReal.tsum_le_tsum hle)
  exact (ENNReal.summable_toReal hfin).congr (fun m => ENNReal.toReal_ofReal (by positivity))

theorem rawEnergy_eq_ofReal (ω : ℤ → ℝ) (r : RawPair)
    (hs : ∀ ch, Summable (fun m : ℤ => ω (2 * m) ^ 2 * ‖r ch m‖ ^ 2)) :
    rawEnergy ω r = ENNReal.ofReal (∑' m : ℤ, ω (2 * m) ^ 2 * (‖r true m‖ ^ 2 + ‖r false m‖ ^ 2)) := by
  have hsum : Summable (fun m : ℤ => ω (2 * m) ^ 2 * (‖r true m‖ ^ 2 + ‖r false m‖ ^ 2)) :=
    ((hs true).add (hs false)).congr (fun m => by ring)
  unfold rawEnergy
  exact (ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hsum).symm

theorem lift_spec (ω : ℤ → ℝ) (hω : ∀ k, 1 ≤ ω k)
    [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)] (x : Weighted ω) (N : ℕ) (R : ℝ)
    (hD : rawEnergy ω (adaptedCoefficients N (weightedPotential ω hω x) -
      rawFourier (weightedPotential ω hω x)) ≤ ENNReal.ofReal (R ^ 2)) (hR : 0 ≤ R) :
    weightedCoeffs ω (adaptedFourier ω hω N x) = adaptedCoefficients N (weightedPotential ω hω x) ∧
      ‖adaptedFourier ω hω N x - x‖ ≤ R := by
  set φ := weightedPotential ω hω x with hφ
  set r := adaptedCoefficients N φ with hr
  set D : RawPair := r - rawFourier φ with hDdef
  have hrawx : ∀ ch m, rawFourier φ ch m = (x ch : ℤ → ℂ) m := fun ch m =>
    weightedPairPhysical_fourier (periodOneWeight ω) (fun m => hω (2 * m)) x ch m
  have hDch : ∀ ch m, D ch m = r ch m - (x ch : ℤ → ℂ) m := fun ch m => by
    simp only [hDdef, Pi.sub_apply, hrawx]
  have hDfin : rawEnergy ω D ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hD
  have hDs := summable_of_rawEnergy ω D hDfin
  have hxs : ∀ ch, Summable (fun m : ℤ => ω (2 * m) ^ 2 * ‖(x ch : ℤ → ℂ) m‖ ^ 2) := fun ch =>
    (weightedHilbert_hasSum (fun k => periodOneWeight ω k ^ 2) (x ch)).summable
  have hrs : ∀ ch, Summable (fun m : ℤ => ω (2 * m) ^ 2 * ‖r ch m‖ ^ 2) := by
    intro ch
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
      (((hxs ch).mul_left 2).add ((hDs ch).mul_left 2))
    have hrx : r ch m = (x ch : ℤ → ℂ) m + D ch m := by rw [hDch]; ring
    have h1 : ‖r ch m‖ ≤ ‖(x ch : ℤ → ℂ) m‖ + ‖D ch m‖ := by
      rw [hrx]; exact norm_add_le _ _
    have h2 : ‖r ch m‖ ^ 2 ≤ 2 * ‖(x ch : ℤ → ℂ) m‖ ^ 2 + 2 * ‖D ch m‖ ^ 2 := by
      nlinarith [norm_nonneg (r ch m), norm_nonneg ((x ch : ℤ → ℂ) m), norm_nonneg (D ch m),
        sq_nonneg (‖(x ch : ℤ → ℂ) m‖ - ‖D ch m‖)]
    nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg (ω (2 * m)))]
  have hmem : ∀ ch, Memℓp (weightedCoordinates (fun k => periodOneWeight ω k ^ 2) (r ch)) 2 :=
    fun ch => (weightedCoordinates_mem_l2_iff _ (fun n => by positivity) (r ch)).2 (hrs ch)
  let y : Weighted ω := WithLp.toLp 2 (fun ch =>
    (⟨r ch, hmem ch⟩ : weightedSubmodule (fun k => periodOneWeight ω k ^ 2)))
  have hy : weightedCoeffs ω y = r := by
    funext ch m; rfl
  have hex : ∃ y' : Weighted ω, weightedCoeffs ω y' = r := ⟨y, hy⟩
  have hcoef : weightedCoeffs ω (adaptedFourier ω hω N x) = r := by
    show weightedCoeffs ω (if h : ∃ y' : Weighted ω, weightedCoeffs ω y' = r
      then Classical.choose h else 0) = r
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  refine ⟨hcoef, ?_⟩
  set z := adaptedFourier ω hω N x with hz
  have hzx : ∀ ch m, ((z - x) ch : ℤ → ℂ) m = D ch m := by
    intro ch m
    rw [K027L5b4.weighted_coord_sub, hDch]
    have := congrFun (congrFun hcoef ch) m
    simp only [weightedCoeffs] at this
    rw [this]
  have hnorm := NlsGge.Atomic.DM048.weightedPairHilbert_norm_sq (periodOneWeight ω) (z - x)
  simp only [hzx] at hnorm
  have hS : ‖z - x‖ ^ 2 = ∑' m : ℤ, ω (2 * m) ^ 2 * (‖D true m‖ ^ 2 + ‖D false m‖ ^ 2) := hnorm
  have hE := rawEnergy_eq_ofReal ω D hDs
  rw [hE] at hD
  have hle : ∑' m : ℤ, ω (2 * m) ^ 2 * (‖D true m‖ ^ 2 + ‖D false m‖ ^ 2) ≤ R ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hD
  rw [← hS] at hle
  by_contra hlt
  have hlt' := not_le.mp hlt
  have := mul_self_lt_mul_self hR hlt'
  nlinarith

end KST035L

end
end NlsGge.ThirdConsultation.KST
