import Mathlib
import NlsGge.Atomic.G6.G6039Host
import NlsGge.Atomic.G6.G6038Core
import NlsGge.GK38.Lib.InterpolationLemma

                                                                                       
                                                                                                             
                                                                                                    
                                                                                                                        
                                                                       
                                                                                                           
                                                                                                             
                                                                                                       
                                                                                        
                                                                                            
set_option autoImplicit false

open Set Filter Topology Metric
open scoped ENNReal
open NlsGge.GK38 NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.G6039S
noncomputable section

theorem coe_finsum_single (T : Finset ℤ) (c : ℤ → ℂ) (m : ℤ) :
    ((∑ n ∈ T, lp.single 2 n (c n) : ComplexDiagonalSpace) : ℤ → ℂ) m = if m ∈ T then c m else 0 := by
  have h := map_sum (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 m) (fun k => lp.single 2 k (c k)) T
  have e : ∀ x : ComplexDiagonalSpace, lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 m x = (x : ℤ → ℂ) m := fun x => rfl
  rw [e] at h
  rw [h]
  simp only [e, lp.single_apply]
  split_ifs with hm
  · rw [Finset.sum_eq_single m]
    · simp
    · intro b _ hb; simp [Pi.single_apply, Ne.symm hb]
    · intro h'; exact absurd hm h'
  · refine Finset.sum_eq_zero (fun k hk => ?_)
    have : m ≠ k := fun h => hm (h ▸ hk)
    simp [Pi.single_apply, this]

def flipD (T : Finset ℤ) (x : ComplexDiagonalSpace) : ComplexDiagonalSpace :=
  x - ∑ n ∈ T, lp.single 2 n (2 * x n)

theorem flipD_apply (T : Finset ℤ) (x : ComplexDiagonalSpace) (m : ℤ) :
    (flipD T x : ℤ → ℂ) m = if m ∈ T then -x m else x m := by
  unfold flipD
  rw [lp.coeFn_sub, Pi.sub_apply, coe_finsum_single]
  split_ifs <;> ring

theorem norm_sq_eq_of_norm_coord (x y : ComplexDiagonalSpace) (h : ∀ n, ‖x n‖ = ‖y n‖) : ‖x‖ = ‖y‖ := by
  have hx := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) x
  have hy := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) y
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hx hy
  have he : (fun n : ℤ => ‖x n‖ ^ 2) = fun n => ‖y n‖ ^ 2 := funext fun n => by rw [h n]
  rw [he] at hx
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (hx.unique hy)

theorem norm_flipD (T : Finset ℤ) (x : ComplexDiagonalSpace) : ‖flipD T x‖ = ‖x‖ :=
  norm_sq_eq_of_norm_coord _ _ fun n => by rw [flipD_apply]; split_ifs <;> simp

theorem flipD_insert (a : ℤ) (T : Finset ℤ) (ha : a ∉ T) (x : ComplexDiagonalSpace) :
    flipD (insert a T) x = flipComplexCoordinate a (flipD T x) := by
  apply lp.ext; funext m
  unfold flipComplexCoordinate
  rw [flipD_apply, lp.coeFn_sub, Pi.sub_apply, lp.single_apply, flipD_apply, flipD_apply]
  by_cases hm : m = a
  · subst hm; simp [ha, Pi.single_apply]; ring
  · simp [hm, Pi.single_apply]

theorem f_flipD (g : ComplexDiagonalSpace → ℂ) (r : ℝ)
    (hev : CoordinatewiseEvenOn g Set.univ (ball (0 : ComplexDiagonalSpace) r)) :
    ∀ T : Finset ℤ, ∀ x ∈ ball (0 : ComplexDiagonalSpace) r, g (flipD T x) = g x := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro x _
    have : flipD (∅ : Finset ℤ) x = x := by simp [flipD]
    rw [this]
  | insert a T ha ih =>
    intro x hx
    have hT : flipD T x ∈ ball (0 : ComplexDiagonalSpace) r := by
      rw [mem_ball, dist_zero_right, norm_flipD]; rwa [mem_ball, dist_zero_right] at hx
    rw [flipD_insert a T ha, hev _ hT a (Set.mem_univ _), ih x hx]

theorem norm_sq_of_sq (I : ComplexActionSpace) (x : ComplexDiagonalSpace) (hx : ∀ n : ℤ, (x n)^2 = I n) :
    ‖x‖ ^ 2 = ‖I‖ := by
  have h := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) x
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  have he : (fun n : ℤ => ‖x n‖ ^ 2) = fun n => ‖I n‖ := funext fun n => by rw [← norm_pow, hx n]
  rw [he] at h
  exact h.unique (NlsGge.ThirdConsultation.G6038S.hasSum_norm1 I)

theorem mem_ball_of_sq {r : ℝ} (hr : 0 < r) (I : ComplexActionSpace) (hI : I ∈ ball (0 : ComplexActionSpace) (r^2))
    (x : ComplexDiagonalSpace) (hx : ∀ n : ℤ, (x n)^2 = I n) : x ∈ ball (0 : ComplexDiagonalSpace) r := by
  rw [mem_ball, dist_zero_right] at hI ⊢
  exact lt_of_pow_lt_pow_left₀ 2 hr.le (by rw [norm_sq_of_sq I x hx]; exact hI)

theorem tendsto_window_sum (z : ComplexDiagonalSpace) :
    Tendsto (fun N : ℕ => ∑ n ∈ Lib.win N, lp.single 2 n (z n)) atTop (𝓝 z) := by
  have hs := lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) z
  have hw : Tendsto (fun N : ℕ => Lib.win N) atTop atTop :=
    tendsto_atTop_finset_of_monotone (fun a b h => Lib.win_mono h)
      (fun n => ⟨n.natAbs, Lib.mem_win_of_natAbs_le le_rfl⟩)
  exact hs.comp hw

theorem tail_identity (g : ComplexDiagonalSpace → ℂ) (r : ℝ) (hr : 0 < r)
    (hev : CoordinatewiseEvenOn g Set.univ (ball (0 : ComplexDiagonalSpace) r))
    (hcont : ∀ x ∈ ball (0 : ComplexDiagonalSpace) r, ContinuousAt g x)
    (I : ComplexActionSpace) (hI : I ∈ ball (0 : ComplexActionSpace) (r^2))
    (x : ComplexDiagonalSpace) (hx : ∀ n : ℤ, (x n)^2 = I n) :
    g x = g (complexActionRoot I) := by
  classical
  have hxb := mem_ball_of_sq hr I hI x hx
  have hroot : ∀ n : ℤ, (complexActionRoot I n)^2 = I n := fun n => by
    rw [NlsGge.ThirdConsultation.G6038S.root_apply, NlsGge.GK38.Lib.sqrt_sq]
  have hrb := mem_ball_of_sq hr I hI _ hroot
  set z : ComplexDiagonalSpace := x - complexActionRoot I with hz
  have hy : ∀ N : ℕ, x - ∑ n ∈ Lib.win N, lp.single 2 n (z n) =
      flipD ((Lib.win N).filter (fun n => x n ≠ complexActionRoot I n)) x := by
    intro N
    apply lp.ext; funext m
    rw [flipD_apply, lp.coeFn_sub, Pi.sub_apply, coe_finsum_single]
    have hzm : z m = x m - complexActionRoot I m := by rw [hz, lp.coeFn_sub, Pi.sub_apply]
    by_cases hmw : m ∈ Lib.win N
    · by_cases hne : x m = complexActionRoot I m
      · rw [if_pos hmw, if_neg (by simp [hne]), hzm, hne]; ring
      · rw [if_pos hmw, if_pos (by simp [hmw, hne]), hzm]
        have hsq : (complexActionRoot I m)^2 = (x m)^2 := by rw [hroot m, hx m]
        rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
        · exact absurd h.symm hne
        · rw [h]; ring
    · rw [if_neg hmw, if_neg (by simp [hmw])]; ring
  have hconst : ∀ N : ℕ, g (x - ∑ n ∈ Lib.win N, lp.single 2 n (z n)) = g x := fun N => by
    rw [hy N]; exact f_flipD g r hev _ x hxb
  have hlim : Tendsto (fun N : ℕ => x - ∑ n ∈ Lib.win N, lp.single 2 n (z n)) atTop
      (𝓝 (complexActionRoot I)) := by
    have := (tendsto_window_sum z).const_sub x
    rwa [hz, sub_sub_cancel] at this
  have h1 := (hcont _ hrb).tendsto.comp hlim
  have h2 : Tendsto (fun N : ℕ => g (x - ∑ n ∈ Lib.win N, lp.single 2 n (z n))) atTop (𝓝 (g x)) := by
    simp only [hconst]; exact tendsto_const_nhds
  exact tendsto_nhds_unique h2 h1

theorem parametric_identity
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P]
    (U : Set P) (f : P × ComplexDiagonalSpace → ℂ) (r : ℝ) (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (U ×ˢ Metric.ball (0 : ComplexDiagonalSpace) r))
    (heven : ∀ p : P, p ∈ U →
      CoordinatewiseEvenOn (fun x : ComplexDiagonalSpace => f (p, x))
        Set.univ (Metric.ball (0 : ComplexDiagonalSpace) r)) :
  ∀ (p : P) (I : ComplexActionSpace) (x : ComplexDiagonalSpace),
    p ∈ U → I ∈ Metric.ball (0 : ComplexActionSpace) (r^2) →
    (∀ n : ℤ, (x n)^2 = I n) → f (p, x) = parametricActionDescent f (p, I) := by
  intro p I x hp hI hx
  unfold parametricActionDescent
  refine tail_identity (fun y => f (p, y)) r hr (heven p hp) (fun y hy => ?_) I hI x hx
  exact (hf (p, y) ⟨hp, hy⟩).continuousAt.comp (continuous_const.prodMk continuous_id).continuousAt

end
end NlsGge.ThirdConsultation.G6039S
