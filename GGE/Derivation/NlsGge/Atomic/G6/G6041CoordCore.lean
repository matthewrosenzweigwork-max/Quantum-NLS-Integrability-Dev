import Mathlib
import NlsGge.Atomic.G6.G6036Host
import NlsGge.Atomic.G6.G6038Host

/- G6041 COORD CORE PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G6/G6041CoordCore.lean, namespace NlsGge.ThirdConsultation.G6041S.  SUPPORT (no packet
   increment) for G6-040/041 (Pro r16 §Q3 common-neighbourhood route, L987-998): the concrete real/imaginary
   identification of the diagonal sequence spaces,
     diagC : RealDiagonalSpace × RealDiagonalSpace ≃L[ℝ] ComplexDiagonalSpace,  (x, y) ↦ (x_n + i y_n)_n,
   with Pro's compatibility diagC_hc (the hypothesis shape of exists_local_complexification and LIB-100), its
   coordinates on the real slice, and the real-slice isometry ‖diagC (y, 0)‖ = ‖y‖.  Elementary lp arithmetic only.
   Own imports: Mathlib, G6036Host (RealDiagonalSpace), G6038Host (ComplexDiagonalSpace). -/
set_option autoImplicit false

open scoped ENNReal
open NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.G6041S
noncomputable section

theorem memℓp2_of_le {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (f : ℤ → E) (g : ℤ → F) (hg : Memℓp g 2) (h : ∀ n, ‖f n‖ ≤ ‖g n‖) : Memℓp f 2 := by
  refine memℓp_gen ?_
  have hs := hg.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  exact Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => Real.rpow_le_rpow (norm_nonneg _) (h n) (by norm_num)) hs

theorem norm_le_of_coord {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (f : lp (fun _ : ℤ => E) 2) (g : lp (fun _ : ℤ => F) 2) (h : ∀ n, ‖f n‖ ≤ ‖g n‖) : ‖f‖ ≤ ‖g‖ := by
  have hf := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) f
  have hg := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) g
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hf hg
  have hle : ‖f‖ ^ 2 ≤ ‖g‖ ^ 2 :=
    hasSum_le (fun n => pow_le_pow_left₀ (norm_nonneg _) (h n) 2) hf hg
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hle

theorem norm_eq_of_coord {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (f : lp (fun _ : ℤ => E) 2) (g : lp (fun _ : ℤ => F) 2) (h : ∀ n, ‖f n‖ = ‖g n‖) : ‖f‖ = ‖g‖ :=
  le_antisymm (norm_le_of_coord f g fun n => (h n).le) (norm_le_of_coord g f fun n => (h n).ge)

/-- Real sequence as a complex sequence. -/
def ofRealD (x : RealDiagonalSpace) : ComplexDiagonalSpace :=
  ⟨fun n => ((x n : ℝ) : ℂ), memℓp2_of_le _ _ (lp.memℓp x) fun n => by rw [Complex.norm_real]⟩

theorem ofRealD_apply (x : RealDiagonalSpace) (n : ℤ) : ofRealD x n = ((x n : ℝ) : ℂ) := rfl

theorem norm_ofRealD (x : RealDiagonalSpace) : ‖ofRealD x‖ = ‖x‖ :=
  norm_eq_of_coord _ _ fun n => by rw [ofRealD_apply, Complex.norm_real]

def toCfun (q : RealDiagonalSpace × RealDiagonalSpace) : ComplexDiagonalSpace :=
  ofRealD q.1 + Complex.I • ofRealD q.2

theorem toCfun_apply (q : RealDiagonalSpace × RealDiagonalSpace) (n : ℤ) :
    toCfun q n = ((q.1 n : ℝ) : ℂ) + Complex.I * ((q.2 n : ℝ) : ℂ) := by
  unfold toCfun
  rw [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ofRealD_apply, ofRealD_apply]

def reD (z : ComplexDiagonalSpace) : RealDiagonalSpace :=
  ⟨fun n => (z n).re, memℓp2_of_le _ _ (lp.memℓp z) fun n => by
    rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _⟩

def imD (z : ComplexDiagonalSpace) : RealDiagonalSpace :=
  ⟨fun n => (z n).im, memℓp2_of_le _ _ (lp.memℓp z) fun n => by
    rw [Real.norm_eq_abs]; exact Complex.abs_im_le_norm _⟩

def diagLE : (RealDiagonalSpace × RealDiagonalSpace) ≃ₗ[ℝ] ComplexDiagonalSpace where
  toFun := toCfun
  invFun z := (reD z, imD z)
  map_add' q q' := by
    apply lp.ext; funext n
    simp only [toCfun_apply, Prod.fst_add, Prod.snd_add, lp.coeFn_add, Pi.add_apply]
    push_cast; ring
  map_smul' a q := by
    apply lp.ext; funext n
    simp only [toCfun_apply, Prod.smul_fst, Prod.smul_snd, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, Complex.real_smul]
    push_cast; ring
  left_inv q := by
    obtain ⟨x, y⟩ := q
    refine Prod.ext ?_ ?_
    · apply lp.ext; funext n
      show (toCfun (x, y) n).re = x n
      rw [toCfun_apply]; simp
    · apply lp.ext; funext n
      show (toCfun (x, y) n).im = y n
      rw [toCfun_apply]; simp
  right_inv z := by
    apply lp.ext; funext n
    rw [toCfun_apply]
    show ((z n).re : ℂ) + Complex.I * ((z n).im : ℂ) = z n
    rw [mul_comm]; exact Complex.re_add_im (z n)

def diagC : (RealDiagonalSpace × RealDiagonalSpace) ≃L[ℝ] ComplexDiagonalSpace :=
  diagLE.toContinuousLinearEquivOfBounds 2 1
    (fun q => by
      show ‖toCfun q‖ ≤ 2 * ‖q‖
      calc ‖toCfun q‖ ≤ ‖ofRealD q.1‖ + ‖Complex.I • ofRealD q.2‖ := norm_add_le _ _
        _ = ‖q.1‖ + ‖q.2‖ := by rw [norm_smul, Complex.norm_I, one_mul, norm_ofRealD, norm_ofRealD]
        _ ≤ 2 * ‖q‖ := by linarith [norm_fst_le q, norm_snd_le q])
    (fun z => by
      show ‖((reD z, imD z) : RealDiagonalSpace × RealDiagonalSpace)‖ ≤ 1 * ‖z‖
      rw [one_mul, Prod.norm_def]
      refine max_le (norm_le_of_coord _ _ fun n => ?_) (norm_le_of_coord _ _ fun n => ?_)
      · show ‖(z n).re‖ ≤ ‖z n‖; rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
      · show ‖(z n).im‖ ≤ ‖z n‖; rw [Real.norm_eq_abs]; exact Complex.abs_im_le_norm _)

theorem diagC_apply (q : RealDiagonalSpace × RealDiagonalSpace) (n : ℤ) :
    diagC q n = ((q.1 n : ℝ) : ℂ) + Complex.I * ((q.2 n : ℝ) : ℂ) := toCfun_apply q n

theorem diagC_real_apply (x : RealDiagonalSpace) (n : ℤ) : diagC (x, 0) n = ((x n : ℝ) : ℂ) := by
  rw [diagC_apply]; simp

theorem diagC_real (x : RealDiagonalSpace) : diagC (x, 0) = ofRealD x := by
  apply lp.ext; funext n; rw [diagC_real_apply, ofRealD_apply]

theorem diagC_hc (x y : RealDiagonalSpace) :
    diagC (x, y) = diagC (x, 0) + Complex.I • diagC (y, 0) := by
  apply lp.ext; funext n
  rw [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, diagC_apply,
    diagC_real_apply, diagC_real_apply]

theorem norm_diagC_real (y : RealDiagonalSpace) : ‖diagC (y, 0)‖ = ‖y‖ := by
  rw [diagC_real, norm_ofRealD]

theorem dist_diagC_real (y y' : RealDiagonalSpace) : dist (diagC (y, 0)) (diagC (y', 0)) = dist y y' := by
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, Prod.mk_sub_mk, sub_zero, norm_diagC_real]

end
end NlsGge.ThirdConsultation.G6041S
