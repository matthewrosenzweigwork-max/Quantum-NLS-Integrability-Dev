import Mathlib
import NlsGge.Atomic.G5.G5012Host
import NlsGge.Atomic.G5.G5012Sup1
import NlsGge.Atomic.G5.G5017Host
import NlsGge.ThirdConsultation.G5.G5017Support1
import NlsGge.Atomic.G4.G4044
import NlsGge.Atomic.X.X004

/- G5-012 SUPPORT3 PRODUCTION02 (proof development fix of proof development PRODUCTION01 after root main probe G5012S_MAINPROBE01/c9e69429;
   tactic-only repairs: proj_smul closing step, scalar re/im split moved to pure lemma g5012_re_im_aux (no realSlice unfolding),
   hfun via Complex.re_ofReal_mul, explicit if_pos/if_neg closing; AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G5/G5012Sup3.lean.
   Head `gradient_physicalCoordinate` verbatim from Pro round 14 section "G5012/013".  Route: landed X004
   samePhi_cartesian_normalization (Phi = (X - iY)/sqrt 2, X, Y real on the slice), landed G4-042/G4-044 differentiability of
   cartesianX/Y on sourceBetaW, then gradient_realSlice_re applied to the complex-scalar multiples (1/sqrt 2) X and (-1/sqrt 2) Y. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38
open NlsGge.ThirdConsultation.G5017Support1

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g5012_cart_diff (n : ℤ) (φ : PotPair) (hφ : φ ∈ sourceBetaW) :
    DifferentiableAt ℂ (cartesianX n) φ ∧ DifferentiableAt ℂ (cartesianY n) φ := by
  obtain ⟨hX, hY⟩ := G4044Aux.coord_eventuallyEq φ hφ n
  have hd : DifferentiableAt ℂ birkhoffCartesian φ := (G4042.1 φ hφ).differentiableAt
  have h1 : DifferentiableAt ℂ (fun ψ : PotPair => birkhoffCartesian ψ (true, n)) φ :=
    ((lp.evalCLM ℂ (fun _ : Bool × ℤ => ℂ) 2 (true, n)).differentiableAt).comp φ hd
  have h2 : DifferentiableAt ℂ (fun ψ : PotPair => birkhoffCartesian ψ (false, n)) φ :=
    ((lp.evalCLM ℂ (fun _ : Bool × ℤ => ℂ) 2 (false, n)).differentiableAt).comp φ hd
  exact ⟨h1.congr_of_eventuallyEq hX.symm, h2.congr_of_eventuallyEq hY.symm⟩

theorem g5012_proj_smul (r : ℝ) (v : PotPair) :
    pairGradientProjection (((r : ℝ) : ℂ) • v) = r • pairGradientProjection v := by
  unfold pairGradientProjection
  simp only [Prod.smul_fst, Prod.smul_snd]
  rw [star_smul_lp, Complex.conj_ofReal, ← smul_add]
  first
  | exact algebraMap_smul ℂ r _
  | exact Complex.coe_smul r _
  | (rw [Complex.coe_smul]; rfl)

theorem g5012_pg_const_mul (c : ℂ) (f : PotPair → ℂ) (φ : PotPair)
    (hf : DifferentiableAt ℂ f φ) :
    pairGradient (fun ψ => c * f ψ) φ = c • pairGradient f φ := by
  unfold pairGradient
  rw [fderiv_const_mul hf c, pairGradientCLM_smul]

theorem g5012_re_im_aux (P X Y : ℂ) (hx : X.im = 0) (hy : Y.im = 0)
    (hphi : P = (X - Complex.I * Y) / (Real.sqrt 2 : ℂ)) :
    P.re = (1 / Real.sqrt 2 : ℝ) * X.re ∧ P.im = (-1 / Real.sqrt 2 : ℝ) * Y.re := by
  subst hphi
  constructor
  · rw [Complex.div_ofReal_re]
    simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, hy]
    ring
  · rw [Complex.div_ofReal_im]
    simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im, hx]
    ring

theorem g5012_phi_re_im (v : PhysicalL2) (n : ℤ) :
    (sourceFamily.Phi v n).re = (1 / Real.sqrt 2 : ℝ) * (cartesianX n (realSlice v)).re ∧
    (sourceFamily.Phi v n).im = (-1 / Real.sqrt 2 : ℝ) * (cartesianY n (realSlice v)).re := by
  obtain ⟨hx, hy, hphi, -⟩ := NlsGge.Atomic.X004.samePhi_cartesian_normalization v n
  exact g5012_re_im_aux _ _ _ hx hy hphi

theorem gradient_physicalCoordinate (u : PhysicalL2) (j : Bool × ℤ) :
  gradient (physicalCoordinate j) u =
    if j.1 then
      (1 / Real.sqrt 2 : ℝ) •
        pairGradientProjection (pairGradient (cartesianX j.2) (realSlice u))
    else
      (-1 / Real.sqrt 2 : ℝ) •
        pairGradientProjection (pairGradient (cartesianY j.2) (realSlice u)) := by
  obtain ⟨b, n⟩ := j
  have hφ : realSlice u ∈ sourceBetaW := sourceFamily.V_real (Set.mem_range_self u)
  obtain ⟨hXd, hYd⟩ := g5012_cart_diff n _ hφ
  cases b
  · have hfun : physicalCoordinate (false, n) = fun v : PhysicalL2 =>
        ((((-1 / Real.sqrt 2 : ℝ)) : ℂ) * cartesianY n (realSlice v)).re := by
      funext v
      show (sourceFamily.Phi v n).im = _
      rw [(g5012_phi_re_im v n).2, Complex.re_ofReal_mul]
    show gradient (physicalCoordinate (false, n)) u = _
    rw [hfun, gradient_realSlice_re (fun φ => (((-1 / Real.sqrt 2 : ℝ)) : ℂ) * cartesianY n φ) u
      (hYd.const_mul _), g5012_pg_const_mul _ _ _ hYd, g5012_proj_smul]
    exact (if_neg Bool.false_ne_true).symm
  · have hfun : physicalCoordinate (true, n) = fun v : PhysicalL2 =>
        ((((1 / Real.sqrt 2 : ℝ)) : ℂ) * cartesianX n (realSlice v)).re := by
      funext v
      show (sourceFamily.Phi v n).re = _
      rw [(g5012_phi_re_im v n).1, Complex.re_ofReal_mul]
    show gradient (physicalCoordinate (true, n)) u = _
    rw [hfun, gradient_realSlice_re (fun φ => (((1 / Real.sqrt 2 : ℝ)) : ℂ) * cartesianX n φ) u
      (hXd.const_mul _), g5012_pg_const_mul _ _ _ hXd, g5012_proj_smul]
    exact (if_pos rfl).symm

end
end NlsGge.GKDefinitionDesign
