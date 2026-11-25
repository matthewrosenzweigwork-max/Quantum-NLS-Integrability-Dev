import Mathlib
import NlsGge.Birkhoff.BirkhoffAPI38

/- PDE058SUPGEN PRODUCTION01 (proof development, AUTHOR; not reviewed). Proposed target
   NlsGge/ThirdConsultation/PDE/PDE058SupGen.lean, namespace NlsGge.ThirdConsultation.PDE. Supporting results for PDE-058
   (no packet increment). Generic statements, instantiated in PDE058SupB:
   (d1) fderiv_apply_fderiv_rightInverse: for mutually inverse maps f, g, Df(g(f p)) ∘ Dg(f p) = id, applied to v;
   (d2) fderiv_comp_leftInverse_apply: chain rule for h ∘ g at f p, with g (f p) = p;
   (c)  TC_one_comp_symplectic: for any Birkhoff record B with analytic levels {0,1} and the canonical record, and any
        continuous linear equivalence F onto h1, D(TC 1 ∘ F)(p) preserves stdSymplectic38 between the h1 coordinate
        sequences of F h and F k. Proof: chain rule through F, h0/h1 derivative compatibility (fderiv_TC_compat_coe 0 1),
        level-0 canonicity, carrierCoe38_incl38. Differentiability always comes from analyticity / hypotheses before any
        fderiv identity is used. -/
set_option autoImplicit false
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
noncomputable section
namespace NlsGge.ThirdConsultation.PDE

theorem fderiv_apply_fderiv_rightInverse {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (g : F → E)
    (hfg : Function.RightInverse g f) (hgf : Function.LeftInverse g f) (p : E)
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g (f p)) (v : F) :
    fderiv ℝ f p (fderiv ℝ g (f p) v) = v := by
  have hp : g (f p) = p := hgf p
  have hf' : HasFDerivAt f (fderiv ℝ f p) (g (f p)) := by rw [hp]; exact hf.hasFDerivAt
  have hc := hf'.comp (f p) hg.hasFDerivAt
  have hid : f ∘ g = id := funext hfg
  rw [hid] at hc
  have h1 := hc.unique (hasFDerivAt_id (f p))
  have h2 := congrArg (fun L : F →L[ℝ] F => L v) h1
  simpa using h2

theorem fderiv_comp_leftInverse_apply {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (h : E → G) (f : E → F) (g : F → E) (hgf : Function.LeftInverse g f) (p : E)
    (hh : DifferentiableAt ℝ h p) (hg : DifferentiableAt ℝ g (f p)) (v : F) :
    fderiv ℝ (fun z => h (g z)) (f p) v = fderiv ℝ h p (fderiv ℝ g (f p) v) := by
  have hp : g (f p) = p := hgf p
  have hh' : HasFDerivAt h (fderiv ℝ h p) (g (f p)) := by rw [hp]; exact hh.hasFDerivAt
  have hc := hh'.comp (f p) hg.hasFDerivAt
  show fderiv ℝ (h ∘ g) (f p) v = _
  rw [hc.fderiv]
  rfl

theorem TC_one_comp_symplectic {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (B : BirkhoffTop38) (hA : BirkhoffAnalytic38 B {0, 1}) (hC : BirkhoffCanonical38 B)
    (F : P ≃L[ℝ] SobolevCarrier38 ((1 : ℕ) : ℝ)) (p h k : P) :
    stdSymplectic38
        (carrierCoe38 ((1 : ℕ) : ℝ) (fderiv ℝ (fun q => B.TC 1 (F q)) p h))
        (carrierCoe38 ((1 : ℕ) : ℝ) (fderiv ℝ (fun q => B.TC 1 (F q)) p k)) =
      stdSymplectic38 (carrierCoe38 ((1 : ℕ) : ℝ) (F h)) (carrierCoe38 ((1 : ℕ) : ℝ) (F k)) := by
  have hT : HasFDerivAt (B.TC 1) (fderiv ℝ (B.TC 1) (F p)) (F p) :=
    (hA.analyticOnNhd_TC (m := 1) (by simp) (F p) (Set.mem_univ _)).differentiableAt.hasFDerivAt
  have hd : ∀ x : P, fderiv ℝ (fun q => B.TC 1 (F q)) p x = fderiv ℝ (B.TC 1) (F p) (F x) := by
    intro x
    have hc := (hT.comp p F.hasFDerivAt).fderiv
    show fderiv ℝ (B.TC 1 ∘ F) p x = _
    rw [hc]
    rfl
  rw [hd, hd,
    ← hA.fderiv_TC_compat_coe 0 1 (by simp) (by simp) (by norm_num) (F p) (F h),
    ← hA.fderiv_TC_compat_coe 0 1 (by simp) (by simp) (by norm_num) (F p) (F k),
    hC.canonical, carrierCoe38_incl38, carrierCoe38_incl38]

end NlsGge.ThirdConsultation.PDE
