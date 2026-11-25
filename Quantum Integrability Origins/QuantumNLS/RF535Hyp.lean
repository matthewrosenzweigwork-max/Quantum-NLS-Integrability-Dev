import Mathlib
import QuantumNLS.RF535Bridge
import QuantumNLS.Ext025A4D01Discharge
import QuantumNLS.Local023Final
import QuantumNLS.AnalyticIdentity
import QuantumNLS.RealAnalyticDef

/-!
# R-F5355ABD `thm:global-actual-chart` (`actual_chart.tex:15`), stage 2: the hypotheses of `thm:global-D01-reconstruction` for the actual objects

Builds `QuantumNLS.D01LocalPrimitive.Hyp (L2T L)` (the literal bundle of the printed hypotheses 1-4 of R-701613DA) for the actual quantum indexed actions `Iact hκ = I^{(κ)}`:
* item 1: analytic `I`, `I_n ≥ 0`, `Σ I_n = ‖u‖²`, properness (stage 1, accepted nodes);
* item 2: the jointly continuous action `ρ_θ = act (e^{iθ})` of `𝕋^ℤ = ℤ → ℝ/2πℤ` (angle-sequence form `tc θ_n = e^{iθ_n}` of the product-torus action `Torus = ℤ → Circle`), by analytic strong symplectic maps (`rho_analytic`, `rho_symp`), preserving `I`, with `n`th circle the complete Hamiltonian flow of `I_n` (`rho_flow`);
* item 3: the dual-norm analytic averaged primitive `Abar = ᾱ` (`ProductTorusPrimitive.alphaBarCLM`, definitionally `ᾱ_u(h) = ∫ α_{T_ψ u}(DT_ψ(u)h) dψ`), `dᾱ = ω`, `ρ_θ^*ᾱ = ᾱ`, `ᾱ(X_{I_n}) = -I_n` (all from the accepted product-torus theorem) and the involution `C_H u = conj u(-·)` (`Cphys`, `ResetNormalizationBinding.Cphys`) which is a real-linear isometric antisymplectic involution (`omega_Cphys`), preserves every actual action (`Iact_Cphys`: on the local ball from `|Φ_n|² = I_n` and `Φ ∘ C = conj Φ`, then on all of `L²` by the accepted Hilbert identity theorem `AnalyticIdentity`, exactly the printed `t ↦ I_n(C_H(tu)) - I_n(tu)` argument), and `C_H^*ᾱ = -ᾱ` (`Abar_CH`);
* item 4: the entire-ball local chart `φ = Φ_{κ,loc}`, `ψ = Φ_{κ,loc}^{-1}` of LOCAL-023 (`LocalData`, supplied by the caller from the LOCAL-023 conclusion, not assumed).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open Set Filter Topology Metric
open scoped ComplexConjugate

namespace QuantumNLS.RF535Hyp
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.RF535Bridge
open QuantumNLS.D01LocalPrimitive (K Tor)
open QuantumNLS.Ext025B6TorusCoordinates (Torus)

variable {L κ : ℝ} [Fact (0 < L)]

/-- The unit-circle valued sequence of an angle sequence. -/
def tc (θ : Tor) : Torus := fun n => (θ n).toCircle

theorem tc_add (θ θ' : Tor) : tc (θ + θ') = tc θ * tc θ' := by
  funext n; simp [tc, Real.Angle.toCircle_add]

theorem tc_zero : tc 0 = 1 := by
  funext n; simp [tc]

theorem tc_neg (θ : Tor) : tc (-θ) = (tc θ)⁻¹ := by
  funext n; simp [tc]

theorem tc_single (n : ℤ) (s : ℝ) :
    tc (Pi.single n (s : Real.Angle)) = Pi.mulSingle n (Circle.exp s) := by
  funext m
  by_cases hm : m = n
  · subst hm; simp [tc]
  · simp [tc, Pi.single_eq_of_ne hm, Pi.mulSingle_eq_of_ne hm]

theorem continuous_tc : Continuous tc :=
  continuous_pi fun n => continuous_toCircle.comp (continuous_apply n)

/-- The action of `𝕋^ℤ = ℤ → ℝ/2πℤ` on `L²` from the product-torus theorem. -/
def rhoMap (hκ : 0 < κ) (θ : Tor) : L2T L → L2T L :=
  QuantumNLS.ProductTorusAction.act (fderiv ℝ (Iact (L := L) hκ)) (tc θ)

theorem rho_zero (hκ : 0 < κ) : rhoMap (L := L) hκ 0 = id := by
  funext u
  unfold rhoMap
  rw [tc_zero]
  exact QuantumNLS.ProductTorusAction.act_one (phyp hκ).hyp (hpos hκ) (hprop hκ) (hper hκ) u

theorem rho_add (hκ : 0 < κ) (θ θ' : Tor) :
    rhoMap (L := L) hκ (θ + θ') = rhoMap hκ θ ∘ rhoMap hκ θ' := by
  funext u
  unfold rhoMap
  rw [tc_add]
  exact QuantumNLS.ProductTorusAction.act_mul (phyp hκ).hyp (hpos hκ) (hprop hκ) (hper hκ) _ _ u

theorem rho_cont (hκ : 0 < κ) :
    Continuous (fun p : Tor × L2T L => rhoMap hκ p.1 p.2) :=
  (QuantumNLS.ProductTorusAction.act_continuous (phyp hκ).hyp (hpos hκ) (hprop hκ) (hper hκ)).comp
    ((continuous_tc.comp continuous_fst).prodMk continuous_snd)

theorem rho_act (hκ : 0 < κ) (θ : Tor) (u : L2T L) : Iact hκ (rhoMap hκ θ u) = Iact hκ u :=
  QuantumNLS.ProductTorusFlow.I_T (phyp hκ).hyp _ u

theorem rho_flow (hκ : 0 < κ) (n : ℤ) (u : L2T L) (t : ℝ) :
    HasDerivAt (fun s : ℝ => rhoMap hκ (Pi.single n (s : Real.Angle)) u)
      (SymplecticBracket.hamField (fun v => (Iact (L := L) hκ v : ℤ → ℝ) n)
        (rhoMap hκ (Pi.single n (t : Real.Angle)) u)) t := by
  have h1 : ∀ s : ℝ, rhoMap hκ (Pi.single n (s : Real.Angle)) u =
      QuantumNLS.ProductTorusFlow.flow (fderiv ℝ (Iact (L := L) hκ))
        (QuantumNLS.ProductTorusCommute.e n) s u := by
    intro s
    unfold rhoMap
    rw [tc_single]
    exact QuantumNLS.ProductTorusAction.act_single (phyp hκ).hyp (hpos hκ) (hprop hκ) (hper hκ) n s u
  have h2 := QuantumNLS.ProductTorusFlow.hasDerivAt_flow (flowHyp (L := L) hκ)
    (QuantumNLS.ProductTorusCommute.e n) u t
  have hX : QuantumNLS.ProductTorusGenerator.X (fderiv ℝ (Iact (L := L) hκ))
      (QuantumNLS.ProductTorusCommute.e n)
      (QuantumNLS.ProductTorusFlow.flow (fderiv ℝ (Iact (L := L) hκ))
        (QuantumNLS.ProductTorusCommute.e n) t u) =
      SymplecticBracket.hamField (fun v => (Iact (L := L) hκ v : ℤ → ℝ) n)
        (rhoMap hκ (Pi.single n (t : Real.Angle)) u) := by
    rw [QuantumNLS.ProductTorusCommute.X_e, h1 t]
    exact Xn_eq_gen (fun u => (hI hκ u (mem_univ u)).differentiableAt) n _
  have h3 : (fun s : ℝ => rhoMap hκ (Pi.single n (s : Real.Angle)) u) =
      fun s => QuantumNLS.ProductTorusFlow.flow (fderiv ℝ (Iact (L := L) hκ))
        (QuantumNLS.ProductTorusCommute.e n) s u := funext h1
  rw [h3]
  exact h2.congr_deriv hX


section Generic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A differentiable bijection with differentiable inverse, preserving `ω` infinitesimally, is a DEF-016 map. -/
theorem stronglySymplectic_of_inverse (f g : E → E) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y)
    (hs : ∀ u h k, SymplecticBracket.omega (fderiv ℝ f u h) (fderiv ℝ f u k) =
      SymplecticBracket.omega h k) : QuantumNLS.StrongSymplectic.IsStronglySymplectic f where
  exists_inverse := ⟨g, hgf, hfg, hg⟩
  differentiable := hf
  deriv_iso := fun u => by
    have h1 : (fderiv ℝ g (f u)).comp (fderiv ℝ f u) = ContinuousLinearMap.id ℝ E := by
      have := (hg (f u)).hasFDerivAt.comp u (hf u).hasFDerivAt
      have e : g ∘ f = id := funext hgf
      rw [e] at this
      exact this.unique (hasFDerivAt_id u)
    have h2 : (fderiv ℝ f u).comp (fderiv ℝ g (f u)) = ContinuousLinearMap.id ℝ E := by
      have := (hf (g (f u))).hasFDerivAt.comp (f u) (hg (f u)).hasFDerivAt
      have e : f ∘ g = id := funext hfg
      rw [e, hgf u] at this
      exact this.unique (hasFDerivAt_id (f u))
    exact ⟨ContinuousLinearEquiv.equivOfInverse (fderiv ℝ f u) (fderiv ℝ g (f u))
      (fun x => by simpa using congrArg (fun T => T x) h1)
      (fun x => by simpa using congrArg (fun T => T x) h2), rfl⟩
  symplectic := hs

end Generic

/-- The consequences of `thm:global-product-torus` for the actual masses, used below. -/
theorem rho_symp (hκ : 0 < κ) (θ : Tor) :
    QuantumNLS.StrongSymplectic.IsStronglySymplectic (rhoMap (L := L) hκ θ) := by
  have PT := QuantumNLS.Ext025A4ProductDischarge.thm_global_product_torus_ext (hI (L := L) hκ) (hpos hκ)
    (hmass hκ) (hinv hκ) (hprop hκ) (hper hκ)
  obtain ⟨⟨⟨⟨hmul, hone, hcont, hsingle⟩, hB, hC, hD, hE, hF, hadd, hsmul, hbd, hbd2, hd, hinvar, hXn, hCs, hUV⟩,
    ha, hb, hΦ⟩, hc⟩ := PT
  have hψ := fun u => hB (tc θ) u
  refine stronglySymplectic_of_inverse (rhoMap hκ θ) (QuantumNLS.ProductTorusAction.act
    (fderiv ℝ (Iact (L := L) hκ)) (tc θ)⁻¹) (fun u => (hψ u).1.differentiableAt)
    (fun u => (hψ u).2.1.differentiableAt) (fun x => (hψ x).2.2.1 x) (fun y => (hψ y).2.2.2.1 y)
    (fun u h k => (hψ u).2.2.2.2 h k)


theorem rho_analytic (hκ : 0 < κ) (θ : Tor) (u : L2T L) : AnalyticAt ℝ (rhoMap (L := L) hκ θ) u :=
  QuantumNLS.ProductTorusAnalytic.act_analyticAt (phyp hκ) (hI hκ).fderiv
    QuantumNLS.Ext025A4ProductDischarge.held_product (tc θ) u

/-- The averaged primitive `ᾱ` of `thm:global-product-torus` for the actual masses. -/
def Abar (hκ : 0 < κ) : L2T L → (L2T L →L[ℝ] ℝ) :=
  QuantumNLS.ProductTorusPrimitive.alphaBarCLM (phyp (L := L) hκ)

theorem Abar_apply (hκ : 0 < κ) (u h : L2T L) :
    Abar hκ u h = QuantumNLS.ProductTorusPrimitive.alphaBar (fderiv ℝ (Iact (L := L) hκ)) u h := rfl

theorem Abar_analytic (hκ : 0 < κ) : AnalyticOnNhd ℝ (Abar (L := L) hκ) univ := by
  have PT := QuantumNLS.Ext025A4ProductDischarge.thm_global_product_torus_ext (hI (L := L) hκ) (hpos hκ)
    (hmass hκ) (hinv hκ) (hprop hκ) (hper hκ)
  obtain ⟨⟨⟨⟨hmul, hone, hcont, hsingle⟩, hB, hC, hD, hE, hF, hadd, hsmul, hbd, hbd2, hd, hinvar, hXn, hCs, hUV⟩,
    ha, hb, hΦ⟩, hc⟩ := PT
  obtain ⟨Φa, hΦa, hΦe⟩ := hΦ
  have : Abar (L := L) hκ = Φa := by
    funext u
    exact ContinuousLinearMap.ext fun h => (Abar_apply hκ u h).trans (hΦe u h).symm
  rw [this]
  exact hΦa

theorem Abar_isRealAnalyticMap (hκ : 0 < κ) : QuantumNLS.RealAnalyticDef.IsRealAnalyticMap (Abar (L := L) hκ) :=
  (QuantumNLS.RealAnalyticDef.isRealAnalyticMap_iff _).2 fun u => Abar_analytic hκ u (mem_univ u)

theorem Abar_d (hκ : 0 < κ) (u h k : L2T L) :
    fderiv ℝ (Abar (L := L) hκ) u h k - fderiv ℝ (Abar (L := L) hκ) u k h =
      SymplecticBracket.omega h k := by
  have H := QuantumNLS.ProductTorusPrimitiveExterior.d_alphaBar (phyp (L := L) hκ) u h k
  have hdiff : HasFDerivAt (Abar (L := L) hκ) (fderiv ℝ (Abar (L := L) hκ) u) u :=
    ((Abar_analytic hκ u (mem_univ u)).differentiableAt).hasFDerivAt
  have curve : ∀ a b : L2T L, QuantumNLS.ProductTorusPrimitiveExterior.dAlpha (fderiv ℝ (Iact (L := L) hκ)) u a b =
      fderiv ℝ (Abar (L := L) hκ) u a b := by
    intro a b
    have h1 := (QuantumNLS.ProductTorusPrimitiveExterior.d_alphaBar (phyp (L := L) hκ) u a b).1
    have h2 : HasDerivAt (fun s : ℝ => Abar (L := L) hκ (u + s • a)) (fderiv ℝ (Abar (L := L) hκ) u a) 0 := by
      have hc : HasDerivAt (fun s : ℝ => u + s • a) a 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const a).const_add u
      exact hdiff.comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)
    have h3 := (ContinuousLinearMap.apply ℝ ℝ b).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
    exact h1.unique h3
  rw [← curve, ← curve]
  exact H.2


theorem Abar_inv (hκ : 0 < κ) (θ : Tor) (u h : L2T L) :
    Abar hκ (rhoMap hκ θ u) (fderiv ℝ (rhoMap (L := L) hκ θ) u h) = Abar hκ u h := by
  have PT := QuantumNLS.Ext025A4ProductDischarge.thm_global_product_torus_ext (hI (L := L) hκ) (hpos hκ)
    (hmass hκ) (hinv hκ) (hprop hκ) (hper hκ)
  obtain ⟨⟨⟨⟨hmul, hone, hcont, hsingle⟩, hB, hC, hD, hE, hF, hadd, hsmul, hbd, hbd2, hd, hinvar, hXn, hCs, hUV⟩,
    ha, hb, hΦ⟩, hc⟩ := PT
  exact hinvar (tc θ) u h

theorem Abar_X (hκ : 0 < κ) (n : ℤ) (u : L2T L) :
    Abar hκ u (SymplecticBracket.hamField (fun v => (Iact (L := L) hκ v : ℤ → ℝ) n) u) =
      -((Iact (L := L) hκ u : ℤ → ℝ) n) := by
  have PT := QuantumNLS.Ext025A4ProductDischarge.thm_global_product_torus_ext (hI (L := L) hκ) (hpos hκ)
    (hmass hκ) (hinv hκ) (hprop hκ) (hper hκ)
  obtain ⟨⟨⟨⟨hmul, hone, hcont, hsingle⟩, hB, hC, hD, hE, hF, hadd, hsmul, hbd, hbd2, hd, hinvar, hXn, hCs, hUV⟩,
    ha, hb, hΦ⟩, hc⟩ := PT
  have := hXn n u
  rw [Xn_eq_gen (fun u => (hI hκ u (mem_univ u)).differentiableAt)] at this
  exact this


/-! ## The conjugation-reflection `C_H` -/

open QuantumNLS.ResetNormalizationUniqueness (Cphys)

theorem inner_Cphys (h k : L2T L) :
    inner ℂ (Cphys L h) (Cphys L k) = conj (inner ℂ h k) := by
  have e : ∀ u : L2T L, QuantumNLS.Fourier.fourierL2 L (Cphys L u) = star (QuantumNLS.Fourier.fourierL2 L u) :=
    fun u => lp.ext (funext fun n => by
      rw [lp.star_apply]
      exact QuantumNLS.ResetNormalizationUniqueness.fourier_Cphys L u n)
  rw [← (QuantumNLS.Fourier.fourierL2 L).inner_map_map (Cphys L h) (Cphys L k), e h, e k,
    QuantumNLS.D01LocalPrimitive.inner_star, (QuantumNLS.Fourier.fourierL2 L).inner_map_map]

theorem omega_Cphys (h k : L2T L) :
    SymplecticBracket.omega (Cphys L h) (Cphys L k) = -SymplecticBracket.omega h k := by
  unfold SymplecticBracket.omega
  rw [inner_Cphys, Complex.conj_im]
  ring

/-- Bundle of the properties of the LOCAL-023 local chart used by the global reconstruction. -/
structure LocalData (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (d : ℝ) (Φ : L2T L → K) (Ψ : K → L2T L) :
    Prop where
  hd : 0 < d
  anaΦ : AnalyticOnNhd ℝ Φ (ball (0 : L2T L) (d / Real.sqrt κ))
  anaΨ : AnalyticOnNhd ℝ Ψ (ball (0 : K) (d / Real.sqrt κ))
  mapsΦ : MapsTo Φ (ball (0 : L2T L) (d / Real.sqrt κ)) (ball (0 : K) (d / Real.sqrt κ))
  mapsΨ : MapsTo Ψ (ball (0 : K) (d / Real.sqrt κ)) (ball (0 : L2T L) (d / Real.sqrt κ))
  ΨΦ : ∀ u ∈ ball (0 : L2T L) (d / Real.sqrt κ), Ψ (Φ u) = u
  ΦΨ : ∀ y ∈ ball (0 : K) (d / Real.sqrt κ), Φ (Ψ y) = y
  mass : ∀ u ∈ ball (0 : L2T L) (d / Real.sqrt κ), ∀ n : ℤ,
    ‖Φ u n‖ ^ 2 = (QuantumNLS.RootIndexedMasses.masses hκ u).1 n
  symp : ∀ u ∈ ball (0 : L2T L) (d / Real.sqrt κ), ∀ h k : L2T L,
    2 * (inner ℂ (fderiv ℝ Φ u h) (fderiv ℝ Φ u k)).im = 2 * (inner ℂ h k).im
  conjR : ∀ u ∈ ball (0 : L2T L) (d / Real.sqrt κ), ∀ n : ℤ, Φ (Cphys L u) n = conj (Φ u n)

theorem Iact_Cphys (hκ : 0 < κ) {d : ℝ} {Φ : L2T L → K} {Ψ : K → L2T L}
    (hl : LocalData L κ hκ d Φ Ψ) (v : L2T L) : Iact hκ (Cphys L v) = Iact hκ v := by
  have hρ : 0 < d / Real.sqrt κ := div_pos hl.hd (Real.sqrt_pos.2 hκ)
  refine Subtype.ext (funext fun n => ?_)
  have hA := AnalyticIdentity.identity_of_vanishing_ball
    (fun w : L2T L => RootMassInvolutionR8.mass (L := L) hκ n (Cphys L w) -
      RootMassInvolutionR8.mass (L := L) hκ n w)
    (fun w => (((RootMassInvolutionR9.root_mass_involution (L := L) hκ).1 n (Cphys L w)).comp
      ((Cphys L).toContinuousLinearMap.analyticAt w)).sub
      ((RootMassInvolutionR9.root_mass_involution (L := L) hκ).1 n w)) hρ
    (fun w hw => by
      have hw' : w ∈ ball (0 : L2T L) (d / Real.sqrt κ) := hw
      have hw2 : Cphys L w ∈ ball (0 : L2T L) (d / Real.sqrt κ) := by
        rw [mem_ball_zero_iff] at hw' ⊢
        rwa [QuantumNLS.ResetNormalizationUniqueness.norm_Cphys]
      have e1 := hl.mass (Cphys L w) hw2 n
      have e2 := hl.mass w hw' n
      rw [hl.conjR w hw' n, Complex.norm_conj] at e1
      show _ - _ = 0
      have : RootMassInvolutionR8.mass (L := L) hκ n (Cphys L w) = RootMassInvolutionR8.mass (L := L) hκ n w :=
        e1.symm.trans e2
      rw [this, sub_self]) v
  exact sub_eq_zero.1 hA


theorem Abar_CH (hκ : 0 < κ) {d : ℝ} {Φ : L2T L → K} {Ψ : K → L2T L}
    (hl : LocalData L κ hκ d Φ Ψ) (u h : L2T L) :
    Abar hκ (Cphys L u) (Cphys L h) = -Abar hκ u h := by
  have PT := QuantumNLS.Ext025A4ProductDischarge.thm_global_product_torus_ext (hI (L := L) hκ) (hpos hκ)
    (hmass hκ) (hinv hκ) (hprop hκ) (hper hκ)
  obtain ⟨⟨⟨⟨hmul, hone, hcont, hsingle⟩, hB, hC, hD, hE, hF, hadd, hsmul, hbd, hbd2, hd, hinvar, hXn, hCs, hUV⟩,
    ha, hb, hΦ⟩, hc⟩ := PT
  exact hCs (Cphys L).toContinuousLinearMap (fun v => QuantumNLS.ResetNormalizationUniqueness.Cphys_Cphys L v)
    (fun a b => omega_Cphys a b) (fun v => Iact_Cphys hκ hl v) u h

/-- The hypotheses of `thm:global-D01-reconstruction` (`D01LocalPrimitive.Hyp`) for the actual quantum
indexed actions and the LOCAL-023 chart. -/
def actualHyp (hκ : 0 < κ) {d : ℝ} {Φ : L2T L → K} {Ψ : K → L2T L} (hl : LocalData L κ hκ d Φ Ψ) :
    QuantumNLS.D01LocalPrimitive.Hyp (L2T L) where
  act := Iact hκ
  act_analytic := (QuantumNLS.RealAnalyticDef.isRealAnalyticMap_iff _).2 fun u => hI hκ u (mem_univ u)
  act_nonneg := hpos hκ
  act_mass := hmass hκ
  act_proper := hprop hκ
  rho := rhoMap hκ
  rho_cont := rho_cont hκ
  rho_zero := rho_zero hκ
  rho_add := rho_add hκ
  rho_act := rho_act hκ
  rho_analytic := fun θ => (QuantumNLS.RealAnalyticDef.isRealAnalyticMap_iff _).2 (rho_analytic hκ θ)
  rho_symp := rho_symp hκ
  rho_flow := rho_flow hκ
  abar := Abar hκ
  abar_analytic := Abar_isRealAnalyticMap hκ
  abar_d := Abar_d hκ
  abar_inv := Abar_inv hκ
  abar_X := Abar_X hκ
  CH := Cphys L
  CH_invol := QuantumNLS.ResetNormalizationUniqueness.Cphys_Cphys L
  CH_anti := omega_Cphys
  CH_act := Iact_Cphys hκ hl
  abar_CH := Abar_CH hκ hl
  ε := d / Real.sqrt κ
  ε_pos := div_pos hl.hd (Real.sqrt_pos.2 hκ)
  phi := Φ
  psi := Ψ
  phi_maps := hl.mapsΦ
  psi_maps := hl.mapsΨ
  psi_phi := hl.ΨΦ
  phi_psi := hl.ΦΨ
  phi_analytic := fun u hu => (QuantumNLS.RealAnalyticDef.analyticAt_iff_isRealAnalyticPoly _ _).1 (hl.anaΦ u hu)
  psi_analytic := fun z hz => (QuantumNLS.RealAnalyticDef.analyticAt_iff_isRealAnalyticPoly _ _).1 (hl.anaΨ z hz)
  phi_symp := fun u hu h k => hl.symp u hu h k
  phi_q := fun u hu n => hl.mass u hu n
  phi_CH := fun u hu => lp.ext (funext fun n => by
    rw [lp.star_apply]
    exact hl.conjR u hu n)

end QuantumNLS.RF535Hyp

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.RF535Hyp.rho_symp
#print axioms QuantumNLS.RF535Hyp.Abar_analytic
#print axioms QuantumNLS.RF535Hyp.Abar_d
#print axioms QuantumNLS.RF535Hyp.Iact_Cphys
#print axioms QuantumNLS.RF535Hyp.actualHyp
