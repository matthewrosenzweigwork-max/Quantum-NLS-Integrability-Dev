import Mathlib
import NlsGge.ThirdConsultation.M.MRound11Host
import NlsGge.ThirdConsultation.M.MRound11Paths
import NlsGge.ThirdConsultation.M.MRound11Sector
import NlsGge.Atomic.KST.KST012
import NlsGge.Atomic.KST.KST013
import NlsGge.Atomic.KST.KST016

/-!
# Round-11 elimination / reconstruction / determinant core (proof development, AUTHOR; not self-reviewed)

Pro round 11 (c7aa9978) sections 5.2-5.3.  This module proves, WITHOUT any high-index cutoff, the
equivalence between a nonzero proper-domain parity-`n` eigenvector of `KST013.dirac` and a nonzero
kernel vector of the literal reduced operator `KST013.reducedS`, and then the determinant of the
two-diagonal matrix `schurMatrix`, under the ambient small-square hypothesis.

Four landed-but-`private` KST012/KST013 statements are named as explicit Prop-valued hypotheses
`ElimAC`, `ElimG`, `ElimK`, `ElimD` (verbatim types of KST013.stage13AC_actual_proper_operator_graph_iff,
KST013.stage13G_projection_zero_forces_zero, KST013.stage13K_actual_forward_reduced_formula and
KST012.stageD_reconstructed_actual_bridges).  They are proved theorems of landed files; only their
visibility blocks direct use (see M024_NOTES).  The core theorem takes them as arguments; the final
M-024 head instantiates them once they are public.
-/

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.MTwoModeSupp

open MeasureTheory NlsGge.Schur NlsGge.Atomic.KST003 NlsGge.Atomic.KST004
open scoped InnerProduct InnerProductSpace
open NlsGge.ThirdConsultation.MTwoMode

/-! ### Landed-lemma statements as hypotheses -/

/-- Verbatim type of `KST013.stage13AC_actual_proper_operator_graph_iff`. -/
def ElimAC : Prop :=
  ∀ (ψ : NlsGge.Atomic.KST002.PhysicalPairLp) (f y : KSTPairL2),
    (∃ g : KSTPairL2, HasKSTFreeDiracGraph f (y - g) ∧
      ∀ b : Bool, (g b : SpectralCircle → ℂ) =ᵐ[spectralHaar]
        (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (ψ b) x * f (!b) x)) ↔
    ∃ hf : f ∈ actualFullPeriodTwoSourceDoubledCircleDomain,
      actualFullPeriodTwoDoubledCirclePerturbedDiracAction (-(ψ true)) (-(ψ false))
        ⟨f, hf⟩ = -y

/-- Verbatim type of `KST013.stage13G_projection_zero_forces_zero`. -/
def ElimG : Prop :=
  ∀ (ψ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (f g : KSTPairL2),
    HasKSTFreeDiracGraph f (z • f - g) →
    (∀ b : Bool, (g b : SpectralCircle → ℂ) =ᵐ[spectralHaar]
      (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (ψ b) x * f (!b) x)) →
    IsUnit (1 - NlsGge.Atomic.KST006.qOperator ψ n z hz) →
    spectralPn n f = 0 → f = 0

/-- Verbatim type of `KST013.stage13K_actual_forward_reduced_formula`. -/
def ElimK : Prop :=
  ∀ (ψ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (f g : KSTPairL2),
    HasKSTFreeDiracGraph f (z • f - g) →
    (∀ b : Bool, (g b : SpectralCircle → ℂ) =ᵐ[spectralHaar]
      (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (ψ b) x * f (!b) x)) →
    IsUnit (1 - NlsGge.Atomic.KST006.qOperator ψ n z hz) →
    (z - (n : ℂ) * (Real.pi : ℂ)) • spectralPn n f =
      spectralPn n
        (Ring.inverse (1 - NlsGge.Atomic.KST006.qOperator ψ n z hz)
          (NlsGge.Atomic.KST012.potentialOnPn ψ n (spectralPn n f)))

/-- Verbatim type of `KST012.stageD_reconstructed_actual_bridges`. -/
def ElimD : Prop :=
  ∀ (ψ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (u : KSTPairL2),
    spectralQn n (NlsGge.Atomic.KST012.reconstructedComplement ψ n z hz u) =
        NlsGge.Atomic.KST012.reconstructedComplement ψ n z hz u ∧
      HasKSTFreeDiracGraph (NlsGge.Atomic.KST012.reconstructedComplement ψ n z hz u)
        (z • NlsGge.Atomic.KST012.reconstructedComplement ψ n z hz u -
          spectralQn n (NlsGge.Atomic.KST012.potentialOnPn ψ n u +
            NlsGge.Atomic.KST012.qEquationSolution ψ n z hz u)) ∧
      MemLp (fun x : SpectralCircle =>
        NlsGge.Analysis.naturalPhysicalCoverL2 (ψ true) x *
          NlsGge.Atomic.KST012.reconstructedComplement ψ n z hz u false x) 2 spectralHaar ∧
      MemLp (fun x : SpectralCircle =>
        NlsGge.Analysis.naturalPhysicalCoverL2 (ψ false) x *
          NlsGge.Atomic.KST012.reconstructedComplement ψ n z hz u true x) 2 spectralHaar ∧
      (NlsGge.Atomic.KST006.qOperator ψ n z hz
          (NlsGge.Atomic.KST012.potentialOnPn ψ n u +
            NlsGge.Atomic.KST012.qEquationSolution ψ n z hz u) true :
            SpectralCircle → ℂ) =ᵐ[spectralHaar]
        (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (ψ true) x *
          NlsGge.Atomic.KST012.reconstructedComplement ψ n z hz u false x) ∧
      (NlsGge.Atomic.KST006.qOperator ψ n z hz
          (NlsGge.Atomic.KST012.potentialOnPn ψ n u +
            NlsGge.Atomic.KST012.qEquationSolution ψ n z hz u) false :
            SpectralCircle → ℂ) =ᵐ[spectralHaar]
        (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (ψ false) x *
          NlsGge.Atomic.KST012.reconstructedComplement ψ n z hz u true x)

/-! ### Graph additivity (verbatim copy of the private KST013 stage13L lemmas) -/

theorem elim_weakDerivative_add {u₁ u₂ v₁ v₂ : SpectralScalarL2}
    (h₁ : NlsGge.Atomic.LIB002.HasWeakDerivativeL2 (2 : ℝ) 1 u₁ v₁)
    (h₂ : NlsGge.Atomic.LIB002.HasWeakDerivativeL2 (2 : ℝ) 1 u₂ v₂) :
    NlsGge.Atomic.LIB002.HasWeakDerivativeL2 (2 : ℝ) 1 (u₁ + u₂) (v₁ + v₂) := by
  have hraw
      (a b c d : Lp ℂ 2 (@AddCircle.haarAddCircle (2 : ℝ) inferInstance))
      (ha : NlsGge.Atomic.LIB002.HasWeakDerivativeL2 (2 : ℝ) 1 a c)
      (hb : NlsGge.Atomic.LIB002.HasWeakDerivativeL2 (2 : ℝ) 1 b d) :
      NlsGge.Atomic.LIB002.HasWeakDerivativeL2 (2 : ℝ) 1 (a + b) (c + d) := by
    intro test
    simp only [inner_add_right]
    rw [ha test, hb test]
    ring
  simpa only [SpectralCircle, SpectralScalarL2, spectralHaar] using!
    (hraw u₁ u₂ v₁ v₂ h₁ h₂)

theorem elim_freeGraph_add {x₁ x₂ y₁ y₂ : KSTPairL2}
    (h₁ : HasKSTFreeDiracGraph x₁ y₁)
    (h₂ : HasKSTFreeDiracGraph x₂ y₂) :
    HasKSTFreeDiracGraph (x₁ + x₂) (y₁ + y₂) := by
  obtain ⟨du₁, dl₁, hdu₁, hdl₁, hy₁⟩ := h₁
  obtain ⟨du₂, dl₂, hdu₂, hdl₂, hy₂⟩ := h₂
  refine ⟨du₁ + du₂, dl₁ + dl₂,
    elim_weakDerivative_add hdu₁ hdu₂,
    elim_weakDerivative_add hdl₁ hdl₂, ?_⟩
  rw [hy₁, hy₂]
  apply PiLp.ext
  intro b
  cases b <;> simp [smul_add]

/-! ### Backward construction at an arbitrary small-square parameter -/

theorem backward_construct (hD : ElimD)
    (ψ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n)
    (hT : ‖NlsGge.Atomic.KST006.qOperator ψ n z hz ^ 2‖ < 1)
    (u : KSTPairL2) (hu : spectralPn n u = u)
    (hred : (z - (n : ℂ) * (Real.pi : ℂ)) • u =
      spectralPn n
        (Ring.inverse (1 - NlsGge.Atomic.KST006.qOperator ψ n z hz)
          (NlsGge.Atomic.KST012.potentialOnPn ψ n u))) :
    HasKSTFreeDiracGraph
        (u + NlsGge.Atomic.KST012.reconstructedComplement ψ n z hz u)
        (z • (u + NlsGge.Atomic.KST012.reconstructedComplement ψ n z hz u) -
          (NlsGge.Atomic.KST012.potentialOnPn ψ n u +
            NlsGge.Atomic.KST012.qEquationSolution ψ n z hz u)) ∧
      (∀ b : Bool,
        ((NlsGge.Atomic.KST012.potentialOnPn ψ n u +
            NlsGge.Atomic.KST012.qEquationSolution ψ n z hz u) b :
            SpectralCircle → ℂ) =ᵐ[spectralHaar]
          (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (ψ b) x *
            (u + NlsGge.Atomic.KST012.reconstructedComplement ψ n z hz u) (!b) x)) ∧
      spectralPn n (u + NlsGge.Atomic.KST012.reconstructedComplement ψ n z hz u) = u ∧
      (u ≠ 0 → u + NlsGge.Atomic.KST012.reconstructedComplement ψ n z hz u ≠ 0) := by
  obtain ⟨hunit, _hformula, _hright, _hleft⟩ :=
    NlsGge.Atomic.KST012.inverse_one_sub_of_sq_norm_lt
      (NlsGge.Atomic.KST006.qOperator ψ n z hz) hT
  let T : KSTPairL2 →L[ℂ] KSTPairL2 := NlsGge.Atomic.KST006.qOperator ψ n z hz
  let p : KSTPairL2 := NlsGge.Atomic.KST012.potentialOnPn ψ n u
  let w : KSTPairL2 := NlsGge.Atomic.KST012.qEquationSolution ψ n z hz u
  let v : KSTPairL2 := NlsGge.Atomic.KST012.reconstructedComplement ψ n z hz u
  let g : KSTPairL2 := p + w
  let c : ℂ := (n : ℂ) * (Real.pi : ℂ)
  have hw : (1 - T) w = T p := by
    change (1 - T) (Ring.inverse (1 - T) (T p)) = T p
    have happ := congrArg (fun S : KSTPairL2 →L[ℂ] KSTPairL2 => S (T p))
      (Ring.mul_inverse_cancel (1 - T) hunit)
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using happ
  have hsum : T (p + w) = w := by
    have hs : w - T w = T p := by
      simpa only [sub_apply, one_apply_eq_self] using hw
    calc
      T (p + w) = T p + T w := map_add T p w
      _ = (w - T w) + T w := by rw [hs]
      _ = w := sub_add_cancel _ _
  obtain ⟨hqrange, hgraphv, _hmem_upper, _hmem_lower, hup, hlow⟩ :=
    hD ψ n z hz u
  have hupw : (w true : SpectralCircle → ℂ) =ᵐ[spectralHaar]
      (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (ψ true) x * v false x) := by
    change (T (p + w) true : SpectralCircle → ℂ) =ᵐ[spectralHaar]
      (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (ψ true) x * v false x) at hup
    rw [hsum] at hup
    exact hup
  have hloww : (w false : SpectralCircle → ℂ) =ᵐ[spectralHaar]
      (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (ψ false) x * v true x) := by
    change (T (p + w) false : SpectralCircle → ℂ) =ᵐ[spectralHaar]
      (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (ψ false) x * v true x) at hlow
    rw [hsum] at hlow
    exact hlow
  have hag : (1 - T) g = p := by
    have heq : w - T w = T p := by
      simpa only [sub_apply, one_apply_eq_self] using hw
    change (1 - T) (p + w) = p
    rw [map_add]
    change (p - T p) + (w - T w) = p
    rw [heq]
    abel
  have hginv : g = Ring.inverse (1 - T) p := by
    have hi := congrArg (fun S : KSTPairL2 →L[ℂ] KSTPairL2 => S g)
      (Ring.inverse_mul_cancel (1 - T) hunit)
    have hback : Ring.inverse (1 - T) ((1 - T) g) = g := by
      simpa only [mul_apply_eq_comp, one_apply_eq_self] using hi
    calc
      g = Ring.inverse (1 - T) ((1 - T) g) := hback.symm
      _ = Ring.inverse (1 - T) p :=
        congrArg (fun x : KSTPairL2 => Ring.inverse (1 - T) x) hag
  have hpg : spectralPn n g = (z - c) • u := by
    rw [hginv]
    exact hred.symm
  have hgraphu : HasKSTFreeDiracGraph u (c • u) := by
    have h := kstFreeDirac_on_Pn n u
    rw [hu] at h
    have hscalar : ((n * Real.pi : ℝ) : ℂ) = c := by
      dsimp only [c]
      push_cast
      rfl
    have hreal : HasKSTFreeDiracGraph u (((n * Real.pi : ℝ) : ℂ) • u) := by
      simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ) (E := KSTPairL2)] using! h
    rw [hscalar] at hreal
    exact hreal
  have hgraph : HasKSTFreeDiracGraph (u + v) (z • (u + v) - g) := by
    have h := elim_freeGraph_add hgraphu hgraphv
    have hout : c • u + (z • v - spectralQn n g) = z • (u + v) - g := by
      change c • u + (z • v - (g - spectralPn n g)) = _
      rw [hpg, sub_smul, smul_add]
      abel
    rw [hout] at h
    exact h
  have hproduct (b : Bool) :
      (g b : SpectralCircle → ℂ) =ᵐ[spectralHaar]
        (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (ψ b) x * (u + v) (!b) x) := by
    have hp : (p b : SpectralCircle → ℂ) =ᵐ[spectralHaar]
        (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (ψ b) x * u (!b) x) := by
      have hpae := NlsGge.Atomic.KST012.potentialOnPn_ae ψ n u hu
      cases b
      · simpa only [Bool.not_false] using hpae.2
      · simpa only [Bool.not_true] using hpae.1
    have hwprod : (w b : SpectralCircle → ℂ) =ᵐ[spectralHaar]
        (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (ψ b) x * v (!b) x) := by
      cases b
      · simpa only [Bool.not_false] using hloww
      · simpa only [Bool.not_true] using hupw
    change ((p b + w b : SpectralScalarL2) : SpectralCircle → ℂ) =ᵐ[spectralHaar]
      (fun x => NlsGge.Analysis.naturalPhysicalCoverL2 (ψ b) x * (u (!b) + v (!b)) x)
    filter_upwards [hp, hwprod, Lp.coeFn_add (p b) (w b),
      Lp.coeFn_add (u (!b)) (v (!b))] with x hpx hwx hsumg hsumf
    rw [hsumg, hsumf]
    change p b x + w b x =
      NlsGge.Analysis.naturalPhysicalCoverL2 (ψ b) x * (u (!b) x + v (!b) x)
    rw [hpx, hwx]
    ring
  have hpv : spectralPn n v = 0 := by
    have hq : v - spectralPn n v = v := hqrange
    have heq : spectralPn n v = 0 := by
      have : v - spectralPn n v - v = 0 := sub_eq_zero.mpr hq
      have hz' : -(spectralPn n v) = 0 := by
        calc
          -(spectralPn n v) = v - spectralPn n v - v := by abel
          _ = 0 := this
      exact neg_eq_zero.mp hz'
    exact heq
  have hpuv : spectralPn n (u + v) = u := by rw [map_add, hu, hpv, add_zero]
  refine ⟨hgraph, hproduct, hpuv, ?_⟩
  intro hne hzero
  apply hne
  calc
    u = spectralPn n (u + v) := hpuv.symm
    _ = 0 := by rw [hzero, map_zero]

/-! ### Raw reduced equation versus the kernel of `reducedS` -/

theorem raw_iff_kernel (ψ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) :
    (∃ u : KSTPairL2, u ≠ 0 ∧ spectralPn n u = u ∧
        (z - (n : ℂ) * (Real.pi : ℂ)) • u =
          spectralPn n
            (Ring.inverse (1 - NlsGge.Atomic.KST006.qOperator ψ n z hz)
              (NlsGge.Atomic.KST012.potentialOnPn ψ n u))) ↔
      ∃ u : NlsGge.Atomic.KST013.resonantSubspace n, u ≠ 0 ∧
        NlsGge.Atomic.KST013.reducedS ψ n z hz u = 0 := by
  have hfix (u : NlsGge.Atomic.KST013.resonantSubspace n) :
      spectralPn n (u : KSTPairL2) = u := by
    obtain ⟨v, hv⟩ := u.property
    change spectralPn n v = (u : KSTPairL2) at hv
    have h := congrArg (fun S : KSTPairL2 →L[ℂ] KSTPairL2 => S v)
      (spectralPn_idempotent n)
    change spectralPn n (spectralPn n v) = spectralPn n v at h
    rw [hv] at h
    exact h
  constructor
  · rintro ⟨u, hune, hu, heq⟩
    let v : NlsGge.Atomic.KST013.resonantSubspace n := ⟨u, ⟨u, hu⟩⟩
    refine ⟨v, ?_, ?_⟩
    · intro hv
      apply hune
      exact congrArg (fun a : NlsGge.Atomic.KST013.resonantSubspace n => (a : KSTPairL2)) hv
    · apply Subtype.ext
      change (z - (n : ℂ) * (Real.pi : ℂ)) • u -
        spectralPn n
          (Ring.inverse (1 - NlsGge.Atomic.KST006.qOperator ψ n z hz)
            (NlsGge.Atomic.KST012.potentialOnPn ψ n u)) = 0
      exact sub_eq_zero.mpr heq
  · rintro ⟨u, hune, heq⟩
    refine ⟨u, ?_, hfix u, ?_⟩
    · intro hu
      apply hune
      exact Subtype.ext hu
    · have h := congrArg (fun a : NlsGge.Atomic.KST013.resonantSubspace n => (a : KSTPairL2)) heq
      change (z - (n : ℂ) * (Real.pi : ℂ)) • (u : KSTPairL2) -
        spectralPn n
          (Ring.inverse (1 - NlsGge.Atomic.KST006.qOperator ψ n z hz)
            (NlsGge.Atomic.KST012.potentialOnPn ψ n u)) = 0 at h
      exact sub_eq_zero.mp h

/-! ### Kernel of `reducedS` versus the determinant of `schurMatrix` -/

theorem resonant_expand (n : ℤ) (w : NlsGge.Atomic.KST013.resonantSubspace n) :
    (w : KSTPairL2) =
      inner ℂ (schurFrame n false : KSTPairL2) (w : KSTPairL2) • (schurFrame n false : KSTPairL2) +
      inner ℂ (schurFrame n true : KSTPairL2) (w : KSTPairL2) • (schurFrame n true : KSTPairL2) := by
  obtain ⟨v, hv⟩ := w.property
  have hfix : spectralPn n (w : KSTPairL2) = w := by
    change spectralPn n v = (w : KSTPairL2) at hv
    have h := congrArg (fun S : KSTPairL2 →L[ℂ] KSTPairL2 => S v)
      (spectralPn_idempotent n)
    change spectralPn n (spectralPn n v) = spectralPn n v at h
    rw [hv] at h
    exact h
  have e0 : (schurFrame n false : KSTPairL2) = kstPnLower n := rfl
  have e1 : (schurFrame n true : KSTPairL2) = kstPnUpper n := rfl
  rw [e0, e1]
  conv_lhs => rw [← hfix, spectralPn_apply]
  exact add_comm _ _

/-- The combination `c₀ e_false + c₁ e_true` as an element of the resonant subspace. -/
def comb (n : ℤ) (c0 c1 : ℂ) : NlsGge.Atomic.KST013.resonantSubspace n :=
  c0 • schurFrame n false + c1 • schurFrame n true

theorem comb_coe (n : ℤ) (c0 c1 : ℂ) :
    (comb n c0 c1 : KSTPairL2) =
      c0 • (schurFrame n false : KSTPairL2) + c1 • (schurFrame n true : KSTPairL2) := rfl

theorem inner_comb (n : ℤ) (c0 c1 : ℂ) (b : Bool) :
    inner ℂ (schurFrame n b : KSTPairL2) (comb n c0 c1 : KSTPairL2) =
      if b then c1 else c0 := by
  rw [comb_coe, inner_add_right, inner_smul_right, inner_smul_right, schurFrame_inner,
    schurFrame_inner]
  cases b <;> simp

theorem resonant_eq_comb (n : ℤ) (w : NlsGge.Atomic.KST013.resonantSubspace n) :
    w = comb n (inner ℂ (schurFrame n false : KSTPairL2) (w : KSTPairL2))
      (inner ℂ (schurFrame n true : KSTPairL2) (w : KSTPairL2)) :=
  Subtype.ext (resonant_expand n w)

theorem inner_reduced_comb (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n) (c0 c1 : ℂ) (b : Bool) :
    inner ℂ (schurFrame n b : KSTPairL2)
        (NlsGge.Atomic.KST013.reducedS (schurPhysicalPair φ) n lam hlam (comb n c0 c1) :
          KSTPairL2) =
      c0 * schurEntry φ n lam hlam b false + c1 * schurEntry φ n lam hlam b true := by
  have h : NlsGge.Atomic.KST013.reducedS (schurPhysicalPair φ) n lam hlam (comb n c0 c1) =
      c0 • NlsGge.Atomic.KST013.reducedS (schurPhysicalPair φ) n lam hlam (schurFrame n false) +
      c1 • NlsGge.Atomic.KST013.reducedS (schurPhysicalPair φ) n lam hlam (schurFrame n true) := by
    unfold comb
    rw [map_add, map_smul, map_smul]
  rw [h]
  change inner ℂ (schurFrame n b : KSTPairL2)
    (c0 • (NlsGge.Atomic.KST013.reducedS (schurPhysicalPair φ) n lam hlam (schurFrame n false) :
        KSTPairL2) +
      c1 • (NlsGge.Atomic.KST013.reducedS (schurPhysicalPair φ) n lam hlam (schurFrame n true) :
        KSTPairL2)) = _
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  rfl

theorem schurMatrix_00 (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n) :
    schurMatrix φ n lam hlam 0 0 = schurEntry φ n lam hlam false false := by
  simp [schurMatrix, schurDiagonalPlus]

theorem schurMatrix_01 (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n) :
    schurMatrix φ n lam hlam 0 1 = schurEntry φ n lam hlam false true := by
  simp [schurMatrix, offDiagonal]

theorem schurMatrix_10 (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n) :
    schurMatrix φ n lam hlam 1 0 = schurEntry φ n lam hlam true false := by
  simp [schurMatrix, offDiagonal]

theorem schurMatrix_11 (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n) :
    schurMatrix φ n lam hlam 1 1 = schurEntry φ n lam hlam true true := by
  simp [schurMatrix, schurDiagonalMinus]

theorem schurMatrix_mulVec (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n) (c0 c1 : ℂ) :
    Matrix.mulVec (schurMatrix φ n lam hlam) ![c0, c1] =
      ![inner ℂ (schurFrame n false : KSTPairL2)
          (NlsGge.Atomic.KST013.reducedS (schurPhysicalPair φ) n lam hlam (comb n c0 c1) :
            KSTPairL2),
        inner ℂ (schurFrame n true : KSTPairL2)
          (NlsGge.Atomic.KST013.reducedS (schurPhysicalPair φ) n lam hlam (comb n c0 c1) :
            KSTPairL2)] := by
  rw [inner_reduced_comb, inner_reduced_comb]
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, schurMatrix_00, schurMatrix_01]
    ring
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, schurMatrix_10, schurMatrix_11]
    ring

theorem kernel_iff_det (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n) :
    (∃ u : NlsGge.Atomic.KST013.resonantSubspace n, u ≠ 0 ∧
        NlsGge.Atomic.KST013.reducedS (schurPhysicalPair φ) n lam hlam u = 0) ↔
      Matrix.det (schurMatrix φ n lam hlam) = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨u, hune, hS⟩
    refine ⟨![inner ℂ (schurFrame n false : KSTPairL2) (u : KSTPairL2),
      inner ℂ (schurFrame n true : KSTPairL2) (u : KSTPairL2)], ?_, ?_⟩
    · intro h0
      apply hune
      have h00 := congrFun h0 0
      have h01 := congrFun h0 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h00 h01
      rw [resonant_eq_comb n u, h00, h01]
      apply Subtype.ext
      simp [comb_coe]
    · rw [schurMatrix_mulVec, ← resonant_eq_comb n u, hS]
      ext i
      fin_cases i <;> simp
  · rintro ⟨c, hcne, hMc⟩
    have hc : c = ![c 0, c 1] := by
      ext i
      fin_cases i <;> simp
    rw [hc, schurMatrix_mulVec] at hMc
    have h00 := congrFun hMc 0
    have h01 := congrFun hMc 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h00 h01
    refine ⟨comb n (c 0) (c 1), ?_, ?_⟩
    · intro h0
      apply hcne
      have e0 := inner_comb n (c 0) (c 1) false
      have e1 := inner_comb n (c 0) (c 1) true
      rw [h0] at e0 e1
      simp only [Submodule.coe_zero, inner_zero_right, Bool.false_eq_true, ↓reduceIte] at e0 e1
      ext i
      fin_cases i
      · simpa using e0.symm
      · simpa using e1.symm
    · apply Subtype.ext
      rw [resonant_expand n (NlsGge.Atomic.KST013.reducedS (schurPhysicalPair φ) n lam hlam
        (comb n (c 0) (c 1))), h00, h01]
      simp

/-! ### The core equivalence -/

theorem periodicEigenvalue_iff_det_core (hAC : ElimAC) (hG : ElimG) (hK : ElimK) (hD : ElimD)
    (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hsmall : ‖ambientT φ n lam hlam ^ 2‖ ≤ (1 / 2 : ℝ)) :
    PeriodicEigenvalue φ n lam ↔ Matrix.det (schurMatrix φ n lam hlam) = 0 := by
  have hT := sq_norm_lt_one φ n lam hlam hsmall
  have hT' : ‖NlsGge.Atomic.KST006.qOperator (schurPhysicalPair φ) n lam hlam ^ 2‖ < 1 := hT
  obtain ⟨hunit, _, _, _⟩ := NlsGge.Atomic.KST012.inverse_one_sub_of_sq_norm_lt
    (NlsGge.Atomic.KST006.qOperator (schurPhysicalPair φ) n lam hlam) hT'
  refine Iff.trans ?_
    ((raw_iff_kernel (schurPhysicalPair φ) n lam hlam).trans (kernel_iff_det φ n lam hlam))
  constructor
  · rintro ⟨F, hFne, _hpar, heq⟩
    have hdirac : NlsGge.Atomic.KST013.dirac (schurPhysicalPair φ) F =
        -actualFullPeriodTwoDoubledCirclePerturbedDiracAction
          (-(schurPhysicalPair φ true)) (-(schurPhysicalPair φ false))
          ⟨(F : KSTPairL2), F.property⟩ := rfl
    have hact : actualFullPeriodTwoDoubledCirclePerturbedDiracAction
        (-(schurPhysicalPair φ true)) (-(schurPhysicalPair φ false))
        ⟨(F : KSTPairL2), F.property⟩ = -(lam • (F : KSTPairL2)) := by
      rw [hdirac] at heq
      exact neg_eq_iff_eq_neg.mp heq
    obtain ⟨g, hgraph, hprod⟩ :=
      (hAC (schurPhysicalPair φ) (F : KSTPairL2) (lam • (F : KSTPairL2))).2
        ⟨F.property, hact⟩
    have hpne : spectralPn n (F : KSTPairL2) ≠ 0 := fun h0 =>
      hFne (hG (schurPhysicalPair φ) n lam hlam (F : KSTPairL2) g hgraph hprod hunit h0)
    refine ⟨spectralPn n (F : KSTPairL2), hpne, ?_,
      hK (schurPhysicalPair φ) n lam hlam (F : KSTPairL2) g hgraph hprod hunit⟩
    have hi := congrArg (fun S : KSTPairL2 →L[ℂ] KSTPairL2 => S (F : KSTPairL2))
      (spectralPn_idempotent n)
    simpa only [ContinuousLinearMap.comp_apply] using hi
  · rintro ⟨u, hune, hu, hred⟩
    obtain ⟨hgraph, hprod, hPu, hnz⟩ :=
      backward_construct hD (schurPhysicalPair φ) n lam hlam hT' u hu hred
    obtain ⟨hf, hact⟩ := (hAC (schurPhysicalPair φ)
      (u + NlsGge.Atomic.KST012.reconstructedComplement (schurPhysicalPair φ) n lam hlam u)
      (lam • (u + NlsGge.Atomic.KST012.reconstructedComplement (schurPhysicalPair φ) n lam hlam u))).1
      ⟨_, hgraph, hprod⟩
    have hmem : spectralPn n u ∈ sectorSub n := spectralPn_mem n u
    rw [hu] at hmem
    refine ⟨⟨_, hf⟩, hnz hune, ?_, ?_⟩
    · exact (mem_sectorSub_iff_parity n _).mp
        (reconstruction_mem (schurPhysicalPair φ) n lam hlam hT' u hmem)
    · change -actualFullPeriodTwoDoubledCirclePerturbedDiracAction
          (-(schurPhysicalPair φ true)) (-(schurPhysicalPair φ false)) ⟨_, hf⟩ = _
      rw [hact, neg_neg]

end NlsGge.ThirdConsultation.MTwoModeSupp

end
