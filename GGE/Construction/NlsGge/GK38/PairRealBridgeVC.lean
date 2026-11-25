import NlsGge.GK38.PairVolterraProbe
import NlsGge.GK38.PairAnalyticDet
import NlsGge.Spectral.ComplexAbsolutelyContinuousAEODEIntegralIdentityV1

/-!
# F4 (part 1): variation of constants, from an AC a.e. solution to the book integral equation

Source: Grébert-Kappeler book, Chapter I, section 1 (the integral equation `(1.2)` and the proof of
Theorem 1.1).  F2's `fundCont_unique` identifies a *continuous solution of the book integral
equation* `M = E_z + 𝒱 M` on `[0,1]`.  E02's notion of fundamental solution is different: an
absolutely continuous function with the ODE `M' = (-zR + Φ̃) M` almost everywhere and `M(0) = 1`
(`actualPhysicalL2ZsDysonTsum_is_AC_fundamental`).  This file bridges the two for an arbitrary
`φ : PotPair`, with the coefficient `zsCoeffPot38 φ z` of F1's representatives:

  `d/ds [E_z(-s) D(s)] = E_z(-s) Φ̃(s) D(s)`  (a.e., product of absolutely continuous functions)

so `E_z(-t) D(t) = 1 + ∫₀ᵗ E_z(-s) Φ̃ D` (FTC for AC functions), then multiply by `E_z(t)`
(`volterraFun_eq`).  The result `fundPair_eq_of_ac_ae_ode38` is the pair analogue of E02's
`actualPhysicalL2Zs_AC_fundamental_eq_Dyson`.  No continuity of `D` or of `Φ̃` is assumed
beyond what absolute continuity gives.
-/

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace NlsGge.GK38

noncomputable section

/-- The exponents of the diagonal of `E_z(-y)`: `E_z(-y)_{ii} = exp (c_i y)`. -/
def diagExp38 (z : ℂ) : Fin 2 → ℂ := ![Complex.I * z, -(Complex.I * z)]

theorem freeE_neg_diag38 (z : ℂ) (y : ℝ) (i : Fin 2) :
    freeE z (-y) i i = Complex.exp (diagExp38 z i * y) := by
  fin_cases i <;> simp [freeE, diagExp38]

theorem hasDerivAt_freeE_neg_diag38 (z : ℂ) (i : Fin 2) (x : ℝ) :
    HasDerivAt (fun y : ℝ => freeE z (-y) i i) (diagExp38 z i * freeE z (-x) i i) x := by
  have h := hasDerivAt_cexp_mul (diagExp38 z i) x
  have e : (fun y : ℝ => freeE z (-y) i i) = fun y : ℝ => Complex.exp (diagExp38 z i * y) :=
    funext fun y => freeE_neg_diag38 z y i
  rw [e, freeE_neg_diag38]
  exact h

theorem contDiff_freeE_neg_diag38 (z : ℂ) (i : Fin 2) :
    ContDiff ℝ 1 (fun y : ℝ => freeE z (-y) i i) := by
  have e : (fun y : ℝ => freeE z (-y) i i) = fun y : ℝ => Complex.exp (diagExp38 z i * y) :=
    funext fun y => freeE_neg_diag38 z y i
  rw [e]
  exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

/-- Variation of constants, pointwise: for `G' = (-zR + Φ̃) G` at `x` (entry `(i,j)`),
`d/dy [E_z(-y)_{ii} G(y)_{ij}] = (E_z(-x) Φ̃(x) G(x))_{ij}`. -/
theorem hasDerivAt_vc38 (φ : PotPair) (z : ℂ) (G : ℝ → PairMat38) (x : ℝ) (i j : Fin 2)
    (hG : HasDerivAt (fun y => G y i j) ((zsCoeffPot38 φ z x * G x) i j) x) :
    HasDerivAt (fun y => freeE z (-y) i i * G y i j)
      ((freeE z (-x) * potCoeff38 φ x * G x) i j) x := by
  refine ((hasDerivAt_freeE_neg_diag38 z i x).mul hG).congr_deriv ?_
  rw [zsCoeffPot38_eq]
  fin_cases i <;> fin_cases j <;>
    simp [freeE, diagExp38, potCoeff38, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Restriction of a function continuous on `[0,1]` to a continuous map on `Icc 0 1`. -/
def restrictCont38 (D : ℝ → PairMat38) (h : ContinuousOn D (Set.Icc (0 : ℝ) 1)) :
    C(Set.Icc (0 : ℝ) 1, Matrix (Fin 2) (Fin 2) ℂ) :=
  ⟨fun t => D t, h.domRestrict⟩

theorem restrictCont38_apply (D : ℝ → PairMat38) (h : ContinuousOn D (Set.Icc (0 : ℝ) 1))
    (t : Set.Icc (0 : ℝ) 1) : restrictCont38 D h t = D t := rfl

theorem restrictCont38_ext {D : ℝ → PairMat38} (h : ContinuousOn D (Set.Icc (0 : ℝ) 1)) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) : Set.IccExtend zero_le_one (restrictCont38 D h) s = D s := by
  rw [Set.IccExtend_of_mem _ _ hs]; rfl

theorem continuousOn_of_ac38 {D : ℝ → PairMat38}
    (hAC : ∀ i j : Fin 2, AbsolutelyContinuousOnInterval (fun t => D t i j) 0 2) :
    ContinuousOn D (Set.Icc (0 : ℝ) 1) := by
  apply continuousOn_pi.2
  intro i
  apply continuousOn_pi.2
  intro j
  have := (hAC i j).continuousOn
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at this
  exact this.mono (Set.Icc_subset_Icc le_rfl (by norm_num))

/-- **Variation of constants** (book `(1.2)`): an entrywise absolutely continuous `D` on `[0,2]` with
`D 0 = 1` and `D' = (-zR + Φ̃) D` almost everywhere satisfies the book integral equation on `[0,1]`
(with the continuous restriction of `D`). -/
theorem bookIntegralEq_of_ac_ae_ode38 (φ : PotPair) (z : ℂ) (D : ℝ → PairMat38)
    (hinit : D 0 = 1)
    (hAC : ∀ i j : Fin 2, AbsolutelyContinuousOnInterval (fun t => D t i j) 0 2)
    (hODE : ∀ i j : Fin 2, ∀ᵐ t ∂volume, t ∈ Set.uIcc (0 : ℝ) 2 →
      HasDerivAt (fun s => D s i j) ((zsCoeffPot38 φ z t * D t) i j) t)
    (t : Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    D t i j = freeE z t i j + ∫ s in (0 : ℝ)..t,
      (freeE z (t - s) * potCoeff38 φ s *
        Set.IccExtend zero_le_one (restrictCont38 D (continuousOn_of_ac38 hAC)) s) i j := by
  set hc := continuousOn_of_ac38 hAC with hhc
  set Gc := restrictCont38 D hc with hGc
  have hext : ∀ s ∈ Set.Icc (0 : ℝ) 1, Set.IccExtend zero_le_one Gc s = D s :=
    fun s hs => restrictCont38_ext hc hs
  have hfac : ∫ s in (0 : ℝ)..t, (freeE z (t - s) * potCoeff38 φ s *
        Set.IccExtend zero_le_one Gc s) i j =
      freeE z t i i * ∫ s in (0 : ℝ)..t, (freeE z (-s) * potCoeff38 φ s *
        Set.IccExtend zero_le_one Gc s) i j := by
    have h := congrArg (fun M => M i j) (volterraFun_eq φ z Gc t)
    simp only [volterraKer, Matrix.of_apply, freeE_mul_apply] at h
    exact h
  set g : ℝ → ℂ := fun s => (freeE z (-s) * potCoeff38 φ s * Set.IccExtend zero_le_one Gc s) i j
    with hg
  have hK : Continuous fun s : ℝ => freeE z (-s) :=
    (continuous_freeE z).comp continuous_neg
  have hgint : IntervalIntegrable g volume 0 1 :=
    intervalIntegrable_triple_entry φ hK (continuous_ext38 Gc) i j
  have h01 : Set.uIcc (0 : ℝ) 1 ⊆ Set.uIcc 0 2 := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    exact Set.Icc_subset_Icc le_rfl (by norm_num)
  have hE : AbsolutelyContinuousOnInterval (fun y : ℝ => freeE z (-y) i i) 0 1 :=
    (contDiff_freeE_neg_diag38 z i).contDiffOn.absolutelyContinuousOnInterval
  have hF : AbsolutelyContinuousOnInterval (fun y : ℝ => freeE z (-y) i i * D y i j) 0 1 :=
    hE.smul ((hAC i j).mono h01)
  have hder : ∀ᵐ x ∂volume, x ∈ Set.uIcc (0 : ℝ) 1 →
      HasDerivAt (fun y : ℝ => freeE z (-y) i i * D y i j) (g x) x := by
    filter_upwards [hODE i j] with x hx hx1
    have hx1' : x ∈ Set.Icc (0 : ℝ) 1 := by rwa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx1
    have := hasDerivAt_vc38 φ z D x i j (hx (h01 hx1))
    simpa only [hg, hext x hx1'] using this
  have hftc := NlsGge.SpectralFoundations.complex_absolutelyContinuous_eq_initial_add_integral_of_ae_hasDerivAt hF hgint hder
    t (by rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact t.2)
  have hint : ∫ s in (0 : ℝ)..t, g s =
      ∫ s in (0 : ℝ)..t, (freeE z (-s) * potCoeff38 φ s * Set.IccExtend zero_le_one Gc s) i j := rfl
  rw [hfac, ← hint]
  have hF0 : freeE z (-(0 : ℝ)) i i * D 0 i j = (1 : PairMat38) i j := by
    rw [neg_zero, freeE_zero, hinit]; simp
  have hu := freeE_mul_freeE_neg z t i
  have he := freeE_apply_eq z t i j
  rw [he]
  linear_combination (-(D t i j)) * hu + (freeE z t i i) * hftc + (freeE z t i i) * hF0

/-- **Pair analogue of E02's `actualPhysicalL2Zs_AC_fundamental_eq_Dyson`.**  An entrywise absolutely
continuous solution `D` of `D' = (-zR + Φ̃) D` a.e. on `[0,2]`, `D 0 = 1`, equals F2's fundamental
solution `fundPair φ z` on `[0,1]`: by `bookIntegralEq_of_ac_ae_ode38` and F2's `fundCont_unique`. -/
theorem fundPair_eq_of_ac_ae_ode38 (φ : PotPair) (z : ℂ) (D : ℝ → PairMat38)
    (hinit : D 0 = 1)
    (hAC : ∀ i j : Fin 2, AbsolutelyContinuousOnInterval (fun t => D t i j) 0 2)
    (hODE : ∀ i j : Fin 2, ∀ᵐ t ∂volume, t ∈ Set.uIcc (0 : ℝ) 2 →
      HasDerivAt (fun s => D s i j) ((zsCoeffPot38 φ z t * D t) i j) t)
    (t : Set.Icc (0 : ℝ) 1) : fundPair φ z t = D t := by
  have h := fundCont_unique φ z (restrictCont38 D (continuousOn_of_ac38 hAC))
    (fun t i j => bookIntegralEq_of_ac_ae_ode38 φ z D hinit hAC hODE t i j)
  rw [fundPair_eq, ← h]
  rfl

end

end NlsGge.GK38
