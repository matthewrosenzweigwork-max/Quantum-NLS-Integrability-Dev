import NlsGge.NLS38.SolutionNotion38a

/-! # GWP piece A4 (file b): the interaction-picture equivalence for a general profile

For a continuous radial profile `χ`, the coefficientwise equation
`u_n' = -i((2πn)² u_n + χ(‖u‖_{h¹}) N(u)_n)` with `u ∈ C(ℝ; h^m)` is equivalent to the carrier ODE
`v' = G_χ(t, v)` for `v = e^{itΛ}u ∈ C¹(ℝ; h^m)`.  `IsCutSolM` is the case `χ = cutoff R`,
`IsNLSSolM` the case `χ = 1`; both specialisations are in `SolutionNotion38`.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.NLS38

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open scoped ComplexConjugate NNReal

/-- Solutions of the equation with nonlinearity multiplied by `χ ‖u t‖_{h¹}`. -/
structure IsChiSolM (m : ℕ) (χ : ℝ → ℝ) (u : ℝ → ℤ → ℂ) : Prop where
  mem   : ∀ t, u t ∈ seqSobolev38 (m : ℝ)
  cont  : Continuous fun t => carrierMk38 (m : ℝ) (u t) (mem t)
  deriv : ∀ t n, HasDerivAt (fun s => u s n)
            (-Complex.I * (((disp n : ℝ) : ℂ) * u t n +
              ((χ (hn 1 (u t)) : ℝ) : ℂ) * nonlin (u t) n)) t

theorem hn_phase38 (m : ℕ) (t : ℝ) (x : ℤ → ℂ) : hn m (phase t x) = hn m x := by
  unfold hn
  simp only [norm_phase_apply]

theorem norm_inclOne38_eq_hn (m : ℕ) (hm : 1 ≤ m) (v : SobolevCarrier38 (m : ℝ)) :
    ‖inclOne38 m hm v‖ = hn 1 (carrierCoe38 (m : ℝ) v) := by
  rw [← hn_coe38 1 (inclOne38 m hm v)]
  unfold inclOne38
  rw [carrierCoe38_incl38]

/-- Coordinates of the carrier curve `v_t = e^{itΛ} u_t` have the derivative `(G_χ(t, v_t))_n`. -/
theorem hasDerivAt_coord_interaction38 (m : ℕ) (hm : 1 ≤ m) (χ : ℝ → ℝ) {u : ℝ → ℤ → ℂ}
    {v : ℝ → SobolevCarrier38 (m : ℝ)}
    (hcoe : ∀ t, carrierCoe38 (m : ℝ) (v t) = phase (-t) (u t))
    (hu : ∀ t n, HasDerivAt (fun s => u s n)
      (-Complex.I * (((disp n : ℝ) : ℂ) * u t n +
        ((χ (hn 1 (u t)) : ℝ) : ℂ) * nonlin (u t) n)) t) (t : ℝ) (n : ℤ) :
    HasDerivAt (fun s => carrierCoe38 (m : ℝ) (v s) n)
      (carrierCoe38 (m : ℝ) (Gchi m hm χ t (v t)) n) t := by
  have hph := hasDerivAt_phaseFactor (-(disp n)) t
  have hfun : (fun s => carrierCoe38 (m : ℝ) (v s) n) =
      fun s => Complex.exp (-(Complex.I * ((s * -(disp n) : ℝ) : ℂ))) * u s n := by
    funext s
    rw [hcoe s]
    have e : (-s * disp n) = s * -(disp n) := by ring
    show Complex.exp (-(Complex.I * ((-s * disp n : ℝ) : ℂ))) * u s n = _
    rw [e]
  rw [hfun]
  have hp := hph.mul (hu t n)
  have hphu : phase t (carrierCoe38 (m : ℝ) (v t)) = u t := by
    rw [hcoe t, phase_phase_neg_apply]
  have hχ : χ ‖inclOne38 m hm (v t)‖ = χ (hn 1 (u t)) := by
    rw [norm_inclOne38_eq_hn, hcoe t, hn_phase38]
  rw [carrierCoe38_Gchi, hphu, hχ]
  have e : t * -(disp n) = -t * disp n := by ring
  rw [e] at hp
  refine hp.congr_deriv ?_
  push_cast
  ring


/-- Two carrier curves whose coordinates have the same derivatives and which agree at `0` agree. -/
theorem eq_of_coord_deriv38 (r : ℝ) (w v : ℝ → SobolevCarrier38 r) (a : ℝ → ℤ → ℂ)
    (hw : ∀ t n, HasDerivAt (fun s => carrierCoe38 r (w s) n) (a t n) t)
    (hv : ∀ t n, HasDerivAt (fun s => carrierCoe38 r (v s) n) (a t n) t) (h0 : w 0 = v 0) :
    w = v := by
  funext s
  apply carrierExt38
  funext n
  have hd : ∀ x, HasDerivAt (fun q => carrierCoe38 r (w q) n - carrierCoe38 r (v q) n) 0 x :=
    fun x => by
      have h := (hw x n).sub (hv x n)
      rwa [sub_self] at h
  have hconst := is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt)
    (fun x => (hd x).deriv) s 0
  rw [h0, sub_self] at hconst
  exact sub_eq_zero.1 hconst

/-- Upgrade of coordinatewise to carrier differentiability: if `v` is continuous into the carrier and
its coordinates `v_n` have derivative `(G_χ(t, v_t))_n`, then `v` has carrier derivative
`G_χ(t, v_t)` (the FTC primitive `w` of the continuous field has the same coordinates as `v`). -/
theorem hasDerivAt_of_coord38 (m : ℕ) (hm : 1 ≤ m) {χ : ℝ → ℝ} (hχ : Continuous χ)
    (v : ℝ → SobolevCarrier38 (m : ℝ)) (hvc : Continuous v)
    (hco : ∀ t n, HasDerivAt (fun s => carrierCoe38 (m : ℝ) (v s) n)
      (carrierCoe38 (m : ℝ) (Gchi m hm χ t (v t)) n) t) (t : ℝ) :
    HasDerivAt v (Gchi m hm χ t (v t)) t := by
  have hp : Continuous fun s : ℝ => (s, v s) := continuous_id.prodMk hvc
  have hG := continuous_Gchi_uncurry m hm hχ
  have hF' := hG.comp hp
  have hF : Continuous fun s => Gchi m hm χ s (v s) := hF'
  have hwd : ∀ t, HasDerivAt (fun t => v 0 + ∫ s in (0 : ℝ)..t, Gchi m hm χ s (v s))
      (Gchi m hm χ t (v t)) t := fun t =>
    ((hF.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add (v 0)
  have hwc : ∀ t n, HasDerivAt (fun s => carrierCoe38 (m : ℝ)
      (v 0 + ∫ x in (0 : ℝ)..s, Gchi m hm χ x (v x)) n)
      (carrierCoe38 (m : ℝ) (Gchi m hm χ t (v t)) n) t := fun t n =>
    (coordC38 (m : ℝ) n).hasFDerivAt.comp_hasDerivAt t (hwd t)
  have hwv := eq_of_coord_deriv38 (m : ℝ)
    (fun t => v 0 + ∫ s in (0 : ℝ)..t, Gchi m hm χ s (v s)) v _ hwc hco (by simp)
  have h := hwd t
  rw [hwv] at h
  exact h


theorem isChiSolM_iff (m : ℕ) (hm : 1 ≤ m) {χ : ℝ → ℝ} (hχ : Continuous χ) (u : ℝ → ℤ → ℂ) :
    IsChiSolM m χ u ↔
      ∃ (hmem : ∀ t, u t ∈ seqSobolev38 (m : ℝ)) (v : ℝ → SobolevCarrier38 (m : ℝ)),
        (∀ t, carrierCoe38 (m : ℝ) (v t) = phase (-t) (u t)) ∧
          ∀ t, HasDerivAt v (Gchi m hm χ t (v t)) t := by
  constructor
  · intro h
    have hneg : Continuous fun t : ℝ => -t := continuous_neg
    have hpr := Continuous.prodMk hneg h.cont
    have hvc : Continuous fun t => phaseC (m : ℝ) (-t) (carrierMk38 (m : ℝ) (u t) (h.mem t)) :=
      (continuous_phaseC (m : ℝ)).comp hpr
    refine ⟨h.mem, fun t => phaseC (m : ℝ) (-t) (carrierMk38 (m : ℝ) (u t) (h.mem t)),
      fun t => rfl, fun t => ?_⟩
    exact hasDerivAt_of_coord38 m hm hχ _ hvc
      (fun t n => hasDerivAt_coord_interaction38 m hm χ (fun t => rfl) h.deriv t n) t
  · rintro ⟨hmem, v, hcoe, hv⟩
    have hphu : ∀ t, phase t (carrierCoe38 (m : ℝ) (v t)) = u t := fun t => by
      rw [hcoe t, phase_phase_neg_apply]
    have hvc : Continuous v := continuous_iff_continuousAt.2 fun t => (hv t).continuousAt
    refine ⟨hmem, ?_, ?_⟩
    · have hfun : (fun t => carrierMk38 (m : ℝ) (u t) (hmem t)) =
          fun t => phaseC (m : ℝ) t (v t) := by
        funext t
        apply carrierExt38
        funext n
        rw [carrierCoe38_mk, carrierCoe38_phaseC, hphu]
      rw [hfun]
      have hpr : Continuous fun t : ℝ => (t, v t) := continuous_id.prodMk hvc
      have hc := (continuous_phaseC (m : ℝ)).comp hpr
      exact hc
    · intro t n
      have hph := hasDerivAt_phaseFactor (disp n) t
      have hco : HasDerivAt (fun s => carrierCoe38 (m : ℝ) (v s) n)
          (carrierCoe38 (m : ℝ) (Gchi m hm χ t (v t)) n) t :=
        (coordC38 (m : ℝ) n).hasFDerivAt.comp_hasDerivAt t (hv t)
      have hfun : (fun s => u s n) =
          fun s => Complex.exp (-(Complex.I * ((s * disp n : ℝ) : ℂ))) *
            carrierCoe38 (m : ℝ) (v s) n := by
        funext s
        rw [← hphu s]
        rfl
      rw [hfun]
      have hp := hph.mul hco
      have hχ' : χ ‖inclOne38 m hm (v t)‖ = χ (hn 1 (u t)) := by
        rw [norm_inclOne38_eq_hn, ← hphu t, hn_phase38]
      rw [carrierCoe38_Gchi, hphu, hχ'] at hp
      refine hp.congr_deriv ?_
      have e2 : u t n = Complex.exp (-(Complex.I * ((t * disp n : ℝ) : ℂ))) *
          carrierCoe38 (m : ℝ) (v t) n := by
        rw [← hphu t]; rfl
      have e1 : Complex.exp (-(Complex.I * ((-t * disp n : ℝ) : ℂ))) *
          Complex.exp (-(Complex.I * ((t * disp n : ℝ) : ℂ))) = 1 := by
        rw [← Complex.exp_add]
        convert Complex.exp_zero using 2
        push_cast
        ring
      rw [e2]
      set E := Complex.exp (-(Complex.I * ((t * disp n : ℝ) : ℂ))) with hE
      set E' := Complex.exp (-(Complex.I * ((-t * disp n : ℝ) : ℂ))) with hE'
      set X := carrierCoe38 (m : ℝ) (v t) n
      linear_combination (-(Complex.I * ((χ (hn 1 (u t)) : ℝ) : ℂ) * nonlin (u t) n)) * e1

end NlsGge.NLS38
