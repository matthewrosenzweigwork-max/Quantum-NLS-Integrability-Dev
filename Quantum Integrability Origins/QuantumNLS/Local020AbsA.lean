import Mathlib
import QuantumNLS.Local020Abs

/-! LOCAL-020 stage S5a: abstract antiunitary intertwining.

`AntiU X` is a real-linear isometry `K` of `X` with `K(c x) = conj c · K x`, `K K = 1` and
`⟪Kx, Ky⟫ = conj ⟪x, y⟫`.  `cjT KA KB T = K_B ∘ T ∘ K_A` is the induced conjugate-linear transport of operators
`A → B`; it is multiplicative, adjoint-compatible and norm preserving.  If the graph `G'` is `{(Kf, -Kφ)}` of `G` then
`res G' (-conj z) = - K (res G z) K`, and contour integrals transform by the reflection `z ↦ -conj z`
(`riesz_transportA`, `dressed_transportA`).  The reduced-matrix pipeline `cmpM/isoU/redM` of `Local020Abs` is
transported (`redM_transportA`). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
noncomputable section
open Filter Topology Set MeasureTheory ComplexConjugate QuantumNLS.Local020Abs
open scoped InnerProductSpace

namespace QuantumNLS.Local020AbsA

structure AntiU (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℂ X] where
  K : X →ₗᵢ[ℝ] X
  smul : ∀ (c : ℂ) (x : X), K (c • x) = conj c • K x
  invol : ∀ x, K (K x) = x
  inner : ∀ x y, ⟪K x, K y⟫_ℂ = conj ⟪x, y⟫_ℂ

section Basic

variable {A B C : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [NormedAddCommGroup B]
  [InnerProductSpace ℂ B] [NormedAddCommGroup C] [InnerProductSpace ℂ C]

/-- Conjugate-linear transport `T ↦ K_B T K_A`. -/
def cjT (KA : AntiU A) (KB : AntiU B) (T : A →L[ℂ] B) : A →L[ℂ] B where
  toFun x := KB.K (T (KA.K x))
  map_add' x y := by simp [map_add]
  map_smul' c x := by
    simp only [RingHom.id_apply]
    rw [KA.smul, T.map_smul, KB.smul, Complex.conj_conj]
  cont := KB.K.continuous.comp (T.continuous.comp KA.K.continuous)

theorem cjT_apply (KA : AntiU A) (KB : AntiU B) (T : A →L[ℂ] B) (x : A) :
    cjT KA KB T x = KB.K (T (KA.K x)) := rfl

theorem cjT_add (KA : AntiU A) (KB : AntiU B) (S T : A →L[ℂ] B) :
    cjT KA KB (S + T) = cjT KA KB S + cjT KA KB T := by
  ext x; simp [cjT_apply]

theorem cjT_sub (KA : AntiU A) (KB : AntiU B) (S T : A →L[ℂ] B) :
    cjT KA KB (S - T) = cjT KA KB S - cjT KA KB T := by
  ext x; simp [cjT_apply]

theorem cjT_smul (KA : AntiU A) (KB : AntiU B) (c : ℂ) (T : A →L[ℂ] B) :
    cjT KA KB (c • T) = conj c • cjT KA KB T := by
  ext x; simp [cjT_apply, KB.smul]

theorem cjT_comp (KA : AntiU A) (KB : AntiU B) (KC : AntiU C) (S : B →L[ℂ] C) (T : A →L[ℂ] B) :
    cjT KA KC (S ∘L T) = cjT KB KC S ∘L cjT KA KB T := by
  ext x; simp [cjT_apply, KB.invol]

theorem cjT_cjT (KA : AntiU A) (KB : AntiU B) (T : A →L[ℂ] B) :
    cjT KA KB (cjT KA KB T) = T := by
  ext x; simp [cjT_apply, KA.invol, KB.invol]

theorem cjT_id (KA : AntiU A) : cjT KA KA (ContinuousLinearMap.id ℂ A) = ContinuousLinearMap.id ℂ A := by
  ext x; simp [cjT_apply, KA.invol]

theorem norm_cjT_le (KA : AntiU A) (KB : AntiU B) (T : A →L[ℂ] B) : ‖cjT KA KB T‖ ≤ ‖T‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  rw [cjT_apply, KB.K.norm_map]
  exact (T.le_opNorm _).trans (by rw [KA.K.norm_map])

theorem norm_cjT (KA : AntiU A) (KB : AntiU B) (T : A →L[ℂ] B) : ‖cjT KA KB T‖ = ‖T‖ := by
  refine le_antisymm (norm_cjT_le KA KB T) ?_
  have := norm_cjT_le KA KB (cjT KA KB T)
  rwa [cjT_cjT] at this

theorem cjT_real_smul (KA : AntiU A) (KB : AntiU B) (r : ℝ) (T : A →L[ℂ] B) :
    cjT KA KB ((r : ℂ) • T) = (r : ℂ) • cjT KA KB T := by
  rw [cjT_smul, Complex.conj_ofReal]

variable [CompleteSpace A] [CompleteSpace B]

theorem adjoint_cjT (KA : AntiU A) (KB : AntiU B) (T : A →L[ℂ] B) :
    ContinuousLinearMap.adjoint (cjT KA KB T) = cjT KB KA (ContinuousLinearMap.adjoint T) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro y x
  simp only [cjT_apply]
  have h1 : ⟪KA.K (ContinuousLinearMap.adjoint T (KB.K y)), x⟫_ℂ =
      conj ⟪ContinuousLinearMap.adjoint T (KB.K y), KA.K x⟫_ℂ := by
    conv_lhs => rw [← KA.invol x]
    rw [KA.inner]
  have h2 : ⟪y, KB.K (T (KA.K x))⟫_ℂ = conj ⟪KB.K y, T (KA.K x)⟫_ℂ := by
    conv_lhs => rw [← KB.invol y]
    rw [KB.inner]
  rw [h1, h2, ContinuousLinearMap.adjoint_inner_left]

/-- `cjT` as a real-linear continuous equivalence of the operator space. -/
def cjL (KA : AntiU A) (KB : AntiU B) : (A →L[ℂ] B) →L[ℝ] (A →L[ℂ] B) :=
  LinearMap.mkContinuous
    { toFun := cjT KA KB
      map_add' := cjT_add KA KB
      map_smul' := fun r T => by
        simp only [RingHom.id_apply]
        rw [← Complex.coe_smul, ← Complex.coe_smul, cjT_real_smul] }
    1 (fun T => by rw [one_mul]; exact norm_cjT_le KA KB T)

def cjEquiv (KA : AntiU A) (KB : AntiU B) : (A →L[ℂ] B) ≃L[ℝ] (A →L[ℂ] B) :=
  ContinuousLinearEquiv.equivOfInverse (cjL KA KB) (cjL KA KB)
    (fun T => cjT_cjT KA KB T) (fun T => cjT_cjT KA KB T)

theorem cjEquiv_apply (KA : AntiU A) (KB : AntiU B) (T : A →L[ℂ] B) : cjEquiv KA KB T = cjT KA KB T := rfl

theorem cjT_tsum (KA : AntiU A) (KB : AntiU B) {ι : Type*} (f : ι → (A →L[ℂ] B)) :
    cjT KA KB (∑' k, f k) = ∑' k, cjT KA KB (f k) := by
  simpa only [cjEquiv_apply] using (cjEquiv KA KB).map_tsum (f := f)

end Basic

/-! ### Contour integrals under `z ↦ -conj z` -/

section Circle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem exp_pi_sub (θ : ℝ) :
    Complex.exp ((((Real.pi - θ : ℝ)) : ℂ) * Complex.I) = - Complex.exp (-(θ * Complex.I)) := by
  push_cast
  rw [sub_mul, Complex.exp_sub, Complex.exp_pi_mul_I, Complex.exp_neg (θ * Complex.I)]
  rw [div_eq_mul_inv]; simp

theorem conj_circle_pt (c : ℂ) (r θ : ℝ) :
    -(conj (circleMap (-(conj c)) r θ)) = circleMap c r (Real.pi - θ) := by
  have h : conj (Complex.exp (θ * Complex.I)) = Complex.exp (-(θ * Complex.I)) := by
    rw [← Complex.exp_conj]; simp
  simp only [circleMap, map_add, map_neg, map_mul, Complex.conj_ofReal, Complex.conj_conj, h]
  rw [exp_pi_sub]
  ring

theorem conj_circle_deriv (c : ℂ) (r θ : ℝ) :
    conj (deriv (circleMap (-(conj c)) r) θ) = deriv (circleMap c r) (Real.pi - θ) := by
  have h : conj (Complex.exp (θ * Complex.I)) = Complex.exp (-(θ * Complex.I)) := by
    rw [← Complex.exp_conj]; simp
  rw [deriv_circleMap, deriv_circleMap, circleMap_zero, circleMap_zero]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, h]
  rw [exp_pi_sub]
  ring

theorem circle_conj (Φ : E ≃L[ℝ] E) (hΦ : ∀ (c : ℂ) (x : E), Φ (c • x) = conj c • Φ x) (F : ℂ → E)
    (c : ℂ) (r : ℝ) :
    circleIntegral (fun z' => Φ (F (-(conj z')))) (-(conj c)) r = Φ (circleIntegral F c r) := by
  unfold circleIntegral
  have h0 : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  rw [intervalIntegral.integral_of_le h0, intervalIntegral.integral_of_le h0,
    ← ContinuousLinearEquiv.integral_comp_comm]
  set f : ℝ → E := fun φ => deriv (circleMap c r) φ • F (circleMap c r φ) with hf
  have key : ∀ θ : ℝ, deriv (circleMap (-(conj c)) r) θ • Φ (F (-(conj (circleMap (-(conj c)) r θ)))) =
      Φ (f (Real.pi - θ)) := by
    intro θ
    simp only [hf]
    rw [conj_circle_pt, ← conj_circle_deriv c r θ, hΦ, Complex.conj_conj]
  have hper : Function.Periodic (fun θ => Φ (f θ)) (2 * Real.pi) := by
    intro θ
    simp only [hf, deriv_circleMap, periodic_circleMap c r θ, periodic_circleMap 0 r θ]
  rw [← intervalIntegral.integral_of_le h0, ← intervalIntegral.integral_of_le h0]
  simp only [key]
  have h1 := intervalIntegral.integral_comp_sub_left (fun θ => Φ (f θ)) (a := 0) (b := 2 * Real.pi) Real.pi
  rw [h1]
  have h2 := hper.intervalIntegral_add_eq (Real.pi - 2 * Real.pi) 0
  rw [show Real.pi - 2 * Real.pi + 2 * Real.pi = Real.pi - 0 by ring, zero_add] at h2
  rw [h2]

end Circle

/-! ### Resolvents under conjugation -/

section Res

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `G' = {(Kf, -Kφ) : (f, φ) ∈ G}`, both graphs being subspaces. -/
structure InterA (G G' : Set (H × H)) (K : AntiU H) : Prop where
  iff : ∀ f φ, (f, φ) ∈ G ↔ (K.K f, -K.K φ) ∈ G'
  neg : ∀ f φ, (f, φ) ∈ G' → (-f, -φ) ∈ G'

theorem InterA.symm {G G' : Set (H × H)} {K : AntiU H} (h : InterA G G' K) : InterA G' G K := by
  have hK : ∀ x, K.K (-x) = -K.K x := fun x => map_neg K.K x
  refine ⟨fun f' φ' => ?_, fun f φ hfφ => ?_⟩
  · have := h.iff (K.K f') (-K.K φ')
    rw [K.invol, hK, K.invol, neg_neg] at this
    exact this.symm
  · have h1 := h.neg _ _ ((h.iff f φ).1 hfφ)
    rw [h.iff]
    rw [hK, hK, neg_neg]
    rw [neg_neg] at h1
    exact h1

theorem InterA.isRes {G G' : Set (H × H)} {K : AntiU H} (h : InterA G G' K) {z : ℂ}
    {R : H →L[ℂ] H} (hR : IsRes G z R) :
    IsRes G' (-(conj z)) (-(cjT K K R)) := by
  have hK : ∀ x, K.K (-x) = -K.K x := fun x => map_neg K.K x
  refine ⟨fun ψ => ?_, fun p hp => ?_⟩
  · have h1 := (h.iff _ _).1 (hR.1 (K.K ψ))
    have h2 := h.neg _ _ h1
    have e : -(-K.K (z • R (K.K ψ) - K.K ψ)) = (-(conj z)) • (-(cjT K K R ψ)) - ψ := by
      rw [neg_neg, map_sub, K.smul, K.invol]
      simp only [cjT_apply, smul_neg, neg_smul, neg_neg]
    simp only [ContinuousLinearMap.neg_apply]
    rw [← e]
    simpa [hK, cjT_apply] using h2
  · have hq := (h.symm.iff p.1 p.2).1 hp
    have h3 := hR.2 _ hq
    simp only [ContinuousLinearMap.neg_apply, cjT_apply]
    have e : K.K ((-(conj z)) • p.1 - p.2) = -(z • K.K p.1 + K.K p.2) := by
      rw [map_sub, K.smul]
      simp only [map_neg, Complex.conj_conj, neg_smul]
      abel
    have h4 : R (z • K.K p.1 + K.K p.2) = K.K p.1 := by
      simpa [sub_neg_eq_add] using h3
    rw [e, map_neg, h4, hK, K.invol, neg_neg]

variable {G G' : Set (H × H)} {K : AntiU H}

theorem res_transportA (h : InterA G G' K) (z : ℂ) :
    res G' (-(conj z)) = -(cjT K K (res G z)) := by
  by_cases hex : ∃ R, IsRes G z R
  · obtain ⟨R, hR⟩ := hex
    rw [res_eq hR, res_eq (h.isRes hR)]
  · rw [res_eq_zero hex]
    have : ¬ ∃ R', IsRes G' (-(conj z)) R' := by
      rintro ⟨R', hR'⟩
      have h4 := h.symm.isRes hR'
      rw [map_neg, Complex.conj_conj, neg_neg] at h4
      exact hex ⟨_, h4⟩
    rw [res_eq_zero this]
    ext x
    simp [cjT_apply]

theorem res_transportA' (h : InterA G G' K) (z' : ℂ) :
    res G' z' = -(cjT K K (res G (-(conj z')))) := by
  have := res_transportA h (-(conj z'))
  rwa [map_neg, Complex.conj_conj, neg_neg] at this

end Res

section Contour

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {G G' : Set (H × H)} {K : AntiU H}

theorem cjEquiv_smul (c : ℂ) (T : H →L[ℂ] H) : cjEquiv K K (c • T) = conj c • cjEquiv K K T := by
  simp only [cjEquiv_apply]; exact cjT_smul K K c T

theorem circleIntegral_neg' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (F : ℂ → E) (c : ℂ) (r : ℝ) :
    circleIntegral (fun z => -(F z)) c r = -circleIntegral F c r := by
  unfold circleIntegral
  simp [intervalIntegral.integral_neg]

/-- `∮_{C(-conj c, r)} (z - Γ)⁻¹ dz = - K (∮_{C(c, r)} (z - Γ)⁻¹ dz) K`. -/
theorem riesz_transportA (h : InterA G G' K) (c : ℂ) (r : ℝ) :
    circleIntegral (fun z => res G' z) (-(conj c)) r =
      -(cjT K K (circleIntegral (fun z => res G z) c r)) := by
  have e1 : (fun z => res G' z) = fun z' => -(cjEquiv K K (res G (-(conj z')))) := by
    funext z'; rw [res_transportA' h z']; rfl
  rw [e1, circleIntegral_neg', circle_conj (cjEquiv K K) (fun c x => cjEquiv_smul c x) (fun w => res G w) c r]
  rfl

/-- The dressed integral `∮ (z - p)(z - Γ)⁻¹ dz` with `p = c`, `p' = -conj c`. -/
theorem dressed_transportA (h : InterA G G' K) (c : ℂ) (r : ℝ) :
    circleIntegral (fun z => (z - (-(conj c))) • res G' z) (-(conj c)) r =
      cjT K K (circleIntegral (fun z => (z - c) • res G z) c r) := by
  have e1 : (fun z => (z - (-(conj c))) • res G' z) =
      fun z' => cjEquiv K K ((fun w => (w - c) • res G w) (-(conj z'))) := by
    funext z'
    show (z' - -(conj c)) • res G' z' = cjEquiv K K ((-(conj z') - c) • res G (-(conj z')))
    rw [res_transportA' h z', cjEquiv_smul, cjEquiv_apply, map_sub, map_neg, Complex.conj_conj, smul_neg,
      ← neg_smul]
    congr 1; ring
  rw [e1]
  exact circle_conj (cjEquiv K K) (fun c x => cjEquiv_smul c x) (fun w => (w - c) • res G w) c r

end Contour


/-! ### The reduction pipeline under conjugation -/

section Pipe

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (KH : AntiU H) (KK : AntiU K)

theorem cjT_one {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] (KX : AntiU X) :
    cjT KX KX (1 : X →L[ℂ] X) = 1 := cjT_id KX

theorem cjT_mul {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] (KX : AntiU X)
    (S T : X →L[ℂ] X) : cjT KX KX (S * T) = cjT KX KX S * cjT KX KX T := cjT_comp KX KX KX S T

theorem cjT_pow {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] (KX : AntiU X)
    (T : X →L[ℂ] X) (k : ℕ) : cjT KX KX (T ^ k) = (cjT KX KX T) ^ k := by
  induction k with
  | zero => simpa using cjT_one KX
  | succ k ih => rw [pow_succ, cjT_mul, ih, pow_succ]

theorem cjT_isqs {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    (KX : AntiU X) (cf : ℕ → ℂ) (hcf : ∀ k, conj (cf k) = cf k) (T : X →L[ℂ] X) :
    cjT KX KX (isqs cf T) = isqs cf (cjT KX KX T) := by
  unfold isqs
  rw [cjT_tsum]
  refine tsum_congr fun k => ?_
  rw [cjT_smul, hcf, cjT_pow, cjT_sub, cjT_one]

variable (cf : ℕ → ℂ)
  (P D : H →L[ℂ] H) (E E' : K →L[ℂ] H)

theorem cmpM_transportA (hE : E' = cjT KK KH E) :
    cmpM (cjT KH KH P) E' = cjT KK KK (cmpM P E) := by
  unfold cmpM
  rw [cjT_comp KK KH KK, cjT_comp KK KH KH, hE, adjoint_cjT]

theorem isoU_transportA (hcf : ∀ k, conj (cf k) = cf k) (hE : E' = cjT KK KH E) :
    isoU cf (cjT KH KH P) E' = cjT KK KH (isoU cf P E) := by
  have hc : isqs cf (cmpM (cjT KH KH P) E') = cjT KK KK (isqs cf (cmpM P E)) := by
    rw [cmpM_transportA KH KK P E E' hE, cjT_isqs KK cf hcf]
  unfold isoU
  rw [hc, hE, cjT_comp KK KH KH, cjT_comp KK KK KH]

theorem redM_transportA (hcf : ∀ k, conj (cf k) = cf k) (p p' : ℂ) (hE : E' = cjT KK KH E) :
    redM cf p' (cjT KH KH P) (-(cjT KH KH D)) E' =
      p' • ContinuousLinearMap.id ℂ K - cjT KK KK (redM cf p P D E - p • ContinuousLinearMap.id ℂ K) := by
  have hU := isoU_transportA KH KK cf P E E' hcf hE
  unfold redM
  rw [hU, adjoint_cjT, add_sub_cancel_left, cjT_comp KK KH KK, cjT_comp KK KH KH]
  ext x
  simp [ContinuousLinearMap.comp_apply, sub_eq_add_neg]

end Pipe


#print axioms QuantumNLS.Local020AbsA.res_transportA
#print axioms QuantumNLS.Local020AbsA.riesz_transportA
#print axioms QuantumNLS.Local020AbsA.dressed_transportA
#print axioms QuantumNLS.Local020AbsA.cmpM_transportA
#print axioms QuantumNLS.Local020AbsA.isoU_transportA
#print axioms QuantumNLS.Local020AbsA.redM_transportA
#print axioms QuantumNLS.Local020AbsA.circle_conj
end QuantumNLS.Local020AbsA
