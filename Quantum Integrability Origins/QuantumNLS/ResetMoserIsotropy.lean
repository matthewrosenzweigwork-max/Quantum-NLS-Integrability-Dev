import QuantumNLS.ResetMoserHyp

/-!
# `thm:reset-moser` (LOCAL-017), stage 1b: isotropy of every coordinate torus

Source: `symplectic_correction.tex`, "Isotropy of every coordinate torus": "At a point for which every `z_j`, `j ∈ F`, is nonzero, the differentials `dq_j` on `ℋ_F` are linearly independent. Their Hamiltonian fields are linearly independent, lie in the tangent space of the torus with these prescribed coordinate moduli, and have zero mutual `Ω` pairings. There are `|F|` of them, exactly the real dimension of that torus. Consequently the torus is isotropic for `Ω`. ... For an arbitrary `z ∈ ℋ`, truncate `z` to increasing finite sets ... Continuity of `Ω` and the preceding identity show that it vanishes on pairs of finitely supported vectors of the form `(i a_n z_n)_n` with real `a_n`. By boundedness it vanishes on the closed real subspace `𝒯_z`."

* `isotropy_finite`: for `w ∈ B_R` with finite support, `Ω_w` vanishes on `𝒯_w × 𝒯_w`. The fields `X_j(w) ∈ 𝒯_w` (`Hyp.Xn_mem_Tz`) form, in the basis `e_m = i w_m e_m` of `𝒯_w`, a matrix `M` whose transpose is injective (the `dq_j(w)` are independent); `Σ_m M_{jm} Ω(e_m, e_k) = Ω(X_j, e_k) = dq_j(e_k) = 0` gives `Ω(e_m, e_k) = 0`.
* `trunc`, `trunc_tendsto`: coordinate truncation, convergence from `lp.hasSum_single`.
* `isotropy`: for every `z ∈ B_R`, `Ω_z` vanishes on `𝒯_z × 𝒯_z`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology ENNReal
open Filter Set Metric

namespace QuantumNLS.ResetMoser

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.RealAnalyticDef

/-! ## 1. The finitely supported case -/

/-- The basis vector `e_m = i w_m e_m` of `𝒯_w`. -/
def eT (w : K) (m : ℤ) : K := Complex.I • (lp.single (E := fun _ : ℤ => ℂ) 2 m (w m) : K)

theorem eT_apply (w : K) (m n : ℤ) : eT w m n = if n = m then Complex.I * w m else 0 := by
  have h : eT w m n = Complex.I * (lp.single (E := fun _ : ℤ => ℂ) 2 m (w m) : K) n := rfl
  rw [h, lp.single_apply, Pi.single_apply]
  by_cases hnm : n = m
  · subst hnm; simp
  · simp [hnm]

theorem rsmul_apply (r : ℝ) (x : K) (n : ℤ) : (r • x) n = (r : ℂ) * x n := by
  rw [lp.coeFn_smul, Pi.smul_apply, Complex.real_smul]

theorem eT_mem (w : K) (m : ℤ) : eT w m ∈ Tz w := by
  intro n
  by_cases h : n = m
  · refine ⟨1, ?_⟩; rw [eT_apply, if_pos h]; subst h; simp
  · refine ⟨0, ?_⟩; rw [eT_apply, if_neg h]; simp

theorem Tz_sum {w : K} (T : Finset ℤ) (hT : ∀ n, w n ≠ 0 → n ∈ T) {h : K} (hh : h ∈ Tz w) :
    ∃ a : ℤ → ℝ, (∀ n, h n = Complex.I * w n * a n) ∧ h = ∑ m ∈ T, a m • eT w m := by
  choose a ha using hh
  refine ⟨a, ha, ?_⟩
  ext n
  have hs : (∑ m ∈ T, a m • eT w m) n = ∑ m ∈ T, ((a m : ℂ) * eT w m n) := by
    rw [lp.coeFn_sum]
    simp only [Finset.sum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    exact rsmul_apply _ _ _
  rw [hs]
  simp_rw [eT_apply]
  by_cases hn : n ∈ T
  · rw [Finset.sum_eq_single n]
    · rw [if_pos rfl, ha n]; ring
    · intro m _ hm; rw [if_neg (Ne.symm hm)]; simp
    · intro h'; exact absurd hn h'
  · have hw : w n = 0 := by
      by_contra hne; exact hn (hT n hne)
    rw [ha n, hw]
    rw [Finset.sum_eq_zero]
    · simp
    · intro m hm
      have : n ≠ m := fun e => hn (e ▸ hm)
      rw [if_neg this]; simp

theorem isotropy_finite (S : Hyp) {w : K} (hw : w ∈ ball (0 : K) S.R) (hfin : {n | w n ≠ 0}.Finite) :
    ∀ h ∈ Tz w, ∀ h' ∈ Tz w, S.Ω w h h' = 0 := by
  classical
  set T : Finset ℤ := hfin.toFinset with hTdef
  have hT : ∀ n, w n ≠ 0 → n ∈ T := fun n hn => by simp [hTdef, hn]
  -- the key claim: `Ω_w(e_m, e_k) = 0`
  have key : ∀ m ∈ T, ∀ k ∈ T, S.Ω w (eT w m) (eT w k) = 0 := by
    have hX : ∀ j : ℤ, ∃ a : ℤ → ℝ, (∀ n, (Xn S.Ω j w) n = Complex.I * w n * a n) ∧
        Xn S.Ω j w = ∑ m ∈ T, a m • eT w m := fun j => Tz_sum T hT (S.Xn_mem_Tz hw j)
    choose aX haX1 haX2 using hX
    let M : Matrix T T ℝ := fun j m => aX (j : ℤ) (m : ℤ)
    -- the kernel of `Mᵀ` is trivial
    have hker : ∀ c : T → ℝ, M.transpose.mulVec c = 0 → c = 0 := by
      intro c hc
      have hcm : ∀ m : T, ∑ j : T, M j m * c j = 0 := fun m => by
        have := congrFun hc m
        simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply] using this
      -- `Σ_j c_j X_j = 0`
      have hsum : ∑ j : T, c j • Xn S.Ω (j : ℤ) w = 0 := by
        ext n
        rw [lp.coeFn_sum]
        simp only [Finset.sum_apply]
        have hl : ∀ j : T, (c j • Xn S.Ω (j : ℤ) w) n = ((c j : ℝ) : ℂ) * (Complex.I * w n * aX (j : ℤ) n) := by
          intro j
          rw [rsmul_apply, haX1]
        simp_rw [hl]
        by_cases hn : n ∈ T
        · have := hcm ⟨n, hn⟩
          have h2 : ∑ j : T, ((c j : ℝ) : ℂ) * (Complex.I * w n * aX (j : ℤ) n) =
              Complex.I * w n * ((∑ j : T, M j ⟨n, hn⟩ * c j : ℝ) : ℂ) := by
            push_cast
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            simp only [M]
            ring
          rw [h2, this]; simp
        · have hw0 : w n = 0 := by by_contra hne; exact hn (hT n hne)
          simp [hw0]
      funext k
      by_contra hck
      have hk := k.2
      have hwk : w k ≠ 0 := (Set.Finite.mem_toFinset hfin).1 hk
      set hk' : K := lp.single (E := fun _ : ℤ => ℂ) 2 (k : ℤ) (w k) with hhk
      have h0 : ∑ j : T, c j * fderiv ℝ (q (j : ℤ)) w hk' = 0 := by
        have := congrArg (fun v => S.Ω w v hk') hsum
        simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul, ContinuousLinearMap.smul_apply,
          smul_eq_mul, ContinuousLinearMap.zero_apply, map_zero] at this
        rw [← this]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Xn_spec (S.Ω_lt w hw)]
      have h3 : ∀ j : T, c j * fderiv ℝ (q (j : ℤ)) w hk' = if j = k then c k * (2 * ‖w k‖ ^ 2) else 0 := by
        intro j
        rw [fderiv_q_apply]
        have : (hk' : ℤ → ℂ) (j : ℤ) = if (j : ℤ) = (k : ℤ) then w k else 0 := by
          show (lp.single (E := fun _ : ℤ => ℂ) 2 (k : ℤ) (w k) : K) (j : ℤ) = _
          rw [lp.single_apply, Pi.single_apply]
        rw [this]
        by_cases hjk : j = k
        · subst hjk
          simp [Complex.conj_mul', ← Complex.ofReal_pow]
        · have : (j : ℤ) ≠ (k : ℤ) := fun e => hjk (Subtype.ext e)
          simp [this, hjk]
      simp_rw [h3] at h0
      rw [Finset.sum_ite_eq' Finset.univ k] at h0
      simp at h0
      have hpos : 0 < ‖w k‖ ^ 2 := by positivity
      rcases h0 with h0 | h0
      · exact hck (by simpa using h0)
      · exact hwk h0
    have hinj : Function.Injective M.transpose.mulVec := by
      refine (injective_iff_map_eq_zero (Matrix.mulVecLin M.transpose)).2 fun c hc => hker c ?_
      rw [Matrix.mulVecLin_apply] at hc
      exact hc
    have hU1 : IsUnit M.transpose := Matrix.mulVec_injective_iff_isUnit.1 hinj
    have hU2 : IsUnit M := by
      rw [Matrix.isUnit_iff_isUnit_det] at hU1 ⊢
      rwa [Matrix.det_transpose] at hU1
    have hMinj : Function.Injective M.mulVec := Matrix.mulVec_injective_iff_isUnit.2 hU2
    intro m hm k hk
    have hv : M.mulVec (fun m' : T => S.Ω w (eT w (m' : ℤ)) (eT w k)) = 0 := by
      funext j
      have h1 : Xn S.Ω (j : ℤ) w = ∑ m' : T, aX (j : ℤ) (m' : ℤ) • eT w (m' : ℤ) := by
        rw [haX2 (j : ℤ)]
        exact (Finset.sum_coe_sort T (fun m' => aX (j : ℤ) m' • eT w m')).symm
      have h2 : S.Ω w (Xn S.Ω (j : ℤ) w) (eT w k) = 0 := by
        rw [Xn_spec (S.Ω_lt w hw), dq_Tz (eT_mem w k)]
      rw [h1] at h2
      simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul, ContinuousLinearMap.smul_apply,
        smul_eq_mul] at h2
      simpa [Matrix.mulVec, dotProduct, M] using h2
    have := hMinj (hv.trans (Matrix.mulVec_zero M).symm)
    exact congrFun this ⟨m, hm⟩
  intro h hh h' hh'
  obtain ⟨a, ha1, ha2⟩ := Tz_sum T hT hh
  obtain ⟨b, hb1, hb2⟩ := Tz_sum T hT hh'
  rw [ha2, hb2]
  simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  refine Finset.sum_eq_zero fun m hm => ?_
  have h0 : ∑ x ∈ T, a x * (S.Ω w (eT w x)) (eT w m) = 0 :=
    Finset.sum_eq_zero fun x hx => by rw [key x hx m hm]; ring
  rw [h0, mul_zero]

/-! ## 2. Truncation and the general case -/

/-- Coordinate truncation `v ↦ Σ_{i ∈ F} v_i e_i`. -/
def trunc (F : Finset ℤ) (v : K) : K := ∑ i ∈ F, lp.single 2 i (v i)

theorem trunc_apply (F : Finset ℤ) (v : K) (n : ℤ) : trunc F v n = if n ∈ F then v n else 0 := by
  unfold trunc
  rw [lp.coeFn_sum]
  simp only [Finset.sum_apply, lp.single_apply, Pi.single_apply]
  rw [Finset.sum_ite_eq]

theorem trunc_tendsto (v : K) : Tendsto (fun F : Finset ℤ => trunc F v) atTop (𝓝 v) :=
  lp.hasSum_single (p := 2) (by simp) v

theorem trunc_mem_Tz {z h : K} (F : Finset ℤ) (hh : h ∈ Tz z) : trunc F h ∈ Tz (trunc F z) := by
  intro n
  obtain ⟨a, ha⟩ := hh n
  rw [trunc_apply, trunc_apply]
  by_cases hn : n ∈ F
  · refine ⟨a, ?_⟩; simp [hn, ha]
  · refine ⟨0, ?_⟩; simp [hn]

theorem trunc_finite (F : Finset ℤ) (z : K) : {n | trunc F z n ≠ 0}.Finite := by
  refine F.finite_toSet.subset fun n hn => ?_
  by_contra h
  apply hn
  have h' : n ∉ F := by simpa using h
  simp [trunc_apply, h']

/-- **Isotropy of every coordinate torus**: `Ω_z` vanishes on `𝒯_z × 𝒯_z` for every `z ∈ B_R`. -/
theorem isotropy (S : Hyp) {z : K} (hz : z ∈ ball (0 : K) S.R) :
    ∀ h ∈ Tz z, ∀ h' ∈ Tz z, S.Ω z h h' = 0 := by
  intro h hh h' hh'
  have hev : ∀ᶠ F : Finset ℤ in atTop, trunc F z ∈ ball (0 : K) S.R :=
    (trunc_tendsto z).eventually (isOpen_ball.mem_nhds hz)
  have h1 : Tendsto (fun F : Finset ℤ => S.Ω (trunc F z)) atTop (𝓝 (S.Ω z)) :=
    (S.Ω_continuousOn.continuousAt (isOpen_ball.mem_nhds hz)).tendsto.comp (trunc_tendsto z)
  have h2 : Tendsto (fun F : Finset ℤ => S.Ω (trunc F z) (trunc F h)) atTop (𝓝 (S.Ω z h)) :=
    ((isBoundedBilinearMap_apply (𝕜 := ℝ) (E := K) (F := Cov)).continuous.tendsto
      (S.Ω z, h)).comp (h1.prodMk_nhds (trunc_tendsto h))
  have hlim : Tendsto (fun F : Finset ℤ => S.Ω (trunc F z) (trunc F h) (trunc F h')) atTop
      (𝓝 (S.Ω z h h')) :=
    ((isBoundedBilinearMap_apply (𝕜 := ℝ) (E := K) (F := ℝ)).continuous.tendsto
      (S.Ω z h, h')).comp (h2.prodMk_nhds (trunc_tendsto h'))
  have hzero : ∀ᶠ F : Finset ℤ in atTop, S.Ω (trunc F z) (trunc F h) (trunc F h') = 0 :=
    hev.mono fun F hF => isotropy_finite S hF (trunc_finite F z) _ (trunc_mem_Tz F hh) _
      (trunc_mem_Tz F hh')
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hzero.mono fun F hF => hF.symm))

end QuantumNLS.ResetMoser

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoser.isotropy_finite
#print axioms QuantumNLS.ResetMoser.trunc_tendsto
#print axioms QuantumNLS.ResetMoser.isotropy
