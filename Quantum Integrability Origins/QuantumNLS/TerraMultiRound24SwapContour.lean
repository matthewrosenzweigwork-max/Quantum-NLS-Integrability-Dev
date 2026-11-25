import QuantumNLS.TerraMultiRound24ParityContour

/-! Conjugate-orientation transport for operator-valued contour integrals. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ComplexConjugate
namespace QuantumNLS.LocalSpectral.Round24

/-- Reflection of the positive contour parameter conjugates its point. -/
theorem circle_reflect (a r θ : ℝ) :
    circleMap (a : ℂ) r (2 * Real.pi - θ) = conj (circleMap (a : ℂ) r θ) := by
  have hp := periodic_circleMap (a : ℂ) r (-θ)
  simpa [conj_circleMap, add_comm, sub_eq_add_neg] using hp

/-- The contour tangent picks up the minus sign from orientation reversal. -/
theorem tangent_reflect (a r θ : ℝ) :
    conj (deriv (circleMap (a : ℂ) r) (2 * Real.pi - θ)) =
      -deriv (circleMap (a : ℂ) r) θ := by
  simp only [deriv_circleMap, map_mul, Complex.conj_I]
  have h := circle_reflect 0 r θ
  change circleMap (0 : ℂ) r (2 * Real.pi - θ) = conj (circleMap 0 r θ) at h
  rw [h]
  simp

/-- The unnormalized contour integral picks up the orientation sign under
an anti-linear intertwiner. -/
theorem circle_swap_raw {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H] (J : H →L[ℝ] H)
    (hJ : ∀ z : ℂ, ∀ x : H, J (z • x) = conj z • J x)
    (F G : ℂ → H →L[ℂ] H) (a r : ℝ) (hr : 0 ≤ r)
    (hF : CircleIntegrable F (a : ℂ) r) (hG : CircleIntegrable G (a : ℂ) r)
    (h : ∀ z ∈ Metric.sphere (a : ℂ) r, ∀ x, G z (J x) = J (F (conj z) x))
    (x : H) :
    (circleIntegral G (a : ℂ) r) (J x) = - J ((circleIntegral F (a : ℂ) r) x) := by
  unfold circleIntegral
  rw [ContinuousLinearMap.intervalIntegral_apply hG.out,
    ContinuousLinearMap.intervalIntegral_apply hF.out]
  have hFi : IntervalIntegrable (fun t : ℝ =>
      (deriv (circleMap (a : ℂ) r) t • F (circleMap (a : ℂ) r t)) x)
      volume 0 (2 * Real.pi) :=
    ⟨hF.out.1.apply_continuousLinearMap x, hF.out.2.apply_continuousLinearMap x⟩
  calc
    _ = ∫ t : ℝ in 0..2 * Real.pi,
        -J ((deriv (circleMap (a : ℂ) r) (2 * Real.pi - t) •
          F (circleMap (a : ℂ) r (2 * Real.pi - t))) x) := by
      apply intervalIntegral.integral_congr
      intro t ht
      simp only [smul_apply]
      rw [h _ (circleMap_mem_sphere _ hr t) x, hJ, tangent_reflect, circle_reflect]
      simp
    _ = -(∫ t : ℝ in 0..2 * Real.pi,
        J ((deriv (circleMap (a : ℂ) r) (2 * Real.pi - t) •
          F (circleMap (a : ℂ) r (2 * Real.pi - t))) x)) := by
      rw [intervalIntegral.integral_neg]
    _ = -(∫ t : ℝ in 0..2 * Real.pi,
        J ((deriv (circleMap (a : ℂ) r) t • F (circleMap (a : ℂ) r t)) x)) := by
      have hp := intervalIntegral.integral_comp_sub_left
        (a := (0 : ℝ)) (b := 2 * Real.pi)
        (fun t : ℝ => J ((deriv (circleMap (a : ℂ) r) t •
          F (circleMap (a : ℂ) r t)) x)) (2 * Real.pi)
      simpa using congrArg Neg.neg hp
    _ = _ := by rw [J.intervalIntegral_comp_comm hFi]

/-- The normalizing factor cancels the orientation sign. -/
theorem circle_swap_normalized {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H] (J : H →L[ℝ] H)
    (hJ : ∀ z : ℂ, ∀ x : H, J (z • x) = conj z • J x)
    (F G : ℂ → H →L[ℂ] H) (a r : ℝ) (hr : 0 ≤ r)
    (hF : CircleIntegrable F (a : ℂ) r) (hG : CircleIntegrable G (a : ℂ) r)
    (h : ∀ z ∈ Metric.sphere (a : ℂ) r, ∀ x, G z (J x) = J (F (conj z) x))
    (x : H) :
    (((2 * Real.pi * Complex.I)⁻¹ : ℂ) • circleIntegral G (a : ℂ) r) (J x) =
      J ((((2 * Real.pi * Complex.I)⁻¹ : ℂ) • circleIntegral F (a : ℂ) r) x) := by
  simp only [smul_apply, hJ, circle_swap_raw J hJ F G a r hr hF hG h x]
  have hc : conj (((2 * Real.pi * Complex.I)⁻¹ : ℂ)) =
      -(((2 * Real.pi * Complex.I)⁻¹ : ℂ)) := by simp [map_ofNat]
  rw [hc]
  simp

/-- Swap-conjugation lifted to the interval Hilbert space, viewed as a real
bounded map. -/
def swapOp (L : ℝ) : H2 L →L[ℝ] H2 L :=
  Round23.swapConjIsometry.toContinuousLinearMap.compLpL 2 (μI L)

/-- The actual Riesz projection commutes with swap-conjugation when both
conjugate contour resolvents exist and their operator-valued function is
circle integrable. -/
theorem riesz_swap (L κ : ℝ) (u : ℝ → ℂ) (σ : ℤˣ) (n : ℤ) (r : ℝ)
    (hr : 0 ≤ r)
    (hR : ∀ z ∈ Metric.sphere (center L n) r,
      (∃ R, IsResolvent L κ u σ z R) ∧
      (∃ S, IsResolvent L κ u σ (conj z) S))
    (hF : CircleIntegrable (fun z => resolvent L κ u σ z) (center L n) r)
    (x : H2 L) :
    rieszProj L κ u σ n r (swapOp L x) = swapOp L (rieszProj L κ u σ n r x) := by
  unfold rieszProj center at *
  refine circle_swap_normalized (swapOp L) (fun z v => ?_) _ _ _ r hr hF hF ?_ x
  · exact Round23.liftFiber_swap_smul L z v
  · intro z hz v
    obtain ⟨⟨R, hRz⟩, ⟨S, hSz⟩⟩ := hR z hz
    rw [QuantumNLS.Local002.resolvent_eq hRz, QuantumNLS.Local002.resolvent_eq hSz]
    exact Round23.resolvent_swap_intertwines L κ u σ (conj z) S R hSz (by simpa using hRz) v

/-- Swap-conjugation also commutes with the dressed contour integral. -/
theorem dressed_swap (L κ : ℝ) (u : ℝ → ℂ) (n : ℤ) (r : ℝ)
    (hr : 0 ≤ r)
    (hR : ∀ z ∈ Metric.sphere (center L n) r,
      (∃ R, IsResolvent L κ u (parity n) z R) ∧
      (∃ S, IsResolvent L κ u (parity n) (conj z) S))
    (hF : CircleIntegrable (fun z => resolvent L κ u (parity n) z) (center L n) r)
    (x : H2 L) :
    dressedIntegral L κ u n r (swapOp L x) = swapOp L (dressedIntegral L κ u n r x) := by
  unfold dressedIntegral center at *
  refine circle_swap_normalized (swapOp L)
    (fun z v => Round23.liftFiber_swap_smul L z v) _ _ _ r hr
    (hF.fun_continuousOn_smul (continuousOn_id.sub continuousOn_const))
    (hF.fun_continuousOn_smul (continuousOn_id.sub continuousOn_const)) ?_ x
  intro z hz v
  simp only [smul_apply]
  obtain ⟨⟨R, hRz⟩, ⟨S, hSz⟩⟩ := hR z hz
  rw [QuantumNLS.Local002.resolvent_eq hRz, QuantumNLS.Local002.resolvent_eq hSz]
  have hh := Round23.resolvent_swap_intertwines L κ u (parity n) (conj z) S R hSz
    (by simpa using hRz) v
  change (z - (pm L n : ℂ)) • R (Round23.liftFiber L Round23.swapConjIsometry v) =
    Round23.liftFiber L Round23.swapConjIsometry ((conj z - (pm L n : ℂ)) • S v)
  rw [hh, Round23.liftFiber_swap_smul]
  simp


end QuantumNLS.LocalSpectral.Round24
#print axioms QuantumNLS.LocalSpectral.Round24.circle_reflect
#print axioms QuantumNLS.LocalSpectral.Round24.tangent_reflect
#print axioms QuantumNLS.LocalSpectral.Round24.circle_swap_raw
#print axioms QuantumNLS.LocalSpectral.Round24.circle_swap_normalized
#print axioms QuantumNLS.LocalSpectral.Round24.swapOp
#print axioms QuantumNLS.LocalSpectral.Round24.riesz_swap
#print axioms QuantumNLS.LocalSpectral.Round24.dressed_swap
