import NlsGge.GK38.GradEigenKernels

/-! K2: actual state components are absolutely continuous and satisfy the
coefficient ODE almost everywhere, for arbitrary complex L² pairs and seeds. -/
set_option autoImplicit false
open Set Filter Topology MeasureTheory
namespace NlsGge.GK38.GradEigen38
noncomputable section

theorem state_ext (φ : PotPair) (z : ℂ) (a : PairVec38) (s : ℝ) (i : Fin 2) :
    pairKernelExt38 (state φ z a) s i =
      a 0 * ext38 (fundContP φ z) s i 0 +
        a 1 * ext38 (fundContP φ z) s i 1 := by
  let t : Time := projIcc 0 1 zero_le_one s
  have he : ext38 (fundContP φ z) (t : ℝ) = ext38 (fundContP φ z) s := by
    rw [ext38_of_mem _ t.2]
    rfl
  have hf : fundPair φ z t = ext38 (fundContP φ z) s := by
    rw [fundPair_eq, ← he, ext38_of_mem _ t.2]
    rfl
  change state φ z a t i = _
  rw [state_eq_mulVec, hf]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem ac_state_component (φ : PotPair) (z : ℂ) (a : PairVec38) (i : Fin 2) :
    AbsolutelyContinuousOnInterval
      (fun s => pairKernelExt38 (state φ z a) s i) 0 1 := by
  have h := ((ac_fundContP_entry38 φ z i 0).const_smul (a 0)).add
    ((ac_fundContP_entry38 φ z i 1).const_smul (a 1))
  exact h.congr (fun s _ => by simpa only [Pi.add_apply, smul_eq_mul] using
    (state_ext φ z a s i).symm)

theorem ae_hasDerivAt_state_component (φ : PotPair) (z : ℂ)
    (a : PairVec38) (i : Fin 2) :
    ∀ᵐ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      HasDerivAt (fun r => pairKernelExt38 (state φ z a) r i)
        (Matrix.mulVec (zsCoeffPot38 φ z s)
          (pairKernelExt38 (state φ z a) s) i) s := by
  filter_upwards [ae_hasDerivAt_fundContP_entry38 φ z i 0,
    ae_hasDerivAt_fundContP_entry38 φ z i 1] with s h0 h1 hs
  have hd := ((h0 hs).const_mul (a 0)).add ((h1 hs).const_mul (a 1))
  have he : (fun r => pairKernelExt38 (state φ z a) r i) =
      (fun r => a 0 * ext38 (fundContP φ z) r i 0 +
        a 1 * ext38 (fundContP φ z) r i 1) := by
    funext r
    exact state_ext φ z a r i
  rw [he]
  apply hd.congr_deriv
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    state_ext]
  ring

theorem state_ODE (φ : PotPair) (z : ℂ) (a : PairVec38) :
    state φ z a t0 = a ∧ ∀ i : Fin 2,
      AbsolutelyContinuousOnInterval
        (fun s => pairKernelExt38 (state φ z a) s i) 0 1 ∧
      ∀ᵐ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
        HasDerivAt (fun r => pairKernelExt38 (state φ z a) r i)
          (Matrix.mulVec (zsCoeffPot38 φ z s)
            (pairKernelExt38 (state φ z a) s) i) s :=
  ⟨state_initial φ z a, fun i =>
    ⟨ac_state_component φ z a i, ae_hasDerivAt_state_component φ z a i⟩⟩

theorem ae_hasDerivAt_state_component_restrict (φ : PotPair) (z : ℂ)
    (a : PairVec38) (i : Fin 2) :
    ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      HasDerivAt (fun r => pairKernelExt38 (state φ z a) r i)
        (Matrix.mulVec (zsCoeffPot38 φ z s)
          (pairKernelExt38 (state φ z a) s) i) s :=
  (ae_restrict_iff' measurableSet_Icc).2
    (ae_hasDerivAt_state_component φ z a i)

theorem state_ODE_restrict (φ : PotPair) (z : ℂ) (a : PairVec38) :
    state φ z a t0 = a ∧ ∀ i : Fin 2,
      AbsolutelyContinuousOnInterval
        (fun s => pairKernelExt38 (state φ z a) s i) 0 1 ∧
      ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
        HasDerivAt (fun r => pairKernelExt38 (state φ z a) r i)
          (Matrix.mulVec (zsCoeffPot38 φ z s)
            (pairKernelExt38 (state φ z a) s) i) s :=
  ⟨state_initial φ z a, fun i =>
    ⟨ac_state_component φ z a i, ae_hasDerivAt_state_component_restrict φ z a i⟩⟩

end
end NlsGge.GK38.GradEigen38
