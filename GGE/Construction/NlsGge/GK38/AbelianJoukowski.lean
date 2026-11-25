import NlsGge.GK38.StdRootBranchesSlit

/-! Scalar branch-selected Joukowski prerequisites for the genuine P2 root average.
UNCOMPILED prospective proof source; no contour identity is assumed. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

/-- Slit membership earns STRICT positivity, beyond global nonnegativity. -/
theorem p2Sqrt_re_pos38 (r : ℂ) (hr : r ∈ Complex.slitPlane) :
    0 < (Complex.sqrt r).re := by
  have hn := Lib.re_sqrt_nonneg r
  by_contra hp
  have he : (Complex.sqrt r).re = 0 := le_antisymm (not_lt.mp hp) hn
  have hs := Lib.sqrt_sq r
  have hre := congrArg Complex.re hs
  have him := congrArg Complex.im hs
  simp only [pow_two,Complex.mul_re,he,zero_mul] at hre
  simp only [pow_two,Complex.mul_im,he,zero_mul,mul_zero,zero_add] at him
  rcases Complex.mem_slitPlane_iff.mp hr with hrp | hri
  · nlinarith [sq_nonneg (Complex.sqrt r).im]
  · exact hri him.symm

/-- This inequality is what selects the outside Joukowski pole. -/
theorem p2Norm_one_sub_lt_one_add38 (q : ℂ) (hq : 0 < q.re) :
    ‖1-q‖ < ‖1+q‖ := by
  have hm : ‖1-q‖^2=(1-q.re)^2+q.im^2 := by
    simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.one_re,
      Complex.sub_im,Complex.one_im,zero_sub]
    ring
  have hp : ‖1+q‖^2=(1+q.re)^2+q.im^2 := by
    simp only [Complex.sq_norm,Complex.normSq_apply,Complex.add_re,Complex.one_re,
      Complex.add_im,Complex.one_im,zero_add]
    ring
  nlinarith [norm_nonneg (1-q),norm_nonneg (1+q)]

/-- Pure algebra: the selected q gives a pole strictly outside the unit disc.
The hypotheses describe the actual off-cut branch; their realization is a separate next lemma. -/
theorem p2Joukowski_outside38 (w d q : ℂ) (hw : w ≠ 0) (hd : d ≠ 0)
    (hq : q^2=1-d^2/w^2) (hqr : 0 < q.re) :
    1 < ‖-w*(1+q)/d‖ := by
  let u : ℂ := -w*(1+q)/d
  have he : u^2*(1-q)=1+q := by
    dsimp [u]
    field_simp [hw,hd] at hq ⊢
    linear_combination -(1+q)*hq
  have hn := congrArg norm he
  simp only [norm_mul,norm_pow] at hn
  have hlt := p2Norm_one_sub_lt_one_add38 q hqr
  have hnon := norm_nonneg (1-q)
  have hu := norm_nonneg u
  change 1 < ‖u‖
  by_contra hnot
  have hu1 : ‖u‖ ≤ 1 := not_lt.mp hnot
  have hs : ‖u‖^2 ≤ 1 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hs hnon
  rw [one_mul] at hm
  nlinarith

/-- Exact partial fractions on the unit circle, with every inverse nonzero.
No integral identity is used here. -/
theorem p2Joukowski_partial_fractions38 (A R d u v : ℂ)
    (hA : A=(d/2)*(u+u⁻¹)) (hR : R=(d/2)*(u⁻¹-u))
    (hd : d ≠ 0) (hu : u ≠ 0) (hRn : R ≠ 0) (hv : v ≠ 0)
    (hvu : v-u ≠ 0) (hvui : v-u⁻¹ ≠ 0)
    (hden : A-(d/2)*(v+v⁻¹) ≠ 0) :
    1/(Complex.I*v*(A-(d/2)*(v+v⁻¹))) =
      (Complex.I/R)*(1/(v-u⁻¹)-1/(v-u)) := by
  have hfact : A-(d/2)*(v+v⁻¹) =
      -(d/(2*v))*(v-u)*(v-u⁻¹) := by
    rw [hA]
    field_simp [hu,hv]
    ring
  have hvden : v*(A-(d/2)*(v+v⁻¹)) = -(d/2)*(v-u)*(v-u⁻¹) := by
    rw [hfact]
    field_simp [hu,hv]
  rw [div_sub_div 1 1 hvui hvu]
  simp only [one_mul,mul_one]
  have hnum : (v-u)-(v-u⁻¹)=u⁻¹-u := by ring
  rw [hnum,div_mul_div_comm]
  apply (div_eq_div_iff (mul_ne_zero (mul_ne_zero Complex.I_ne_zero hv) hden)
    (mul_ne_zero hRn (mul_ne_zero hvui hvu))).mpr
  calc
    1*(R*((v-u⁻¹)*(v-u))) = (d/2)*(u⁻¹-u)*((v-u)*(v-u⁻¹)) := by
      rw [hR]
      ring
    _ = -(u⁻¹-u)*(v*(A-(d/2)*(v+v⁻¹))) := by
      rw [hvden]
      ring
    _ = (Complex.I*(u⁻¹-u))*(Complex.I*v*(A-(d/2)*(v+v⁻¹))) := by
      ring_nf
      simp [Complex.I_sq]
      ring

#print axioms p2Sqrt_re_pos38
#print axioms p2Norm_one_sub_lt_one_add38
#print axioms p2Joukowski_outside38
#print axioms p2Joukowski_partial_fractions38
end
end NlsGge.GK38
