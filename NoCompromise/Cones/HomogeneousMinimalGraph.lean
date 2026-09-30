module

public import NoCompromise.Stationary.BootstrapC2
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Trace

@[expose] public section

/-! A homogeneous minimal graph in two variables has vanishing Hessian. -/

noncomputable section

open Filter InnerProductSpace
open scoped Topology RealInnerProductSpace

namespace LiquidDrop

/-- Differentiating local degree-one homogeneity gives Euler's identity. -/
theorem homogeneous_graph_euler {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : ContDiffOn ℝ 2 f U)
    {v : EuclideanSpace ℝ (Fin 2)}
    (hhom : ∀ x ∈ U, ∀ᶠ l in nhds (1 : ℝ), f (v + l • (x - v)) = l * f x)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ U) :
    fderiv ℝ f x (x - v) = f x := by
  have hd := ((hf x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt two_ne_zero
  have hr : HasDerivAt (fun l : ℝ => v + l • (x - v)) (x - v) 1 := by
    simpa using ((hasDerivAt_id (1 : ℝ)).smul_const (x - v)).const_add v
  have hc : HasDerivAt (fun l : ℝ => f (v + l • (x - v)))
      (fderiv ℝ f x (x - v)) 1 := by
    have hd' : HasFDerivAt f (fderiv ℝ f x) (v + (1 : ℝ) • (x - v)) := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm] using hd.hasFDerivAt
    exact hd'.comp_hasDerivAt 1 hr
  simpa using hc.unique (((hasDerivAt_id (1 : ℝ)).mul_const (f x)).congr_of_eventuallyEq
    (hhom x hx))

/-- The radial direction lies in the right kernel of the Hessian. -/
theorem homogeneous_graph_hessian_radial {U : Set (EuclideanSpace ℝ (Fin 2))}
    (hU : IsOpen U) {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : ContDiffOn ℝ 2 f U)
    {v : EuclideanSpace ℝ (Fin 2)}
    (hhom : ∀ x ∈ U, ∀ᶠ l in nhds (1 : ℝ), f (v + l • (x - v)) = l * f x)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ U) (h : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (fderiv ℝ f) x h (x - v) = 0 := by
  have hfx := (hf x hx).contDiffAt (hU.mem_nhds hx)
  have hdf := (hfx.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have he : (fun y => fderiv ℝ f y (y - v)) =ᶠ[nhds x] f := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact homogeneous_graph_euler hU hf hhom hy
  have hd := congrArg (fun L : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ => L h)
    he.fderiv_eq
  have hs : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 2) => y - v) x :=
    differentiableAt_id.sub_const v
  rw [fderiv_clm_apply hdf hs] at hd
  have hs' : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => y - v) x =
      ContinuousLinearMap.id ℝ _ := ((hasFDerivAt_id x).sub_const v).fderiv
  simp only [hs', add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.flip_apply] at hd
  exact add_eq_left.mp hd

/-- In dimension two, a symmetric operator with a nonzero kernel and zero
elliptically weighted trace vanishes. -/
theorem planar_symmetric_eq_zero_of_kernel_of_trace
    (H A : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2))
    (hH : H.IsSymmetric)
    (hA : ∀ z : EuclideanSpace ℝ (Fin 2), z ≠ 0 → 0 < inner ℝ (A z) z)
    {w : EuclideanSpace ℝ (Fin 2)} (hw : w ≠ 0) (hHw : H w = 0)
    (htr : LinearMap.trace ℝ _ (A.comp H) = 0) : H = 0 := by
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by simp
  let b := hH.eigenvectorBasis hn
  let μ := hH.eigenvalues hn
  have he (i : Fin 2) : H (b i) = μ i • b i := hH.apply_eigenvectorBasis hn i
  have hz : Module.End.HasEigenvalue H 0 := Module.End.hasEigenvalue_of_hasEigenvector
    ⟨Module.End.mem_eigenspace_iff.mpr (by simpa using hHw), hw⟩
  obtain ⟨i, hi⟩ := hH.exists_eigenvalues_eq hn hz
  have hp (j : Fin 2) : 0 < inner ℝ (A (b j)) (b j) :=
    hA (b j) (b.toBasis.ne_zero j)
  rw [LinearMap.trace_eq_sum_inner _ b] at htr
  simp only [LinearMap.comp_apply, he, map_smul, inner_smul_right,
    Fin.sum_univ_two] at htr
  rw [real_inner_comm (A (b 0)) (b 0), real_inner_comm (A (b 1)) (b 1)] at htr
  have hμ : ∀ j, μ j = 0 := by
    change μ i = 0 at hi
    fin_cases i
    · change μ 0 = 0 at hi
      have h1 : μ 1 = 0 := by
        rw [hi, zero_mul, zero_add] at htr
        exact (mul_eq_zero.mp htr).resolve_right (ne_of_gt (hp 1))
      intro j
      fin_cases j <;> assumption
    · change μ 1 = 0 at hi
      have h0 : μ 0 = 0 := by
        rw [hi, zero_mul, add_zero] at htr
        exact (mul_eq_zero.mp htr).resolve_right (ne_of_gt (hp 0))
      intro j
      fin_cases j <;> assumption
  apply b.toBasis.ext
  intro j
  simp only [OrthonormalBasis.coe_toBasis, he, hμ, zero_smul, LinearMap.zero_apply]

/-- A locally degree-one homogeneous C² minimal graph over a plane has zero Hessian. -/
theorem hessian_eq_zero_of_homogeneous_minimal {U : Set (EuclideanSpace ℝ (Fin 2))}
    (hU : IsOpen U) {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : ContDiffOn ℝ 2 f U)
    {v : EuclideanSpace ℝ (Fin 2)} (hvU : v ∉ U)
    (hhom : ∀ x ∈ U, ∀ᶠ l in nhds (1 : ℝ), f (v + l • (x - v)) = l * f x)
    (hmse : ∀ x ∈ U, LinearMap.trace ℝ (EuclideanSpace ℝ (Fin 2))
      ((fderiv ℝ (fun y => mcFlux (gradient f y)) x :
        EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :
        EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) = 0) :
    ∀ x ∈ U, fderiv ℝ (fderiv ℝ f) x = 0 := by
  intro x hx
  have hfx := (hf x hx).contDiffAt (hU.mem_nhds hx)
  have hgrad : DifferentiableAt ℝ (gradient f) x :=
    ((toDual ℝ (EuclideanSpace ℝ (Fin 2))).symm.contDiff.contDiffAt.comp x
      (hfx.fderiv_right (m := 1) (by norm_num))).differentiableAt one_ne_zero
  have hd := (toDual ℝ (EuclideanSpace ℝ (Fin 2))).toContinuousLinearEquiv.hasFDerivAt.comp
    x hgrad.hasFDerivAt
  have hfun : (toDual ℝ (EuclideanSpace ℝ (Fin 2))).toContinuousLinearEquiv ∘
      gradient f = fderiv ℝ f := by
    funext y
    exact toDual_gradient
  rw [hfun] at hd
  have he (a b : EuclideanSpace ℝ (Fin 2)) :
      inner ℝ (fderiv ℝ (gradient f) x a) b = fderiv ℝ (fderiv ℝ f) x a b := by
    rw [hd.fderiv]
    rfl
  have hsym := hfx.isSymmSndFDerivAt (by simp)
  have hH : (fderiv ℝ (gradient f) x).toLinearMap.IsSymmetric := by
    intro a b
    change inner ℝ (fderiv ℝ (gradient f) x a) b =
      inner ℝ a (fderiv ℝ (gradient f) x b)
    rw [real_inner_comm (fderiv ℝ (gradient f) x b) a, he, he]
    exact hsym a b
  have hw : x - v ≠ 0 := sub_ne_zero.mpr (fun h => hvU (h ▸ hx))
  have hHw : fderiv ℝ (gradient f) x (x - v) = 0 := by
    apply ext_inner_right ℝ
    intro a
    rw [inner_zero_left, he, hsym]
    exact homogeneous_graph_hessian_radial hU hf hhom hx a
  have hA : ∀ z : EuclideanSpace ℝ (Fin 2), z ≠ 0 →
      0 < inner ℝ (fderiv ℝ mcFlux (gradient f x) z) z := by
    intro z hz
    obtain ⟨lam, hlam, hell⟩ := mcCoefficient_elliptic (norm_nonneg (gradient f x))
    rw [mcFlux_fderiv_inner]
    exact lt_of_lt_of_le (mul_pos hlam (sq_pos_of_pos (norm_pos_iff.mpr hz)))
      (hell (gradient f x) le_rfl z)
  have hchain := fderiv_comp x
    (contDiff_mcFlux.differentiable (by simp) (gradient f x)) hgrad
  have htr : LinearMap.trace ℝ _
      ((fderiv ℝ mcFlux (gradient f x)).toLinearMap.comp
        (fderiv ℝ (gradient f) x).toLinearMap) = 0 := by
    rw [← ContinuousLinearMap.toLinearMap_comp, ← hchain]
    exact hmse x hx
  have hzero := planar_symmetric_eq_zero_of_kernel_of_trace
    (fderiv ℝ (gradient f) x).toLinearMap
    (fderiv ℝ mcFlux (gradient f x)).toLinearMap hH hA hw hHw htr
  ext a b
  rw [← he]
  have ha : fderiv ℝ (gradient f) x a = 0 := LinearMap.congr_fun hzero a
  simp [ha]

end LiquidDrop
