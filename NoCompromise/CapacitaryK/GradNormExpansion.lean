module

public import NoCompromise.CapacitaryK.Bochner
public import NoCompromise.Capacity.Kelvin

@[expose] public section

/-!
# Calculus ingredients for the far-field gradient-length expansion

These are partial ingredients for Chapter 31, `eq:K-p-expansion` (volume route).
They include the Euler identities, uniform quadrupole derivative bounds,
monopole formulas, exact linear cross terms, the scalar coefficient eighteen,
and far-field noncriticality with the unregularized Bochner identity.

The uniform nonlinear remainder estimate and the theorem
`gradNorm_laplacian_far_expansion` are not proved in this file.

The quadrupole potential is `Q x / ‖x‖ ^ 5`. Differential identities for this
potential are asserted only off the origin. The inverse at zero follows Lean's
total inverse convention.
-/

noncomputable section
open Filter Set Metric InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace

namespace LiquidDrop.CapacitaryK

/-- Bochner's identity at a noncritical point of a locally harmonic function. -/
theorem laplacianN_gradNorm_of_harmonic {u : E3 → ℝ} {x : E3}
    (hu : ContDiffAt ℝ 3 u x) (hΔ : ∀ᶠ y in 𝓝 x, laplacianN u y = 0)
    (hw : 0 < gradNorm u x) :
    laplacianN (gradNorm u) x =
      hessNormSq u x / gradNorm u x - hessGradNormSq u x / gradNorm u x ^ 3 := by
  simpa only [gradNormEps_zero, zero_pow (by decide : 2 ≠ 0), add_zero] using
    laplacianN_gradNormEps (ε := 0) hu hΔ (by simpa using sq_pos_of_pos hw)

/-- The quadrupole potential in the far-field expansion. -/
def farQuadrupole (Q : E3 → ℝ) (x : E3) : ℝ := Q x / ‖x‖ ^ 5

/-- A degree-two homogeneous function has this quadrupole as its Kelvin transform. -/
theorem farQuadrupole_eq_kelvinTransform {Q : E3 → ℝ}
    (hQh : ∀ (c : ℝ) (x : E3), Q (c • x) = c ^ 2 * Q x) :
    farQuadrupole Q = kelvinTransform Q := by
  funext x
  simp only [farQuadrupole, kelvinTransform, kelvinInversion, hQh, inv_pow,
    div_eq_mul_inv]
  ring

/-- The quadrupole is smooth off the origin. -/
theorem contDiffAt_farQuadrupole {Q : E3 → ℝ}
    (hQ : ContDiff ℝ (⊤ : ℕ∞) Q) {x : E3} (hx : x ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (farQuadrupole Q) x :=
  hQ.contDiffAt.div ((contDiffAt_id.norm ℝ hx).pow 5)
    (pow_ne_zero _ (norm_ne_zero_iff.mpr hx))

/-- Harmonicity of the degree-minus-three quadrupole. -/
theorem laplacianN_farQuadrupole {Q : E3 → ℝ}
    (hQ : ContDiff ℝ (⊤ : ℕ∞) Q)
    (hQh : ∀ (c : ℝ) (x : E3), Q (c • x) = c ^ 2 * Q x)
    (hQl : ∀ x : E3, laplacianN Q x = 0) {x : E3} (hx : x ≠ 0) :
    laplacianN (farQuadrupole Q) x = 0 := by
  rw [farQuadrupole_eq_kelvinTransform hQh,
    laplacianN_kelvinTransform hx (hQ.contDiffAt.of_le (by simp)), hQl, mul_zero]

/-- Positive rescaling gives degree minus three; no assertion at negative scales
is needed for the radial estimates. -/
theorem farQuadrupole_smul {Q : E3 → ℝ}
    (hQh : ∀ (c : ℝ) (x : E3), Q (c • x) = c ^ 2 * Q x)
    {c : ℝ} (hc : 0 < c) (x : E3) :
    farQuadrupole Q (c • x) = (c ^ 3)⁻¹ * farQuadrupole Q x := by
  simp only [farQuadrupole, hQh, norm_smul, Real.norm_eq_abs, abs_of_pos hc, mul_pow]
  field_simp

/-- Differentiation lowers a negative homogeneity degree by one. This identity
uses the total Fréchet derivative and needs no regularity assumption. -/
theorem fderiv_smul_of_negative_homogeneous
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E3 → F} {k : ℕ}
    (hf : ∀ (c : ℝ), 0 < c → ∀ x : E3, f (c • x) = (c ^ k)⁻¹ • f x)
    {c : ℝ} (hc : 0 < c) (x : E3) :
    fderiv ℝ f (c • x) = (c ^ (k + 1))⁻¹ • fderiv ℝ f x := by
  have he : (fun y : E3 => f (c • y)) = (c ^ k)⁻¹ • f := funext (hf c hc)
  have hd := congrArg (fun g : E3 → F => fderiv ℝ g x) he
  rw [fderiv_comp_smul, fderiv_const_smul_field] at hd
  have hh := congrArg (fun L : E3 →L[ℝ] F => c⁻¹ • L) hd
  have hs : c⁻¹ * (c ^ k)⁻¹ = (c ^ (k + 1))⁻¹ := by rw [pow_succ, mul_inv_rev]
  simpa only [Pi.smul_apply, smul_smul, inv_mul_cancel₀ hc.ne', one_smul, hs] using hh

/-- Euler's identity for a function of degree `-k`, differentiated along the
positive ray through a point where the function is differentiable. -/
theorem euler_of_negative_homogeneous
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E3 → F} {k : ℕ}
    (hf : ∀ (c : ℝ), 0 < c → ∀ x : E3, f (c • x) = (c ^ k)⁻¹ • f x)
    {x : E3} (hd : DifferentiableAt ℝ f x) :
    fderiv ℝ f x x = -(k : ℝ) • f x := by
  have hl : HasDerivAt (fun c : ℝ => f (c • x)) (fderiv ℝ f x x) 1 := by
    simpa only [one_smul, Function.comp_def, id_eq] using
      hd.hasFDerivAt.comp_hasDerivAt_of_eq 1 ((hasDerivAt_id (1 : ℝ)).smul_const x)
        (one_smul ℝ x).symm
  have hr : HasDerivAt (fun c : ℝ => (c ^ k)⁻¹ • f x) (-(k : ℝ) • f x) 1 := by
    simpa using (((hasDerivAt_id (1 : ℝ)).pow k).inv (by simp)).smul_const (f x)
  have he : (fun c : ℝ => f (c • x)) =ᶠ[𝓝 1] (fun c : ℝ => (c ^ k)⁻¹ • f x) := by
    filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)] with c hc
    exact hf c hc x
  exact (hl.congr_of_eventuallyEq he.symm).unique hr

/-- Compactness of the unit sphere gives the uniform bound for any continuous
negative homogeneous function on the punctured space. -/
theorem bound_of_negative_homogeneous
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E3 → F} {k : ℕ}
    (hc : ContinuousOn f (sphere 0 1))
    (hf : ∀ (c : ℝ), 0 < c → ∀ x : E3, f (c • x) = (c ^ k)⁻¹ • f x) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : E3, x ≠ 0 → ‖f x‖ ≤ B / ‖x‖ ^ k := by
  obtain ⟨B, hB⟩ := (isCompact_sphere (0 : E3) 1).exists_bound_of_continuousOn hc
  refine ⟨max B 1, zero_lt_one.trans_le (le_max_right _ _), fun x hx => ?_⟩
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let y : E3 := ‖x‖⁻¹ • x
  have hny : ‖y‖ = 1 := by simp [y, norm_smul, hn.ne']
  have hxy : ‖x‖ • y = x := by simp [y, smul_smul, hn.ne']
  have he := hf ‖x‖ hn y
  rw [hxy] at he
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (‖x‖ ^ k)⁻¹ * max B 1 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (hB y (by simpa only [mem_sphere, dist_zero_right] using hny)).trans
        (le_max_left _ _)
    _ = _ := by rw [div_eq_mul_inv, mul_comm]

/-- Degree minus four for the first derivative of the quadrupole. -/
theorem fderiv_farQuadrupole_smul {Q : E3 → ℝ}
    (hQh : ∀ (c : ℝ) (x : E3), Q (c • x) = c ^ 2 * Q x)
    {c : ℝ} (hc : 0 < c) (x : E3) :
    fderiv ℝ (farQuadrupole Q) (c • x) =
      (c ^ 4)⁻¹ • fderiv ℝ (farQuadrupole Q) x :=
  fderiv_smul_of_negative_homogeneous (fun _ hc x => farQuadrupole_smul hQh hc x) hc x

/-- Degree minus five for the second derivative of the quadrupole. -/
theorem fderiv_two_farQuadrupole_smul {Q : E3 → ℝ}
    (hQh : ∀ (c : ℝ) (x : E3), Q (c • x) = c ^ 2 * Q x)
    {c : ℝ} (hc : 0 < c) (x : E3) :
    fderiv ℝ (fderiv ℝ (farQuadrupole Q)) (c • x) =
      (c ^ 5)⁻¹ • fderiv ℝ (fderiv ℝ (farQuadrupole Q)) x :=
  fderiv_smul_of_negative_homogeneous (fun _ hc x => fderiv_farQuadrupole_smul hQh hc x) hc x

/-- Euler identity E1 for the quadrupole. -/
theorem inner_gradient_farQuadrupole {Q : E3 → ℝ}
    (hQ : ContDiff ℝ (⊤ : ℕ∞) Q)
    (hQh : ∀ (c : ℝ) (x : E3), Q (c • x) = c ^ 2 * Q x)
    {x : E3} (hx : x ≠ 0) :
    ⟪x, gradient (farQuadrupole Q) x⟫ = -3 * farQuadrupole Q x := by
  simpa only [inner_gradient_right, conj_trivial, smul_eq_mul, Nat.cast_ofNat] using
    euler_of_negative_homogeneous (fun c hc x => farQuadrupole_smul hQh hc x)
      ((contDiffAt_farQuadrupole hQ hx).differentiableAt (by simp))

/-- Euler identity E2, with the Hessian represented as a continuous bilinear form. -/
theorem fderiv_two_farQuadrupole_radial {Q : E3 → ℝ}
    (hQ : ContDiff ℝ (⊤ : ℕ∞) Q)
    (hQh : ∀ (c : ℝ) (x : E3), Q (c • x) = c ^ 2 * Q x)
    {x : E3} (hx : x ≠ 0) :
    fderiv ℝ (fderiv ℝ (farQuadrupole Q)) x x =
      (-4 : ℝ) • fderiv ℝ (farQuadrupole Q) x := by
  exact euler_of_negative_homogeneous (fun c hc x => fderiv_farQuadrupole_smul hQh hc x)
    (((contDiffAt_farQuadrupole hQ hx).fderiv_right (m := 1) (by simp)).differentiableAt
      one_ne_zero)

/-- Simultaneous uniform bounds for the quadrupole and its first two derivatives. -/
theorem farQuadrupole_derivative_bounds {Q : E3 → ℝ}
    (hQ : ContDiff ℝ (⊤ : ℕ∞) Q)
    (hQh : ∀ (c : ℝ) (x : E3), Q (c • x) = c ^ 2 * Q x) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : E3, x ≠ 0 →
      |farQuadrupole Q x| ≤ B / ‖x‖ ^ 3 ∧
      ‖fderiv ℝ (farQuadrupole Q) x‖ ≤ B / ‖x‖ ^ 4 ∧
      ‖fderiv ℝ (fderiv ℝ (farQuadrupole Q)) x‖ ≤ B / ‖x‖ ^ 5 := by
  have hs (x : E3) (hx : x ∈ sphere (0 : E3) 1) : x ≠ 0 := by
    intro he
    simp [he] at hx
  have hc₀ : ContinuousOn (farQuadrupole Q) (sphere 0 1) := fun x hx =>
    (contDiffAt_farQuadrupole hQ (hs x hx)).continuousAt.continuousWithinAt
  have hc₁ : ContinuousOn (fderiv ℝ (farQuadrupole Q)) (sphere 0 1) := fun x hx =>
    ((contDiffAt_farQuadrupole hQ (hs x hx)).fderiv_right (m := 0) (by simp)).continuousAt
      |>.continuousWithinAt
  have hc₂ : ContinuousOn (fderiv ℝ (fderiv ℝ (farQuadrupole Q))) (sphere 0 1) := by
    intro x hx
    have hd := (contDiffAt_farQuadrupole hQ (hs x hx)).fderiv_right (m := 1) (by simp)
    exact (hd.fderiv_right (m := 0) (by simp)).continuousAt.continuousWithinAt
  obtain ⟨B₀, hB₀, hb₀⟩ := bound_of_negative_homogeneous hc₀
    (fun c hc x => farQuadrupole_smul hQh hc x)
  obtain ⟨B₁, _, hb₁⟩ := bound_of_negative_homogeneous hc₁
    (fun c hc x => fderiv_farQuadrupole_smul hQh hc x)
  obtain ⟨B₂, _, hb₂⟩ := bound_of_negative_homogeneous
    (f := fderiv ℝ (fderiv ℝ (farQuadrupole Q))) (k := 5) hc₂
    (fun c hc x => fderiv_two_farQuadrupole_smul hQh hc x)
  refine ⟨max B₀ (max B₁ B₂), hB₀.trans_le (le_max_left _ _), fun x hx => ?_⟩
  refine ⟨(hb₀ x hx).trans ?_, (hb₁ x hx).trans ?_, (hb₂ x hx).trans ?_⟩
  · exact div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
  · exact div_le_div_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _))
      (by positivity)
  · exact div_le_div_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _))
      (by positivity)

/-- The gradient and the first Fréchet derivative have the same norm. -/
theorem gradNorm_eq_norm_fderiv (u : E3 → ℝ) (x : E3) :
    gradNorm u x = ‖fderiv ℝ u x‖ := by
  simp only [gradNorm, gradient, LinearIsometryEquiv.norm_map]

/-- Coordinate entries of the Hessian agree with the iterated Fréchet derivative. -/
theorem hess_eq_fderiv_two {u : E3 → ℝ} {x : E3}
    (hu : ContDiffAt ℝ 2 u x) (i j : Fin 3) :
    hess u x i j = fderiv ℝ (fderiv ℝ u) x (basisVec i) (basisVec j) := by
  have hd := (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  change fderiv ℝ (fun y => fderiv ℝ u y (basisVec j)) x (basisVec i) = _
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

/-- The coordinate Hessian is symmetric for a twice continuously differentiable function. -/
theorem hess_symmetric {u : E3 → ℝ} {x : E3}
    (hu : ContDiffAt ℝ 2 u x) (i j : Fin 3) : hess u x i j = hess u x j i := by
  rw [hess_eq_fderiv_two hu, hess_eq_fderiv_two hu]
  exact hu.isSymmSndFDerivAt (by norm_num) _ _

/-- A bilinear operator-norm remainder controls every coordinate Hessian entry. -/
theorem abs_hess_le_norm_fderiv_two {u : E3 → ℝ} {x : E3}
    (hu : ContDiffAt ℝ 2 u x) (i j : Fin 3) :
    |hess u x i j| ≤ ‖fderiv ℝ (fderiv ℝ u) x‖ := by
  rw [hess_eq_fderiv_two hu]
  have hi : ‖basisVec i‖ = 1 := by simp [basisVec]
  have hj : ‖basisVec j‖ = 1 := by simp [basisVec]
  have h := ((fderiv ℝ (fderiv ℝ u) x (basisVec i)).le_opNorm (basisVec j)).trans
    (mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ u) x).le_opNorm (basisVec i))
      (norm_nonneg (basisVec j)))
  simpa only [hi, hj, mul_one, Real.norm_eq_abs] using h

/-- An explicit comparison of the coordinate Hilbert--Schmidt norm and the
bilinear operator norm; the factor nine is sufficient for remainder bounds. -/
theorem hessNormSq_le_nine_norm_fderiv_two_sq {u : E3 → ℝ} {x : E3}
    (hu : ContDiffAt ℝ 2 u x) :
    hessNormSq u x ≤ 9 * ‖fderiv ℝ (fderiv ℝ u) x‖ ^ 2 := by
  calc
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, ‖fderiv ℝ (fderiv ℝ u) x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have h := sq_le_sq₀ (abs_nonneg (hess u x i j))
        (norm_nonneg (fderiv ℝ (fderiv ℝ u) x)) |>.mpr (abs_hess_le_norm_fderiv_two hu i j)
      simpa only [sq_abs] using h
    _ = _ := by simp; ring

private lemma sum_basis_apply (L : E3 →L[ℝ] ℝ) (v : E3) :
    (∑ j, L (basisVec j) * v j) = L v := by
  have h := congrArg L ((EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v)
  simpa only [map_sum, map_smul, smul_eq_mul, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, mul_comm] using h

/-- The Hessian-gradient vector can be read directly from the bilinear derivative. -/
theorem hessGrad_eq_fderiv_two {u : E3 → ℝ} {x : E3}
    (hu : ContDiffAt ℝ 2 u x) (i : Fin 3) :
    hessGrad u x i = fderiv ℝ (fderiv ℝ u) x (basisVec i) (gradient u x) := by
  simp only [hessGrad, hess_eq_fderiv_two hu]
  exact sum_basis_apply _ _

/-- The trace identity E3 in the coordinate conventions of `Calculus.lean`. -/
theorem hess_farQuadrupole_trace {Q : E3 → ℝ}
    (hQ : ContDiff ℝ (⊤ : ℕ∞) Q)
    (hQh : ∀ (c : ℝ) (x : E3), Q (c • x) = c ^ 2 * Q x)
    (hQl : ∀ x : E3, laplacianN Q x = 0) {x : E3} (hx : x ≠ 0) :
    (∑ i, hess (farQuadrupole Q) x i i) = 0 :=
  laplacianN_farQuadrupole hQ hQh hQl hx

/-- The twice-radial Hessian of a quadrupole is twelve times its value. -/
theorem fderiv_two_farQuadrupole_radial_radial {Q : E3 → ℝ}
    (hQ : ContDiff ℝ (⊤ : ℕ∞) Q)
    (hQh : ∀ (c : ℝ) (x : E3), Q (c • x) = c ^ 2 * Q x)
    {x : E3} (hx : x ≠ 0) :
    fderiv ℝ (fderiv ℝ (farQuadrupole Q)) x x x = 12 * farQuadrupole Q x := by
  rw [fderiv_two_farQuadrupole_radial hQ hQh hx, smul_apply,
    smul_eq_mul, ← inner_gradient_left, real_inner_comm,
    inner_gradient_farQuadrupole hQ hQh hx]
  ring

/-- Smoothness of the monopole off the origin. -/
theorem contDiffAt_monopole (C : ℝ) {x : E3} (hx : x ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y : E3 => C / ‖y‖) x :=
  contDiffAt_const.div (contDiffAt_id.norm ℝ hx) (norm_ne_zero_iff.mpr hx)

/-- The derivative of the monopole, as a continuous linear functional. -/
theorem hasFDerivAt_monopole (C : ℝ) {x : E3} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E3 => C / ‖y‖) ((-C / ‖x‖ ^ 3) • innerSL ℝ x) x := by
  convert! (schauderNewton_hasFDerivAt_inv_norm_pow hx 0).const_mul C using 1
  · funext y
    simp only [zero_add, pow_one, div_eq_mul_inv]
  · ext v
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, Nat.cast_one,
      Nat.reduceAdd]
    ring

/-- The gradient of `C/r`. -/
theorem gradient_monopole (C : ℝ) {x : E3} (hx : x ≠ 0) :
    gradient (fun y : E3 => C / ‖y‖) x = (-C / ‖x‖ ^ 3) • x := by
  apply PiLp.ext
  intro i
  rw [gradient_apply_eq_fderiv_basisVec, (hasFDerivAt_monopole C hx).fderiv]
  simp only [smul_apply, innerSL_apply_apply, EuclideanSpace.inner_single_right,
    PiLp.smul_apply, smul_eq_mul, starRingEnd_apply, star_trivial, one_mul]

/-- Exact monopole gradient length. -/
theorem gradNorm_monopole {C : ℝ} (hC : 0 ≤ C) {x : E3} (hx : x ≠ 0) :
    gradNorm (fun y : E3 => C / ‖y‖) x = C / ‖x‖ ^ 2 := by
  rw [gradNorm, gradient_monopole C hx, norm_smul, Real.norm_eq_abs, abs_div,
    abs_neg, abs_of_nonneg hC, abs_of_nonneg (by positivity : 0 ≤ ‖x‖ ^ 3)]
  field_simp

/-- The Hessian of `C/r`, evaluated on two arbitrary vectors. -/
theorem fderiv_two_monopole (C : ℝ) {x : E3} (hx : x ≠ 0) (v w : E3) :
    fderiv ℝ (fderiv ℝ (fun y : E3 => C / ‖y‖)) x v w =
      C * (3 * ⟪x, v⟫ * ⟪x, w⟫ / ‖x‖ ^ 5 - ⟪v, w⟫ / ‖x‖ ^ 3) := by
  have he : fderiv ℝ (fun y : E3 => C / ‖y‖) =ᶠ[𝓝 x]
      (fun y => (-C / ‖y‖ ^ 3) • innerSL ℝ y) := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    exact (hasFDerivAt_monopole C hy).fderiv
  have hd := ((schauderNewton_hasFDerivAt_inv_norm_pow hx 2).const_mul (-C)).smul
    (((innerSL ℝ (E := E3)).restrictScalars ℝ).hasFDerivAt (x := x))
  change HasFDerivAt (fun y : E3 => (-C * (‖y‖ ^ (2 + 1))⁻¹) • innerSL ℝ y)
    (_ : E3 →L[ℝ] (E3 →L[ℝ] ℝ)) x at hd
  have hf : (fun y : E3 => (-C * (‖y‖ ^ (2 + 1))⁻¹) • innerSL ℝ y) =
      (fun y : E3 => (-C / ‖y‖ ^ 3) • innerSL ℝ y) := by
    funext y
    simp only [div_eq_mul_inv]
  rw [he.fderiv_eq, ← hf, hd.fderiv]
  change (-C * (‖x‖ ^ 3)⁻¹) * ⟪v, w⟫ +
    (-C * (-((2 + 1 : ℕ) : ℝ) / ‖x‖ ^ 5 * ⟪x, v⟫)) * ⟪x, w⟫ = _
  norm_num
  ring

/-- The coordinate matrix of the monopole Hessian. -/
theorem hess_monopole (C : ℝ) {x : E3} (hx : x ≠ 0) (i j : Fin 3) :
    hess (fun y : E3 => C / ‖y‖) x i j =
      C * (3 * x i * x j / ‖x‖ ^ 5 - (if i = j then 1 else 0) / ‖x‖ ^ 3) := by
  rw [hess_eq_fderiv_two ((contDiffAt_monopole C hx).of_le (by simp)),
    fderiv_two_monopole C hx]
  simp only [EuclideanSpace.inner_single_right]
  by_cases hij : i = j <;> simp [hij]

/-- The squared Hilbert--Schmidt norm of the monopole Hessian. -/
theorem hessNormSq_monopole (C : ℝ) {x : E3} (hx : x ≠ 0) :
    hessNormSq (fun y : E3 => C / ‖y‖) x = 6 * C ^ 2 / ‖x‖ ^ 6 := by
  calc
    _ = 9 * C ^ 2 / ‖x‖ ^ 10 * (∑ i : Fin 3, x i ^ 2) ^ 2 -
        6 * C ^ 2 / ‖x‖ ^ 8 * (∑ i : Fin 3, x i ^ 2) + 3 * C ^ 2 / ‖x‖ ^ 6 := by
      simp only [hessNormSq, hess_monopole C hx, Fin.sum_univ_three]
      norm_num [Fin.ext_iff]
      ring
    _ = _ := by
      rw [← EuclideanSpace.real_norm_sq_eq]
      field_simp
      ring

/-- The monopole Hessian applied to its gradient. -/
theorem hessGrad_monopole (C : ℝ) {x : E3} (hx : x ≠ 0) (i : Fin 3) :
    hessGrad (fun y : E3 => C / ‖y‖) x i = -2 * C ^ 2 * x i / ‖x‖ ^ 6 := by
  rw [hessGrad_eq_fderiv_two ((contDiffAt_monopole C hx).of_le (by simp)),
    fderiv_two_monopole C hx, gradient_monopole C hx]
  simp only [real_inner_smul_right, real_inner_self_eq_norm_sq,
    EuclideanSpace.inner_single_right, EuclideanSpace.inner_single_left,
    starRingEnd_apply, star_trivial, one_mul, PiLp.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Squared norm of the monopole Hessian-gradient vector. -/
theorem hessGradNormSq_monopole (C : ℝ) {x : E3} (hx : x ≠ 0) :
    hessGradNormSq (fun y : E3 => C / ‖y‖) x = 4 * C ^ 4 / ‖x‖ ^ 10 := by
  calc
    _ = 4 * C ^ 4 / ‖x‖ ^ 12 * (∑ i : Fin 3, x i ^ 2) := by
      simp only [hessGradNormSq, hessGrad_monopole C hx, Fin.sum_univ_three]
      ring
    _ = _ := by rw [← EuclideanSpace.real_norm_sq_eq]; field_simp

/-- Contracting the monopole Hessian against any Hessian splits into its radial
part and its trace. -/
theorem monopole_hess_pairing (C : ℝ) {u : E3 → ℝ} {x : E3} (hx : x ≠ 0)
    (hu : ContDiffAt ℝ 2 u x) :
    (∑ i, ∑ j, hess (fun y : E3 => C / ‖y‖) x i j * hess u x i j) =
      3 * C / ‖x‖ ^ 5 * fderiv ℝ (fderiv ℝ u) x x x -
        C / ‖x‖ ^ 3 * laplacianN u x := by
  have hrad : (∑ i, ∑ j, x i * x j * hess u x i j) =
      fderiv ℝ (fderiv ℝ u) x x x := by
    simp only [hess_eq_fderiv_two hu]
    have hi (i : Fin 3) :
        (∑ j, x i * x j * fderiv ℝ (fderiv ℝ u) x (basisVec i) (basisVec j)) =
          x i * fderiv ℝ (fderiv ℝ u) x (basisVec i) x := by
      rw [← sum_basis_apply (fderiv ℝ (fderiv ℝ u) x (basisVec i)) x, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    simp only [hi]
    simpa only [ContinuousLinearMap.flip_apply, mul_comm] using
      sum_basis_apply ((fderiv ℝ (fderiv ℝ u) x).flip x) x
  calc
    _ = 3 * C / ‖x‖ ^ 5 * (∑ i, ∑ j, x i * x j * hess u x i j) -
        C / ‖x‖ ^ 3 * (∑ i, hess u x i i) := by
      simp only [hess_monopole C hx, Fin.sum_univ_three]
      norm_num [Fin.ext_iff]
      ring
    _ = _ := by rw [hrad]; rfl

/-- The exact monopole--quadrupole Hessian cross term. -/
theorem monopole_farQuadrupole_hess_pairing (C : ℝ) {Q : E3 → ℝ}
    (hQ : ContDiff ℝ (⊤ : ℕ∞) Q)
    (hQh : ∀ (c : ℝ) (x : E3), Q (c • x) = c ^ 2 * Q x)
    (hQl : ∀ x : E3, laplacianN Q x = 0) {x : E3} (hx : x ≠ 0) :
    (∑ i, ∑ j, hess (fun y : E3 => C / ‖y‖) x i j * hess (farQuadrupole Q) x i j) =
      36 * C * farQuadrupole Q x / ‖x‖ ^ 5 := by
  rw [monopole_hess_pairing C hx ((contDiffAt_farQuadrupole hQ hx).of_le (by simp)),
    fderiv_two_farQuadrupole_radial_radial hQ hQh hx,
    laplacianN_farQuadrupole hQ hQh hQl hx]
  ring

/-- The exact gradient cross term in the squared gradient-length expansion. -/
theorem monopole_farQuadrupole_gradient_inner (C : ℝ) {Q : E3 → ℝ}
    (hQ : ContDiff ℝ (⊤ : ℕ∞) Q)
    (hQh : ∀ (c : ℝ) (x : E3), Q (c • x) = c ^ 2 * Q x)
    {x : E3} (hx : x ≠ 0) :
    ⟪gradient (fun y : E3 => C / ‖y‖) x, gradient (farQuadrupole Q) x⟫ =
      3 * C * farQuadrupole Q x / ‖x‖ ^ 3 := by
  rw [gradient_monopole C hx, real_inner_smul_left,
    inner_gradient_farQuadrupole hQ hQh hx]
  ring

/-- The part of the Hessian-gradient vector which is linear in the quadrupole. -/
theorem monopole_farQuadrupole_hessGrad_cross (C : ℝ) {Q : E3 → ℝ}
    (hQ : ContDiff ℝ (⊤ : ℕ∞) Q)
    (hQh : ∀ (c : ℝ) (x : E3), Q (c • x) = c ^ 2 * Q x)
    {x : E3} (hx : x ≠ 0) (i : Fin 3) :
    (∑ j, hess (farQuadrupole Q) x i j * gradient (fun y : E3 => C / ‖y‖) x j) +
      (∑ j, hess (fun y : E3 => C / ‖y‖) x i j * gradient (farQuadrupole Q) x j) =
      3 * C * gradient (farQuadrupole Q) x i / ‖x‖ ^ 3 -
        9 * C * farQuadrupole Q x * x i / ‖x‖ ^ 5 := by
  have hq₂ : ContDiffAt ℝ 2 (farQuadrupole Q) x :=
    (contDiffAt_farQuadrupole hQ hx).of_le (by simp)
  have hm₂ : ContDiffAt ℝ 2 (fun y : E3 => C / ‖y‖) x :=
    (contDiffAt_monopole C hx).of_le (by simp)
  simp only [hess_eq_fderiv_two hq₂, hess_eq_fderiv_two hm₂, sum_basis_apply]
  rw [gradient_monopole C hx, map_smul, smul_eq_mul,
    hq₂.isSymmSndFDerivAt (by norm_num) (basisVec i) x,
    fderiv_two_farQuadrupole_radial hQ hQh hx, smul_apply, smul_eq_mul,
    ← gradient_apply_eq_fderiv_basisVec, fderiv_two_monopole C hx,
    inner_gradient_farQuadrupole hQ hQh hx]
  simp only [EuclideanSpace.inner_single_right, EuclideanSpace.inner_single_left,
    starRingEnd_apply, star_trivial, one_mul]
  ring

/-- The exact cross term in the squared Hessian-gradient norm expansion. -/
theorem monopole_farQuadrupole_hessGrad_pairing (C : ℝ) {Q : E3 → ℝ}
    (hQ : ContDiff ℝ (⊤ : ℕ∞) Q)
    (hQh : ∀ (c : ℝ) (x : E3), Q (c • x) = c ^ 2 * Q x)
    {x : E3} (hx : x ≠ 0) :
    (∑ i, hessGrad (fun y : E3 => C / ‖y‖) x i *
      ((∑ j, hess (farQuadrupole Q) x i j * gradient (fun y : E3 => C / ‖y‖) x j) +
        (∑ j, hess (fun y : E3 => C / ‖y‖) x i j * gradient (farQuadrupole Q) x j))) =
      36 * C ^ 3 * farQuadrupole Q x / ‖x‖ ^ 9 := by
  have hi : (∑ i : Fin 3, x i * gradient (farQuadrupole Q) x i) =
      -3 * farQuadrupole Q x := by
    calc
      _ = fderiv ℝ (farQuadrupole Q) x x := by
        simp only [gradient_apply_eq_fderiv_basisVec]
        simpa only [mul_comm] using sum_basis_apply (fderiv ℝ (farQuadrupole Q) x) x
      _ = _ := by
        simpa only [inner_gradient_right, conj_trivial] using
          inner_gradient_farQuadrupole hQ hQh hx
  calc
    _ = -6 * C ^ 3 / ‖x‖ ^ 9 * (∑ i : Fin 3, x i * gradient (farQuadrupole Q) x i) +
        18 * C ^ 3 * farQuadrupole Q x / ‖x‖ ^ 11 * (∑ i : Fin 3, x i ^ 2) := by
      simp_rw [hessGrad_monopole C hx, monopole_farQuadrupole_hessGrad_cross C hQ hQh hx]
      simp only [Fin.sum_univ_three]
      ring
    _ = _ := by rw [hi, ← EuclideanSpace.real_norm_sq_eq]; field_simp; ring

/-- The scalar linearization of the Bochner expression at the monopole. The
three affine inputs are the value and first variation of `|g|²`, `|H|²`, and
`|Hg|²`, respectively; their first variation gives the coefficient eighteen. -/
theorem bochner_scalar_linearization {C r : ℝ} (hC : 0 < C) (hr : 0 < r) (h : ℝ) :
    HasDerivAt (fun t : ℝ =>
      (6 * C ^ 2 / r ^ 6 + t * (72 * C * h / r ^ 5)) /
        Real.sqrt (C ^ 2 / r ^ 4 + t * (6 * C * h / r ^ 3)) -
      (4 * C ^ 4 / r ^ 10 + t * (72 * C ^ 3 * h / r ^ 9)) /
        Real.sqrt (C ^ 2 / r ^ 4 + t * (6 * C * h / r ^ 3)) ^ 3)
      (18 * h / r ^ 3) 0 := by
  have hs : Real.sqrt (C ^ 2 / r ^ 4) = C / r ^ 2 := by
    rw [show C ^ 2 / r ^ 4 = (C / r ^ 2) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hg := (((hasDerivAt_id (0 : ℝ)).mul_const (6 * C * h / r ^ 3)).const_add
    (C ^ 2 / r ^ 4)).sqrt (by
      simpa only [id_eq, zero_mul, add_zero] using
        (show C ^ 2 / r ^ 4 ≠ 0 by positivity))
  have hg' : HasDerivAt (fun t : ℝ => Real.sqrt (C ^ 2 / r ^ 4 + t * (6 * C * h / r ^ 3)))
      (3 * h / r) 0 := by
    convert! hg using 1
    simp only [id_eq, one_mul, zero_mul, add_zero, hs]
    field_simp
    ring
  have hA := ((hasDerivAt_id (0 : ℝ)).mul_const (72 * C * h / r ^ 5)).const_add
    (6 * C ^ 2 / r ^ 6)
  have hB := ((hasDerivAt_id (0 : ℝ)).mul_const (72 * C ^ 3 * h / r ^ 9)).const_add
    (4 * C ^ 4 / r ^ 10)
  have hg0 : Real.sqrt (C ^ 2 / r ^ 4 + 0 * (6 * C * h / r ^ 3)) ≠ 0 := by
    simp only [zero_mul, add_zero, hs]
    positivity
  convert! (hA.div hg' hg0).sub (hB.div (hg'.pow 3) (pow_ne_zero 3 hg0)) using 1
  simp only [id_eq, Pi.pow_apply, one_mul, zero_mul, add_zero, hs]
  field_simp [hC.ne', hr.ne']
  ring_nf
  field_simp [hr.ne']
  norm_num

/-- The first-derivative remainder estimate already ensures a quantitative
positive lower bound for the gradient length sufficiently far from the origin.
Neither harmonicity nor the second-derivative remainder bound is needed here. -/
theorem gradNorm_far_lower_bound {U Q : E3 → ℝ} {C R M : ℝ} (hC : 0 < C)
    (hU : ContDiffOn ℝ (⊤ : ℕ∞) U {x | R < ‖x‖})
    (hQ : ContDiff ℝ (⊤ : ℕ∞) Q)
    (hQh : ∀ (c : ℝ) (x : E3), Q (c • x) = c ^ 2 * Q x)
    (hW : ∀ x : E3, R ≤ ‖x‖ →
      ‖fderiv ℝ (fun y => U y - C / ‖y‖ - Q y / ‖y‖ ^ 5) x‖ ≤ M / ‖x‖ ^ 5) :
    ∃ R' : ℝ, 0 < R' ∧ ∀ x : E3, R' ≤ ‖x‖ →
      C / (2 * ‖x‖ ^ 2) ≤ gradNorm U x ∧ 0 < gradNorm U x := by
  obtain ⟨B, hB, hb⟩ := farQuadrupole_derivative_bounds hQ hQh
  let A := B + |M|
  let R' := max (R + 1) (max 1 (2 * A / C))
  have hR' : 0 < R' := zero_lt_one.trans_le
    ((le_max_left 1 (2 * A / C)).trans (le_max_right _ _))
  refine ⟨R', hR', fun x hx => ?_⟩
  have hn : 0 < ‖x‖ := hR'.trans_le hx
  have hx0 : x ≠ 0 := norm_pos_iff.mp hn
  have hr₁ : 1 ≤ ‖x‖ := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hrR : R < ‖x‖ := lt_of_lt_of_le (by linarith : R < R + 1)
    ((le_max_left _ _).trans hx)
  have hrA : 2 * A / C ≤ ‖x‖ :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  have hdU : DifferentiableAt ℝ U x :=
    (hU.contDiffAt ((isOpen_lt continuous_const continuous_norm).mem_nhds hrR)).differentiableAt
      (by simp)
  have hdm := (hasFDerivAt_monopole C hx0).differentiableAt
  have hdq := (contDiffAt_farQuadrupole hQ hx0).differentiableAt (by simp)
  have hdUm : DifferentiableAt ℝ (fun y : E3 => U y - C / ‖y‖) x := hdU.sub hdm
  have he : fderiv ℝ U x - fderiv ℝ (fun y : E3 => C / ‖y‖) x =
      fderiv ℝ (fun y => U y - C / ‖y‖ - Q y / ‖y‖ ^ 5) x +
        fderiv ℝ (farQuadrupole Q) x := by
    change _ = fderiv ℝ (fun y => (U y - C / ‖y‖) - farQuadrupole Q y) x + _
    rw [fderiv_fun_sub hdUm hdq, fderiv_fun_sub hdU hdm, sub_add_cancel]
  have hsmall : ‖fderiv ℝ U x - fderiv ℝ (fun y : E3 => C / ‖y‖) x‖ ≤
      A / ‖x‖ ^ 4 := by
    rw [he]
    calc
      _ ≤ ‖fderiv ℝ (fun y => U y - C / ‖y‖ - Q y / ‖y‖ ^ 5) x‖ +
          ‖fderiv ℝ (farQuadrupole Q) x‖ := norm_add_le _ _
      _ ≤ M / ‖x‖ ^ 5 + B / ‖x‖ ^ 4 := add_le_add (hW x hrR.le) (hb x hx0).2.1
      _ ≤ |M| / ‖x‖ ^ 5 + B / ‖x‖ ^ 4 := by gcongr; exact le_abs_self M
      _ ≤ |M| / ‖x‖ ^ 4 + B / ‖x‖ ^ 4 := by
        apply add_le_add _ le_rfl
        apply div_le_div_of_nonneg_left (abs_nonneg M) (by positivity)
        calc
          ‖x‖ ^ 4 = ‖x‖ ^ 4 * 1 := (mul_one _).symm
          _ ≤ ‖x‖ ^ 4 * ‖x‖ := mul_le_mul_of_nonneg_left hr₁ (by positivity)
          _ = ‖x‖ ^ 5 := (pow_succ _ _).symm
      _ = _ := by dsimp [A]; ring
  have hsmall' : A / ‖x‖ ^ 4 ≤ C / (2 * ‖x‖ ^ 2) := by
    have hAC : 2 * A ≤ ‖x‖ * C := (div_le_iff₀ hC).mp hrA
    have hsq : ‖x‖ ≤ ‖x‖ ^ 2 := by nlinarith
    have hAC₂ : 2 * A ≤ C * ‖x‖ ^ 2 := by nlinarith
    apply (div_le_div_iff₀ (pow_pos hn 4) (by positivity : 0 < 2 * ‖x‖ ^ 2)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hAC₂ (sq_nonneg ‖x‖)]
  have hrev := norm_sub_norm_le
    (fderiv ℝ (fun y : E3 => C / ‖y‖) x) (fderiv ℝ U x)
  rw [← gradNorm_eq_norm_fderiv, gradNorm_monopole hC.le hx0,
    ← gradNorm_eq_norm_fderiv, norm_sub_rev] at hrev
  have hhalf : C / ‖x‖ ^ 2 = 2 * (C / (2 * ‖x‖ ^ 2)) := by ring
  have hlower : C / (2 * ‖x‖ ^ 2) ≤ gradNorm U x := by
    rw [hhalf] at hrev
    linarith [hsmall.trans hsmall']
  exact ⟨hlower, (div_pos hC (by positivity : 0 < 2 * ‖x‖ ^ 2)).trans_le hlower⟩

/-- Assembly of noncriticality and the unregularized Bochner identity in the
far region, with only the first-derivative part of the remainder hypothesis. -/
theorem gradNorm_far_bochner {U Q : E3 → ℝ} {C R M : ℝ} (hC : 0 < C)
    (hU : ContDiffOn ℝ (⊤ : ℕ∞) U {x | R < ‖x‖})
    (hUh : ∀ x : E3, R < ‖x‖ → laplacianN U x = 0)
    (hQ : ContDiff ℝ (⊤ : ℕ∞) Q)
    (hQh : ∀ (c : ℝ) (x : E3), Q (c • x) = c ^ 2 * Q x)
    (hW : ∀ x : E3, R ≤ ‖x‖ →
      ‖fderiv ℝ (fun y => U y - C / ‖y‖ - Q y / ‖y‖ ^ 5) x‖ ≤ M / ‖x‖ ^ 5) :
    ∃ R' : ℝ, 0 < R' ∧ ∀ x : E3, R' ≤ ‖x‖ →
      0 < gradNorm U x ∧
      laplacianN (gradNorm U) x = hessNormSq U x / gradNorm U x -
        hessGradNormSq U x / gradNorm U x ^ 3 := by
  obtain ⟨R', hR', hb⟩ := gradNorm_far_lower_bound hC hU hQ hQh hW
  refine ⟨max R' (R + 1), hR'.trans_le (le_max_left _ _), fun x hx => ?_⟩
  have hw := (hb x ((le_max_left _ _).trans hx)).2
  have hr : R < ‖x‖ := lt_of_lt_of_le (by linarith : R < R + 1)
    ((le_max_right _ _).trans hx)
  have hopen : IsOpen {y : E3 | R < ‖y‖} := isOpen_lt continuous_const continuous_norm
  refine ⟨hw, laplacianN_gradNorm_of_harmonic
    ((hU.contDiffAt (hopen.mem_nhds hr)).of_le (by simp)) ?_ hw⟩
  filter_upwards [hopen.mem_nhds hr] with y hy
  exact hUh y hy

end LiquidDrop.CapacitaryK
