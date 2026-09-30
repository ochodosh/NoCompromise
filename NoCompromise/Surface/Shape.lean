module

public import NoCompromise.Surface.Geometry
public import NoCompromise.Area.Linear
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

@[expose] public section

/-!
# Gauss-map Jacobian and the Hessian of height

* `lem:gauss-jacobian`: `tangentPlane_sphere_normal_eq` (`T_{n(p)}S² = T_pΣ`),
  `fderiv_normal_eq_tangentShapeOperator` (`d_pn = A_p` on `T_pΣ`),
  `det_tangentShapeOperator_eq_gaussCurvature`, and
  `jacobian2Linear_normal_eq_abs_gaussCurvature` (`J₂(d_pn) = |κ(p)|`, computed through any
  linear isometry of `ℝ²` onto `T_pΣ`).
* `lem:hess-height`: `isSurfaceCriticalPoint_height_iff` and `surfaceHessian_height`
  (with the `±` specialisations).

The shape operator uses the positive-sphere convention.

**Definition of the surface Hessian.** For an ambient
function `f` and a unit normal field `n`,
`surfaceHessian n f p X Y := D²f(p)(X,Y) − Df(p)(n p) · II_p(X,Y)`, to be evaluated on
`X, Y ∈ T_pΣ`. The naive restriction of `D²f(p)` to `T_pΣ` is *not* intrinsic (it depends
on the extension and vanishes for linear height functions). The definition is justified by
`hasDerivAt_deriv_comp_eq_surfaceHessian`: at a critical point `p` of `f|_Σ`, for every
`C²` curve `γ` in `Σ` with `γ 0 = p`, `(f ∘ γ)''(0) = surfaceHessian n f p (γ'(0)) (γ'(0))`,
which is the intrinsic second derivative of `f|_Σ` along `γ`.
-/

noncomputable section
open Set Filter Function InnerProductSpace
open scoped Topology
namespace LiquidDrop

set_option maxSynthPendingDepth 8

theorem tangentPlane_sphere_normal_eq {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n) {p : E₃} (hp : p ∈ S) :
    tangentPlane (Metric.sphere (0 : E₃) 1) (n p) = tangentPlane S p := by
  have hpSphere : n p ∈ Metric.sphere (0 : E₃) 1 := by simpa using (hn.2 p hp).1
  have he := (isUnitNormalField_sphere (by norm_num : (0 : ℝ) < 1)).tangentPlane_eq
    (isSmoothEmbeddedSurface_sphere (by norm_num)) hpSphere
  simpa only [inv_one, one_smul, hn.tangentPlane_eq hS hp] using he

theorem fderiv_normal_mem_tangentPlane_sphere {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n) {p X : E₃}
    (hp : p ∈ S) (hX : X ∈ tangentPlane S p) :
    fderiv ℝ n p X ∈ tangentPlane (Metric.sphere (0 : E₃) 1) (n p) := by
  rw [tangentPlane_sphere_normal_eq hS hn hp]
  exact hn.shapeOperator_mem hS hp hX

theorem fderiv_normal_eq_tangentShapeOperator {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n) {p : E₃}
    (hp : p ∈ S) (X : tangentPlane S p) :
    fderiv ℝ n p X = (tangentShapeOperator S n p X : E₃) :=
  (hn.coe_tangentShapeOperator hS hp X).symm

theorem det_tangentShapeOperator_eq_gaussCurvature (S : Set E₃) (n : E₃ → E₃) (p : E₃) :
    LinearMap.det (tangentShapeOperator S n p).toLinearMap = gaussCurvature S n p := rfl

/-- The Gauss-map Jacobian, computed through any isometry onto the tangent plane. -/
theorem jacobian2Linear_normal_eq_abs_gaussCurvature {S : Set E₃} {n : E₃ → E₃} {p : E₃}
    (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n) (hp : p ∈ S)
    (ι : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] E₃)
    (hι : LinearMap.range ι.toLinearMap = tangentPlane S p) :
    jacobian2Linear ((fderiv ℝ n p).comp ι.toContinuousLinearMap) = |gaussCurvature S n p| := by
  have hi (x) : ι x ∈ tangentPlane S p := hι ▸ LinearMap.mem_range_self ι.toLinearMap x
  let j := ι.toLinearMap.codRestrict (tangentPlane S p) hi
  let L := (fderiv ℝ n p).comp ι.toContinuousLinearMap
  have hL (x) : L x ∈ tangentPlane S p := hn.shapeOperator_mem hS hp (hi x)
  have he : L.toLinearMap.codRestrict (tangentPlane S p) hL =
      (tangentShapeOperator S n p).toLinearMap.comp j := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact fderiv_normal_eq_tangentShapeOperator hS hn hp (j x)
  rw [jacobian2Linear_eq_normDet]
  change L.toLinearMap.normDet = _
  rw [← LinearMap.normDet_codRestrict hL, he,
    LinearMap.normDet_comp_of_finrank_eq _ _ (by simp [hS.finrank_tangentPlane hp]),
    LinearMap.normDet_eq_abs_det]
  have hj : j.normDet = 1 := by
    rw [LinearMap.normDet_codRestrict]
    exact ι.normDet_eq_one
  rw [hj, mul_one]
  rfl

/-- `p` is a critical point of the restriction of `f` to `S`. -/
def IsSurfaceCriticalPoint (S : Set E₃) (f : E₃ → ℝ) (p : E₃) : Prop :=
  p ∈ S ∧ ∀ X ∈ tangentPlane S p, fderiv ℝ f p X = 0

/-- Hessian from an ambient extension, with the normal correction term. -/
def surfaceHessian (n : E₃ → E₃) (f : E₃ → ℝ) (p X Y : E₃) : ℝ :=
  fderiv ℝ (fderiv ℝ f) p X Y - fderiv ℝ f p (n p) * secondFundamentalForm n p X Y

private lemma deriv_mem_tangentPlane {S : Set E₃} {γ : ℝ → E₃} {t : ℝ}
    (hγ : DifferentiableAt ℝ γ t) (hγS : ∀ᶠ u in 𝓝 t, γ u ∈ S) :
    deriv γ t ∈ tangentPlane S (γ t) := by
  rw [mem_tangentPlane_iff]
  intro g hg hgzero
  have ht : Tendsto γ (𝓝 t) (𝓝[S] (γ t)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hγ.continuousAt.tendsto, hγS⟩
  have he : g ∘ γ =ᶠ[𝓝 t] fun _ => 0 := ht.eventually hgzero
  have hd := hg.hasFDerivAt.comp_hasDerivAt t hγ.hasDerivAt
  have hz := (hd.congr_of_eventuallyEq he.symm).deriv
  simpa using hz.symm

private lemma critical_fderiv_eq_normal {S : Set E₃} {n : E₃ → E₃} {f : E₃ → ℝ}
    {p : E₃} (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n)
    (hc : IsSurfaceCriticalPoint S f p) (Z : E₃) :
    fderiv ℝ f p Z = inner ℝ (n p) Z * fderiv ℝ f p (n p) := by
  have ht : Z - inner ℝ (n p) Z • n p ∈ tangentPlane S p := by
    rw [hn.tangentPlane_eq hS hc.1, Submodule.mem_orthogonal_singleton_iff_inner_right]
    simp [inner_sub_right, real_inner_smul_right, (hn.2 p hc.1).1]
  have hz := hc.2 _ ht
  rw [map_sub, map_smul] at hz
  exact sub_eq_zero.mp hz

/-- At a critical point the surface Hessian gives the second derivative along
any twice continuously differentiable surface curve. -/
theorem hasDerivAt_deriv_comp_eq_surfaceHessian {S : Set E₃} {n : E₃ → E₃} {f : E₃ → ℝ}
    {p : E₃} (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n)
    (hf : ContDiffAt ℝ 2 f p) (hcrit : IsSurfaceCriticalPoint S f p)
    {γ : ℝ → E₃} (hγ : ContDiffAt ℝ 2 γ 0) (hγ0 : γ 0 = p)
    (hγS : ∀ᶠ t in 𝓝 0, γ t ∈ S) :
    HasDerivAt (deriv (f ∘ γ)) (surfaceHessian n f p (deriv γ 0) (deriv γ 0)) 0 := by
  have hdγ : DifferentiableAt ℝ γ 0 := hγ.differentiableAt (by norm_num)
  have hdγ' : DifferentiableAt ℝ (deriv γ) 0 :=
    (hγ.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdn : HasFDerivAt n (fderiv ℝ n p) (γ 0) := by
    rw [hγ0]
    exact ((hn.contDiffAt hcrit.1).differentiableAt (by simp)).hasFDerivAt
  have horth : (fun t => inner ℝ (n (γ t)) (deriv γ t)) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [hγS, hγS.eventually_nhds, hγ.eventually (by norm_num)] with t ht htS htγ
    exact (hn.2 (γ t) ht).2 _ (deriv_mem_tangentPlane (htγ.differentiableAt (by norm_num)) htS)
  have hdorth := (hdn.comp_hasDerivAt 0 hdγ.hasDerivAt).inner ℝ hdγ'.hasDerivAt
  have hz := (hdorth.congr_of_eventuallyEq horth.symm).deriv
  have hacc : inner ℝ (n p) (deriv (deriv γ) 0) =
      -secondFundamentalForm n p (deriv γ 0) (deriv γ 0) := by
    have he : inner ℝ (n p) (deriv (deriv γ) 0) +
        inner ℝ (fderiv ℝ n p (deriv γ 0)) (deriv γ 0) = 0 := by
      simpa [hγ0] using hz.symm
    exact eq_neg_of_add_eq_zero_left he
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) p :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdfγ : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) p) (γ 0) := by
    simpa only [hγ0] using hdf.hasFDerivAt
  have hchain := (hdfγ.comp_hasDerivAt 0 hdγ.hasDerivAt).clm_apply hdγ'.hasDerivAt
  have hchainEq : deriv (f ∘ γ) =ᶠ[𝓝 0] fun t => fderiv ℝ f (γ t) (deriv γ t) := by
    have hnear : ∀ᶠ t in 𝓝 0, ContDiffAt ℝ 2 f (γ t) := by
      apply (show Tendsto γ (𝓝 0) (𝓝 p) by simpa [hγ0] using hdγ.continuousAt.tendsto).eventually
      exact hf.eventually (by norm_num)
    filter_upwards [hnear, hγ.eventually (by norm_num)] with t hft hγt
    exact ((hft.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t
      (hγt.differentiableAt (by norm_num)).hasDerivAt).deriv
  have he := hchain.congr_of_eventuallyEq hchainEq
  have hfa := critical_fderiv_eq_normal hS hn hcrit (deriv (deriv γ) 0)
  rw [hacc] at hfa
  have heq : fderiv ℝ (fderiv ℝ f) p (deriv γ 0) (deriv γ 0) +
      fderiv ℝ f (γ 0) (deriv (deriv γ) 0) =
      surfaceHessian n f p (deriv γ 0) (deriv γ 0) := by
    rw [hγ0, hfa]
    unfold surfaceHessian
    ring
  rw [← heq]
  exact he

private lemma fderiv_height (p v : E₃) :
    fderiv ℝ (fun x : E₃ => inner ℝ x v) p = innerSL ℝ v := by
  have he : (fun x : E₃ => inner ℝ x v) = innerSL ℝ v := by
    ext x
    exact (real_inner_comm x v).symm
  rw [he]
  exact (innerSL ℝ v).fderiv

/-- Critical points of height are exactly the points with normal `±v`. -/
theorem isSurfaceCriticalPoint_height_iff {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n)
    {p : E₃} (hp : p ∈ S) {v : E₃} (hv : ‖v‖ = 1) :
    IsSurfaceCriticalPoint S (fun x => inner ℝ x v) p ↔ n p = v ∨ n p = -v := by
  constructor
  · intro hc
    have hvperp : v ∈ (tangentPlane S p)ᗮ := by
      apply (Submodule.mem_orthogonal' _ _).mpr
      intro X hX
      simpa only [fderiv_height, innerSL_apply_apply] using hc.2 X hX
    rw [hn.tangentPlane_eq hS hp, Submodule.orthogonal_orthogonal] at hvperp
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hvperp
    have habs : |a| = 1 := by
      have := congrArg norm ha
      simpa [norm_smul, (hn.2 p hp).1, hv] using this
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp habs with he | he
    · left
      simpa [he] using ha
    · right
      simpa [he] using congrArg Neg.neg ha
  · intro he
    refine ⟨hp, fun X hX => ?_⟩
    rw [fderiv_height, innerSL_apply_apply]
    rcases he with he | he
    · rw [← he]
      exact (hn.2 p hp).2 X hX
    · have hz := (hn.2 p hp).2 X hX
      rw [he, inner_neg_left] at hz
      exact neg_eq_zero.mp hz

/-- The Hessian of height with the positive-sphere convention. -/
theorem surfaceHessian_height (n : E₃ → E₃) (p v X Y : E₃) :
    surfaceHessian n (fun x => inner ℝ x v) p X Y =
      -(inner ℝ (n p) v) * secondFundamentalForm n p X Y := by
  have he : fderiv ℝ (fun x : E₃ => inner ℝ x v) = fun _ => innerSL ℝ v :=
    funext fun q => fderiv_height q v
  unfold surfaceHessian
  simp only [he, fderiv_const_apply, zero_apply,
    innerSL_apply_apply, zero_sub, neg_mul]
  rw [real_inner_comm]

theorem surfaceHessian_height_of_eq {n : E₃ → E₃} {p v X Y : E₃}
    (h : n p = v) (hv : ‖v‖ = 1) :
    surfaceHessian n (fun x => inner ℝ x v) p X Y = -secondFundamentalForm n p X Y := by
  rw [surfaceHessian_height, h, real_inner_self_eq_norm_sq, hv]
  ring

theorem surfaceHessian_height_of_eq_neg {n : E₃ → E₃} {p v X Y : E₃}
    (h : n p = -v) (hv : ‖v‖ = 1) :
    surfaceHessian n (fun x => inner ℝ x v) p X Y = secondFundamentalForm n p X Y := by
  rw [surfaceHessian_height, h, inner_neg_left, real_inner_self_eq_norm_sq, hv]
  ring

end LiquidDrop
