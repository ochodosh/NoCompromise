module

public import NoCompromise.BV.SmoothApproxBoundary
public import Mathlib.Analysis.Calculus.Implicit
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
public import Mathlib.Analysis.Calculus.FDeriv.Affine

@[expose] public section

/-!
# Concrete smooth surfaces and the positive-sphere curvature convention

Surfaces are locally regular scalar zero sets in Euclidean three-space. The
tangent plane is defined intrinsically by differentials of locally vanishing
functions; `tangentPlane_eq` identifies it with the orthogonal complement of
the gradient of *any* regular defining function. Thus no chosen chart enters
the definitions. A normal field is an ambient function smooth on an open
neighbourhood, with unit length required only on the surface.
-/

noncomputable section
open Set Filter Function InnerProductSpace
open scoped Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

abbrev E₃ := EuclideanSpace ℝ (Fin 3)

/-- The local regular-level-set definition, without a closedness assumption. -/
def IsSmoothEmbeddedSurface (S : Set E₃) : Prop :=
  ∀ p ∈ S, ∃ (U : Set E₃) (φ : E₃ → ℝ), IsOpen U ∧ p ∈ U ∧
    ContDiff ℝ (⊤ : ℕ∞) φ ∧ S ∩ U = {x ∈ U | φ x = 0} ∧
    ∀ x ∈ S ∩ U, gradient φ x ≠ 0

/-- Intrinsic tangent plane: annihilate every locally vanishing differential.
For a regular level chart this is precisely `(ℝ ∙ gradient φ p)ᗮ`. -/
def tangentPlane (S : Set E₃) (p : E₃) : Submodule ℝ E₃ :=
  ⨅ (f : E₃ → ℝ) (_ : DifferentiableAt ℝ f p)
    (_ : ∀ᶠ x in 𝓝[S] p, f x = 0), (fderiv ℝ f p).ker

lemma mem_tangentPlane_iff {S : Set E₃} {p X : E₃} :
    X ∈ tangentPlane S p ↔ ∀ (f : E₃ → ℝ), DifferentiableAt ℝ f p →
      (∀ᶠ x in 𝓝[S] p, f x = 0) → fderiv ℝ f p X = 0 := by
  simp [tangentPlane]

/-- Every regular defining function computes the same tangent plane. -/
theorem tangentPlane_eq {S U : Set E₃} {p : E₃} {φ : E₃ → ℝ}
    (hU : IsOpen U) (hp : p ∈ U) (hφ : ContDiffAt ℝ 1 φ p)
    (hzero : S ∩ U = {x ∈ U | φ x = 0}) (hpS : p ∈ S)
    (hreg : gradient φ p ≠ 0) :
    tangentPlane S p = (ℝ ∙ gradient φ p)ᗮ := by
  have hz : φ p = 0 := (hzero ▸ (show p ∈ S ∩ U from ⟨hpS, hp⟩)).2
  have hnear : ∀ᶠ x in 𝓝[S] p, φ x = 0 := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hp)] with x hx hxU
    exact (hzero ▸ (show x ∈ S ∩ U from ⟨hx, hxU⟩)).2
  have hd := hφ.hasStrictFDerivAt one_ne_zero
  have hrange : (fderiv ℝ φ p).range = ⊤ := by
    apply Module.Dual.range_eq_top_of_ne_zero
    intro hh
    apply hreg
    apply (toDual ℝ E₃).injective
    rw [toDual_gradient, map_zero]
    exact ContinuousLinearMap.ext fun x => congrArg (fun L : E₃ →ₗ[ℝ] ℝ => L x) hh
  let γ := hd.implicitFunction φ (fderiv ℝ φ p) hrange (φ p)
  have hγ : HasFDerivAt γ (fderiv ℝ φ p).ker.subtypeL 0 :=
    (hd.to_implicitFunction hrange).hasFDerivAt
  have hγp : γ 0 = p := hd.implicitFunction_apply_image hrange
  have hγzero : ∀ᶠ v in 𝓝 (0 : (fderiv ℝ φ p).ker), φ (γ v) = 0 := by
    have ht : Tendsto (fun v : (fderiv ℝ φ p).ker => (φ p, v)) (𝓝 0) (𝓝 (φ p, 0)) :=
      tendsto_const_nhds.prodMk_nhds tendsto_id
    simpa only [γ, hz] using ht.eventually (hd.map_implicitFunction_eq hrange)
  have hγS : ∀ᶠ v in 𝓝 (0 : (fderiv ℝ φ p).ker), γ v ∈ S := by
    have hγU := hγ.continuousAt.preimage_mem_nhds (hγp.symm ▸ hU.mem_nhds hp)
    filter_upwards [hγzero, hγU] with v hv hvU
    exact ((congrArg (fun S : Set E₃ => γ v ∈ S) hzero).mpr ⟨hvU, hv⟩).1
  ext X
  rw [mem_tangentPlane_iff, Submodule.mem_orthogonal_singleton_iff_inner_right,
    inner_gradient_left]
  constructor
  · intro hX
    exact hX φ (hφ.differentiableAt one_ne_zero) hnear
  · intro hX f hf hfzero
    have ht : Tendsto γ (𝓝 (0 : (fderiv ℝ φ p).ker)) (𝓝[S] p) :=
      tendsto_nhdsWithin_iff.mpr ⟨by simpa only [hγp] using hγ.continuousAt.tendsto, hγS⟩
    have heq : (fun v => f (γ v)) =ᶠ[𝓝 (0 : (fderiv ℝ φ p).ker)] fun _ => 0 :=
      ht.eventually hfzero
    have hfp : HasFDerivAt f (fderiv ℝ f p) (γ 0) := by
      simpa only [hγp] using hf.hasFDerivAt
    have hdf := hfp.comp 0 hγ
    have heqD := (hdf.congr_of_eventuallyEq heq.symm).fderiv
    have hval := congrArg (fun L => L (⟨X, hX⟩ : (fderiv ℝ φ p).ker)) heqD
    simpa using hval.symm

/-- A smooth ambient extension is part of the normal-field convention. -/
def IsUnitNormalField (S : Set E₃) (n : E₃ → E₃) : Prop :=
  (∃ U : Set E₃, IsOpen U ∧ S ⊆ U ∧ ContDiffOn ℝ (⊤ : ℕ∞) n U) ∧
    ∀ p ∈ S, ‖n p‖ = 1 ∧ ∀ X ∈ tangentPlane S p, inner ℝ (n p) X = 0

/-- One-sided smooth graph charts give regular defining functions for the boundary. -/
theorem HasSmoothBoundary.isSmoothEmbeddedSurface {D : Set E₃}
    (hD : HasSmoothBoundary D) : IsSmoothEmbeddedSurface (frontier D) := by
  intro p hp
  obtain ⟨c, hc, hpc, hheight⟩ := hD p hp
  let ψ : E₃ → ℝ := fun z => c.height (graphProjectionN 2 z) - z (Fin.last 2)
  let φ : E₃ → ℝ := fun z => ψ (c.placement.symm z)
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    (hheight.comp (graphProjectionN 2).contDiff).sub
      (show ContDiff ℝ (⊤ : ℕ∞) (fun z : E₃ => z (Fin.last 2)) from
        (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last 2)).contDiff)
  have ha : ContDiff ℝ (⊤ : ℕ∞) c.placement :=
    c.placement.toAffineIsometry.toContinuousAffineMap.contDiff
  have hai : ContDiff ℝ (⊤ : ℕ∞) c.placement.symm :=
    c.placement.symm.toAffineIsometry.toContinuousAffineMap.contDiff
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hψ.comp hai
  refine ⟨c.region, φ, c.isOpen_region, hpc, hφ, ?_, ?_⟩
  · rw [hc.frontier_inter_eq]
    ext z
    change (z ∈ c.placement '' range (graphMapN c.height) ∧ z ∈ c.region) ↔
      z ∈ c.region ∧ φ z = 0
    constructor
    · rintro ⟨⟨_, ⟨x, rfl⟩, rfl⟩, hz⟩
      refine ⟨hz, ?_⟩
      simp only [φ, c.placement.symm_apply_apply]
      change c.height (graphProjectionN 2 (graphAppendN x (c.height x))) -
        graphAppendN x (c.height x) (Fin.last 2) = 0
      simp only [graphProjectionN_append, graphAppendN_last, sub_self]
    · rintro ⟨hz, hφz⟩
      refine ⟨⟨c.placement.symm z, ⟨graphProjectionN 2 (c.placement.symm z), ?_⟩,
        c.placement.apply_symm_apply z⟩, hz⟩
      have he : c.height (graphProjectionN 2 (c.placement.symm z)) =
          c.placement.symm z (Fin.last 2) := sub_eq_zero.mp hφz
      change graphAppendN _ _ = _
      rw [he, graphAppendN_projection]
  · intro z _ hzero
    have hdf : fderiv ℝ φ z = 0 := by rw [← toDual_gradient, hzero, map_zero]
    have heq : φ ∘ c.placement = ψ := by ext y; simp [φ]
    have hdφ : HasFDerivAt φ (fderiv ℝ φ z) (c.placement (c.placement.symm z)) := by
      rw [c.placement.apply_symm_apply]
      exact (hφ.differentiable (by simp) z).hasFDerivAt
    have hcomp := hdφ.comp (c.placement.symm z) ((ha.differentiable (by simp) _).hasFDerivAt)
    rw [hdf, ContinuousLinearMap.zero_comp, heq] at hcomp
    have hψderiv := (((hheight.differentiable (by simp) _).hasFDerivAt.comp
      (c.placement.symm z) (graphProjectionN 2).hasFDerivAt).sub
        (EuclideanSpace.proj (Fin.last 2)).hasFDerivAt).fderiv
    have he := congrArg (fun L : E₃ →L[ℝ] ℝ => L (EuclideanSpace.single (Fin.last 2) 1))
      (hψderiv.symm.trans hcomp.fderiv)
    have hzproj : graphProjectionN 2 (EuclideanSpace.single (Fin.last 2) 1) = 0 := by
      apply PiLp.ext
      intro i
      rw [graphProjectionN_apply]
      simp only [EuclideanSpace.single, PiLp.single_apply, PiLp.zero_apply,
        ite_eq_right (Fin.castSucc_ne_last i)]
    change fderiv ℝ c.height _
      (graphProjectionN 2 (EuclideanSpace.single (Fin.last 2) 1)) - 1 = 0 at he
    rw [hzproj, map_zero] at he
    norm_num at he

lemma IsSmoothEmbeddedSurface.finrank_tangentPlane {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) {p : E₃} (hp : p ∈ S) :
    Module.finrank ℝ (tangentPlane S p) = 2 := by
  obtain ⟨U, φ, hU, hpU, hφ, hz, hr⟩ := hS p hp
  rw [tangentPlane_eq hU hpU (hφ.of_le (by simp)).contDiffAt hz hp (hr p ⟨hp, hpU⟩)]
  have : Fact (Module.finrank ℝ E₃ = 2 + 1) := ⟨by simp [E₃]⟩
  exact Submodule.finrank_orthogonal_span_singleton (hr p ⟨hp, hpU⟩)

lemma IsUnitNormalField.contDiffAt {S : Set E₃} {n : E₃ → E₃}
    (hn : IsUnitNormalField S n) {p : E₃} (hp : p ∈ S) :
    ContDiffAt ℝ (⊤ : ℕ∞) n p := by
  obtain ⟨U, hU, hSU, hnU⟩ := hn.1
  exact hnU.contDiffAt (hU.mem_nhds (hSU hp))

lemma IsUnitNormalField.tangentPlane_eq {S : Set E₃} {n : E₃ → E₃}
    (hn : IsUnitNormalField S n) (hS : IsSmoothEmbeddedSurface S) {p : E₃} (hp : p ∈ S) :
    tangentPlane S p = (ℝ ∙ n p)ᗮ := by
  apply Submodule.eq_of_le_of_finrank_eq
  · intro X hX
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (hn.2 p hp |>.2 X hX)
  · have hnp : n p ≠ 0 := by
      intro he
      have := (hn.2 p hp).1
      simp [he] at this
    have : Fact (Module.finrank ℝ E₃ = 2 + 1) := ⟨by simp [E₃]⟩
    rw [hS.finrank_tangentPlane hp, Submodule.finrank_orthogonal_span_singleton (n := 2) hnp]

/-- Ambient representatives agreeing on the surface have identical tangent derivatives. -/
theorem fderiv_eq_on_tangentPlane {S : Set E₃} {p X : E₃} {f g : E₃ → E₃}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p)
    (heq : f =ᶠ[𝓝[S] p] g) (hX : X ∈ tangentPlane S p) :
    fderiv ℝ f p X = fderiv ℝ g p X := by
  apply PiLp.ext
  intro i
  have hd := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp p
    (hf.hasFDerivAt.sub hg.hasFDerivAt)
  have hz : ∀ᶠ x in 𝓝[S] p, (f x - g x) i = 0 := by
    filter_upwards [heq] with x hx
    simp [hx]
  have h := (mem_tangentPlane_iff.mp hX) _ hd.differentiableAt hz
  rw [hd.fderiv] at h
  simpa using sub_eq_zero.mp h

/-- The ambient derivative, to be evaluated only on tangent vectors. -/
def shapeOperator (n : E₃ → E₃) (p : E₃) : E₃ →L[ℝ] E₃ := fderiv ℝ n p

/-- Positive-sphere convention: no minus sign precedes the normal derivative. -/
def secondFundamentalForm (n : E₃ → E₃) (p X Y : E₃) : ℝ :=
  inner ℝ (shapeOperator n p X) Y

theorem IsUnitNormalField.shapeOperator_mem {S : Set E₃} {n : E₃ → E₃}
    (hn : IsUnitNormalField S n) (hS : IsSmoothEmbeddedSurface S) {p X : E₃}
    (hp : p ∈ S) (hX : X ∈ tangentPlane S p) :
    shapeOperator n p X ∈ tangentPlane S p := by
  have hd := ((hn.contDiffAt hp).differentiableAt (by simp)).hasFDerivAt
  have hsq := hd.norm_sq.sub_const 1
  have hz : ∀ᶠ x in 𝓝[S] p, ‖n x‖ ^ 2 - 1 = 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp [(hn.2 x hx).1]
  have h := (mem_tangentPlane_iff.mp hX) _ hsq.differentiableAt hz
  rw [hsq.fderiv] at h
  rw [hn.tangentPlane_eq hS hp, Submodule.mem_orthogonal_singleton_iff_inner_right]
  change inner ℝ (n p) (fderiv ℝ n p X) = 0
  simpa using (mul_eq_zero.mp (show 2 * inner ℝ (n p) (fderiv ℝ n p X) = 0 by
    simpa using h)).resolve_left (by norm_num)

/-- Tangential compression. For a smooth unit normal the projection is redundant
on tangent inputs (`IsUnitNormalField.shapeOperator_mem`). -/
def tangentShapeOperator (S : Set E₃) (n : E₃ → E₃) (p : E₃) :
    tangentPlane S p →L[ℝ] tangentPlane S p :=
  (tangentPlane S p).orthogonalProjectionOnto ∘L shapeOperator n p ∘L
    (tangentPlane S p).subtypeL

/-- Intrinsic trace; independent of a basis and of the ambient normal extension. -/
def meanCurvature (S : Set E₃) (n : E₃ → E₃) (p : E₃) : ℝ :=
  LinearMap.trace ℝ (tangentPlane S p) (tangentShapeOperator S n p).toLinearMap

/-- Intrinsic determinant on the two-dimensional tangent plane. -/
def gaussCurvature (S : Set E₃) (n : E₃ → E₃) (p : E₃) : ℝ :=
  LinearMap.det (tangentShapeOperator S n p).toLinearMap

lemma IsUnitNormalField.coe_tangentShapeOperator {S : Set E₃} {n : E₃ → E₃}
    (hn : IsUnitNormalField S n) (hS : IsSmoothEmbeddedSurface S) {p : E₃}
    (hp : p ∈ S) (X : tangentPlane S p) :
    (tangentShapeOperator S n p X : E₃) = shapeOperator n p X := by
  exact (tangentPlane S p).starProjection_eq_self_iff.mpr (hn.shapeOperator_mem hS hp X.property)

theorem tangentShapeOperator_congr {S : Set E₃} {p : E₃} {n m : E₃ → E₃}
    (hn : DifferentiableAt ℝ n p) (hm : DifferentiableAt ℝ m p)
    (heq : n =ᶠ[𝓝[S] p] m) : tangentShapeOperator S n p = tangentShapeOperator S m p := by
  apply ContinuousLinearMap.ext
  intro X
  exact congrArg ((tangentPlane S p).orthogonalProjectionOnto)
    (fderiv_eq_on_tangentPlane hn hm heq X.property)

private lemma contDiff_gradient_surface {φ : E₃ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (gradient φ) :=
  (toDual ℝ E₃).symm.contDiff.comp (hφ.fderiv_right (by simp))

private lemma inner_fderiv_gradient_symm {φ : E₃ → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (p X Y : E₃) :
    inner ℝ (fderiv ℝ (gradient φ) p X) Y =
      inner ℝ (fderiv ℝ (gradient φ) p Y) X := by
  have hdg := ((contDiff_gradient_surface hφ).differentiable (by simp) p).hasFDerivAt
  have hd := (toDual ℝ E₃).toContinuousLinearEquiv.hasFDerivAt.comp p hdg
  have hfun : (toDual ℝ E₃).toContinuousLinearEquiv ∘ gradient φ = fderiv ℝ φ := by
    funext x
    exact toDual_gradient
  rw [hfun] at hd
  have he (v w : E₃) : inner ℝ (fderiv ℝ (gradient φ) p v) w =
      fderiv ℝ (fderiv ℝ φ) p v w := by
    rw [hd.fderiv]
    rfl
  rw [he X Y, he Y X]
  exact hφ.contDiffAt.isSymmSndFDerivAt (by simp) X Y

/-- Symmetry of the second fundamental form on the actual tangent plane. -/
theorem secondFundamentalForm_symm {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n)
    {p X Y : E₃} (hp : p ∈ S) (hX : X ∈ tangentPlane S p) (hY : Y ∈ tangentPlane S p) :
    secondFundamentalForm n p X Y = secondFundamentalForm n p Y X := by
  obtain ⟨U, φ, hU, hpU, hφ, hz, hr⟩ := hS p hp
  let a : E₃ → ℝ := fun x => inner ℝ (n x) (gradient φ x) /
    inner ℝ (gradient φ x) (gradient φ x)
  have hg := contDiff_gradient_surface hφ
  have hng : DifferentiableAt ℝ n p := (hn.contDiffAt hp).differentiableAt (by simp)
  have hgg : DifferentiableAt ℝ (gradient φ) p := hg.differentiable (by simp) p
  have hden : inner ℝ (gradient φ p) (gradient φ p) ≠ 0 :=
    inner_self_ne_zero.mpr (hr p ⟨hp, hpU⟩)
  have hnum : DifferentiableAt ℝ (fun x => inner ℝ (n x) (gradient φ x)) p := hng.inner ℝ hgg
  have hden' : DifferentiableAt ℝ (fun x => inner ℝ (gradient φ x) (gradient φ x)) p :=
    hgg.inner ℝ hgg
  have ha : DifferentiableAt ℝ a p := hnum.mul (hden'.inv hden)
  have heq : n =ᶠ[𝓝[S] p] fun x => a x • gradient φ x := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hpU)] with q hq hqU
    have hT := tangentPlane_eq hU hqU (hφ.of_le (by simp)).contDiffAt hz hq (hr q ⟨hq, hqU⟩)
    have hnspan : n q ∈ ℝ ∙ gradient φ q := by
      rw [← Submodule.orthogonal_orthogonal (ℝ ∙ gradient φ q), ← hT]
      exact (Submodule.mem_orthogonal' _ _).mpr (hn.2 q hq).2
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hnspan
    have hdenq : inner ℝ (gradient φ q) (gradient φ q) ≠ 0 :=
      inner_self_ne_zero.mpr (hr q ⟨hq, hqU⟩)
    dsimp only [a]
    rw [← hb, real_inner_smul_left, mul_div_cancel_right₀ _ hdenq]
  have hT := tangentPlane_eq hU hpU (hφ.of_le (by simp)).contDiffAt hz hp (hr p ⟨hp, hpU⟩)
  have hx : inner ℝ (gradient φ p) X = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hT ▸ hX)
  have hy : inner ℝ (gradient φ p) Y = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hT ▸ hY)
  have hd := (ha.hasFDerivAt.smul hgg.hasFDerivAt).fderiv
  have hform (V W : E₃) (hV : V ∈ tangentPlane S p)
      (hW : inner ℝ (gradient φ p) W = 0) :
      secondFundamentalForm n p V W = a p * inner ℝ (fderiv ℝ (gradient φ) p V) W := by
    unfold secondFundamentalForm shapeOperator
    rw [fderiv_eq_on_tangentPlane hng (ha.smul hgg) heq hV, hd]
    simp [real_inner_smul_left, inner_add_left, hW]
  rw [hform X Y hX hy, hform Y X hY hx, inner_fderiv_gradient_symm hφ p X Y]

private lemma gradient_sphere_defining (R : ℝ) (p : E₃) :
    gradient (fun x : E₃ => ‖x‖ ^ 2 - R ^ 2) p = (2 : ℝ) • p := by
  apply (toDual ℝ E₃).injective
  have hd := ((hasFDerivAt_id (𝕜 := ℝ) p).norm_sq.sub_const (R ^ 2)).fderiv
  simp only [id_eq] at hd
  rw [toDual_gradient, hd]
  ext X
  simp [innerSL_apply_apply]

theorem isSmoothEmbeddedSurface_sphere {R : ℝ} (hR : 0 < R) :
    IsSmoothEmbeddedSurface (Metric.sphere (0 : E₃) R) := by
  intro p hp
  refine ⟨univ, fun x => ‖x‖ ^ 2 - R ^ 2, isOpen_univ, mem_univ p, ?_, ?_, ?_⟩
  · exact ((contDiff_id (𝕜 := ℝ) (E := E₃)).norm_sq (𝕜 := ℝ)).sub contDiff_const
  · ext x
    simp only [inter_univ, mem_ofPred, mem_univ, true_and, Metric.mem_sphere, dist_zero_right]
    constructor
    · intro h; rw [h]; ring
    · intro h
      nlinarith [norm_nonneg x]
  · intro x hx
    rw [gradient_sphere_defining, smul_ne_zero_iff]
    refine ⟨by norm_num, ?_⟩
    intro hz
    have hnorm : ‖x‖ = R := by simpa using hx.1
    simp [hz] at hnorm
    linarith

theorem isUnitNormalField_sphere {R : ℝ} (hR : 0 < R) :
    IsUnitNormalField (Metric.sphere (0 : E₃) R) (fun p => R⁻¹ • p) := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun p : E₃ => R⁻¹ • p) :=
    (contDiff_id (𝕜 := ℝ) (E := E₃)).const_smul R⁻¹
  refine ⟨⟨univ, isOpen_univ, subset_univ _, hs.contDiffOn⟩, ?_⟩
  intro p hp
  have hnorm : ‖p‖ = R := by simpa using hp
  refine ⟨by simp [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le), hnorm, hR.ne'], ?_⟩
  intro X hX
  have hz : ∀ᶠ x in 𝓝[Metric.sphere (0 : E₃) R] p, ‖x‖ ^ 2 - R ^ 2 = 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxR : ‖x‖ = R := by simpa using hx
    rw [hxR, sub_self]
  have hd := (hasFDerivAt_id p).norm_sq.sub_const (R ^ 2)
  have h := (mem_tangentPlane_iff.mp hX) _ hd.differentiableAt hz
  rw [hd.fderiv] at h
  have hinner : inner ℝ p X = 0 := by
    have hh : 2 * inner ℝ p X = 0 := by simpa using h
    linarith
  simp [real_inner_smul_left, hinner]

private lemma tangentShapeOperator_smul_id (S : Set E₃) (p : E₃) (c : ℝ) :
    tangentShapeOperator S (fun x => c • x) p =
      c • ContinuousLinearMap.id ℝ (tangentPlane S p) := by
  apply ContinuousLinearMap.ext
  intro X
  have hd := ((hasFDerivAt_id (𝕜 := ℝ) p).const_smul c).fderiv
  change fderiv ℝ (fun x : E₃ => c • x) p = _ at hd
  simp [tangentShapeOperator, shapeOperator, hd]

/-- The outward normal on a round sphere has positive mean curvature `2 / R`. -/
theorem meanCurvature_sphere {R : ℝ} (hR : 0 < R) {p : E₃}
    (hp : p ∈ Metric.sphere (0 : E₃) R) :
    meanCurvature (Metric.sphere (0 : E₃) R) (fun x => R⁻¹ • x) p = 2 / R ∧
      0 < meanCurvature (Metric.sphere (0 : E₃) R) (fun x => R⁻¹ • x) p := by
  have hdim := (isSmoothEmbeddedSurface_sphere hR).finrank_tangentPlane hp
  have heq : meanCurvature (Metric.sphere (0 : E₃) R) (fun x => R⁻¹ • x) p = 2 / R := by
    simp [meanCurvature, tangentShapeOperator_smul_id, LinearMap.trace_id, hdim, div_eq_mul_inv,
      mul_comm]
  exact ⟨heq, heq ▸ div_pos (by norm_num) hR⟩

end LiquidDrop
