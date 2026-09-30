module

public import NoCompromise.BV.CoareaCoordinates
public import NoCompromise.BV.StrictApprox
public import NoCompromise.Area.C1Graph
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
# Distributional boundary formula for a C¹ subgraph

Vertical graph coordinates reduce compact-test pairings to Fubini and the
one-dimensional fundamental theorem of calculus. The outward normal of a
subgraph points upwards. No global bound on the graph slope is required.
-/

noncomputable section
open MeasureTheory Set Function Topology InnerProductSpace
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The open set lying strictly below a graph. -/
def smoothSubgraph {k : ℕ} (f : EuclideanSpace ℝ (Fin k) → ℝ) :
    Set (EuclideanSpace ℝ (Fin (k + 1))) :=
  {z | z (Fin.last k) < f (graphProjectionN k z)}

lemma isOpen_smoothSubgraph {k : ℕ} {f : EuclideanSpace ℝ (Fin k) → ℝ}
    (hf : Continuous f) : IsOpen (smoothSubgraph f) :=
  isOpen_lt (EuclideanSpace.proj (Fin.last k)).continuous
    (hf.comp (graphProjectionN k).continuous)

/-- A vertical shear gives global coordinates around a continuous graph. -/
def smoothGraphCoordinates {k : ℕ} {f : EuclideanSpace ℝ (Fin k) → ℝ}
    (hf : Continuous f) :
    (EuclideanSpace ℝ (Fin k) × ℝ) ≃ₜ EuclideanSpace ℝ (Fin (k + 1)) where
  toFun p := graphAppendN p.1 (p.2 + f p.1)
  invFun z := (graphProjectionN k z, z (Fin.last k) - f (graphProjectionN k z))
  left_inv p := by ext <;> simp
  right_inv z := by simp
  continuous_toFun := by
    change Continuous (fun p : EuclideanSpace ℝ (Fin k) × ℝ =>
      graphBaseN k p.1 + (p.2 + f p.1) • EuclideanSpace.single (Fin.last k) 1)
    fun_prop
  continuous_invFun := by fun_prop

@[simp] lemma smoothGraphCoordinates_apply {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : Continuous f)
    (p : EuclideanSpace ℝ (Fin k) × ℝ) :
    smoothGraphCoordinates hf p = graphAppendN p.1 (p.2 + f p.1) := rfl

lemma smoothGraphCoordinates_measurePreserving {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : Continuous f) :
    MeasurePreserving (smoothGraphCoordinates hf) (volume.prod volume) volume := by
  have hs : MeasurePreserving
      (fun p : EuclideanSpace ℝ (Fin k) × ℝ => (p.1, p.2 + f p.1))
      (volume.prod volume) (volume.prod volume) :=
    (MeasurePreserving.id volume).skew_product (by fun_prop)
      (Filter.Eventually.of_forall fun x => (measurePreserving_add_right volume (f x)).map_eq)
  exact ((euclideanLastEquiv_measurePreserving k).symm
    (euclideanLastEquiv k).toHomeomorph.toMeasurableEquiv).comp
      (Measure.measurePreserving_swap.comp hs)

lemma smoothGraphCoordinates_preimage_subgraph {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : Continuous f) :
    smoothGraphCoordinates hf ⁻¹' smoothSubgraph f = univ ×ˢ Iio (0 : ℝ) := by
  ext p
  simp [smoothSubgraph]

/-- Fubini in vertical graph coordinates. -/
lemma integral_smoothSubgraph {k : ℕ} {f : EuclideanSpace ℝ (Fin k) → ℝ}
    (hf : Continuous f) {g : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    (hg : Integrable g) :
    ∫ z in smoothSubgraph f, g z =
      ∫ x, ∫ t in Iio (0 : ℝ), g (graphAppendN x (t + f x)) := by
  have hp := (smoothGraphCoordinates_measurePreserving hf).restrict_preimage
    (isOpen_smoothSubgraph hf).measurableSet
  rw [smoothGraphCoordinates_preimage_subgraph] at hp
  rw [← hp.integral_comp (smoothGraphCoordinates hf).measurableEmbedding g]
  have hi : Integrable (g ∘ smoothGraphCoordinates hf) (volume.prod volume) :=
    ((smoothGraphCoordinates_measurePreserving hf).integrable_comp
      hg.aestronglyMeasurable).mpr hg
  exact (setIntegral_prod _ hi.integrableOn).trans (by simp)

/-- A compactly supported scalar derivative has zero integral. -/
lemma integral_compact_scalar_fderiv_eq_zero {k : ℕ}
    {φ : EuclideanSpace ℝ (Fin k) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hcφ : HasCompactSupport φ) (v : EuclideanSpace ℝ (Fin k)) :
    ∫ x, fderiv ℝ φ x v = 0 := by
  have hi : Integrable (fun x => fderiv ℝ φ x v) :=
    ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hcφ.fderiv_apply ℝ v)
  have h := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    (μ := volume) (f := fun _ : EuclideanSpace ℝ (Fin k) => (1 : ℝ)) (g := φ) (v := v)
    (by simp) (by simpa using hi)
    (by simpa using hφ.continuous.integrable_of_hasCompactSupport hcφ)
    (fun _ _ => differentiableAt_const _) (fun x _ => hφ.differentiable one_ne_zero x)
  simpa using h

/-- Smoothness of the vertical graph coordinates. -/
lemma contDiff_smoothGraphCoordinates {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiff ℝ 1 f) :
    ContDiff ℝ 1 (smoothGraphCoordinates hf.continuous) := by
  change ContDiff ℝ 1 (fun p : EuclideanSpace ℝ (Fin k) × ℝ =>
    graphBaseN k p.1 + (p.2 + f p.1) • EuclideanSpace.single (Fin.last k) 1)
  fun_prop

/-- The compact pullback of a test has compact horizontal slices. -/
lemma hasCompactSupport_smoothGraph_horizontal {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : Continuous f)
    {φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ} (hcφ : HasCompactSupport φ) (t : ℝ) :
    HasCompactSupport (fun x => φ (graphAppendN x (t + f x))) := by
  have he : IsClosedEmbedding (fun x : EuclideanSpace ℝ (Fin k) => (x, t)) :=
    .of_isEmbedding_isClosedMap (isEmbedding_prodMkLeft t) (isClosedMap_prodMk_right t)
  have hc : HasCompactSupport (φ ∘ smoothGraphCoordinates hf) :=
    hcφ.comp_homeomorph (smoothGraphCoordinates hf)
  have H : HasCompactSupport ((φ ∘ smoothGraphCoordinates hf) ∘
      (fun x : EuclideanSpace ℝ (Fin k) => (x, t))) := hc.comp_isClosedEmbedding he
  simpa only [Function.comp_def, smoothGraphCoordinates_apply] using H

/-- The compact pullback of a test has compact vertical slices. -/
lemma hasCompactSupport_smoothGraph_vertical {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : Continuous f)
    {φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ} (hcφ : HasCompactSupport φ)
    (x : EuclideanSpace ℝ (Fin k)) :
    HasCompactSupport (fun t => φ (graphAppendN x (t + f x))) := by
  have he : IsClosedEmbedding (fun t : ℝ => (x, t)) :=
    .of_isEmbedding_isClosedMap (isEmbedding_prodMkRight x) (isClosedMap_prodMk_left x)
  have hc : HasCompactSupport (φ ∘ smoothGraphCoordinates hf) :=
    hcφ.comp_homeomorph (smoothGraphCoordinates hf)
  have H : HasCompactSupport ((φ ∘ smoothGraphCoordinates hf) ∘
      (fun t : ℝ => (x, t))) := hc.comp_isClosedEmbedding he
  simpa only [Function.comp_def, smoothGraphCoordinates_apply] using H

/-- The vertical compact fundamental theorem gives the value on the graph. -/
lemma integral_smoothGraph_vertical {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiff ℝ 1 f)
    {φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hcφ : HasCompactSupport φ) (x : EuclideanSpace ℝ (Fin k)) :
    ∫ t in Iio (0 : ℝ),
      fderiv ℝ φ (graphAppendN x (t + f x)) (EuclideanSpace.single (Fin.last k) 1) =
        φ (graphMapN f x) := by
  let ψ : ℝ → ℝ := fun t => φ (graphAppendN x (t + f x))
  have hψ : ContDiff ℝ 1 ψ :=
    (hφ.comp (contDiff_smoothGraphCoordinates hf)).comp (contDiff_const.prodMk contDiff_id)
  have hcψ : HasCompactSupport ψ := hasCompactSupport_smoothGraph_vertical hf.continuous hcφ x
  have hd (t : ℝ) : deriv ψ t =
      fderiv ℝ φ (graphAppendN x (t + f x)) (EuclideanSpace.single (Fin.last k) 1) := by
    have hp : HasDerivAt (fun t : ℝ => graphAppendN x (t + f x))
        (EuclideanSpace.single (Fin.last k) 1) t := by
      simpa [graphAppendN] using
        (((hasDerivAt_id t).add_const (f x)).smul_const
          (EuclideanSpace.single (Fin.last k) (1 : ℝ))).const_add (graphBaseN k x)
    exact ((hφ.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t hp).deriv
  simp_rw [← hd]
  rw [← integral_Iic_eq_integral_Iio, hcψ.integral_Iic_deriv_eq hψ]
  simp [ψ, graphAppendN, graphMapN]

/-- The derivative of a test pulled back by the graph shear. -/
lemma fderiv_smoothGraph_pullback {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiff ℝ 1 f)
    {φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (p w : EuclideanSpace ℝ (Fin k) × ℝ) :
    fderiv ℝ (φ ∘ smoothGraphCoordinates hf.continuous) p w =
      fderiv ℝ φ (smoothGraphCoordinates hf.continuous p)
        (graphBaseN k w.1 + (w.2 + fderiv ℝ f p.1 w.1) •
          EuclideanSpace.single (Fin.last k) 1) := by
  have hd := ((graphBaseN k).hasFDerivAt.comp p hasFDerivAt_fst).add
    ((hasFDerivAt_snd.add ((hf.differentiable one_ne_zero p.1).hasFDerivAt.comp p
      hasFDerivAt_fst)).smul_const (EuclideanSpace.single (Fin.last k) (1 : ℝ)))
  have hh := (hφ.differentiable one_ne_zero
    (smoothGraphCoordinates hf.continuous p)).hasFDerivAt.comp p hd
  exact congrArg (fun L => L w) hh.fderiv

/-- Horizontal derivatives of the pulled-back test integrate to zero below the flat plane. -/
lemma integral_smoothGraph_horizontal {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiff ℝ 1 f)
    {φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hcφ : HasCompactSupport φ) (v : EuclideanSpace ℝ (Fin k)) :
    ∫ x, ∫ t in Iio (0 : ℝ),
      fderiv ℝ (φ ∘ smoothGraphCoordinates hf.continuous) (x, t) (v, 0) = 0 := by
  let ψ := φ ∘ smoothGraphCoordinates hf.continuous
  have hψ : ContDiff ℝ 1 ψ := hφ.comp (contDiff_smoothGraphCoordinates hf)
  have hcψ : HasCompactSupport ψ := hcφ.comp_homeomorph (smoothGraphCoordinates hf.continuous)
  have hi : Integrable (fun p => fderiv ℝ ψ p (v, 0)) (volume.prod volume) :=
    ((hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hcψ.fderiv_apply ℝ (v, 0))
  have hir : Integrable (fun p => fderiv ℝ ψ p (v, 0))
      (volume.prod (volume.restrict (Iio (0 : ℝ)))) := by
    simpa only [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] using
      (hi.integrableOn : IntegrableOn _ (univ ×ˢ Iio (0 : ℝ)) (volume.prod volume))
  rw [integral_integral_swap hir]
  have hzero (t : ℝ) : ∫ x, fderiv ℝ ψ (x, t) (v, 0) = 0 := by
    have hh : ContDiff ℝ 1 (fun x => ψ (x, t)) :=
      hψ.comp (contDiff_id.prodMk contDiff_const)
    have hd (x : EuclideanSpace ℝ (Fin k)) :
        fderiv ℝ (fun y => ψ (y, t)) x v = fderiv ℝ ψ (x, t) (v, 0) := by
      have hpair : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin k) => (y, t))
          ((ContinuousLinearMap.id ℝ _).prod (0 : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ)) x :=
        (hasFDerivAt_id x).prodMk (hasFDerivAt_const t x)
      exact congrArg (fun L => L v)
        (((hψ.differentiable one_ne_zero (x, t)).hasFDerivAt.comp x hpair).fderiv)
    simp_rw [← hd]
    exact integral_compact_scalar_fderiv_eq_zero hh
      (hasCompactSupport_smoothGraph_horizontal hf.continuous hcφ t) v
  change (∫ t in Iio (0 : ℝ), ∫ x, fderiv ℝ ψ (x, t) (v, 0)) = 0
  simp only [hzero, integral_zero]

/-- The full distributional pairing for a C¹ subgraph, with upward outward normal. -/
theorem smoothSubgraph_directional_pairing {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiff ℝ 1 f)
    {φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hcφ : HasCompactSupport φ) (v : EuclideanSpace ℝ (Fin (k + 1))) :
    ∫ z in smoothSubgraph f, fderiv ℝ φ z v =
      ∫ x, φ (graphMapN f x) *
        (v (Fin.last k) - fderiv ℝ f x (graphProjectionN k v)) := by
  let P := smoothGraphCoordinates hf.continuous
  let a : EuclideanSpace ℝ (Fin k) × ℝ → ℝ :=
    fun p => fderiv ℝ (φ ∘ P) p (graphProjectionN k v, 0)
  let b : EuclideanSpace ℝ (Fin k) × ℝ → ℝ :=
    fun p => (v (Fin.last k) - fderiv ℝ f p.1 (graphProjectionN k v)) *
      fderiv ℝ φ (P p) (EuclideanSpace.single (Fin.last k) 1)
  have hψ : ContDiff ℝ 1 (φ ∘ P) := hφ.comp (contDiff_smoothGraphCoordinates hf)
  have hca : HasCompactSupport a :=
    (hcφ.comp_homeomorph P).fderiv_apply ℝ (graphProjectionN k v, 0)
  have hcb : HasCompactSupport b :=
    ((hcφ.fderiv_apply ℝ (EuclideanSpace.single (Fin.last k) 1)).comp_homeomorph P).mul_left
  have hia : Integrable a (volume.prod volume) :=
    ((hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      hca
  have hib : Integrable b (volume.prod volume) := by
    apply Continuous.integrable_of_hasCompactSupport _ hcb
    exact (continuous_const.sub
      (((hf.continuous_fderiv one_ne_zero).comp continuous_fst).clm_apply continuous_const)).mul
        (((hφ.continuous_fderiv one_ne_zero).comp P.continuous).clm_apply continuous_const)
  have hid : Integrable (fun z => fderiv ℝ φ z v) :=
    ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hcφ.fderiv_apply ℝ v)
  have heq (p : EuclideanSpace ℝ (Fin k) × ℝ) :
      fderiv ℝ φ (P p) v = a p + b p := by
    dsimp only [a, b, P]
    rw [fderiv_smoothGraph_pullback hf hφ]
    have hv := congrArg (fderiv ℝ φ (smoothGraphCoordinates hf.continuous p))
      (graphAppendN_projection v)
    simp only [graphAppendN, map_add, map_smul, smul_eq_mul] at hv ⊢
    simp only [zero_add] at *
    linarith
  rw [integral_smoothSubgraph hf.continuous hid]
  change (∫ x, ∫ t in Iio (0 : ℝ), fderiv ℝ φ (P (x, t)) v) = _
  simp_rw [heq]
  have hiar : Integrable a (volume.prod (volume.restrict (Iio (0 : ℝ)))) := by
    simpa only [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] using
      (hia.integrableOn : IntegrableOn a (univ ×ˢ Iio (0 : ℝ)) (volume.prod volume))
  have hibr : Integrable b (volume.prod (volume.restrict (Iio (0 : ℝ)))) := by
    simpa only [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] using
      (hib.integrableOn : IntegrableOn b (univ ×ˢ Iio (0 : ℝ)) (volume.prod volume))
  rw [integral_integral_add hiar hibr,
    integral_smoothGraph_horizontal hf hφ hcφ, zero_add]
  apply integral_congr_ae
  filter_upwards with x
  dsimp only [b, P, smoothGraphCoordinates_apply]
  rw [integral_const_mul, integral_smoothGraph_vertical hf hφ hcφ]
  exact mul_comm _ _

/-- The upward unit normal associated with a graph slope. -/
def smoothGraphUnitNormal {k : ℕ} (p : EuclideanSpace ℝ (Fin k)) :
    EuclideanSpace ℝ (Fin (k + 1)) :=
  (Real.sqrt (1 + ‖p‖ ^ 2))⁻¹ • graphAppendN (-p) 1

lemma norm_smoothGraphUnitNormal {k : ℕ} (p : EuclideanSpace ℝ (Fin k)) :
    ‖smoothGraphUnitNormal p‖ = 1 := by
  have hn : ‖graphAppendN (-p) 1‖ = Real.sqrt (1 + ‖p‖ ^ 2) := by
    apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [norm_sq_graphProjectionN, graphProjectionN_append, graphAppendN_last,
      norm_neg, Real.sq_sqrt (by positivity)]
    ring
  rw [smoothGraphUnitNormal, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), hn]
  exact inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.2 (by positivity)))

lemma continuous_smoothGraphUnitNormal (k : ℕ) :
    Continuous (@smoothGraphUnitNormal k) := by
  unfold smoothGraphUnitNormal
  have h₁ : Continuous (fun p : EuclideanSpace ℝ (Fin k) => (Real.sqrt (1 + ‖p‖ ^ 2))⁻¹) :=
    (Real.continuous_sqrt.comp (continuous_const.add (continuous_norm.pow 2))).inv₀
      (fun p : EuclideanSpace ℝ (Fin k) =>
        ne_of_gt (Real.sqrt_pos.2 (show 0 < 1 + ‖p‖ ^ 2 by positivity)))
  have h₂ : Continuous (fun p : EuclideanSpace ℝ (Fin k) => graphAppendN (-p) 1) := by
    unfold graphAppendN
    fun_prop
  exact h₁.smul h₂

lemma inner_smoothGraphUnitNormal {k : ℕ} (p : EuclideanSpace ℝ (Fin k))
    (v : EuclideanSpace ℝ (Fin (k + 1))) :
    Real.sqrt (1 + ‖p‖ ^ 2) * inner ℝ v (smoothGraphUnitNormal p) =
      v (Fin.last k) - inner ℝ p (graphProjectionN k v) := by
  rw [smoothGraphUnitNormal, inner_smul_right, inner_graphAppendN, inner_neg_right,
    mul_one, real_inner_comm (graphProjectionN k v) p]
  have hs : Real.sqrt (1 + ‖p‖ ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  field_simp
  ring

/-- A continuous graph is a closed embedding, without a uniform slope bound. -/
lemma isClosedEmbedding_smoothGraphMap {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : Continuous f) :
    IsClosedEmbedding (graphMapN f) := by
  have he : IsClosedEmbedding (fun x : EuclideanSpace ℝ (Fin k) => (x, (0 : ℝ))) :=
    .of_isEmbedding_isClosedMap (isEmbedding_prodMkLeft 0) (isClosedMap_prodMk_right 0)
  have h := (smoothGraphCoordinates hf).isClosedEmbedding.comp he
  simpa only [Function.comp_def, smoothGraphCoordinates_apply, zero_add, graphAppendN, graphMapN]
    using! h

/-- Surface area on the complete C¹ graph. -/
def smoothGraphArea {k : ℕ} (f : EuclideanSpace ℝ (Fin k) → ℝ) :
    Measure (EuclideanSpace ℝ (Fin (k + 1))) :=
  (Measure.euclideanHausdorffMeasure k).restrict (range (graphMapN f))

lemma smoothGraphArea_eq_map {k : ℕ} {f : EuclideanSpace ℝ (Fin k) → ℝ}
    (hf : ContDiff ℝ 1 f) : smoothGraphArea f =
      Measure.map (graphMapN f)
        (volume.withDensity (fun x => ENNReal.ofReal (Real.sqrt (1 + ‖gradient f x‖ ^ 2)))) := by
  simpa only [Measure.restrict_univ, image_univ, smoothGraphArea] using
    (c1_graph_map_withDensity_sqrt isOpen_univ hf.contDiffOn MeasurableSet.univ
      (subset_refl univ)).symm

lemma smoothGraphArea_finiteOnCompacts {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiff ℝ 1 f) :
    IsFiniteMeasureOnCompacts (smoothGraphArea f) := by
  let μ := volume.withDensity (fun x => ENNReal.ofReal (Real.sqrt (1 + ‖gradient f x‖ ^ 2)))
  have hc : Continuous (fun x => Real.sqrt (1 + ‖gradient f x‖ ^ 2)) := by
    exact Real.continuous_sqrt.comp
      (continuous_const.add ((continuous_gradient_of_contDiff hf).norm.pow 2))
  let : IsLocallyFiniteMeasure μ := IsLocallyFiniteMeasure.withDensity_ofReal hc
  refine ⟨fun K hK => ?_⟩
  rw [smoothGraphArea_eq_map hf, Measure.map_apply
    (isClosedEmbedding_smoothGraphMap hf.continuous).continuous.measurable hK.measurableSet]
  exact ((isClosedEmbedding_smoothGraphMap hf.continuous).isProperMap.isCompact_preimage
    hK).measure_lt_top

/-- Signed weighted graph area, valid without an integrability side condition. -/
lemma integral_smoothGraphArea {k : ℕ} {f : EuclideanSpace ℝ (Fin k) → ℝ}
    (hf : ContDiff ℝ 1 f) (g : EuclideanSpace ℝ (Fin (k + 1)) → ℝ) :
    ∫ z, g z ∂smoothGraphArea f =
      ∫ x, Real.sqrt (1 + ‖gradient f x‖ ^ 2) * g (graphMapN f x) := by
  rw [smoothGraphArea_eq_map hf, (isClosedEmbedding_smoothGraphMap hf.continuous).integral_map]
  have hc : Continuous (fun x => Real.sqrt (1 + ‖gradient f x‖ ^ 2)) :=
    Real.continuous_sqrt.comp
      (continuous_const.add ((continuous_gradient_of_contDiff hf).norm.pow 2))
  rw [integral_withDensity_eq_integral_toReal_smul hc.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (Real.sqrt_nonneg _), smul_eq_mul]

/-- The directional boundary formula expressed using normalized Hausdorff surface area. -/
theorem smoothSubgraph_directional_pairing_surface {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiff ℝ 1 f)
    {φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hcφ : HasCompactSupport φ) (v : EuclideanSpace ℝ (Fin (k + 1))) :
    ∫ z in smoothSubgraph f, fderiv ℝ φ z v =
      ∫ z, φ z * inner ℝ v (smoothGraphUnitNormal (gradient f (graphProjectionN k z)))
        ∂smoothGraphArea f := by
  rw [smoothSubgraph_directional_pairing hf hφ hcφ, integral_smoothGraphArea hf]
  apply integral_congr_ae
  filter_upwards with x
  have hp : graphProjectionN k (graphMapN f x) = x := by
    change graphProjectionN k (graphAppendN x (f x)) = x
    simp
  rw [hp, ← mul_assoc, mul_comm _ (φ (graphMapN f x)), mul_assoc,
    inner_smoothGraphUnitNormal, inner_gradient_left]

/-- The outward normal is extended constantly along vertical lines. -/
def smoothSubgraphNormal {k : ℕ} (f : EuclideanSpace ℝ (Fin k) → ℝ)
    (z : EuclideanSpace ℝ (Fin (k + 1))) : EuclideanSpace ℝ (Fin (k + 1)) :=
  smoothGraphUnitNormal (gradient f (graphProjectionN k z))

lemma continuous_smoothSubgraphNormal {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (smoothSubgraphNormal f) :=
  (continuous_smoothGraphUnitNormal k).comp
    ((continuous_gradient_of_contDiff hf).comp (graphProjectionN k).continuous)

lemma smoothGraphArea_regular {k : ℕ} {f : EuclideanSpace ℝ (Fin k) → ℝ}
    (hf : ContDiff ℝ 1 f) : (smoothGraphArea f).Regular := by
  let := smoothGraphArea_finiteOnCompacts hf
  infer_instance

/-- The actual signed distributional derivative of the subgraph indicator. -/
theorem smoothSubgraph_distributionalPolar {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiff ℝ 1 f) :
    IsDistributionalPolarRepresentation ((smoothSubgraph f).indicator (fun _ => (1 : ℝ))) univ
      (Measure.map (Homeomorph.Set.univ (EuclideanSpace ℝ (Fin (k + 1)))).symm
        (smoothGraphArea f))
      (fun z => -smoothSubgraphNormal f z) := by
  refine ⟨(continuous_smoothSubgraphNormal hf).measurable.comp measurable_subtype_coe |>.neg,
    Filter.Eventually.of_forall (fun z => ?_), ?_⟩
  · exact (norm_neg _).trans (norm_smoothGraphUnitNormal _)
  · intro i φ hφ _
    rw [Measure.restrict_univ,
      (Homeomorph.Set.univ (EuclideanSpace ℝ (Fin (k + 1)))).symm.measurableEmbedding.integral_map]
    have heq : (fun x => (smoothSubgraph f).indicator (fun _ => (1 : ℝ)) x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        (smoothSubgraph f).indicator (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
      funext x
      by_cases hx : x ∈ smoothSubgraph f <;> simp [hx]
    rw [heq, integral_indicator (isOpen_smoothSubgraph hf.continuous).measurableSet,
      smoothSubgraph_directional_pairing_surface hf hφ φ.hasCompactSupport]
    simp only [EuclideanSpace.inner_single_left, map_one, one_mul, PiLp.neg_apply,
      smoothSubgraphNormal, mul_neg, integral_neg]
    rfl

/-- The defining BV perimeter equals Hausdorff graph area on every open region. -/
theorem perimeterIn_smoothSubgraph {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiff ℝ 1 f)
    {O : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hO : IsOpen O) :
    perimeterIn (smoothSubgraph f) O = smoothGraphArea f O := by
  let e := Homeomorph.Set.univ (EuclideanSpace ℝ (Fin (k + 1)))
  let := smoothGraphArea_regular hf
  let ρ := Measure.map e.symm (smoothGraphArea f)
  let : ρ.Regular := Measure.Regular.map e.symm
  have h := (smoothSubgraph_distributionalPolar hf).variation_eq_measure isOpen_univ hO
    (subset_univ O) ((locallyIntegrable_indicator_one
      (isOpen_smoothSubgraph hf.continuous).measurableSet.nullMeasurableSet).locallyIntegrableOn
        univ)
  change perimeterIn (smoothSubgraph f) O = ρ (Subtype.val ⁻¹' O) at h
  rw [show ρ = Measure.map e.symm (smoothGraphArea f) from rfl,
    Measure.map_apply e.symm.continuous.measurable
      (hO.measurableSet.preimage measurable_subtype_coe)] at h
  exact h

theorem hasLocallyFinitePerimeter_smoothSubgraph {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiff ℝ 1 f) :
    HasLocallyFinitePerimeter (smoothSubgraph f) := by
  let := smoothGraphArea_finiteOnCompacts hf
  intro O hO hcO
  rw [perimeterIn_smoothSubgraph hf hO]
  exact (measure_mono subset_closure).trans_lt hcO.measure_lt_top

/-- Compact vector fields satisfy the classical divergence theorem on a C¹ subgraph. -/
theorem smoothSubgraph_divergence {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiff ℝ 1 f)
    {X : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) :
    (∫ z in smoothSubgraph f, divergenceN X z) =
      ∫ z, inner ℝ (X z) (smoothSubgraphNormal f z) ∂smoothGraphArea f := by
  let e := Homeomorph.Set.univ (EuclideanSpace ℝ (Fin (k + 1)))
  let := smoothGraphArea_regular hf
  let ρ := Measure.map e.symm (smoothGraphArea f)
  let : ρ.Regular := Measure.Regular.map e.symm
  have h := (smoothSubgraph_distributionalPolar hf).integral_divergence_eq
    ((locallyIntegrable_indicator_one
      (isOpen_smoothSubgraph hf.continuous).measurableSet.nullMeasurableSet).locallyIntegrableOn
        univ)
    hX hcX (subset_univ _)
  rw [Measure.restrict_univ, e.symm.measurableEmbedding.integral_map] at h
  have heq : (fun z => (smoothSubgraph f).indicator (fun _ => (1 : ℝ)) z * divergenceN X z) =
      (smoothSubgraph f).indicator (divergenceN X) := by
    funext z
    by_cases hz : z ∈ smoothSubgraph f <;> simp [hz]
  simpa only [heq, integral_indicator (isOpen_smoothSubgraph hf.continuous).measurableSet,
    inner_neg_right, integral_neg, neg_inj] using! h

lemma frontier_smoothSubgraph {k : ℕ} {f : EuclideanSpace ℝ (Fin k) → ℝ}
    (hf : Continuous f) : frontier (smoothSubgraph f) = range (graphMapN f) := by
  let P := smoothGraphCoordinates hf
  have hpre := smoothGraphCoordinates_preimage_subgraph hf
  have him : P '' (univ ×ˢ Iio (0 : ℝ)) = smoothSubgraph f := by
    rw [← hpre]
    exact P.surjective.image_preimage _
  rw [← him, ← P.image_frontier, frontier_univ_prod_eq, frontier_Iio]
  ext z
  constructor
  · rintro ⟨⟨x, t⟩, ⟨_, ht⟩, rfl⟩
    have ht0 : t = 0 := mem_singleton_iff.mp ht
    subst t
    exact ⟨x, by simp [P, graphAppendN, graphMapN]⟩
  · rintro ⟨x, rfl⟩
    exact ⟨(x, 0), ⟨mem_univ _, mem_singleton _⟩, by simp [P, graphAppendN, graphMapN]⟩

/-- The local smooth-perimeter formula, including regions of infinite area. -/
theorem perimeterIn_smoothSubgraph_frontier {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiff ℝ 1 f)
    {O : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hO : IsOpen O) :
    perimeterIn (smoothSubgraph f) O =
      Measure.euclideanHausdorffMeasure k (O ∩ frontier (smoothSubgraph f)) := by
  rw [perimeterIn_smoothSubgraph hf hO, smoothGraphArea,
    Measure.restrict_apply hO.measurableSet, frontier_smoothSubgraph hf.continuous]

/-- A set which agrees almost everywhere with a graph domain in an open region
has the same local graph perimeter there. -/
theorem perimeterIn_eq_smoothGraphArea_of_ae_eq {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiff ℝ 1 f)
    {E O : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hO : IsOpen O)
    (hE : E =ᵐ[volume.restrict O] smoothSubgraph f) :
    perimeterIn E O = smoothGraphArea f O :=
  (perimeterIn_congr_ae O hE).trans (perimeterIn_smoothSubgraph hf hO)

/-- Graphs have zero ambient volume; surface area is a different measure. -/
lemma volume_range_smoothGraph {k : ℕ} {f : EuclideanSpace ℝ (Fin k) → ℝ}
    (hf : Continuous f) : volume (range (graphMapN f)) = 0 := by
  let P := smoothGraphCoordinates hf
  have hpre : P ⁻¹' range (graphMapN f) = univ ×ˢ ({0} : Set ℝ) := by
    ext p
    constructor
    · rintro ⟨x, hx⟩
      have hx' := congrArg (graphProjectionN k) hx
      have hp : x = p.1 := by
        change graphProjectionN k (graphAppendN x (f x)) =
          graphProjectionN k (graphAppendN p.1 (p.2 + f p.1)) at hx'
        simpa only [graphProjectionN_append] using hx'
      have ht := congrArg (fun z : EuclideanSpace ℝ (Fin (k + 1)) => z (Fin.last k)) hx
      simp only [graphMapN_last, P, smoothGraphCoordinates_apply, graphAppendN_last, hp] at ht
      exact ⟨mem_univ _, by simpa only [mem_singleton_iff] using (show p.2 = 0 by linarith)⟩
    · rintro ⟨_, hp⟩
      refine ⟨p.1, ?_⟩
      simp only [mem_singleton_iff] at hp
      simp [P, hp, graphMapN, graphAppendN]
  have h := (smoothGraphCoordinates_measurePreserving hf).measure_preimage
    (isClosedEmbedding_smoothGraphMap hf).isClosed_range.measurableSet.nullMeasurableSet
  rw [show smoothGraphCoordinates hf ⁻¹' range (graphMapN f) = univ ×ˢ ({0} : Set ℝ) from hpre] at h
  simpa only [Measure.prod_prod, measure_singleton, mul_zero] using h.symm

/-- The open upper graph domain. -/
def smoothEpigraph {k : ℕ} (f : EuclideanSpace ℝ (Fin k) → ℝ) :
    Set (EuclideanSpace ℝ (Fin (k + 1))) :=
  {z | f (graphProjectionN k z) < z (Fin.last k)}

lemma smoothEpigraph_ae_compl {k : ℕ} {f : EuclideanSpace ℝ (Fin k) → ℝ}
    (hf : Continuous f) : smoothEpigraph f =ᵐ[volume] (smoothSubgraph f)ᶜ := by
  have hae : ∀ᵐ z ∂volume, z ∉ range (graphMapN f) := by
    rw [ae_iff]
    simpa using! volume_range_smoothGraph hf
  filter_upwards [hae] with z hz
  have hne : f (graphProjectionN k z) ≠ z (Fin.last k) := by
    intro he
    apply hz
    refine ⟨graphProjectionN k z, ?_⟩
    change graphAppendN (graphProjectionN k z) (f (graphProjectionN k z)) = z
    rw [he, graphAppendN_projection]
  apply propext
  change (f (graphProjectionN k z) < z (Fin.last k)) ↔ ¬ z (Fin.last k) < f (graphProjectionN k z)
  rw [not_lt]
  exact lt_iff_le_and_ne.trans (and_iff_left hne)

/-- The upper graph domain has the same unsigned perimeter as the lower one. -/
theorem perimeterIn_smoothEpigraph {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiff ℝ 1 f)
    {O : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hO : IsOpen O) :
    perimeterIn (smoothEpigraph f) O = smoothGraphArea f O := by
  exact (perimeterIn_congr_ae O (ae_restrict_of_ae (smoothEpigraph_ae_compl hf.continuous))).trans
    ((perimeterIn_compl
      (isOpen_smoothSubgraph hf.continuous).measurableSet.nullMeasurableSet hO).trans
      (perimeterIn_smoothSubgraph hf hO))

/-- The upper graph domain has the downward outward normal. -/
theorem smoothEpigraph_divergence {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiff ℝ 1 f)
    {X : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) :
    (∫ z in smoothEpigraph f, divergenceN X z) =
      ∫ z, inner ℝ (X z) (-smoothSubgraphNormal f z) ∂smoothGraphArea f := by
  calc
    _ = ∫ z in (smoothSubgraph f)ᶜ, divergenceN X z :=
      setIntegral_congr_set (smoothEpigraph_ae_compl hf.continuous)
    _ = _ := by
      rw [setIntegral_compl (isOpen_smoothSubgraph hf.continuous).measurableSet
      (integrable_divergenceN hX hcX), integral_divergenceN_eq_zero hX hcX,
        zero_sub, smoothSubgraph_divergence hf hX hcX]
      simp only [inner_neg_right, integral_neg]

/-- A C¹ height on an open base has a global C¹ replacement near any compact subset. -/
lemma exists_contDiff_height_eq_near_compact {k : ℕ}
    {U K : Set (EuclideanSpace ℝ (Fin k))} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiffOn ℝ 1 f U) :
    ∃ g : EuclideanSpace ℝ (Fin k) → ℝ, ContDiff ℝ 1 g ∧
      ∀ x ∈ K, g =ᶠ[𝓝 x] f := by
  obtain ⟨ζ, hζ, _, hsζ, hζone, _⟩ := exists_smooth_cutoff_one_near_compact hK hU hKU
  refine ⟨fun x => f x * ζ x, ?_, ?_⟩
  · exact contDiff_smul_of_tsupport_subset hU hf (hζ.of_le (by simp)) hsζ
  · intro x hx
    have hz := hζone.filter_mono (nhds_le_nhdsSet hx)
    filter_upwards [hz] with y hy
    simp [hy]

/-- The local graph-domain formula requires C¹ regularity only over the open
base containing the projection of the compact test support. -/
theorem smoothGraph_local_directional_pairing {k : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin k))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiffOn ℝ 1 f U)
    {E : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hE : MeasurableSet E)
    {φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hcφ : HasCompactSupport φ) (hsφ : graphProjectionN k '' tsupport φ ⊆ U)
    (hgraph : ∀ z ∈ tsupport φ, z ∈ E ↔ z (Fin.last k) < f (graphProjectionN k z))
    (v : EuclideanSpace ℝ (Fin (k + 1))) :
    ∫ z in E, fderiv ℝ φ z v =
      ∫ x, φ (graphMapN f x) *
        (v (Fin.last k) - fderiv ℝ f x (graphProjectionN k v)) := by
  classical
  let K := graphProjectionN k '' tsupport φ
  obtain ⟨g, hg, hgf⟩ := exists_contDiff_height_eq_near_compact hU
    (hcφ.image (graphProjectionN k).continuous) hsφ hf
  have hi : (∫ z in E, fderiv ℝ φ z v) =
      ∫ z in smoothSubgraph g, fderiv ℝ φ z v := by
    rw [← integral_indicator hE,
      ← integral_indicator (isOpen_smoothSubgraph hg.continuous).measurableSet]
    apply integral_congr_ae
    filter_upwards with z
    change E.indicator (fun z => fderiv ℝ φ z v) z =
      (smoothSubgraph g).indicator (fun z => fderiv ℝ φ z v) z
    by_cases hz : z ∈ tsupport φ
    · have hK : graphProjectionN k z ∈ K := mem_image_of_mem _ hz
      have hval := (hgf _ hK).self_of_nhds
      have heq : z ∈ E ↔ z ∈ smoothSubgraph g := by
        rw [hgraph z hz]
        change (z (Fin.last k) < f (graphProjectionN k z)) ↔
          z (Fin.last k) < g (graphProjectionN k z)
        rw [hval]
      simp only [indicator_apply, heq]
    · simp [indicator_apply, fderiv_of_notMem_tsupport ℝ hz]
  rw [hi, smoothSubgraph_directional_pairing hg hφ hcφ]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ K
  · have heq : graphMapN g x = graphMapN f x := by
      simp only [graphMapN, (hgf x hx).self_of_nhds]
    rw [heq, (hgf x hx).fderiv_eq]
  · have hz (q : EuclideanSpace ℝ (Fin k) → ℝ) : φ (graphMapN q x) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro h
      apply hx
      refine ⟨graphMapN q x, h, ?_⟩
      change graphProjectionN k (graphAppendN x (q x)) = x
      exact graphProjectionN_append x (q x)
    rw [hz g, hz f, zero_mul, zero_mul]

/-- The graph divergence formula written entirely in base coordinates. -/
theorem smoothSubgraph_divergence_base {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiff ℝ 1 f)
    {X : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) :
    (∫ z in smoothSubgraph f, divergenceN X z) =
      ∫ x, (X (graphMapN f x)) (Fin.last k) -
        inner ℝ (gradient f x) (graphProjectionN k (X (graphMapN f x))) := by
  rw [smoothSubgraph_divergence hf hX hcX, integral_smoothGraphArea hf]
  apply integral_congr_ae
  filter_upwards with x
  have hp : graphProjectionN k (graphMapN f x) = x := graphProjectionN_append x (f x)
  simp only [smoothSubgraphNormal, hp, inner_smoothGraphUnitNormal]

/-- Fubini and FTC give the divergence theorem in a genuine local C¹ graph chart. -/
theorem smoothGraph_local_divergence {k : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin k))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiffOn ℝ 1 f U)
    {E : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hE : MeasurableSet E)
    {X : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X)
    (hsX : graphProjectionN k '' tsupport X ⊆ U)
    (hgraph : ∀ z ∈ tsupport X, z ∈ E ↔ z (Fin.last k) < f (graphProjectionN k z)) :
    (∫ z in E, divergenceN X z) =
      ∫ x, (X (graphMapN f x)) (Fin.last k) -
        inner ℝ (gradient f x) (graphProjectionN k (X (graphMapN f x))) := by
  classical
  let K := graphProjectionN k '' tsupport X
  obtain ⟨g, hg, hgf⟩ := exists_contDiff_height_eq_near_compact hU
    (hcX.image (graphProjectionN k).continuous) hsX hf
  have hi : (∫ z in E, divergenceN X z) = ∫ z in smoothSubgraph g, divergenceN X z := by
    rw [← integral_indicator hE,
      ← integral_indicator (isOpen_smoothSubgraph hg.continuous).measurableSet]
    apply integral_congr_ae
    filter_upwards with z
    change E.indicator (divergenceN X) z = (smoothSubgraph g).indicator (divergenceN X) z
    by_cases hz : z ∈ tsupport X
    · have hK : graphProjectionN k z ∈ K := mem_image_of_mem _ hz
      have hval := (hgf _ hK).self_of_nhds
      have heq : z ∈ E ↔ z ∈ smoothSubgraph g := by
        rw [hgraph z hz]
        change (z (Fin.last k) < f (graphProjectionN k z)) ↔
          z (Fin.last k) < g (graphProjectionN k z)
        rw [hval]
      simp only [indicator_apply, heq]
    · simp [indicator_apply, divergenceN_eq_zero_of_notMem_tsupport hz]
  rw [hi, smoothSubgraph_divergence_base hg hX hcX]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ K
  · have heq : graphMapN g x = graphMapN f x := by
      simp only [graphMapN, (hgf x hx).self_of_nhds]
    rw [heq, (hgf x hx).gradient_eq]
  · have hz (q : EuclideanSpace ℝ (Fin k) → ℝ) : X (graphMapN q x) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro h
      apply hx
      exact ⟨graphMapN q x, h, graphProjectionN_append x (q x)⟩
    simp only [hz g, hz f, PiLp.zero_apply, map_zero, inner_zero_right, sub_zero]

end LiquidDrop
