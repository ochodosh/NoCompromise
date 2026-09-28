import NoCompromise.Area.Cofactor
import NoCompromise.Area.Formula
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Euclidean Lipschitz graphs

The graph map retains the two base coordinates. Its tangent map, Gram Jacobian,
and upward unit normal are computed at differentiability points; the corresponding
almost-everywhere formulas use Rademacher's theorem. The planar-source area formula
then gives normalized Hausdorff area and its weighted pushforward on every Borel
graph patch.
-/

noncomputable section

open MeasureTheory Filter Set Metric InnerProductSpace
open scoped NNReal ENNReal Topology Gradient

namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- Inclusion of the horizontal Euclidean plane into three-dimensional space. -/
def graphBaseEmbedding : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.proj 0).smulRight (EuclideanSpace.single 0 1) +
    (EuclideanSpace.proj 1).smulRight (EuclideanSpace.single 1 1)

@[simp] lemma graphBaseEmbedding_apply_zero (x : EuclideanSpace ℝ (Fin 2)) :
    graphBaseEmbedding x 0 = x 0 := by simp [graphBaseEmbedding]

@[simp] lemma graphBaseEmbedding_apply_one (x : EuclideanSpace ℝ (Fin 2)) :
    graphBaseEmbedding x 1 = x 1 := by simp [graphBaseEmbedding]

@[simp] lemma graphBaseEmbedding_apply_two (x : EuclideanSpace ℝ (Fin 2)) :
    graphBaseEmbedding x 2 = 0 := by simp [graphBaseEmbedding]

lemma norm_graphBaseEmbedding (x : EuclideanSpace ℝ (Fin 2)) : ‖graphBaseEmbedding x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, Fin.sum_univ_two]

/-- The standard graph map `x ↦ (x₀,x₁,f x)`. -/
def graphMap (f : EuclideanSpace ℝ (Fin 2) → ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 3) :=
  graphBaseEmbedding x + f x • EuclideanSpace.single 2 1

@[simp] lemma graphMap_apply_zero (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) : graphMap f x 0 = x 0 := by simp [graphMap]

@[simp] lemma graphMap_apply_one (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) : graphMap f x 1 = x 1 := by simp [graphMap]

@[simp] lemma graphMap_apply_two (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) : graphMap f x 2 = f x := by simp [graphMap]

/-- The graph map is injective, with no regularity premise on the height function. -/
lemma graphMap_injective (f : EuclideanSpace ℝ (Fin 2) → ℝ) : Function.Injective (graphMap f) := by
  intro x y hxy
  apply PiLp.ext
  intro i
  fin_cases i
  · simpa using congrArg (fun z : EuclideanSpace ℝ (Fin 3) => z 0) hxy
  · simpa using congrArg (fun z : EuclideanSpace ℝ (Fin 3) => z 1) hxy

/-- Exact Euclidean distance identity for the graph map. -/
lemma norm_graphMap_sub_sq (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (x y : EuclideanSpace ℝ (Fin 2)) :
    ‖graphMap f x - graphMap f y‖ ^ 2 = ‖x - y‖ ^ 2 + ‖f x - f y‖ ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, Fin.sum_univ_two,
    Real.norm_eq_abs, sq_abs]

/-- A global Lipschitz height function has a global Lipschitz graph map. -/
lemma lipschitzWith_graphMap {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) : LipschitzWith (1 + K) (graphMap f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, NNReal.coe_add, NNReal.coe_one]
  have hbound : ‖graphMap f x - graphMap f y‖ ≤ ‖x - y‖ + ‖f x - f y‖ := by
    have heq := norm_graphMap_sub_sq f x y
    have hprod := mul_nonneg (norm_nonneg (x - y)) (norm_nonneg (f x - f y))
    nlinarith [norm_nonneg (graphMap f x - graphMap f y), norm_nonneg (x - y),
      norm_nonneg (f x - f y)]
  have hheight := hf.norm_sub_le x y
  nlinarith

/-- Projection back to the base gives the lower Lipschitz bound with constant one. -/
lemma antilipschitzWith_graphMap (f : EuclideanSpace ℝ (Fin 2) → ℝ) :
    AntilipschitzWith 1 (graphMap f) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have heq := norm_graphMap_sub_sq f x y
  nlinarith [sq_nonneg ‖f x - f y‖, norm_nonneg (x - y),
    norm_nonneg (graphMap f x - graphMap f y)]

/-- Lipschitz graphs are closed embeddings of their base plane. -/
lemma isClosedEmbedding_graphMap {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) : Topology.IsClosedEmbedding (graphMap f) :=
  (antilipschitzWith_graphMap f).isClosedEmbedding (lipschitzWith_graphMap hf).uniformContinuous

lemma measurableEmbedding_graphMap {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) : MeasurableEmbedding (graphMap f) :=
  (isClosedEmbedding_graphMap hf).measurableEmbedding

/-- The graph above a Borel base set is a Borel subset of three-dimensional space. -/
lemma measurableSet_graphMap_image {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {G : Set (EuclideanSpace ℝ (Fin 2))} (hG : MeasurableSet G) :
    MeasurableSet (graphMap f '' G) :=
  (measurableEmbedding_graphMap hf).measurableSet_image' hG

/-- The tangent graph map with slope vector `p`. -/
def graphTangentMap (p : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  graphBaseEmbedding + (innerSL ℝ p).smulRight (EuclideanSpace.single 2 1)

@[simp] lemma graphTangentMap_apply_zero (p v : EuclideanSpace ℝ (Fin 2)) :
    graphTangentMap p v 0 = v 0 := by simp [graphTangentMap]

@[simp] lemma graphTangentMap_apply_one (p v : EuclideanSpace ℝ (Fin 2)) :
    graphTangentMap p v 1 = v 1 := by simp [graphTangentMap]

@[simp] lemma graphTangentMap_apply_two (p v : EuclideanSpace ℝ (Fin 2)) :
    graphTangentMap p v 2 = inner ℝ p v := by simp [graphTangentMap]

lemma graphTangentMap_injective (p : EuclideanSpace ℝ (Fin 2)) :
    Function.Injective (graphTangentMap p) := by
  intro x y hxy
  apply PiLp.ext
  intro i
  fin_cases i
  · simpa using congrArg (fun z : EuclideanSpace ℝ (Fin 3) => z 0) hxy
  · simpa using congrArg (fun z : EuclideanSpace ℝ (Fin 3) => z 1) hxy

/-- Exact graph derivative at a differentiability point of the height function. -/
lemma hasFDerivAt_graphMap {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    {x : EuclideanSpace ℝ (Fin 2)} (hf : DifferentiableAt ℝ f x) :
    HasFDerivAt (graphMap f) (graphTangentMap (gradient f x)) x := by
  have heq : fderiv ℝ f x = innerSL ℝ (gradient f x) := by
    ext v
    exact inner_gradient_left.symm
  have hdf := hf.hasFDerivAt
  rw [heq] at hdf
  exact graphBaseEmbedding.hasFDerivAt.add (hdf.smul_const (EuclideanSpace.single 2 1))

lemma fderiv_graphMap {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    {x : EuclideanSpace ℝ (Fin 2)} (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ (graphMap f) x = graphTangentMap (gradient f x) :=
  (hasFDerivAt_graphMap hf).fderiv

/-- The non-normalized upward normal to a graph tangent plane. -/
def graphNormalVector (p : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 3) :=
  -graphBaseEmbedding p + EuclideanSpace.single 2 1

@[simp] lemma graphNormalVector_apply_zero (p : EuclideanSpace ℝ (Fin 2)) :
    graphNormalVector p 0 = -p 0 := by simp [graphNormalVector]

@[simp] lemma graphNormalVector_apply_one (p : EuclideanSpace ℝ (Fin 2)) :
    graphNormalVector p 1 = -p 1 := by simp [graphNormalVector]

@[simp] lemma graphNormalVector_apply_two (p : EuclideanSpace ℝ (Fin 2)) :
    graphNormalVector p 2 = 1 := by simp [graphNormalVector]

lemma norm_graphNormalVector_sq (p : EuclideanSpace ℝ (Fin 2)) :
    ‖graphNormalVector p‖ ^ 2 = 1 + ‖p‖ ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, Fin.sum_univ_two]
  ring

lemma norm_graphNormalVector (p : EuclideanSpace ℝ (Fin 2)) :
    ‖graphNormalVector p‖ = Real.sqrt (1 + ‖p‖ ^ 2) := by
  rw [← norm_graphNormalVector_sq, Real.sqrt_sq (norm_nonneg _)]

/-- The upward unit normal associated with a graph slope. -/
def graphUnitNormal (p : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 3) :=
  (Real.sqrt (1 + ‖p‖ ^ 2))⁻¹ • graphNormalVector p

lemma norm_graphUnitNormal (p : EuclideanSpace ℝ (Fin 2)) : ‖graphUnitNormal p‖ = 1 := by
  have hd : 0 < Real.sqrt (1 + ‖p‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [graphUnitNormal, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hd.le),
    norm_graphNormalVector, inv_mul_cancel₀ hd.ne']

lemma graphUnitNormal_upward (p : EuclideanSpace ℝ (Fin 2)) : 0 < graphUnitNormal p 2 := by
  simp only [graphUnitNormal, PiLp.smul_apply, graphNormalVector_apply_two, smul_eq_mul, mul_one]
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))

/-- The graph normal is orthogonal to every tangent direction. -/
lemma inner_graphNormalVector_graphTangentMap (p v : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (graphNormalVector p) (graphTangentMap p v) = 0 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, Fin.sum_univ_two]
  ring

lemma inner_graphUnitNormal_graphTangentMap (p v : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (graphUnitNormal p) (graphTangentMap p v) = 0 := by
  rw [graphUnitNormal, real_inner_smul_left, inner_graphNormalVector_graphTangentMap, mul_zero]

/-- Tangent orthogonality for the actual graph derivative, at differentiability points. -/
lemma inner_graphUnitNormal_fderiv_graphMap {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    {x : EuclideanSpace ℝ (Fin 2)} (hf : DifferentiableAt ℝ f x)
    (v : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (graphUnitNormal (gradient f x)) (fderiv ℝ (graphMap f) x v) = 0 := by
  rw [fderiv_graphMap hf, inner_graphUnitNormal_graphTangentMap]

/-- Rademacher gives the graph derivative formula at almost every base point. -/
lemma ae_fderiv_graphMap {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) :
    ∀ᵐ x ∂volume, fderiv ℝ (graphMap f) x = graphTangentMap (gradient f x) :=
  hf.ae_differentiableAt.mono fun _ hx => fderiv_graphMap hx

/-- The upward unit normal is orthogonal to all graph tangents almost everywhere. -/
lemma ae_inner_graphUnitNormal_fderiv_graphMap
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    ∀ᵐ x ∂volume, ∀ v : EuclideanSpace ℝ (Fin 2),
      inner ℝ (graphUnitNormal (gradient f x)) (fderiv ℝ (graphMap f) x v) = 0 :=
  hf.ae_differentiableAt.mono fun _ hx v => inner_graphUnitNormal_fderiv_graphMap hx v

/-- The two standard tangent columns have the upward graph normal as cross product. -/
lemma cross3_graphTangentMap (p : EuclideanSpace ℝ (Fin 2)) :
    cross3 (graphTangentMap p (EuclideanSpace.single 0 1))
      (graphTangentMap p (EuclideanSpace.single 1 1)) = graphNormalVector p := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp [crossProduct, PiLp.inner_apply]

/-- Gram Jacobian of the linear graph of a slope vector. -/
lemma jacobian2Linear_graphTangentMap (p : EuclideanSpace ℝ (Fin 2)) :
    jacobian2Linear (graphTangentMap p) = Real.sqrt (1 + ‖p‖ ^ 2) := by
  rw [jacobian2Linear_eq_norm_cross3, cross3_graphTangentMap, norm_graphNormalVector]

/-- Graph Jacobian at a differentiability point of the height function. -/
lemma jacobian2_graphMap {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    {x : EuclideanSpace ℝ (Fin 2)} (hf : DifferentiableAt ℝ f x) :
    jacobian2 (graphMap f) x = Real.sqrt (1 + ‖gradient f x‖ ^ 2) := by
  rw [jacobian2, fderiv_graphMap hf, jacobian2Linear_graphTangentMap]

/-- The graph Jacobian formula holds almost everywhere for every Lipschitz height. -/
lemma ae_jacobian2_graphMap {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) :
    ∀ᵐ x ∂volume, jacobian2 (graphMap f) x = Real.sqrt (1 + ‖gradient f x‖ ^ 2) :=
  hf.ae_differentiableAt.mono fun _ hx => jacobian2_graphMap hx

lemma measurable_graphAreaDensity (f : EuclideanSpace ℝ (Fin 2) → ℝ) :
    Measurable (fun x => ENNReal.ofReal (Real.sqrt (1 + ‖gradient f x‖ ^ 2))) := by
  have hg : Measurable (gradient f) :=
    (toDual ℝ (EuclideanSpace ℝ (Fin 2))).symm.continuous.measurable.comp
      (measurable_fderiv ℝ f)
  exact (measurable_const.add (hg.norm.pow_const 2)).sqrt.ennreal_ofReal

/-- A pointwise bound on the graph density from the height's Lipschitz constant. -/
lemma graphAreaDensity_le_of_lipschitz {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (x : EuclideanSpace ℝ (Fin 2)) :
    ENNReal.ofReal (Real.sqrt (1 + ‖gradient f x‖ ^ 2)) ≤ ENNReal.ofReal (1 + (K : ℝ)) := by
  have hg : ‖gradient f x‖ ≤ K := by
    change ‖(toDual ℝ (EuclideanSpace ℝ (Fin 2))).symm (fderiv ℝ f x)‖ ≤ K
    rw [LinearIsometryEquiv.norm_map]
    exact norm_fderiv_le_of_lipschitz ℝ hf
  apply ENNReal.ofReal_le_ofReal
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith [norm_nonneg (gradient f x), K.coe_nonneg]

/-- Exact normalized Hausdorff area of a Lipschitz graph above a Borel base set. -/
theorem hausdorffMeasure2_graphMap_image {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {G : Set (EuclideanSpace ℝ (Fin 2))} (hG : MeasurableSet G) :
    hausdorffMeasure2 3 (graphMap f '' G) =
      ∫⁻ x in G, ENNReal.ofReal (Real.sqrt (1 + ‖gradient f x‖ ^ 2)) := by
  rw [hausdorffMeasure2_image_eq_lintegral_jacobian_of_lipschitz
    (lipschitzWith_graphMap hf) hG (graphMap_injective f).injOn]
  apply lintegral_congr_ae
  exact (ae_restrict_of_ae (ae_jacobian2_graphMap hf)).mono fun _ hx => congrArg ENNReal.ofReal hx

/-- Graph area is the pushforward of the usual graph density on its base. -/
theorem hausdorffMeasure2_restrict_graphMap_image
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {G : Set (EuclideanSpace ℝ (Fin 2))} (hG : MeasurableSet G) :
    (hausdorffMeasure2 3).restrict (graphMap f '' G) =
      Measure.map (graphMap f) ((volume.restrict G).withDensity
        (fun x => ENNReal.ofReal (Real.sqrt (1 + ‖gradient f x‖ ^ 2)))) := by
  ext B hB
  rw [Measure.restrict_apply hB, Measure.map_apply
    (measurableEmbedding_graphMap hf).measurable hB,
    withDensity_apply _ ((measurableEmbedding_graphMap hf).measurable hB),
    Measure.restrict_restrict ((measurableEmbedding_graphMap hf).measurable hB)]
  have heq : B ∩ graphMap f '' G = graphMap f '' (graphMap f ⁻¹' B ∩ G) := by
    rw [Set.image_preimage_inter]
  rw [heq]
  exact hausdorffMeasure2_graphMap_image hf
    (((measurableEmbedding_graphMap hf).measurable hB).inter hG)

/-- The weighted graph area identity, allowing infinite nonnegative integrals. -/
theorem lintegral_graphMap_image {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {G : Set (EuclideanSpace ℝ (Fin 2))} (hG : MeasurableSet G)
    {q : EuclideanSpace ℝ (Fin 3) → ℝ≥0∞} (hq : Measurable q) :
    ∫⁻ y in graphMap f '' G, q y ∂hausdorffMeasure2 3 =
      ∫⁻ x in G, q (graphMap f x) * ENNReal.ofReal (Real.sqrt (1 + ‖gradient f x‖ ^ 2)) := by
  have hm : Measurable (fun x => q (graphMap f x)) :=
    hq.comp (measurableEmbedding_graphMap hf).measurable
  rw [hausdorffMeasure2_restrict_graphMap_image hf hG,
    lintegral_map hq (measurableEmbedding_graphMap hf).measurable,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_graphAreaDensity f) hm]
  simp only [Pi.mul_apply, mul_comm]

/-- The upward normal is a unit vector orthogonal to the classical graph tangent
at Hausdorff-almost every graph point. -/
theorem ae_graphMap_upward_unit_normal {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {G : Set (EuclideanSpace ℝ (Fin 2))} (hG : MeasurableSet G) :
    ∀ᵐ y ∂(hausdorffMeasure2 3).restrict (graphMap f '' G),
      ∃ x ∈ G, graphMap f x = y ∧ DifferentiableAt ℝ f x ∧
        ‖graphUnitNormal (gradient f x)‖ = 1 ∧ 0 < graphUnitNormal (gradient f x) 2 ∧
        ∀ v : EuclideanSpace ℝ (Fin 2),
          inner ℝ (graphUnitNormal (gradient f x)) (fderiv ℝ (graphMap f) x v) = 0 := by
  rw [hausdorffMeasure2_restrict_graphMap_image hf hG,
    (measurableEmbedding_graphMap hf).ae_map_iff]
  have ha : ∀ᵐ x ∂volume.restrict G, x ∈ G ∧ DifferentiableAt ℝ f x :=
    (ae_restrict_mem hG).and (ae_restrict_of_ae hf.ae_differentiableAt)
  filter_upwards [(withDensity_absolutelyContinuous (volume.restrict G)
    (fun x => ENNReal.ofReal (Real.sqrt (1 + ‖gradient f x‖ ^ 2)))).ae_le ha] with x hx
  exact ⟨x, hx.1, rfl, hx.2, norm_graphUnitNormal _, graphUnitNormal_upward _,
    inner_graphUnitNormal_fderiv_graphMap hx.2⟩

/-- A Lipschitz bound controls graph area by base area. -/
lemma hausdorffMeasure2_graphMap_image_le {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {G : Set (EuclideanSpace ℝ (Fin 2))} (hG : MeasurableSet G) :
    hausdorffMeasure2 3 (graphMap f '' G) ≤ ENNReal.ofReal (1 + (K : ℝ)) * volume G := by
  rw [hausdorffMeasure2_graphMap_image hf hG]
  calc
    _ ≤ ∫⁻ _ in G, ENNReal.ofReal (1 + (K : ℝ)) :=
      lintegral_mono fun x => graphAreaDensity_le_of_lipschitz hf x
    _ = _ := by simp

/-- Finite base area implies finite graph area. -/
lemma hausdorffMeasure2_graphMap_image_lt_top {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {G : Set (EuclideanSpace ℝ (Fin 2))} (hG : MeasurableSet G)
    (hGfin : volume G < ∞) : hausdorffMeasure2 3 (graphMap f '' G) < ∞ :=
  (hausdorffMeasure2_graphMap_image_le hf hG).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hGfin)

end LiquidDrop
