module

public import NoCompromise.BV.CoareaCoordinates
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

@[expose] public section

/-!
# Genuine inverse-function charts for regular scalar levels

At a point where the final derivative is nonzero, coordinate replacement is a
local C¹ diffeomorphism. Its horizontal slices are the level graphs used in
coarea. Every chart hypothesis is supplied by the local inverse function theorem.
-/

noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- An inverse coordinate chart, with a nonzero final partial derivative throughout its source. -/
structure ScalarCoareaChart {k : ℕ} (u : EuclideanSpace ℝ (Fin (k + 1)) → ℝ) where
  chart : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (k + 1)))
    (EuclideanSpace ℝ (Fin (k + 1)))
  forward_eq : (chart : EuclideanSpace ℝ (Fin (k + 1)) → _) = coareaCoordinateMap u
  contDiffOn : ContDiffOn ℝ 1 u chart.source
  last_ne_zero : ∀ x ∈ chart.source, gradient u x (Fin.last k) ≠ 0

/-- Every point with nonzero final partial derivative has such a chart inside the given domain. -/
lemma exists_scalarCoareaChart {k : ℕ} {U : Set (EuclideanSpace ℝ (Fin (k + 1)))}
    (hU : IsOpen U) {u : EuclideanSpace ℝ (Fin (k + 1)) → ℝ} (hu : ContDiffOn ℝ 1 u U)
    {x : EuclideanSpace ℝ (Fin (k + 1))} (hx : x ∈ U)
    (hp : gradient u x (Fin.last k) ≠ 0) :
    ∃ d : ScalarCoareaChart u, x ∈ d.chart.source ∧ d.chart.source ⊆ U := by
  have hgrad : ContinuousOn (gradient u) U :=
    (toDual ℝ (EuclideanSpace ℝ (Fin (k + 1)))).symm.continuous.comp_continuousOn
      (hu.continuousOn_fderiv_of_isOpen hU le_rfl)
  let V := U ∩ (fun z => gradient u z (Fin.last k)) ⁻¹' ({0} : Set ℝ)ᶜ
  have hV : IsOpen V :=
    ((EuclideanSpace.proj (Fin.last k)).continuous.comp_continuousOn hgrad).isOpen_inter_preimage
      hU isClosed_singleton.isOpen_compl
  have hdiff := (hu.differentiableOn (by norm_num) x hx).differentiableAt (hU.mem_nhds hx)
  have hderiv : HasFDerivAt (coareaCoordinateMap u)
      (coareaCoordinateEquiv (gradient u x) hp).toContinuousLinearMap x := by
    rw [coareaCoordinateEquiv_toContinuousLinearMap]
    exact hasFDerivAt_coareaCoordinateMap hdiff
  have hc := (contDiffOn_coareaCoordinateMap hu).contDiffAt (hU.mem_nhds hx)
  let e := hc.toOpenPartialHomeomorph (coareaCoordinateMap u) hderiv (by norm_num)
  refine ⟨⟨e.restrOpen V hV, rfl,
    hu.mono (fun z hz => hz.2.1), fun z hz => hz.2.2⟩, ?_, fun z hz => hz.2.1⟩
  exact ⟨hc.mem_toOpenPartialHomeomorph_source hderiv (by norm_num), hx, hp⟩

namespace ScalarCoareaChart
variable {k : ℕ} {u : EuclideanSpace ℝ (Fin (k + 1)) → ℝ} (d : ScalarCoareaChart u)

lemma hasFDerivAt_forward {x : EuclideanSpace ℝ (Fin (k + 1))} (hx : x ∈ d.chart.source) :
    HasFDerivAt d.chart (coareaCoordinateEquiv (gradient u x)
      (d.last_ne_zero x hx)).toContinuousLinearMap x := by
  rw [d.forward_eq, coareaCoordinateEquiv_toContinuousLinearMap]
  exact hasFDerivAt_coareaCoordinateMap
    ((d.contDiffOn.differentiableOn (by norm_num) x hx).differentiableAt
      (d.chart.open_source.mem_nhds hx))

lemma hasFDerivAt_inverse {y : EuclideanSpace ℝ (Fin (k + 1))} (hy : y ∈ d.chart.target) :
    HasFDerivAt d.chart.symm
      (coareaCoordinateEquiv (gradient u (d.chart.symm y))
        (d.last_ne_zero _ (d.chart.map_target hy))).symm.toContinuousLinearMap y :=
  d.chart.hasFDerivAt_symm hy (d.hasFDerivAt_forward (d.chart.map_target hy))

lemma contDiffOn_inverse : ContDiffOn ℝ 1 d.chart.symm d.chart.target := by
  intro y hy
  have hx := d.chart.map_target hy
  apply (d.chart.contDiffAt_symm hy (d.hasFDerivAt_forward hx) ?_).contDiffWithinAt
  rw [d.forward_eq]
  exact (contDiffOn_coareaCoordinateMap d.contDiffOn).contDiffAt
    (d.chart.open_source.mem_nhds hx)

/-- The open horizontal domain of the level graph at height `t`. -/
def levelDomain (t : ℝ) : Set (EuclideanSpace ℝ (Fin k)) :=
  (fun x => graphAppendN x t) ⁻¹' d.chart.target

lemma isOpen_levelDomain (t : ℝ) : IsOpen (d.levelDomain t) :=
  d.chart.open_target.preimage (contDiff_graphAppendN t (r := 1)).continuous

/-- The last coordinate of the inverse parametrizes each level. -/
def levelHeight (t : ℝ) (x : EuclideanSpace ℝ (Fin k)) : ℝ :=
  d.chart.symm (graphAppendN x t) (Fin.last k)

lemma contDiffOn_levelHeight (t : ℝ) : ContDiffOn ℝ 1 (d.levelHeight t) (d.levelDomain t) := by
  change ContDiffOn ℝ 1
    ((EuclideanSpace.proj (Fin.last k) : EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] ℝ) ∘
      d.chart.symm ∘ fun x => graphAppendN x t) (d.levelDomain t)
  exact (EuclideanSpace.proj (Fin.last k)).contDiff.comp_contDiffOn
    (d.contDiffOn_inverse.comp (contDiff_graphAppendN t).contDiffOn (fun _ hx => hx))

lemma inverse_eq_graphMapN {t : ℝ} {x : EuclideanSpace ℝ (Fin k)}
    (hx : x ∈ d.levelDomain t) :
    d.chart.symm (graphAppendN x t) = graphMapN (d.levelHeight t) x := by
  apply PiLp.ext
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [levelHeight]
  · have h := congrArg (fun z : EuclideanSpace ℝ (Fin (k + 1)) => z j.castSucc)
      (d.chart.right_inv hx)
    rw [d.forward_eq] at h
    simpa only [coareaCoordinateMap_castSucc, graphAppendN_castSucc, graphMapN_castSucc] using h

lemma u_inverse_eq {t : ℝ} {x : EuclideanSpace ℝ (Fin k)} (hx : x ∈ d.levelDomain t) :
    u (d.chart.symm (graphAppendN x t)) = t := by
  have h := congrArg (fun z : EuclideanSpace ℝ (Fin (k + 1)) => z (Fin.last k))
    (d.chart.right_inv hx)
  rw [d.forward_eq] at h
  simpa only [coareaCoordinateMap_last, graphAppendN_last] using h

lemma gradient_levelHeight {t : ℝ} {x : EuclideanSpace ℝ (Fin k)}
    (hx : x ∈ d.levelDomain t) :
    gradient (d.levelHeight t) x =
      coareaGraphSlope (gradient u (d.chart.symm (graphAppendN x t))) := by
  have hs := (d.hasFDerivAt_inverse hx).comp x (hasFDerivAt_graphAppendN t x)
  have hlin : (coareaCoordinateEquiv (gradient u (d.chart.symm (graphAppendN x t)))
        (d.last_ne_zero _ (d.chart.map_target hx))).symm.toContinuousLinearMap.comp
      (graphBaseN k) =
      graphTangentN (coareaGraphSlope (gradient u (d.chart.symm (graphAppendN x t)))) := by
    apply ContinuousLinearMap.ext
    intro v
    exact coareaCoordinateEquiv_symm_graphBaseN _ _ v
  rw [hlin] at hs
  have hg := (EuclideanSpace.proj (Fin.last k)).hasFDerivAt.comp x hs
  have heq : (EuclideanSpace.proj (Fin.last k)).comp
      (graphTangentN (coareaGraphSlope (gradient u (d.chart.symm (graphAppendN x t))))) =
      innerSL ℝ (coareaGraphSlope (gradient u (d.chart.symm (graphAppendN x t)))) := by
    apply ContinuousLinearMap.ext
    intro v
    exact graphTangentN_last _ v
  rw [heq] at hg
  have hgrad : HasFDerivAt (d.levelHeight t)
      (innerSL ℝ (coareaGraphSlope (gradient u (d.chart.symm (graphAppendN x t))))) x := hg
  apply (toDual ℝ (EuclideanSpace ℝ (Fin k))).injective
  rw [toDual_gradient, hgrad.fderiv]
  rfl

/-- A Borel source patch gives a Borel coordinate image. -/
lemma measurableSet_image {A : Set (EuclideanSpace ℝ (Fin (k + 1)))}
    (hA : MeasurableSet A) (hAs : A ⊆ d.chart.source) : MeasurableSet (d.chart '' A) :=
  hA.image_of_continuousOn_injOn (d.chart.continuousOn.mono hAs) (d.chart.injOn.mono hAs)

/-- The horizontal slice of the transformed Borel patch. -/
def levelPatch (A : Set (EuclideanSpace ℝ (Fin (k + 1)))) (t : ℝ) :
    Set (EuclideanSpace ℝ (Fin k)) := (fun x => graphAppendN x t) ⁻¹' (d.chart '' A)

lemma levelPatch_subset_levelDomain {A : Set (EuclideanSpace ℝ (Fin (k + 1)))}
    (hAs : A ⊆ d.chart.source) (t : ℝ) : d.levelPatch A t ⊆ d.levelDomain t := by
  rintro x ⟨z, hz, hzmap⟩
  change d.chart z = graphAppendN x t at hzmap
  change graphAppendN x t ∈ d.chart.target
  rw [← hzmap]
  exact d.chart.map_source (hAs hz)

lemma measurableSet_levelPatch {A : Set (EuclideanSpace ℝ (Fin (k + 1)))}
    (hA : MeasurableSet A) (hAs : A ⊆ d.chart.source) (t : ℝ) :
    MeasurableSet (d.levelPatch A t) :=
  (d.measurableSet_image hA hAs).preimage (contDiff_graphAppendN t (r := 1)).continuous.measurable

/-- The inverse horizontal slice is exactly the corresponding scalar level in the patch. -/
lemma graphMapN_levelPatch {A : Set (EuclideanSpace ℝ (Fin (k + 1)))}
    (hAs : A ⊆ d.chart.source) (t : ℝ) :
    graphMapN (d.levelHeight t) '' d.levelPatch A t = A ∩ u ⁻¹' {t} := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxd := d.levelPatch_subset_levelDomain hAs t hx
    obtain ⟨y, hy, hymap⟩ := hx
    dsimp only at hymap
    have hinv : d.chart.symm (graphAppendN x t) = y := by
      rw [← hymap, d.chart.left_inv (hAs hy)]
    rw [← d.inverse_eq_graphMapN hxd]
    exact ⟨hinv ▸ hy, d.u_inverse_eq hxd⟩
  · rintro ⟨hz, hzt⟩
    change u z = t at hzt
    have hzmap : d.chart z = graphAppendN (graphProjectionN k z) t := by
      rw [d.forward_eq, coareaCoordinateMap, hzt]
    have hxp : graphProjectionN k z ∈ d.levelPatch A t := ⟨z, hz, hzmap⟩
    refine ⟨graphProjectionN k z, hxp, ?_⟩
    rw [← d.inverse_eq_graphMapN (d.levelPatch_subset_levelDomain hAs t hxp),
      ← hzmap, d.chart.left_inv (hAs hz)]

/-- Zero outside the inverse chart target, to obtain a globally Borel inverse representative. -/
def measurableInverse (y : EuclideanSpace ℝ (Fin (k + 1))) :
    EuclideanSpace ℝ (Fin (k + 1)) := d.chart.target.indicator d.chart.symm y

lemma measurable_measurableInverse : Measurable d.measurableInverse := by
  classical
  exact d.chart.symm.continuousOn.measurable_piecewise continuousOn_const
    d.chart.open_target.measurableSet

lemma measurableInverse_eq {y : EuclideanSpace ℝ (Fin (k + 1))}
    (hy : y ∈ d.chart.target) : d.measurableInverse y = d.chart.symm y :=
  indicator_of_mem hy _

end ScalarCoareaChart
end LiquidDrop
