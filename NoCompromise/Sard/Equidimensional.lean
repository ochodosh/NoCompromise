module

public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

@[expose] public section

/-!
# Equidimensional Sard by elementary critical-image estimates

The proof uses the elementary near-linear volume distortion estimate and the
countable differentiability partition. On the singular set every linear model
has determinant zero; summing its arbitrarily small image-volume bound on a
bounded set and then exhausting by balls proves nullity. No packaged Sard
statement or change-of-variables integral formula is used.
-/

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter Function Metric
open scoped ENNReal NNReal Topology Manifold
namespace LiquidDrop
set_option maxSynthPendingDepth 8

section NormedSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsAddHaarMeasure μ]
  {s : Set E} {f : E → E} {f' : E → E →L[ℝ] E}

/-- The image of a bounded singular set has an arbitrarily small volume bound.
The sole geometric input is the volume estimate for a map close to a linear map. -/
theorem singular_image_bounded_le
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hdet : ∀ x ∈ s, (f' x).det = 0)
    (R : ℝ) (hs : s ⊆ closedBall 0 R) (ε : ℝ≥0) (hε : 0 < ε) :
    μ (f '' s) ≤ ε * μ (closedBall 0 R) := by
  classical
  rcases eq_empty_or_nonempty s with (rfl | hne)
  · simp
  have hlocal : ∀ A : E →L[ℝ] E, ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ t : Set E, ApproximatesLinearOn f A t δ →
        μ (f '' t) ≤ (Real.toNNReal |A.det| + ε : ℝ≥0) * μ t := by
    intro A
    have hm : ENNReal.ofReal |A.det| < (Real.toNNReal |A.det| + ε : ℝ≥0) := by
      simp only [ENNReal.ofReal, ENNReal.coe_lt_coe, lt_add_iff_pos_right, hε]
    obtain ⟨δ, hδ, hδpos⟩ :=
      ((addHaar_image_le_mul_of_det_lt μ A hm).and self_mem_nhdsWithin).exists
    exact ⟨δ, hδpos, fun t ht => hδ t f ht⟩
  choose δ hδpos hδ using hlocal
  obtain ⟨t, A, hdisj, hmeas, hcover, happrox, hmodel⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf' δ
      (fun A => (hδpos A).ne')
  have hA : ∀ j, (A j).det = 0 := by
    intro j
    obtain ⟨x, hx, hAx⟩ := hmodel hne j
    rw [hAx, hdet x hx]
  calc
    μ (f '' s) ≤ μ (⋃ j, f '' (s ∩ t j)) := by
      rw [← image_iUnion, ← inter_iUnion]
      exact measure_mono (image_mono (subset_inter Subset.rfl hcover))
    _ ≤ ∑' j, μ (f '' (s ∩ t j)) := measure_iUnion_le _
    _ ≤ ∑' j, (ε : ℝ≥0∞) * μ (s ∩ t j) := by
      refine ENNReal.tsum_le_tsum fun j => ?_
      simpa only [hA j, abs_zero, Real.toNNReal_zero, zero_add] using
        hδ (A j) (s ∩ t j) (happrox j)
    _ ≤ ε * ∑' j, μ (closedBall 0 R ∩ t j) := by
      rw [ENNReal.tsum_mul_left]
      gcongr
    _ = ε * μ (⋃ j, closedBall 0 R ∩ t j) := by
      rw [measure_iUnion (pairwise_disjoint_mono hdisj fun _ => inter_subset_right)
        (fun j => measurableSet_closedBall.inter (hmeas j))]
    _ ≤ ε * μ (closedBall 0 R) :=
      by gcongr; exact iUnion_subset fun _ => inter_subset_left

/-- Equidimensional critical-image nullity, even for a derivative specified only
within the singular set. No measurability assumption on that set is needed. -/
theorem singular_image_eq_zero
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hdet : ∀ x ∈ s, (f' x).det = 0) : μ (f '' s) = 0 := by
  have hbounded : ∀ R : ℝ, μ (f '' (s ∩ closedBall 0 R)) = 0 := by
    intro R
    have hsmall : ∀ ε : ℝ≥0, 0 < ε →
        μ (f '' (s ∩ closedBall 0 R)) ≤ ε * μ (closedBall 0 R) := by
      intro ε hε
      exact singular_image_bounded_le μ
        (fun x hx => (hf' x hx.1).mono inter_subset_left)
        (fun x hx => hdet x hx.1) R inter_subset_right ε hε
    have ht : Tendsto (fun ε : ℝ≥0 => (ε : ℝ≥0∞) * μ (closedBall 0 R))
        (𝓝[>] 0) (𝓝 0) := by
      have ht : Tendsto (fun ε : ℝ≥0 => (ε : ℝ≥0∞) * μ (closedBall 0 R))
          (𝓝 0) (𝓝 ((0 : ℝ≥0∞) * μ (closedBall 0 R))) :=
        ENNReal.Tendsto.mul_const (ENNReal.tendsto_coe.2 tendsto_id)
        (Or.inr (measure_closedBall_lt_top (μ := μ) (x := (0 : E)) (r := R)).ne)
      simpa only [ENNReal.coe_zero, zero_mul] using ht.mono_left nhdsWithin_le_nhds
    apply nonpos_iff_eq_zero.mp
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with ε hε using hsmall ε hε
  rw [← iUnion_inter_closedBall_nat s 0, image_iUnion]
  exact measure_iUnion_null fun j => hbounded j

/-- C¹ equidimensional Sard on an open set, in every finite dimension. -/
theorem sard_equidimensional {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) :
    μ (f '' {x | x ∈ U ∧ (fderiv ℝ f x).det = 0}) = 0 := by
  apply singular_image_eq_zero μ (f' := fderiv ℝ f)
  · intro x hx
    exact ((hf.differentiableOn (by norm_num) x hx.1).differentiableAt
      (hU.mem_nhds hx.1)).hasFDerivAt.hasFDerivWithinAt
  · exact fun _ hx => hx.2

end NormedSpace

/-- The planar instance of `lem:sard-equidim`. -/
theorem sard_equidimensional_two {U : Set (EuclideanSpace ℝ (Fin 2))}
    (hU : IsOpen U) {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hf : ContDiffOn ℝ 1 f U) :
    volume (f '' {x | x ∈ U ∧ (fderiv ℝ f x).det = 0}) = 0 :=
  sard_equidimensional volume hU hf

/-- The three-dimensional instance of `lem:sard-equidim`. -/
theorem sard_equidimensional_three {U : Set (EuclideanSpace ℝ (Fin 3))}
    (hU : IsOpen U) {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hf : ContDiffOn ℝ 1 f U) :
    volume (f '' {x | x ∈ U ∧ (fderiv ℝ f x).det = 0}) = 0 :=
  sard_equidimensional volume hU hf

section Manifold
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  (μ : Measure V) [μ.IsAddHaarMeasure]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace V M] [IsManifold 𝓘(ℝ, V) 1 M]

/-- A singular set has a null image after restriction to one source chart. -/
theorem singular_manifold_image_chart_eq_zero {F : M → V} {S : Set M}
    (hF : ∀ x ∈ S, MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, V) F x)
    (hdet : ∀ x ∈ S, (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) F x).det = 0) (p : M) :
    μ (F '' (S ∩ (chartAt V p).source)) = 0 := by
  let e := extChartAt 𝓘(ℝ, V) p
  let T := e '' (S ∩ (chartAt V p).source)
  have hinv (z : V) (hz : z ∈ T) :
      e.symm z ∈ S ∧ z ∈ e.target := by
    obtain ⟨x, hx, rfl⟩ := hz
    have hx' : x ∈ e.source := by simpa only [e, extChartAt_source] using hx.2
    exact ⟨by simpa only [e.left_inv hx'] using hx.1, e.map_source hx'⟩
  have hdi (z : V) (hz : z ∈ T) : MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, V) e.symm z := by
    have hi := mdifferentiableWithinAt_extChartAt_symm (I := 𝓘(ℝ, V)) (hinv z hz).2
    apply hi.mdifferentiableAt
    simp
  have hdiff (z : V) (hz : z ∈ T) : DifferentiableAt ℝ (F ∘ e.symm) z :=
    ((hF _ (hinv z hz).1).comp z (hdi z hz)).differentiableAt
  have hzero : μ ((F ∘ e.symm) '' T) = 0 := by
    apply singular_image_eq_zero μ (f' := fderiv ℝ (F ∘ e.symm))
    · exact fun z hz => (hdiff z hz).hasFDerivAt.hasFDerivWithinAt
    · intro z hz
      have hfd : (fderiv ℝ (F ∘ e.symm) z).det =
          (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) (F ∘ e.symm) z).det := by
        rw [mfderiv_eq_fderiv]; rfl
      rw [hfd, mfderiv_comp z (hF _ (hinv z hz).1) (hdi z hz)]
      let A : V →L[ℝ] V := mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) F (e.symm z)
      let B : V →L[ℝ] V := mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) e.symm z
      have hA : A.det = 0 := hdet _ (hinv z hz).1
      change LinearMap.det (A.toLinearMap.comp B.toLinearMap) = 0
      rw [LinearMap.det_comp]
      exact mul_eq_zero_of_left hA _
  apply measure_mono_null _ hzero
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨e x, ⟨x, hx, rfl⟩, ?_⟩
  dsimp only [comp_apply]
  rw [e.left_inv (by simpa only [e, extChartAt_source] using hx.2)]


variable [SecondCountableTopology M]

/-- Second countability globalizes singular-image nullity from source charts. -/
theorem singular_manifold_image_eq_zero {F : M → V} {S : Set M}
    (hF : ∀ x ∈ S, MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, V) F x)
    (hdet : ∀ x ∈ S, (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) F x).det = 0) :
    μ (F '' S) = 0 := by
  classical
  by_cases hS : S.Nonempty
  · let : Nonempty S := hS.to_subtype
    have hL : IsLindelof S := isLindelof_iff_lindelofSpace.mpr inferInstance
    obtain ⟨c, hc⟩ := hL.indexed_countable_subcover
      (fun x : S => (chartAt V (x : M)).source)
      (fun x => (chartAt V (x : M)).open_source)
      (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, mem_chart_source V x⟩)
    apply measure_mono_null (t := ⋃ j, F '' (S ∩ (chartAt V (c j : M)).source)) _
      (measure_iUnion_null fun j => singular_manifold_image_chart_eq_zero μ hF hdet (c j))
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hc hx)
    exact mem_iUnion.mpr ⟨j, x, ⟨hx, hj⟩, rfl⟩
  · simp only [not_nonempty_iff_eq_empty.mp hS, image_empty, measure_empty]

variable {N : Type*} [TopologicalSpace N] [ChartedSpace V N] [IsManifold 𝓘(ℝ, V) 1 N]

omit [IsManifold 𝓘(ℝ, V) 1 M] [SecondCountableTopology M]
  [IsManifold 𝓘(ℝ, V) 1 N] [MeasurableSpace V] [BorelSpace V] in
/-- The determinant criterion used below agrees with the intrinsic rank-drop
criterion on tangent spaces; no choice of tangent coordinates changes the set. -/
theorem mfderiv_det_eq_zero_iff_not_injective (F : M → N) (x : M) :
    (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) F x).det = 0 ↔
      ¬ Function.Injective (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) F x) := by
  let A : V →L[ℝ] V := mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) F x
  change A.toLinearMap.det = 0 ↔ ¬ Function.Injective A.toLinearMap
  rw [LinearMap.det_eq_zero_iff_ker_ne_bot, ne_eq, LinearMap.ker_eq_bot]

omit [IsManifold 𝓘(ℝ, V) 1 N] in
/-- Critical values are null under every differentiable target coordinate map.
This formulation also applies to coordinate maps from the maximal C¹ atlas. -/
theorem sard_manifold_coordinates {F : M → N}
    (hF : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, V) 1 F)
    {g : N → V} {T : Set N}
    (hg : ∀ y ∈ T, MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, V) g y) :
    μ (g '' ((F '' {x | (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) F x).det = 0}) ∩ T)) = 0 := by
  have hzero : μ ((g ∘ F) ''
      {x | (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) F x).det = 0 ∧ F x ∈ T}) = 0 := by
    apply singular_manifold_image_eq_zero μ
    · exact fun x hx => (hg _ hx.2).comp x (hF.mdifferentiableAt (by norm_num))
    · intro x hx
      rw [mfderiv_comp x (hg _ hx.2) (hF.mdifferentiableAt (by norm_num))]
      let A : V →L[ℝ] V := mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) g (F x)
      let B : V →L[ℝ] V := mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) F x
      have hB : B.det = 0 := hx.1
      change LinearMap.det (A.toLinearMap.comp B.toLinearMap) = 0
      rw [LinearMap.det_comp]
      exact mul_eq_zero_of_right _ hB
  apply measure_mono_null _ hzero
  rintro _ ⟨_, ⟨⟨x, hx, rfl⟩, hT⟩, rfl⟩
  exact ⟨x, ⟨hx, hT⟩, rfl⟩

/-- Equidimensional C¹ Sard in every selected target chart of a second-countable
source manifold. In particular this proves the chart nullity in `cor:sard-charts`. -/
theorem sard_manifold_chart {F : M → N}
    (hF : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, V) 1 F) (q : N) :
    μ ((extChartAt 𝓘(ℝ, V) q) ''
      ((F '' {x | (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) F x).det = 0}) ∩ (chartAt V q).source)) = 0 :=
  sard_manifold_coordinates μ hF (fun _ hy => mdifferentiableAt_extChartAt hy)


omit [IsManifold 𝓘(ℝ, V) 1 N] in
/-- Nullity in every chart of the maximal C¹ atlas, rather than only the charts
selected by `chartAt`. -/
theorem sard_manifold_maximal_chart {F : M → N}
    (hF : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, V) 1 F)
    {e : OpenPartialHomeomorph N V}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, V) 1 N) :
    μ (e '' ((F '' {x | (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) F x).det = 0}) ∩ e.source)) = 0 :=
  sard_manifold_coordinates μ hF (fun _ hy => mdifferentiableAt_of_mem_maximalAtlas he hy)

variable [MeasurableSpace N] [BorelSpace N] [SecondCountableTopology N]

omit [IsManifold 𝓘(ℝ, V) 1 M] [SecondCountableTopology M]
  [IsManifold 𝓘(ℝ, V) 1 N] [FiniteDimensional ℝ V] [μ.IsAddHaarMeasure] in
/-- Chart nullity implies nullity for any measure whose coordinate restrictions
are absolutely continuous with respect to Lebesgue measure. -/
theorem measure_eq_zero_of_chart_images (ν : Measure N)
    (hν : ∀ q : N, (ν.restrict (chartAt V q).source).map
      (extChartAt 𝓘(ℝ, V) q) ≪ μ)
    {S : Set N} (hS : ∀ q : N,
      μ ((extChartAt 𝓘(ℝ, V) q) '' (S ∩ (chartAt V q).source)) = 0) : ν S = 0 := by
  classical
  have hnull (q : N) : ν (S ∩ (chartAt V q).source) = 0 := by
    have hc : ContinuousOn (extChartAt 𝓘(ℝ, V) q) (chartAt V q).source := by
      simpa only [extChartAt_source] using continuousOn_extChartAt (I := 𝓘(ℝ, V)) q
    have hle := Measure.le_map_apply_image
      (hc.aemeasurable (μ := ν) (chartAt V q).open_source.measurableSet)
      (S ∩ (chartAt V q).source)
    rw [Measure.restrict_eq_self ν inter_subset_right] at hle
    exact nonpos_iff_eq_zero.mp (hle.trans_eq (hν q (hS q)))
  by_cases hne : S.Nonempty
  · let : Nonempty S := hne.to_subtype
    have hL : IsLindelof S := isLindelof_iff_lindelofSpace.mpr inferInstance
    obtain ⟨c, hc⟩ := hL.indexed_countable_subcover
      (fun x : S => (chartAt V (x : N)).source)
      (fun x => (chartAt V (x : N)).open_source)
      (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, mem_chart_source V x⟩)
    apply measure_mono_null (t := ⋃ j, S ∩ (chartAt V (c j : N)).source) _
      (measure_iUnion_null fun j => hnull (c j))
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hc hx)
    exact mem_iUnion.mpr ⟨j, hx, hj⟩
  · simp only [not_nonempty_iff_eq_empty.mp hne, measure_empty]

/-- Critical-value nullity for a measure absolutely continuous in charts. -/
theorem sard_manifold_measure {F : M → N}
    (hF : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, V) 1 F) (ν : Measure N)
    (hν : ∀ q : N, (ν.restrict (chartAt V q).source).map
      (extChartAt 𝓘(ℝ, V) q) ≪ μ) :
    ν (F '' {x | (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) F x).det = 0}) = 0 :=
  measure_eq_zero_of_chart_images μ ν hν (sard_manifold_chart μ hF)

/-- The coordinate-density version of `cor:sard-charts`. In particular a smooth
volume density satisfies this explicit measure convention; the density need not
be smooth, positive, or bounded for critical-value nullity. -/
theorem sard_manifold_measure_of_chart_densities {F : M → N}
    (hF : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, V) 1 F) (ν : Measure N)
    (hν : ∀ q : N, ∃ ρ : V → ℝ≥0∞,
      (ν.restrict (chartAt V q).source).map (extChartAt 𝓘(ℝ, V) q) = μ.withDensity ρ) :
    ν (F '' {x | (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) F x).det = 0}) = 0 := by
  apply sard_manifold_measure μ hF ν
  intro q
  obtain ⟨ρ, hρ⟩ := hν q
  rw [hρ]
  exact withDensity_absolutelyContinuous μ ρ

omit [IsManifold 𝓘(ℝ, V) 1 N] [MeasurableSpace N] [BorelSpace N]
  [SecondCountableTopology N] in
/-- `cor:sard-charts` using the intrinsic noninjectivity definition of a
critical point. The chart may be any member of the maximal C¹ atlas. -/
theorem sard_manifold_critical_values_chart {F : M → N}
    (hF : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, V) 1 F)
    {e : OpenPartialHomeomorph N V}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, V) 1 N) :
    μ (e '' ((F '' {x | ¬ Function.Injective (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) F x)}) ∩
      e.source)) = 0 := by
  simpa only [mfderiv_det_eq_zero_iff_not_injective] using
    sard_manifold_maximal_chart μ hF he

/-- The volume-measure consequence with the intrinsic critical set and an
explicit chartwise density convention for the target volume measure. -/
theorem sard_manifold_critical_values_measure {F : M → N}
    (hF : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, V) 1 F) (ν : Measure N)
    (hν : ∀ q : N, ∃ ρ : V → ℝ≥0∞,
      (ν.restrict (chartAt V q).source).map (extChartAt 𝓘(ℝ, V) q) = μ.withDensity ρ) :
    ν (F '' {x | ¬ Function.Injective (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) F x)}) = 0 := by
  simpa only [mfderiv_det_eq_zero_iff_not_injective] using
    sard_manifold_measure_of_chart_densities μ hF ν hν

end Manifold

end LiquidDrop
