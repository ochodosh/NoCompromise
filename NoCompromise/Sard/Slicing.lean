import NoCompromise.Sard.VectorFlat
import NoCompromise.Sard.LevelCharts
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Reduction of critical values by one regular coordinate

A scalar inverse chart straightens one nonzero component derivative. Fubini
then reduces the critical-value problem to maps with one fewer source and target
coordinate. All coordinate maps retain C² regularity.
-/

noncomputable section
open MeasureTheory Set Filter Metric Function InnerProductSpace
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The target Gram determinant vanishes exactly when a linear map is not onto. -/
lemma det_self_comp_adjoint_eq_zero_iff_not_surjective {n m : ℕ}
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    (L.comp L.adjoint).det = 0 ↔ ¬ Surjective L := by
  change (L.toLinearMap.comp L.adjoint.toLinearMap).det = 0 ↔ ¬ Surjective L
  rw [LinearMap.det_eq_zero_iff_ker_ne_bot, ne_eq, LinearMap.ker_eq_bot,
    LinearMap.injective_iff_surjective, ← LinearMap.range_eq_top,
    ← ContinuousLinearMap.adjoint_toLinearMap, LinearMap.range_self_comp_adjoint,
    LinearMap.range_eq_top]
  rfl

/-- Continuity of the target Gram determinant detects the closed critical stratum. -/
lemma continuousOn_target_gram_det {n m : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (hf : ContDiffOn ℝ 1 f U) :
    ContinuousOn (fun x => ((fderiv ℝ f x).comp (fderiv ℝ f x).adjoint).det) U := by
  have hc : Continuous (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin m) => (L.comp L.adjoint).det) := by
    apply ContinuousLinearMap.continuous_det.comp
    fun_prop
  exact hc.comp_continuousOn (hf.continuousOn_fderiv_of_isOpen hU le_rfl)

/-- Critical points in an open Euclidean domain are exhausted by compact sets. -/
lemma exists_compact_cover_critical {n m : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (hf : ContDiffOn ℝ 1 f U) :
    ∃ K : ℕ → Set (EuclideanSpace ℝ (Fin n)),
      (∀ j, IsCompact (K j)) ∧
      (∀ j, K j ⊆ {x | x ∈ U ∧ ¬ Surjective (fderiv ℝ f x)}) ∧
      {x | x ∈ U ∧ ¬ Surjective (fderiv ℝ f x)} = ⋃ j, K j := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let C := CompactExhaustion.choice U
  let A (j : ℕ) : Set (EuclideanSpace ℝ (Fin n)) := Subtype.val '' C j
  have hAc j : IsCompact (A j) := (C.isCompact j).image continuous_subtype_val
  have hAU j : A j ⊆ U := by rintro _ ⟨x, _, rfl⟩; exact x.property
  let d (x : EuclideanSpace ℝ (Fin n)) :=
    ((fderiv ℝ f x).comp (fderiv ℝ f x).adjoint).det
  let K j := A j ∩ d ⁻¹' {0}
  have hd : ContinuousOn d U := continuousOn_target_gram_det hU hf
  refine ⟨K, ?_, ?_, ?_⟩
  · intro j
    apply (hAc j).of_isClosed_subset _ inter_subset_left
    exact (hd.mono (hAU j)).preimage_isClosed_of_isClosed (hAc j).isClosed isClosed_singleton
  · intro j x hx
    exact ⟨hAU j hx.1, (det_self_comp_adjoint_eq_zero_iff_not_surjective _).mp hx.2⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := C.exists_mem ⟨x, hx.1⟩
      exact mem_iUnion.mpr ⟨j, ⟨⟨x, hx.1⟩, hj, rfl⟩,
        (det_self_comp_adjoint_eq_zero_iff_not_surjective _).mpr hx.2⟩
    · intro hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      exact ⟨hAU j hj.1, (det_self_comp_adjoint_eq_zero_iff_not_surjective _).mp hj.2⟩

/-- The critical image of a C¹ Euclidean map on an open domain is Borel. -/
lemma measurableSet_image_critical {n m : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (hf : ContDiffOn ℝ 1 f U) :
    MeasurableSet (f '' {x | x ∈ U ∧ ¬ Surjective (fderiv ℝ f x)}) := by
  obtain ⟨K, hK, hKU, hcover⟩ := exists_compact_cover_critical hU hf
  rw [hcover, image_iUnion]
  apply MeasurableSet.iUnion
  intro j
  exact ((hK j).image_of_continuousOn
    (hf.continuousOn.mono fun x hx => (hKU j hx).1)).measurableSet

/-- In last-coordinate normal form, onto horizontal derivatives imply an onto full derivative. -/
lemma surjective_of_graphBase_comp_surjective {n m : ℕ}
    (L : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))
    (hlast : ∀ v, L v (Fin.last m) = v (Fin.last n))
    (h : Surjective ((graphProjectionN m).comp (L.comp (graphBaseN n)))) :
    Surjective L := by
  intro y
  let v := EuclideanSpace.single (Fin.last n) (1 : ℝ)
  obtain ⟨z, hz⟩ := h (graphProjectionN m y - y (Fin.last m) • graphProjectionN m (L v))
  refine ⟨graphBaseN n z + y (Fin.last m) • v, ?_⟩
  apply PiLp.ext
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [hlast]
    simp [v, graphBaseN]
  · have hh := congrArg (fun p : EuclideanSpace ℝ (Fin m) => p j) hz
    simp only [ContinuousLinearMap.comp_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul, graphProjectionN_apply] at hh
    simp only [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    linarith

/-- The precise C² critical-value assertion used in the dimension-reduction induction. -/
def HasNullCriticalValuesC2 (n m : ℕ) : Prop :=
  ∀ (U : Set (EuclideanSpace ℝ (Fin n))) (_ : IsOpen U)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)),
    ContDiffOn ℝ 2 f U → volume (f '' {x | x ∈ U ∧ ¬ Surjective (fderiv ℝ f x)}) = 0

/-- Differentiating the fixed last coordinate of a normal-form map. -/
lemma fderiv_last_of_normal_form {n m : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (m + 1))}
    (hf : ContDiffOn ℝ 1 f U) (hlast : ∀ x ∈ U, f x (Fin.last m) = x (Fin.last n))
    {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : x ∈ U) (v) :
    fderiv ℝ f x v (Fin.last m) = v (Fin.last n) := by
  have hd := (EuclideanSpace.proj (Fin.last m)).hasFDerivAt.comp x
    ((hf.differentiableOn (by norm_num) x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have heq : (fun y => f y (Fin.last m)) =ᶠ[𝓝 x] fun y => y (Fin.last n) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hlast y hy
  have hdeq := (hd.congr_of_eventuallyEq heq.symm).fderiv
  have hlin : (EuclideanSpace.proj (Fin.last m)).comp (fderiv ℝ f x) =
      EuclideanSpace.proj (Fin.last n) := by
    change fderiv ℝ (EuclideanSpace.proj (Fin.last n)) x =
      (EuclideanSpace.proj (Fin.last m)).comp (fderiv ℝ f x) at hdeq
    rw [ContinuousLinearMap.fderiv] at hdeq
    exact hdeq.symm
  exact congrArg (fun L : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ => L v) hlin

/-- Fubini reduces critical values by one dimension in last-coordinate normal form. -/
theorem measure_image_critical_normal_form {n m : ℕ} (hSard : HasNullCriticalValuesC2 n m)
    {U : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (m + 1))}
    (hf : ContDiffOn ℝ 2 f U) (hlast : ∀ x ∈ U, f x (Fin.last m) = x (Fin.last n)) :
    volume (f '' {x | x ∈ U ∧ ¬ Surjective (fderiv ℝ f x)}) = 0 := by
  let S := {x | x ∈ U ∧ ¬ Surjective (fderiv ℝ f x)}
  have hm : MeasurableSet (f '' S) := measurableSet_image_critical hU (hf.of_le (by norm_num))
  let e := euclideanLastEquiv m
  have he : MeasurePreserving e volume (volume.prod volume) :=
    euclideanLastEquiv_measurePreserving m
  have hme : MeasurableSet (e '' (f '' S)) := hm.image_of_continuousOn_injOn
    e.continuous.continuousOn e.injective.injOn
  have hslice (t : ℝ) : volume (Prod.mk t ⁻¹' (e '' (f '' S))) = 0 := by
    let V := (fun y => graphAppendN y t) ⁻¹' U
    let g := fun y => graphProjectionN m (f (graphAppendN y t))
    have hV : IsOpen V := hU.preimage (contDiff_graphAppendN t (r := 2)).continuous
    have hg : ContDiffOn ℝ 2 g V :=
      (graphProjectionN m).contDiff.comp_contDiffOn
        (hf.comp (contDiff_graphAppendN t).contDiffOn (fun _ hy => hy))
    apply measure_mono_null (t := g '' {y | y ∈ V ∧ ¬ Surjective (fderiv ℝ g y)}) ?_
      (hSard V hV g hg)
    intro z hz
    obtain ⟨_, ⟨x, hx, rfl⟩, heq⟩ := hz
    have hxt : x (Fin.last n) = t := by
      have ht := congrArg Prod.fst heq
      exact (hlast x hx.1).symm.trans ht
    have hxeq : graphAppendN (graphProjectionN n x) t = x := by
      rw [← hxt, graphAppendN_projection]
    refine ⟨graphProjectionN n x, ⟨?_, ?_⟩, ?_⟩
    · change graphAppendN (graphProjectionN n x) t ∈ U
      rw [hxeq]
      exact hx.1
    · intro hs
      have hdf := ((hf.differentiableOn (by norm_num) x hx.1).differentiableAt
        (hU.mem_nhds hx.1)).hasFDerivAt
      have hd := (graphProjectionN m).hasFDerivAt.comp (graphProjectionN n x)
        ((hxeq ▸ hdf).comp (graphProjectionN n x)
          (hasFDerivAt_graphAppendN t (graphProjectionN n x)))
      have hdg : HasFDerivAt g ((graphProjectionN m).comp
          ((fderiv ℝ f x).comp (graphBaseN n))) (graphProjectionN n x) := by
        simpa only [g, Function.comp_def, hxeq] using hd
      rw [hdg.fderiv] at hs
      exact hx.2 (surjective_of_graphBase_comp_surjective (fderiv ℝ f x)
        (fderiv_last_of_normal_form hU (hf.of_le (by norm_num)) hlast hx.1) hs)
    · change graphProjectionN m (f (graphAppendN (graphProjectionN n x) t)) = z
      rw [hxeq]
      exact congrArg Prod.snd heq
  have hnull : (volume.prod volume) (e '' (f '' S)) = 0 := by
    rw [Measure.prod_apply hme]
    simp only [hslice, lintegral_zero]
  rw [← he.measure_preimage hme.nullMeasurableSet] at hnull
  simpa only [Set.preimage_image_eq _ e.injective] using hnull

/-- A nonzero final partial derivative of the final target component supplies
a neighborhood with null critical image, assuming the lower-dimensional assertion. -/
theorem exists_null_critical_image_neighborhood_last {n m : ℕ}
    (hSard : HasNullCriticalValuesC2 n m)
    {U : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (m + 1))}
    (hf : ContDiffOn ℝ 2 f U) {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : x ∈ U)
    (hp : gradient (fun y => f y (Fin.last m)) x (Fin.last n) ≠ 0) :
    ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      volume (f '' ({y | y ∈ U ∧ ¬ Surjective (fderiv ℝ f y)} ∩ V)) = 0 := by
  let u := fun y => f y (Fin.last m)
  have hu : ContDiffOn ℝ 2 u U := by
    change ContDiffOn ℝ 2
      ((EuclideanSpace.proj (Fin.last m) : EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] ℝ) ∘ f) U
    exact (EuclideanSpace.proj (Fin.last m)).contDiff.comp_contDiffOn hf
  obtain ⟨d, hxd, hdU⟩ := exists_scalarCoareaChart hU (hu.of_le (by norm_num)) hx hp
  have hinv : ContDiffOn ℝ 2 d.chart.symm d.chart.target := by
    intro y hy
    have hys := d.chart.map_target hy
    apply (d.chart.contDiffAt_symm hy (d.hasFDerivAt_forward hys) ?_).contDiffWithinAt
    rw [d.forward_eq]
    exact (contDiffOn_coareaCoordinateMap (hu.mono hdU)).contDiffAt
      (d.chart.open_source.mem_nhds hys)
  have hg : ContDiffOn ℝ 2 (f ∘ d.chart.symm) d.chart.target :=
    hf.comp hinv (fun _ hy => hdU (d.chart.map_target hy))
  have hlast : ∀ y ∈ d.chart.target,
      (f ∘ d.chart.symm) y (Fin.last m) = y (Fin.last n) := by
    intro y hy
    have h := congrArg (fun z => z (Fin.last n)) (d.chart.right_inv hy)
    rw [d.forward_eq] at h
    simpa only [coareaCoordinateMap_last, u, Function.comp_def] using h
  have hnull := measure_image_critical_normal_form hSard d.chart.open_target hg hlast
  refine ⟨d.chart.source, d.chart.open_source, hxd, hdU, ?_⟩
  apply measure_mono_null ?_ hnull
  rintro _ ⟨y, hy, rfl⟩
  have hys := hy.2
  have hyt := d.chart.map_source hys
  have hd := ((hf.differentiableOn (by norm_num) y hy.1.1).differentiableAt
    (hU.mem_nhds hy.1.1)).hasFDerivAt
  have hin := d.hasFDerivAt_inverse hyt
  have hdy : d.chart.symm (d.chart y) = y := d.chart.left_inv hys
  have hcomp := (hdy ▸ hd).comp (d.chart y) hin
  refine ⟨d.chart y, ⟨hyt, ?_⟩, ?_⟩
  · intro hs
    rw [hcomp.fderiv] at hs
    rw [ContinuousLinearMap.coe_comp] at hs
    have hsurj := hs.of_comp
    exact hy.1.2 (by simpa only [hdy] using hsurj)
  · exact congrArg f hdy

/-- Invertible linear changes of source and target preserve surjectivity. -/
lemma surjective_comp_equiv_iff {n m : ℕ}
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (a : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m)) :
    Surjective (b.toContinuousLinearMap.comp (L.comp a.toContinuousLinearMap)) ↔
      Surjective L := by
  constructor
  · intro h y
    obtain ⟨z, hz⟩ := h (b y)
    exact ⟨a z, b.injective hz⟩
  · intro h y
    obtain ⟨z, hz⟩ := h (b.symm y)
    refine ⟨a.symm z, ?_⟩
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      a.apply_symm_apply, hz, b.apply_symm_apply]

/-- Orthogonal coordinate changes preserve the critical-point condition. -/
lemma not_surjective_fderiv_comp_isometries_iff {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (a : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m))
    {x : EuclideanSpace ℝ (Fin n)} (hf : DifferentiableAt ℝ f (a x)) :
    (¬ Surjective (fderiv ℝ (b ∘ f ∘ a) x)) ↔ ¬ Surjective (fderiv ℝ f (a x)) := by
  have hd := b.toContinuousLinearEquiv.hasFDerivAt.comp x
    (hf.hasFDerivAt.comp x a.toContinuousLinearEquiv.hasFDerivAt)
  have hd' : HasFDerivAt (b ∘ f ∘ a)
      (b.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((fderiv ℝ f (a x)).comp a.toContinuousLinearEquiv.toContinuousLinearMap)) x := hd
  rw [hd'.fderiv, surjective_comp_equiv_iff]

/-- Every point with a nonzero derivative has a neighborhood with null critical
image, assuming Sard for one fewer source and target coordinate. -/
theorem exists_null_critical_image_neighborhood_of_fderiv_ne_zero {n m : ℕ}
    (hSard : HasNullCriticalValuesC2 n m)
    {U : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (m + 1))}
    (hf : ContDiffOn ℝ 2 f U) {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : x ∈ U)
    (hne : fderiv ℝ f x ≠ 0) :
    ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      volume (f '' ({y | y ∈ U ∧ ¬ Surjective (fderiv ℝ f y)} ∩ V)) = 0 := by
  have hdf := (hf.differentiableOn (by norm_num) x hx).differentiableAt (hU.mem_nhds hx)
  have hex : ∃ i : Fin (m + 1), gradient (fun y => f y i) x ≠ 0 := by
    by_contra! hz
    apply hne
    apply ContinuousLinearMap.ext
    intro v
    apply PiLp.ext
    intro i
    have hd := (EuclideanSpace.proj i).hasFDerivAt.comp x hdf.hasFDerivAt
    have hh : fderiv ℝ (fun y => f y i) x = 0 := by
      rw [← toDual_gradient, hz i, map_zero]
    have he := congrArg (fun L : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ => L v) hd.fderiv
    change fderiv ℝ (fun y => f y i) x v = fderiv ℝ f x v i at he
    rw [hh, zero_apply] at he
    exact he.symm
  obtain ⟨i, hi⟩ := hex
  have hrow : DifferentiableAt ℝ (fun y => f y i) x := by
    change DifferentiableAt ℝ
      ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] ℝ) ∘ f) x
    exact (EuclideanSpace.proj i).differentiableAt.comp x hdf
  obtain ⟨j, hj⟩ := exists_coareaSwap_nonzero_last hrow hi
  let a := coareaSwap j
  let b := coareaSwap i
  let F := b ∘ f ∘ a
  have hUa : IsOpen (a ⁻¹' U) := hU.preimage a.continuous
  have hF : ContDiffOn ℝ 2 F (a ⁻¹' U) :=
    b.toContinuousLinearEquiv.contDiff.comp_contDiffOn
      (hf.comp a.toContinuousLinearEquiv.contDiff.contDiffOn (fun _ hy => hy))
  have hxa : a.symm x ∈ a ⁻¹' U := by simpa only [mem_preimage, a.apply_symm_apply] using hx
  have hcomp : (fun y => F y (Fin.last m)) = (fun y => f y i) ∘ a := by
    funext y
    exact coareaSwap_apply_last i (f (a y))
  obtain ⟨V, hV, hxV, hVU, hnull⟩ := exists_null_critical_image_neighborhood_last
    hSard hUa hF hxa (by simpa only [hcomp] using hj)
  refine ⟨a '' V, a.toHomeomorph.isOpenMap _ hV,
    ⟨a.symm x, hxV, a.apply_symm_apply x⟩, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hVU hy
  · have hz : volume (b '' (f '' ({y | y ∈ U ∧ ¬ Surjective (fderiv ℝ f y)} ∩
        (a '' V)))) = 0 := by
      apply measure_mono_null ?_ hnull
      rintro _ ⟨_, ⟨_, ⟨hy, z, hz, rfl⟩, rfl⟩, rfl⟩
      refine ⟨z, ⟨⟨hVU hz, ?_⟩, hz⟩, rfl⟩
      apply (not_surjective_fderiv_comp_isometries_iff a b
        ((hf.differentiableOn (by norm_num) (a z) hy.1).differentiableAt
          (hU.mem_nhds hy.1))).mpr hy.2
    rw [← b.measurePreserving.measure_preimage_emb b.toHomeomorph.measurableEmbedding] at hz
    simpa only [Set.preimage_image_eq _ b.injective] using hz

/-- A C² Sard statement advances by one source and target dimension, provided
the rank-zero stratum satisfies the strict quadratic dimension inequality. -/
theorem HasNullCriticalValuesC2.succ {n m : ℕ} (hSard : HasNullCriticalValuesC2 n m)
    (hdim : n + 1 < 2 * (m + 1)) : HasNullCriticalValuesC2 (n + 1) (m + 1) := by
  intro U hU f hf
  let R := {x | x ∈ U ∧ ¬ Surjective (fderiv ℝ f x) ∧ fderiv ℝ f x ≠ 0}
  have hR : volume (f '' R) = 0 := by
    apply measure_vector_image_eq_zero_of_local_null
    intro x hx
    obtain ⟨V, hV, hxV, _, hnull⟩ :=
      exists_null_critical_image_neighborhood_of_fderiv_ne_zero hSard hU hf hx.1 hx.2.2
    refine ⟨V, hV, hxV, measure_mono_null (image_mono ?_) hnull⟩
    intro y hy
    exact ⟨⟨hy.1.1, hy.1.2.1⟩, hy.2⟩
  have hzero := measure_image_fderiv_zero_of_contDiffOn hdim hU hf
  apply measure_mono_null (t := f '' R ∪ f '' {x | x ∈ U ∧ fderiv ℝ f x = 0}) ?_
    (measure_union_null hR hzero)
  rintro _ ⟨x, hx, rfl⟩
  by_cases hz : fderiv ℝ f x = 0
  · exact Or.inr ⟨x, ⟨hx.1, hz⟩, rfl⟩
  · exact Or.inl ⟨x, ⟨hx.1, hx.2, hz⟩, rfl⟩

end LiquidDrop
