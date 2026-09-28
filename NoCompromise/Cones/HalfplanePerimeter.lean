import NoCompromise.DeGiorgi.SmoothBoundary
import NoCompromise.BV.FlatCutMeasure
import NoCompromise.Regularity.DeformationCutBounds
import NoCompromise.Regularity.IsometryMinimal

/-!
# Perimeter of a coordinate halfspace (toward `lem:cone-2d`)

The perimeter of the open lower halfspace `{z | z (Fin.last k) < a}` in an open set `U` is the
flat hyperplane measure of `U`, i.e. the `k`-dimensional Lebesgue measure of the slice
`{x | graphAppendN x a ∈ U}`. In the plane (`k = 1`) this is the length of the horizontal line
inside `U`, the basic computation for chord competitors.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace LiquidDrop

/-- The perimeter of a coordinate lower halfspace is the flat hyperplane measure. -/
theorem perimeterIn_lowerHalfspace_eq_flat {k : ℕ} (a : ℝ)
    {U : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hU : IsOpen U) :
    perimeterIn {z : EuclideanSpace ℝ (Fin (k + 1)) | z (Fin.last k) < a} U =
      flatHyperplaneMeasure k a U := by
  have hf : ContDiff ℝ 1 (fun _ : EuclideanSpace ℝ (Fin k) => a) := contDiff_const
  change perimeterIn (smoothSubgraph (fun _ : EuclideanSpace ℝ (Fin k) => a)) U = _
  rw [perimeterIn_smoothSubgraph hf hU, smoothGraphArea_eq_map hf]
  have hg : (fun x : EuclideanSpace ℝ (Fin k) =>
      ENNReal.ofReal (Real.sqrt (1 + ‖gradient (fun _ : EuclideanSpace ℝ (Fin k) => a) x‖ ^ 2)))
        = 1 := by
    funext x
    simp [gradient]
  rw [hg, withDensity_one]
  rfl

/-- The graph of a constant function is the corresponding coordinate hyperplane. -/
lemma range_graphMapN_const {k : ℕ} (c : ℝ) :
    range (graphMapN (fun _ : EuclideanSpace ℝ (Fin k) => c)) =
      {z : EuclideanSpace ℝ (Fin (k + 1)) | z (Fin.last k) = c} := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    exact graphAppendN_last y c
  · intro hz
    refine ⟨graphProjectionN k z, ?_⟩
    change graphAppendN (graphProjectionN k z) c = z
    rw [← (show z (Fin.last k) = c from hz), graphAppendN_projection]

/-- The perimeter of an open coordinate lower halfspace is the `k`-dimensional Hausdorff measure
of the coordinate hyperplane inside the open set. -/
theorem perimeterIn_lowerHalfspace_eq_hausdorff {k : ℕ} (c : ℝ)
    {U : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hU : IsOpen U) :
    perimeterIn {z : EuclideanSpace ℝ (Fin (k + 1)) | z (Fin.last k) < c} U =
      Measure.euclideanHausdorffMeasure k (U ∩ {z | z (Fin.last k) = c}) := by
  have hf : ContDiff ℝ 1 (fun _ : EuclideanSpace ℝ (Fin k) => c) := contDiff_const
  change perimeterIn (smoothSubgraph (fun _ : EuclideanSpace ℝ (Fin k) => c)) U = _
  rw [perimeterIn_smoothSubgraph hf hU, smoothGraphArea,
    Measure.restrict_apply hU.measurableSet, range_graphMapN_const]

/-- **Halfspace perimeter.** For a unit vector `ν`, the perimeter of the open halfspace
`{z | ⟪z, ν⟫ < c}` in a bounded (finite-volume) open set `U` is the `k`-dimensional Hausdorff
measure of the hyperplane `{⟪z, ν⟫ = c}` inside `U`. -/
theorem perimeterIn_halfspace_eq_hausdorff {k : ℕ}
    {ν : EuclideanSpace ℝ (Fin (k + 1))} (hν : ‖ν‖ = 1) (c : ℝ)
    {U : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hU : IsOpen U) (hvol : volume U ≠ ⊤) :
    perimeterIn {z | inner ℝ z ν < c} U =
      Measure.euclideanHausdorffMeasure k (U ∩ {z | inner ℝ z ν = c}) := by
  let u : EuclideanSpace ℝ (Fin (k + 1)) := EuclideanSpace.single (Fin.last k) 1
  let e := (ℝ ∙ (u - ν))ᗮ.reflection
  have heu : e u = ν := Submodule.reflection_sub (by simpa [u] using hν.symm)
  have he (x : EuclideanSpace ℝ (Fin (k + 1))) : inner ℝ (e x) ν = x (Fin.last k) := by
    rw [← heu, e.inner_map_map]
    simp [u, EuclideanSpace.inner_single_right]
  let a := e.toAffineIsometryEquiv
  have hD : IsOpen (a ⁻¹' U) := hU.preimage a.continuous
  have hvolD : volume (a ⁻¹' U) ≠ ⊤ := by
    rwa [(measurePreserving_affineIsometry a).measure_preimage
      hU.measurableSet.nullMeasurableSet]
  have hE : NullMeasurableSet {z : EuclideanSpace ℝ (Fin (k + 1)) | inner ℝ z ν < c} volume :=
    (isOpen_lt (continuous_id.inner continuous_const) continuous_const).measurableSet
      |>.nullMeasurableSet
  have hpre : a ⁻¹' {z | inner ℝ z ν < c} = {z | z (Fin.last k) < c} := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq]
    exact iff_of_eq (congrArg (· < c) (he x))
  have himg : a '' (a ⁻¹' U) = U := a.surjective.image_preimage U
  have h := perimeterIn_preimage_affineIsometry_eq hD hvolD a hE
  rw [hpre, himg, perimeterIn_lowerHalfspace_eq_hausdorff c hD] at h
  rw [← h, ← a.isometry.euclideanHausdorffMeasure_image]
  congr 1
  ext z
  constructor
  · rintro ⟨x, ⟨hxU, hx⟩, rfl⟩
    exact ⟨hxU, by simpa [a, mem_ofPred_eq, he x] using hx⟩
  · rintro ⟨hzU, hz⟩
    refine ⟨a.symm z, ⟨by simpa using hzU, ?_⟩, a.apply_symm_apply z⟩
    show (a.symm z) (Fin.last k) = c
    rw [← he (a.symm z)]
    change inner ℝ (a (a.symm z)) ν = c
    rw [a.apply_symm_apply]
    exact hz

/-- **Halfspace cut.** Intersecting a set of locally finite perimeter with an open halfspace costs
at most the Hausdorff measure of the bounding hyperplane inside a bounded open set. -/
theorem perimeterIn_inter_halfspace_le {k : ℕ} {E : Set (EuclideanSpace ℝ (Fin (k + 1)))}
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {ν : EuclideanSpace ℝ (Fin (k + 1))} (hν : ‖ν‖ = 1) (c : ℝ)
    {U : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hU : IsOpen U) (hvol : volume U ≠ ⊤) :
    perimeterIn (E ∩ {z | inner ℝ z ν < c}) U ≤
      perimeterIn E U + Measure.euclideanHausdorffMeasure k (U ∩ {z | inner ℝ z ν = c}) := by
  let u : EuclideanSpace ℝ (Fin (k + 1)) := EuclideanSpace.single (Fin.last k) 1
  let e := (ℝ ∙ (u - ν))ᗮ.reflection
  have heu : e u = ν := Submodule.reflection_sub (by simpa [u] using hν.symm)
  have he (x : EuclideanSpace ℝ (Fin (k + 1))) : inner ℝ (e x) ν = x (Fin.last k) := by
    rw [← heu, e.inner_map_map]
    simp [u, EuclideanSpace.inner_single_right]
  let a := e.toAffineIsometryEquiv
  have hD : IsOpen (a ⁻¹' U) := hU.preimage a.continuous
  have hvolD : volume (a ⁻¹' U) ≠ ⊤ := by
    rwa [(measurePreserving_affineIsometry a).measure_preimage
      hU.measurableSet.nullMeasurableSet]
  have hH : NullMeasurableSet {z : EuclideanSpace ℝ (Fin (k + 1)) | inner ℝ z ν < c} volume :=
    (isOpen_lt (continuous_id.inner continuous_const) continuous_const).measurableSet
      |>.nullMeasurableSet
  have hpre : a ⁻¹' {z | inner ℝ z ν < c} = {z | z (Fin.last k) < c} := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq]
    exact iff_of_eq (congrArg (· < c) (he x))
  have himg : a '' (a ⁻¹' U) = U := a.surjective.image_preimage U
  have hqmp := (measurePreserving_affineIsometry a).quasiMeasurePreserving
  have h1 := perimeterIn_inter_lowerHalfspace_le (hE.preimage_affineIsometry hmE a)
    (hmE.preimage hqmp) c hD
  rw [← perimeterIn_lowerHalfspace_eq_flat c hD, ← hpre, ← preimage_inter,
    perimeterIn_preimage_affineIsometry_eq hD hvolD a (hmE.inter hH),
    perimeterIn_preimage_affineIsometry_eq hD hvolD a hmE,
    perimeterIn_preimage_affineIsometry_eq hD hvolD a hH, himg,
    perimeterIn_halfspace_eq_hausdorff hν c hU hvol] at h1
  exact h1

/-- The unit-speed affine parametrization of a line is an isometry. -/
lemma isometry_linePoint_unit {k : ℕ} {w : EuclideanSpace ℝ (Fin k)} (hw : ‖w‖ = 1)
    (p : EuclideanSpace ℝ (Fin k)) : Isometry (fun t : ℝ => p + t • w) := by
  refine Isometry.of_dist_eq fun s t => ?_
  rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, hw, mul_one, Real.dist_eq,
    Real.norm_eq_abs]

/-- One-dimensional Hausdorff measure on a unit-speed line is Lebesgue measure of the parameters. -/
theorem euclideanHausdorffMeasure_one_linePoint {k : ℕ} {w : EuclideanSpace ℝ (Fin k)}
    (hw : ‖w‖ = 1) (p : EuclideanSpace ℝ (Fin k)) (S : Set ℝ) :
    Measure.euclideanHausdorffMeasure 1 ((fun t : ℝ => p + t • w) '' S) = volume S := by
  rw [(isometry_linePoint_unit hw p).euclideanHausdorffMeasure_image]
  have h := InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := ℝ)
  rw [Module.finrank_self] at h
  rw [h]

/-- The length of a segment. -/
theorem euclideanHausdorffMeasure_one_segment {k : ℕ} {p q : EuclideanSpace ℝ (Fin k)}
    (hpq : p ≠ q) :
    Measure.euclideanHausdorffMeasure 1 (segment ℝ p q) = ENNReal.ofReal (dist p q) := by
  have hd : 0 < dist p q := dist_pos.mpr hpq
  let w : EuclideanSpace ℝ (Fin k) := (dist p q)⁻¹ • (q - p)
  have hw : ‖w‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hd, ← dist_eq_norm, dist_comm q p,
      inv_mul_cancel₀ hd.ne']
  have hseg : segment ℝ p q = (fun t : ℝ => p + t • w) '' Icc 0 (dist p q) := by
    rw [segment_eq_image_lineMap]
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨s * dist p q, ⟨mul_nonneg hs.1 hd.le, by nlinarith [hs.2]⟩, ?_⟩
      simp only [w, smul_smul, AffineMap.lineMap_apply_module']
      rw [mul_assoc, mul_inv_cancel₀ hd.ne', mul_one]
      abel
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t / dist p q, ⟨div_nonneg ht.1 hd.le, (div_le_one hd).mpr ht.2⟩, ?_⟩
      simp only [w, smul_smul, AffineMap.lineMap_apply_module']
      rw [div_eq_mul_inv]
      abel
  rw [hseg, euclideanHausdorffMeasure_one_linePoint hw, Real.volume_Icc, sub_zero]

/-- A coordinate lower halfspace has locally finite perimeter. -/
theorem hasLocallyFinitePerimeter_lowerHalfspace {k : ℕ} (c : ℝ) :
    HasLocallyFinitePerimeter {z : EuclideanSpace ℝ (Fin (k + 1)) | z (Fin.last k) < c} := by
  intro U hU hcU
  rw [perimeterIn_lowerHalfspace_eq_flat c hU]
  exact (measure_mono subset_closure).trans_lt hcU.measure_lt_top

/-- Every open halfspace with unit normal has locally finite perimeter. -/
theorem hasLocallyFinitePerimeter_halfspace {k : ℕ}
    {ν : EuclideanSpace ℝ (Fin (k + 1))} (hν : ‖ν‖ = 1) (c : ℝ) :
    HasLocallyFinitePerimeter {z : EuclideanSpace ℝ (Fin (k + 1)) | inner ℝ z ν < c} := by
  let u : EuclideanSpace ℝ (Fin (k + 1)) := EuclideanSpace.single (Fin.last k) 1
  let e := (ℝ ∙ (u - ν))ᗮ.reflection
  have heu : e u = ν := Submodule.reflection_sub (by simpa [u] using hν.symm)
  have he (x : EuclideanSpace ℝ (Fin (k + 1))) : inner ℝ (e x) ν = x (Fin.last k) := by
    rw [← heu, e.inner_map_map]
    simp [u, EuclideanSpace.inner_single_right]
  let a := e.toAffineIsometryEquiv
  have hpre : a.symm ⁻¹' {z : EuclideanSpace ℝ (Fin (k + 1)) | z (Fin.last k) < c} =
      {z | inner ℝ z ν < c} := by
    ext z
    simp only [mem_preimage, mem_ofPred_eq]
    rw [← he (a.symm z)]
    change inner ℝ (a (a.symm z)) ν < c ↔ _
    rw [a.apply_symm_apply]
  have h0 := hasLocallyFinitePerimeter_lowerHalfspace (k := k) c
  have hm0 : NullMeasurableSet {z : EuclideanSpace ℝ (Fin (k + 1)) | z (Fin.last k) < c}
      volume :=
    (isOpen_lt (EuclideanSpace.proj (Fin.last k)).continuous continuous_const).measurableSet
      |>.nullMeasurableSet
  simpa only [hpre] using h0.preimage_affineIsometry hm0 a.symm

/-- **Three halfspaces.** The perimeter of an intersection of three open halfspaces in a bounded
open set is at most the sum of the Hausdorff measures of the three bounding hyperplanes there. -/
theorem perimeterIn_inter_three_halfspaces_le {k : ℕ}
    {ν₁ ν₂ ν₃ : EuclideanSpace ℝ (Fin (k + 1))} (h₁ : ‖ν₁‖ = 1) (h₂ : ‖ν₂‖ = 1)
    (h₃ : ‖ν₃‖ = 1) (c₁ c₂ c₃ : ℝ)
    {U : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hU : IsOpen U) (hvol : volume U ≠ ⊤) :
    perimeterIn ({z | inner ℝ z ν₁ < c₁} ∩ {z | inner ℝ z ν₂ < c₂} ∩
        {z | inner ℝ z ν₃ < c₃}) U ≤
      Measure.euclideanHausdorffMeasure k (U ∩ {z | inner ℝ z ν₁ = c₁}) +
        Measure.euclideanHausdorffMeasure k (U ∩ {z | inner ℝ z ν₂ = c₂}) +
        Measure.euclideanHausdorffMeasure k (U ∩ {z | inner ℝ z ν₃ = c₃}) := by
  have hmeas (ν : EuclideanSpace ℝ (Fin (k + 1))) (c : ℝ) :
      NullMeasurableSet {z : EuclideanSpace ℝ (Fin (k + 1)) | inner ℝ z ν < c} volume :=
    (isOpen_lt (continuous_id.inner continuous_const) continuous_const).measurableSet
      |>.nullMeasurableSet
  have h12 (V : Set (EuclideanSpace ℝ (Fin (k + 1)))) (hV : IsOpen V) (hvV : volume V ≠ ⊤) :
      perimeterIn ({z | inner ℝ z ν₁ < c₁} ∩ {z | inner ℝ z ν₂ < c₂}) V ≤
        Measure.euclideanHausdorffMeasure k (V ∩ {z | inner ℝ z ν₁ = c₁}) +
          Measure.euclideanHausdorffMeasure k (V ∩ {z | inner ℝ z ν₂ = c₂}) := by
    have h := perimeterIn_inter_halfspace_le (hasLocallyFinitePerimeter_halfspace h₁ c₁)
      (hmeas ν₁ c₁) h₂ c₂ hV hvV
    rwa [perimeterIn_halfspace_eq_hausdorff h₁ c₁ hV hvV] at h
  have hlf : HasLocallyFinitePerimeter ({z | inner ℝ z ν₁ < c₁} ∩ {z | inner ℝ z ν₂ < c₂}) := by
    intro V hV hcV
    have hvV : volume V ≠ ⊤ := ((measure_mono subset_closure).trans_lt hcV.measure_lt_top).ne
    refine (h12 V hV hvV).trans_lt (ENNReal.add_lt_top.mpr ⟨?_, ?_⟩)
    · rw [← perimeterIn_halfspace_eq_hausdorff h₁ c₁ hV hvV]
      exact hasLocallyFinitePerimeter_halfspace h₁ c₁ V hV hcV
    · rw [← perimeterIn_halfspace_eq_hausdorff h₂ c₂ hV hvV]
      exact hasLocallyFinitePerimeter_halfspace h₂ c₂ V hV hcV
  have h := perimeterIn_inter_halfspace_le hlf ((hmeas ν₁ c₁).inter (hmeas ν₂ c₂)) h₃ c₃ hU hvol
  exact h.trans (add_le_add (h12 U hU hvol) le_rfl)

/-- Points carry no one-dimensional Hausdorff measure in positive dimension. -/
theorem euclideanHausdorffMeasure_one_singleton {k : ℕ} (p : EuclideanSpace ℝ (Fin (k + 1))) :
    Measure.euclideanHausdorffMeasure 1 ({p} : Set (EuclideanSpace ℝ (Fin (k + 1)))) = 0 := by
  have hw : ‖(EuclideanSpace.single (Fin.last k) (1 : ℝ) : EuclideanSpace ℝ (Fin (k + 1)))‖ = 1 := by
    simp
  have h := euclideanHausdorffMeasure_one_linePoint hw p {0}
  rw [image_singleton, zero_smul, add_zero, Real.volume_singleton] at h
  exact h

/-- The part of a hyperplane inside a thickening of a compact set has finite Hausdorff measure. -/
theorem euclideanHausdorffMeasure_thickening_inter_hyperplane_ne_top {k : ℕ}
    {ν : EuclideanSpace ℝ (Fin (k + 1))} (hν : ‖ν‖ = 1) (c : ℝ)
    {K : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hK : IsCompact K) (R : ℝ) :
    Measure.euclideanHausdorffMeasure k (Metric.thickening R K ∩ {z | inner ℝ z ν = c}) ≠ ⊤ := by
  have hcl : IsCompact (closure (Metric.thickening R K)) :=
    (hK.cthickening (r := R)).of_isClosed_subset isClosed_closure
      (Metric.closure_thickening_subset_cthickening _ _)
  have hvol : volume (Metric.thickening R K) ≠ ⊤ :=
    ((measure_mono subset_closure).trans_lt hcl.measure_lt_top).ne
  rw [← perimeterIn_halfspace_eq_hausdorff hν c Metric.isOpen_thickening hvol]
  exact (hasLocallyFinitePerimeter_halfspace hν c _ Metric.isOpen_thickening hcl).ne

/-- **Chord cost.** If near a compact set `K` a set `G` agrees almost everywhere with an
intersection of three open halfspaces, then the perimeter measure of `G` charges `K` at most by
the Hausdorff measures of `K` intersected with the three bounding hyperplanes. Corners, where the
hyperplanes meet, cost nothing. -/
theorem measure_le_of_ae_eq_three_halfspaces {k : ℕ}
    {G : Set (EuclideanSpace ℝ (Fin (k + 1)))} {μ : Measure (EuclideanSpace ℝ (Fin (k + 1)))}
    (hμ : ∀ O, IsOpen O → perimeterIn G O = μ O)
    {K : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hK : IsCompact K)
    {ν₁ ν₂ ν₃ : EuclideanSpace ℝ (Fin (k + 1))} (h₁ : ‖ν₁‖ = 1) (h₂ : ‖ν₂‖ = 1)
    (h₃ : ‖ν₃‖ = 1) (c₁ c₂ c₃ : ℝ) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hG : G =ᵐ[volume.restrict (Metric.thickening ε₀ K)]
      ({z | inner ℝ z ν₁ < c₁} ∩ {z | inner ℝ z ν₂ < c₂} ∩ {z | inner ℝ z ν₃ < c₃} :
        Set (EuclideanSpace ℝ (Fin (k + 1))))) :
    μ K ≤ Measure.euclideanHausdorffMeasure k (K ∩ {z | inner ℝ z ν₁ = c₁}) +
      Measure.euclideanHausdorffMeasure k (K ∩ {z | inner ℝ z ν₂ = c₂}) +
      Measure.euclideanHausdorffMeasure k (K ∩ {z | inner ℝ z ν₃ = c₃}) := by
  have hlim (ν : EuclideanSpace ℝ (Fin (k + 1))) (hν : ‖ν‖ = 1) (c : ℝ) :
      Tendsto (fun ε => Measure.euclideanHausdorffMeasure k
          (Metric.thickening ε K ∩ {z | inner ℝ z ν = c}))
        (𝓝[>] 0) (𝓝 (Measure.euclideanHausdorffMeasure k (K ∩ {z | inner ℝ z ν = c}))) := by
    have hL : MeasurableSet {z : EuclideanSpace ℝ (Fin (k + 1)) | inner ℝ z ν = c} :=
      (isClosed_eq (continuous_id.inner continuous_const) continuous_const).measurableSet
    have h := tendsto_measure_thickening_of_isClosed
      (μ := (Measure.euclideanHausdorffMeasure k).restrict
        {z : EuclideanSpace ℝ (Fin (k + 1)) | inner ℝ z ν = c})
      ⟨1, one_pos, by
        rw [Measure.restrict_apply Metric.isOpen_thickening.measurableSet]
        exact euclideanHausdorffMeasure_thickening_inter_hyperplane_ne_top hν c hK 1⟩
      hK.isClosed
    rw [Measure.restrict_apply hK.isClosed.measurableSet] at h
    refine h.congr' ?_
    filter_upwards with ε
    rw [Measure.restrict_apply Metric.isOpen_thickening.measurableSet]
  have hsum := ((hlim ν₁ h₁ c₁).add (hlim ν₂ h₂ c₂)).add (hlim ν₃ h₃ c₃)
  refine ge_of_tendsto hsum ?_
  filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε
  have hcl : IsCompact (closure (Metric.thickening ε K)) :=
    (hK.cthickening (r := ε)).of_isClosed_subset isClosed_closure
      (Metric.closure_thickening_subset_cthickening _ _)
  have hvol : volume (Metric.thickening ε K) ≠ ⊤ :=
    ((measure_mono subset_closure).trans_lt hcl.measure_lt_top).ne
  have hsub : Metric.thickening ε K ⊆ Metric.thickening ε₀ K :=
    Metric.thickening_mono hε.2.le K
  calc μ K ≤ μ (Metric.thickening ε K) := measure_mono (Metric.self_subset_thickening hε.1 K)
    _ = perimeterIn G (Metric.thickening ε K) := (hμ _ Metric.isOpen_thickening).symm
    _ = perimeterIn ({z | inner ℝ z ν₁ < c₁} ∩ {z | inner ℝ z ν₂ < c₂} ∩
          {z | inner ℝ z ν₃ < c₃}) (Metric.thickening ε K) :=
        perimeterIn_congr_ae _ (ae_restrict_of_ae_restrict_of_subset hsub hG)
    _ ≤ _ := perimeterIn_inter_three_halfspaces_le h₁ h₂ h₃ c₁ c₂ c₃
          Metric.isOpen_thickening hvol

end LiquidDrop
