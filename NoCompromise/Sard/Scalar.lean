import NoCompromise.Sard.OneDimensional
import NoCompromise.BV.CoareaCharts
import NoCompromise.BV.CoareaIsometry
import Mathlib.Topology.Compactness.Lindelof

/-!
# Two-dimensional scalar Sard

The critical set splits into points with zero Hessian and points with a
nonzero derivative of some scalar component of the first derivative. The first
part has uniformly small quadratic remainders on compact subsets. Each point
of the second part has an inverse-function chart placing it on a C¹ curve;
the one-dimensional critical-value theorem applies on that curve.
-/

noncomputable section
open MeasureTheory Set Filter Function InnerProductSpace
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The compact twice-flat stratum has null image in the planar scalar case. -/
lemma measure_image_compact_twice_flat
    {U S : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsOpen U) (hS : IsCompact S)
    (hSU : S ⊆ U) {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hf : ContDiffOn ℝ 2 f U) (hfirst : ∀ x ∈ S, fderiv ℝ f x = 0)
    (hsecond : ∀ x ∈ S, fderiv ℝ (fderiv ℝ f) x = 0) :
    volume (f '' S) = 0 :=
  measure_image_eq_zero_of_bounded_uniform_flat hS.isBounded f
    (compact_uniform_quadratic_flat hU hS hSU hf hfirst hsecond)

/-- Compact exhaustion gives nullity of the full twice-flat stratum. -/
lemma measure_image_twice_flat
    {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : ContDiffOn ℝ 2 f U) :
    volume (f '' {x | x ∈ U ∧ fderiv ℝ f x = 0 ∧ fderiv ℝ (fderiv ℝ f) x = 0}) = 0 := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let K := CompactExhaustion.choice U
  let A : ℕ → Set (EuclideanSpace ℝ (Fin 2)) := fun j => Subtype.val '' K j
  have hAc (j : ℕ) : IsCompact (A j) := (K.isCompact j).image continuous_subtype_val
  have hAU (j : ℕ) : A j ⊆ U := by rintro _ ⟨x, _, rfl⟩; exact x.property
  have hdf : ContDiffOn ℝ 1 (fderiv ℝ f) U :=
    (contDiffOn_succ_iff_fderiv_of_isOpen hU).mp hf |>.2.2
  let S : ℕ → Set (EuclideanSpace ℝ (Fin 2)) := fun j =>
    A j ∩ (fun x => (fderiv ℝ f x, fderiv ℝ (fderiv ℝ f) x)) ⁻¹' {(0, 0)}
  have hSc (j : ℕ) : IsCompact (S j) := by
    apply (hAc j).of_isClosed_subset _ inter_subset_left
    exact (((hf.continuousOn_fderiv_of_isOpen hU (by norm_num)).prodMk
      (hdf.continuousOn_fderiv_of_isOpen hU le_rfl)).mono (hAU j)).preimage_isClosed_of_isClosed
      (hAc j).isClosed isClosed_singleton
  have hnull (j : ℕ) : volume (f '' S j) = 0 :=
    measure_image_compact_twice_flat hU (hSc j) (inter_subset_left.trans (hAU j)) hf
      (fun x hx => congrArg Prod.fst hx.2) (fun x hx => congrArg Prod.snd hx.2)
  apply measure_mono_null (t := ⋃ j, f '' S j) _ (measure_iUnion_null hnull)
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨j, hj⟩ := K.exists_mem ⟨x, hx.1⟩
  exact mem_iUnion.mpr ⟨j, x, ⟨⟨⟨x, hx.1⟩, hj, rfl⟩,
    Prod.ext hx.2.1 hx.2.2⟩, rfl⟩

/-- A regular scalar constraint through a critical set places that set locally
on a C¹ curve and therefore gives a null critical image. -/
lemma exists_null_critical_image_neighborhood_of_constraint
    {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsOpen U)
    {f h : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : ContDiffOn ℝ 1 f U)
    (hh : ContDiffOn ℝ 1 h U) {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ U)
    (hhx : gradient h x ≠ 0)
    (hzero : ∀ y ∈ U, fderiv ℝ f y = 0 → h y = 0) :
    ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      volume (f '' ({y | y ∈ U ∧ fderiv ℝ f y = 0} ∩ V)) = 0 := by
  have hhd := (hh.differentiableOn (by norm_num) x hx).differentiableAt (hU.mem_nhds hx)
  obtain ⟨i, hi⟩ := exists_coareaSwap_nonzero_last hhd hhx
  let e := coareaSwap i
  have hUe : IsOpen (e ⁻¹' U) := hU.preimage e.continuous
  have hhe : ContDiffOn ℝ 1 (h ∘ e) (e ⁻¹' U) :=
    hh.comp e.toContinuousLinearEquiv.contDiff.contDiffOn (fun _ hy => hy)
  have hxe : e.symm x ∈ e ⁻¹' U := by simpa using hx
  obtain ⟨d, hxd, hds⟩ := exists_scalarCoareaChart hUe hhe hxe hi
  let V := e '' d.chart.source
  let γ := e ∘ graphMapN (d.levelHeight 0)
  have hγ : ContDiffOn ℝ 1 γ (d.levelDomain 0) :=
    e.toContinuousLinearEquiv.contDiff.comp_contDiffOn
      (contDiffOn_graphMapN (d.contDiffOn_levelHeight 0))
  have hγU : MapsTo γ (d.levelDomain 0) U := by
    intro y hy
    dsimp only [γ, comp_apply]
    rw [← d.inverse_eq_graphMapN hy]
    exact hds (d.chart.map_target hy)
  have hnull := measure_image_critical_inter_curve hU hf (d.isOpen_levelDomain 0) hγ hγU
  refine ⟨V, e.toHomeomorph.isOpenMap _ d.chart.open_source,
    ⟨e.symm x, hxd, e.apply_symm_apply x⟩, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hds hy
  · apply measure_mono_null (image_mono ?_) hnull
    rintro z ⟨hz, y, hy, rfl⟩
    have hy0 : y ∈ d.chart.source ∩ (h ∘ e) ⁻¹' {(0 : ℝ)} :=
      ⟨hy, hzero _ hz.1 hz.2⟩
    rw [← d.graphMapN_levelPatch (A := d.chart.source) (Subset.refl _) 0] at hy0
    obtain ⟨w, hw, heq⟩ := hy0
    exact ⟨hz, w, d.levelPatch_subset_levelDomain (Subset.refl _) 0 hw,
      congrArg e heq⟩

/-- A nonzero Hessian supplies a regular scalar constraint annihilating the
critical set, without choosing a coordinate convention for Hessian matrices. -/
lemma exists_null_critical_image_neighborhood_of_hessian_ne_zero
    {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : ContDiffOn ℝ 2 f U)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ U)
    (hH : fderiv ℝ (fderiv ℝ f) x ≠ 0) :
    ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      volume (f '' ({y | y ∈ U ∧ fderiv ℝ f y = 0} ∩ V)) = 0 := by
  have hex : ∃ v w, (fderiv ℝ (fderiv ℝ f) x) v w ≠ 0 := by
    by_contra! hn
    apply hH
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    exact hn v w
  obtain ⟨v, w, hvw⟩ := hex
  let h (y : EuclideanSpace ℝ (Fin 2)) := fderiv ℝ f y w
  have hdf : ContDiffOn ℝ 1 (fderiv ℝ f) U :=
    (contDiffOn_succ_iff_fderiv_of_isOpen hU).mp hf |>.2.2
  have hh : ContDiffOn ℝ 1 h U :=
    (ContinuousLinearMap.apply ℝ ℝ w).contDiff.comp_contDiffOn hdf
  have hd := (ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp x
    ((hdf.differentiableOn (by norm_num) x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have hgrad : gradient h x ≠ 0 := by
    intro hz
    have hd0 : fderiv ℝ h x = 0 := by rw [← toDual_gradient, hz, map_zero]
    have heq := congrArg (fun L : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ => L v) hd.fderiv
    change (fderiv ℝ h x) v = (fderiv ℝ (fderiv ℝ f) x) v w at heq
    rw [hd0, zero_apply] at heq
    exact hvw heq.symm
  exact exists_null_critical_image_neighborhood_of_constraint hU (hf.of_le (by norm_num)) hh hx
    hgrad (fun y _ hy => by simp only [h, hy, zero_apply])

/-- Blueprint `lem:sard-2d`: critical values of a C² planar scalar map are null. -/
theorem sard_two_dimensional
    {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : ContDiffOn ℝ 2 f U) :
    volume (f '' {x | x ∈ U ∧ fderiv ℝ f x = 0}) = 0 := by
  classical
  let R := {x | x ∈ U ∧ fderiv ℝ f x = 0 ∧ fderiv ℝ (fderiv ℝ f) x ≠ 0}
  have hRnull : volume (f '' R) = 0 := by
    by_cases hR : R.Nonempty
    · let : Nonempty R := hR.to_subtype
      have hlocal (x : R) := exists_null_critical_image_neighborhood_of_hessian_ne_zero
        hU hf x.property.1 x.property.2.2
      choose V hVo hVx hVU hnull using hlocal
      have hL : IsLindelof R := isLindelof_iff_lindelofSpace.mpr inferInstance
      obtain ⟨c, hc⟩ := hL.indexed_countable_subcover V hVo
        (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hVx ⟨x, hx⟩⟩)
      apply measure_mono_null (t := ⋃ j, f '' ({x | x ∈ U ∧ fderiv ℝ f x = 0} ∩ V (c j))) _
        (measure_iUnion_null fun j => hnull (c j))
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨j, hj⟩ := mem_iUnion.mp (hc hx)
      exact mem_iUnion.mpr ⟨j, x, ⟨⟨hx.1, hx.2.1⟩, hj⟩, rfl⟩
    · simp only [not_nonempty_iff_eq_empty.mp hR, image_empty, measure_empty]
  apply measure_mono_null (t := f '' R ∪
    f '' {x | x ∈ U ∧ fderiv ℝ f x = 0 ∧ fderiv ℝ (fderiv ℝ f) x = 0}) _
    (measure_union_null hRnull (measure_image_twice_flat hU hf))
  rintro _ ⟨x, hx, rfl⟩
  by_cases hH : fderiv ℝ (fderiv ℝ f) x = 0
  · exact Or.inr ⟨x, ⟨hx.1, hx.2, hH⟩, rfl⟩
  · exact Or.inl ⟨x, ⟨hx.1, hx.2, hH⟩, rfl⟩

/-- Equivalent gradient convention for the planar scalar critical set. -/
theorem sard_two_dimensional_gradient
    {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : ContDiffOn ℝ 2 f U) :
    volume (f '' {x | x ∈ U ∧ gradient f x = 0}) = 0 := by
  apply measure_mono_null (image_mono ?_) (sard_two_dimensional hU hf)
  intro x hx
  refine ⟨hx.1, ?_⟩
  rw [← toDual_gradient, hx.2, map_zero]

end LiquidDrop
