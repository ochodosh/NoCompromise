import NoCompromise.Sard.Scalar
import NoCompromise.Sard.LevelCharts
import NoCompromise.Sard.CubicFlat

/-!
# Three-dimensional scalar Sard at C³ regularity

The critical set is split according to the first nonzero derivative after the
first derivative. A nonzero second derivative places the critical set locally
on a C² surface, where planar Sard applies. A nonzero third derivative places
the twice-flat set on a C¹ surface, where quadratic flatness gives a null image.
The remaining thrice-flat set has uniformly small cubic remainders on compact
subsets and is handled by the three-dimensional grid covering estimate.
-/

noncomputable section
open MeasureTheory Set Filter Function InnerProductSpace
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- A countable neighborhood cover turns local null-image estimates into a global one. -/
lemma measure_image_eq_zero_of_local_null {n : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hloc : ∀ x ∈ S, ∃ V, IsOpen V ∧ x ∈ V ∧ volume (f '' (S ∩ V)) = 0) :
    volume (f '' S) = 0 := by
  classical
  by_cases hS : S.Nonempty
  · let : Nonempty S := hS.to_subtype
    choose V hVo hVx hnull using fun x : S => hloc x x.property
    have hL : IsLindelof S := isLindelof_iff_lindelofSpace.mpr inferInstance
    obtain ⟨c, hc⟩ := hL.indexed_countable_subcover V hVo
      (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hVx ⟨x, hx⟩⟩)
    apply measure_mono_null (t := ⋃ j, f '' (S ∩ V (c j))) _
      (measure_iUnion_null fun j => hnull (c j))
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hc hx)
    exact mem_iUnion.mpr ⟨j, x, ⟨hx, hj⟩, rfl⟩
  · simp only [not_nonempty_iff_eq_empty.mp hS, image_empty, measure_empty]

/-- Planar scalar Sard applies to the critical set on a C² parametrized surface. -/
lemma measure_image_critical_inter_surface {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiffOn ℝ 2 f U)
    {W : Set (EuclideanSpace ℝ (Fin 2))} (hW : IsOpen W)
    {γ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin n)}
    (hγ : ContDiffOn ℝ 2 γ W) (hγU : MapsTo γ W U) :
    volume (f '' ({x | x ∈ U ∧ fderiv ℝ f x = 0} ∩ γ '' W)) = 0 := by
  apply measure_mono_null _ (sard_two_dimensional hW (hf.comp hγ hγU))
  rintro _ ⟨x, ⟨hx, y, hy, rfl⟩, rfl⟩
  refine ⟨y, ⟨hy, ?_⟩, rfl⟩
  have hd := ((hf.differentiableOn (by norm_num) _ hx.1).differentiableAt
    (hU.mem_nhds hx.1)).hasFDerivAt
  have hdγ := ((hγ.differentiableOn (by norm_num) y hy).differentiableAt
    (hW.mem_nhds hy)).hasFDerivAt
  simpa only [hx.2, ContinuousLinearMap.zero_comp] using (hd.comp y hdγ).fderiv

/-- A regular C² constraint gives a null critical image in a three-dimensional neighborhood. -/
lemma exists_null_critical_image_surface_neighborhood
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    {f h : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : ContDiffOn ℝ 2 f U)
    (hh : ContDiffOn ℝ 2 h U) {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ U)
    (hhx : gradient h x ≠ 0) (hzero : ∀ y ∈ U, fderiv ℝ f y = 0 → h y = 0) :
    ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      volume (f '' ({y | y ∈ U ∧ fderiv ℝ f y = 0} ∩ V)) = 0 := by
  obtain ⟨V, W, γ, hV, hxV, hVU, hW, hγ, hγU, hcover⟩ :=
    exists_contDiff_zero_level_parametrization (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
      hU hh hx hhx
  refine ⟨V, hV, hxV, hVU, ?_⟩
  apply measure_mono_null (image_mono ?_) (measure_image_critical_inter_surface hU hf hW hγ hγU)
  intro y hy
  exact ⟨hy.1, hcover ⟨hy.2, hzero y hy.1.1 hy.1.2⟩⟩

/-- A regular C¹ constraint gives a null image for the twice-flat set near the point. -/
lemma exists_null_twice_flat_image_surface_neighborhood
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    {f h : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : ContDiffOn ℝ 2 f U)
    (hh : ContDiffOn ℝ 1 h U) {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ U)
    (hhx : gradient h x ≠ 0)
    (hzero : ∀ y ∈ U, fderiv ℝ (fderiv ℝ f) y = 0 → h y = 0) :
    ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      volume (f '' ({y | y ∈ U ∧ fderiv ℝ f y = 0 ∧ fderiv ℝ (fderiv ℝ f) y = 0}
        ∩ V)) = 0 := by
  obtain ⟨V, W, γ, hV, hxV, hVU, hW, hγ, hγU, hcover⟩ :=
    exists_contDiff_zero_level_parametrization le_rfl hU hh hx hhx
  refine ⟨V, hV, hxV, hVU, ?_⟩
  apply measure_mono_null (image_mono ?_)
    (measure_image_twice_flat_inter_surface hU hf hW hγ hγU)
  intro y hy
  exact ⟨hy.1, hcover ⟨hy.2, hzero y hy.1.1 hy.1.2.2⟩⟩

/-- The nonzero-Hessian stratum has a local null critical image at C³ regularity. -/
lemma exists_null_critical_image_neighborhood_c3_hessian
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : ContDiffOn ℝ 3 f U)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ U)
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
  let h (y : EuclideanSpace ℝ (Fin 3)) := fderiv ℝ f y w
  have hdf : ContDiffOn ℝ 2 (fderiv ℝ f) U :=
    (contDiffOn_succ_iff_fderiv_of_isOpen hU).mp hf |>.2.2
  have hh : ContDiffOn ℝ 2 h U :=
    (ContinuousLinearMap.apply ℝ ℝ w).contDiff.comp_contDiffOn hdf
  have hd := (ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp x
    ((hdf.differentiableOn (by norm_num) x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have hgrad : gradient h x ≠ 0 := by
    intro hz
    have hd0 : fderiv ℝ h x = 0 := by rw [← toDual_gradient, hz, map_zero]
    have heq := congrArg (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ => L v) hd.fderiv
    change (fderiv ℝ h x) v = (fderiv ℝ (fderiv ℝ f) x) v w at heq
    rw [hd0, zero_apply] at heq
    exact hvw heq.symm
  exact exists_null_critical_image_surface_neighborhood hU (hf.of_le (by norm_num)) hh hx
    hgrad (fun y _ hy => by simp only [h, hy, zero_apply])

/-- The nonzero-third-derivative stratum has a local null twice-flat image. -/
lemma exists_null_twice_flat_image_neighborhood_c3_third
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : ContDiffOn ℝ 3 f U)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ U)
    (hT : fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x ≠ 0) :
    ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      volume (f '' ({y | y ∈ U ∧ fderiv ℝ f y = 0 ∧ fderiv ℝ (fderiv ℝ f) y = 0}
        ∩ V)) = 0 := by
  have hex : ∃ v w z, (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x) v w z ≠ 0 := by
    by_contra! hn
    apply hT
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    apply ContinuousLinearMap.ext
    intro z
    exact hn v w z
  obtain ⟨v, w, z, hvwz⟩ := hex
  let h (y : EuclideanSpace ℝ (Fin 3)) := fderiv ℝ (fderiv ℝ f) y w z
  have hdf : ContDiffOn ℝ 2 (fderiv ℝ f) U :=
    (contDiffOn_succ_iff_fderiv_of_isOpen hU).mp hf |>.2.2
  have hddf : ContDiffOn ℝ 1 (fderiv ℝ (fderiv ℝ f)) U :=
    (contDiffOn_succ_iff_fderiv_of_isOpen hU).mp hdf |>.2.2
  let evw := ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) w
  let evz := ContinuousLinearMap.apply ℝ ℝ z
  have hh : ContDiffOn ℝ 1 h U :=
    evz.contDiff.comp_contDiffOn (evw.contDiff.comp_contDiffOn hddf)
  have hd := evz.hasFDerivAt.comp x (evw.hasFDerivAt.comp x
    ((hddf.differentiableOn (by norm_num) x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt)
  have hgrad : gradient h x ≠ 0 := by
    intro hz
    have hd0 : fderiv ℝ h x = 0 := by rw [← toDual_gradient, hz, map_zero]
    have heq := congrArg (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ => L v) hd.fderiv
    change (fderiv ℝ h x) v = (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x) v w z at heq
    rw [hd0, zero_apply] at heq
    exact hvwz heq.symm
  exact exists_null_twice_flat_image_surface_neighborhood hU (hf.of_le (by norm_num)) hh hx
    hgrad (fun y _ hy => by simp only [h, hy, zero_apply])

/-- Compact exhaustion handles the stratum where the first three derivatives vanish. -/
lemma measure_image_thrice_flat
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : ContDiffOn ℝ 3 f U) :
    volume (f '' {x | x ∈ U ∧ fderiv ℝ f x = 0 ∧ fderiv ℝ (fderiv ℝ f) x = 0 ∧
      fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x = 0}) = 0 := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let K := CompactExhaustion.choice U
  let A : ℕ → Set (EuclideanSpace ℝ (Fin 3)) := fun j => Subtype.val '' K j
  have hAc (j : ℕ) : IsCompact (A j) := (K.isCompact j).image continuous_subtype_val
  have hAU (j : ℕ) : A j ⊆ U := by rintro _ ⟨x, _, rfl⟩; exact x.property
  have hdf : ContDiffOn ℝ 2 (fderiv ℝ f) U :=
    (contDiffOn_succ_iff_fderiv_of_isOpen hU).mp hf |>.2.2
  have hddf : ContDiffOn ℝ 1 (fderiv ℝ (fderiv ℝ f)) U :=
    (contDiffOn_succ_iff_fderiv_of_isOpen hU).mp hdf |>.2.2
  let D := fun x => ((fderiv ℝ f x, fderiv ℝ (fderiv ℝ f) x),
    fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x)
  have hc : ContinuousOn D U :=
    ((hf.continuousOn_fderiv_of_isOpen hU (by norm_num)).prodMk
      (hdf.continuousOn_fderiv_of_isOpen hU (by norm_num))).prodMk
      (hddf.continuousOn_fderiv_of_isOpen hU le_rfl)
  let S : ℕ → Set (EuclideanSpace ℝ (Fin 3)) := fun j => A j ∩ D ⁻¹' {((0, 0), 0)}
  have hSc (j : ℕ) : IsCompact (S j) := by
    apply (hAc j).of_isClosed_subset _ inter_subset_left
    exact (hc.mono (hAU j)).preimage_isClosed_of_isClosed (hAc j).isClosed isClosed_singleton
  have hnull (j : ℕ) : volume (f '' S j) = 0 :=
    measure_image_compact_thrice_flat hU (hSc j) (inter_subset_left.trans (hAU j)) hf
      (fun _ hx => congrArg (fun p => p.1.1) hx.2)
      (fun _ hx => congrArg (fun p => p.1.2) hx.2) (fun _ hx => congrArg Prod.snd hx.2)
  apply measure_mono_null (t := ⋃ j, f '' S j) _ (measure_iUnion_null hnull)
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨j, hj⟩ := K.exists_mem ⟨x, hx.1⟩
  exact mem_iUnion.mpr ⟨j, x, ⟨⟨⟨x, hx.1⟩, hj, rfl⟩,
    Prod.ext (Prod.ext hx.2.1 hx.2.2.1) hx.2.2.2⟩, rfl⟩

/-- Blueprint `thm:sard-3d`: C³ suffices for null scalar critical values in three dimensions. -/
theorem sard_three_dimensional
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : ContDiffOn ℝ 3 f U) :
    volume (f '' {x | x ∈ U ∧ fderiv ℝ f x = 0}) = 0 := by
  let R₁ := {x | x ∈ U ∧ fderiv ℝ f x = 0 ∧ fderiv ℝ (fderiv ℝ f) x ≠ 0}
  let R₂ := {x | x ∈ U ∧ fderiv ℝ f x = 0 ∧ fderiv ℝ (fderiv ℝ f) x = 0 ∧
    fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x ≠ 0}
  have hR₁ : volume (f '' R₁) = 0 := by
    apply measure_image_eq_zero_of_local_null
    intro x hx
    obtain ⟨V, hV, hxV, _, hnull⟩ :=
      exists_null_critical_image_neighborhood_c3_hessian hU hf hx.1 hx.2.2
    have hs : R₁ ∩ V ⊆ {y | y ∈ U ∧ fderiv ℝ f y = 0} ∩ V := by
      intro y hy
      exact ⟨⟨hy.1.1, hy.1.2.1⟩, hy.2⟩
    exact ⟨V, hV, hxV, measure_mono_null (image_mono hs) hnull⟩
  have hR₂ : volume (f '' R₂) = 0 := by
    apply measure_image_eq_zero_of_local_null
    intro x hx
    obtain ⟨V, hV, hxV, _, hnull⟩ :=
      exists_null_twice_flat_image_neighborhood_c3_third hU hf hx.1 hx.2.2.2
    have hs : R₂ ∩ V ⊆
        {y | y ∈ U ∧ fderiv ℝ f y = 0 ∧ fderiv ℝ (fderiv ℝ f) y = 0} ∩ V := by
      intro y hy
      exact ⟨⟨hy.1.1, hy.1.2.1, hy.1.2.2.1⟩, hy.2⟩
    exact ⟨V, hV, hxV, measure_mono_null (image_mono hs) hnull⟩
  apply measure_mono_null (t := (f '' R₁ ∪ f '' R₂) ∪
    f '' {x | x ∈ U ∧ fderiv ℝ f x = 0 ∧ fderiv ℝ (fderiv ℝ f) x = 0 ∧
      fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x = 0}) _
    (measure_union_null (measure_union_null hR₁ hR₂) (measure_image_thrice_flat hU hf))
  rintro _ ⟨x, hx, rfl⟩
  by_cases hH : fderiv ℝ (fderiv ℝ f) x = 0
  · by_cases hT : fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x = 0
    · exact Or.inr ⟨x, ⟨hx.1, hx.2, hH, hT⟩, rfl⟩
    · exact Or.inl (Or.inr ⟨x, ⟨hx.1, hx.2, hH, hT⟩, rfl⟩)
  · exact Or.inl (Or.inl ⟨x, ⟨hx.1, hx.2, hH⟩, rfl⟩)

/-- The gradient version of the three-dimensional scalar critical-value theorem. -/
theorem sard_three_dimensional_gradient
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : ContDiffOn ℝ 3 f U) :
    volume (f '' {x | x ∈ U ∧ gradient f x = 0}) = 0 := by
  apply measure_mono_null (image_mono ?_) (sard_three_dimensional hU hf)
  intro x hx
  refine ⟨hx.1, ?_⟩
  rw [← toDual_gradient, hx.2, map_zero]

/-- Almost every scalar level of a C³ function on an open three-dimensional domain is regular. -/
theorem ae_regular_values_c3
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : ContDiffOn ℝ 3 f U) :
    ∀ᵐ t : ℝ, ∀ x ∈ U, f x = t → gradient f x ≠ 0 := by
  have hnot : ∀ᵐ t : ℝ, t ∉ f '' {x | x ∈ U ∧ gradient f x = 0} := by
    apply ae_iff.mpr
    convert sard_three_dimensional_gradient hU hf using 1
    congr 1
    ext t
    exact not_not
  filter_upwards [hnot] with t ht
  intro x hx hxt hz
  exact ht ⟨x, ⟨hx, hz⟩, hxt⟩

end LiquidDrop
