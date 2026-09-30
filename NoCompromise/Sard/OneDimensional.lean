module

public import NoCompromise.Sard.Flat

@[expose] public section

/-!
# One-dimensional critical values

The grid covering estimate proves nullity on compact critical sets. Compact
exhaustion gives the open-domain statement; the two endpoints of a closed
interval do not affect its image measure. No coarea or Sard theorem is invoked.
-/

noncomputable section
open MeasureTheory Filter Set Metric InnerProductSpace
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Critical values of a C¹ scalar function on a compact critical subset of a line are null. -/
lemma measure_image_compact_critical_one_dimensional
    {U S : Set (EuclideanSpace ℝ (Fin 1))} (hU : IsOpen U) (hS : IsCompact S)
    (hSU : S ⊆ U) {f : EuclideanSpace ℝ (Fin 1) → ℝ}
    (hf : ContDiffOn ℝ 1 f U) (hzero : ∀ x ∈ S, fderiv ℝ f x = 0) :
    volume (f '' S) = 0 := by
  apply measure_image_eq_zero_of_bounded_uniform_flat hS.isBounded f
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ :=
    compact_uniform_small_slope_of_fderiv_eq_zero hU hS hSU hf hzero ⟨ε, hε.le⟩ hε
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy
  rw [pow_one]
  exact_mod_cast hb x hx y hy

/-- The one-dimensional critical-value theorem in Euclidean coordinates. -/
theorem sard_one_dimensional_euclidean
    {U : Set (EuclideanSpace ℝ (Fin 1))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin 1) → ℝ} (hf : ContDiffOn ℝ 1 f U) :
    volume (f '' {x | x ∈ U ∧ fderiv ℝ f x = 0}) = 0 := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let K := CompactExhaustion.choice U
  let A : ℕ → Set (EuclideanSpace ℝ (Fin 1)) := fun j => Subtype.val '' K j
  have hAc (j : ℕ) : IsCompact (A j) := (K.isCompact j).image continuous_subtype_val
  have hAU (j : ℕ) : A j ⊆ U := by rintro _ ⟨x, _, rfl⟩; exact x.property
  let S : ℕ → Set (EuclideanSpace ℝ (Fin 1)) := fun j => A j ∩ fderiv ℝ f ⁻¹' {0}
  have hSc (j : ℕ) : IsCompact (S j) := by
    apply (hAc j).of_isClosed_subset _ inter_subset_left
    exact ((hf.continuousOn_fderiv_of_isOpen hU le_rfl).mono (hAU j)).preimage_isClosed_of_isClosed
      (hAc j).isClosed isClosed_singleton
  have hnull (j : ℕ) : volume (f '' S j) = 0 :=
    measure_image_compact_critical_one_dimensional hU (hSc j)
      (inter_subset_left.trans (hAU j)) hf (fun _ hx => hx.2)
  apply measure_mono_null (t := ⋃ j, f '' S j) _ (measure_iUnion_null hnull)
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨j, hj⟩ := K.exists_mem ⟨x, hx.1⟩
  exact mem_iUnion.mpr ⟨j, x, ⟨⟨⟨x, hx.1⟩, hj, rfl⟩, hx.2⟩, rfl⟩

/-- Blueprint `lem:sard-1d` on any open subset of the real line. -/
theorem sard_one_dimensional {U : Set ℝ} (hU : IsOpen U)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f U) :
    volume (f '' {x | x ∈ U ∧ deriv f x = 0}) = 0 := by
  let e : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)
  have hV := hU.preimage e.continuous
  have hfe : ContDiffOn ℝ 1 (f ∘ e) (e ⁻¹' U) :=
    hf.comp e.contDiff.contDiffOn (fun _ hx => hx)
  apply measure_mono_null _ (sard_one_dimensional_euclidean hV hfe)
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨e.symm x, ⟨by simpa using hx.1, ?_⟩, by simp⟩
  have hd := ((hf.differentiableOn (by norm_num) x hx.1).differentiableAt
    (hU.mem_nhds hx.1)).hasDerivAt
  have hcomp := hd.comp_hasFDerivAt (e.symm x) e.hasFDerivAt
  simpa [hx.2] using hcomp.fderiv

/-- Closed-interval version, with the derivative taken within that interval.
The result also covers degenerate or reversed intervals. -/
theorem sard_one_dimensional_Icc {a b : ℝ} {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Icc a b)) :
    volume (f '' {x | x ∈ Icc a b ∧ derivWithin f (Icc a b) x = 0}) = 0 := by
  have hi : ContDiffOn ℝ 1 f (Ioo a b) := hf.mono Ioo_subset_Icc_self
  have hnull := sard_one_dimensional isOpen_Ioo hi
  apply measure_mono_null (t := (f '' {x | x ∈ Ioo a b ∧ deriv f x = 0}) ∪ {f a, f b}) _
    (measure_union_null hnull
      (((Set.finite_singleton (f b)).insert (f a)).measure_zero volume))
  rintro _ ⟨x, hx, rfl⟩
  by_cases hxa : x = a
  · simp [hxa]
  by_cases hxb : x = b
  · simp [hxb]
  have hxi : x ∈ Ioo a b := ⟨lt_of_le_of_ne hx.1.1 (Ne.symm hxa),
    lt_of_le_of_ne hx.1.2 hxb⟩
  apply Or.inl
  refine ⟨x, ⟨hxi, ?_⟩, rfl⟩
  have hz := hx.2
  rwa [derivWithin_of_mem_nhds (Icc_mem_nhds hxi.1 hxi.2)] at hz

/-- Critical values contributed by a C¹ parametrized curve are null. -/
lemma measure_image_critical_inter_curve {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiffOn ℝ 1 f U)
    {W : Set (EuclideanSpace ℝ (Fin 1))} (hW : IsOpen W)
    {γ : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin n)}
    (hγ : ContDiffOn ℝ 1 γ W) (hγU : MapsTo γ W U) :
    volume (f '' ({x | x ∈ U ∧ fderiv ℝ f x = 0} ∩ γ '' W)) = 0 := by
  have hc : ContDiffOn ℝ 1 (f ∘ γ) W := hf.comp hγ hγU
  apply measure_mono_null _ (sard_one_dimensional_euclidean hW hc)
  rintro _ ⟨x, ⟨hx, y, hy, rfl⟩, rfl⟩
  refine ⟨y, ⟨hy, ?_⟩, rfl⟩
  have hd := ((hf.differentiableOn (by norm_num) _ hx.1).differentiableAt
    (hU.mem_nhds hx.1)).hasFDerivAt
  have hdγ := ((hγ.differentiableOn (by norm_num) y hy).differentiableAt
    (hW.mem_nhds hy)).hasFDerivAt
  simpa only [hx.2, ContinuousLinearMap.zero_comp] using (hd.comp y hdγ).fderiv

end LiquidDrop
