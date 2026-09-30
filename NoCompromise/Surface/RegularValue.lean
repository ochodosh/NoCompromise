module

public import NoCompromise.Surface.Geometry
public import Mathlib.Topology.Sequences

@[expose] public section

/-!
# Finite regular fibres of compact surfaces

Normalized secants at an accumulation point belong to the intrinsic tangent plane.
Differentiability annihilates their limits along a fibre, while regularity makes the
restriction of the differential to the two-dimensional tangent plane injective.
-/

noncomputable section
open Set Filter Function InnerProductSpace
open scoped Topology Gradient
namespace LiquidDrop

/-- `y` is a regular value of `f|_S : S → S'`: at every point of `S` over `y` the ambient
differential maps `T_pS` onto `T_yS'`. (`f` is an ambient representative.) -/
def IsSurfaceRegularValue (S S' : Set E₃) (f : E₃ → E₃) (y : E₃) : Prop :=
  ∀ p ∈ S, f p = y →
    (tangentPlane S p).map (fderiv ℝ f p : E₃ →ₗ[ℝ] E₃) = tangentPlane S' y

/-- At a regular value the differential is injective on the tangent plane. -/
theorem IsSurfaceRegularValue.injOn_tangentPlane {S S' : Set E₃} {f : E₃ → E₃} {y p : E₃}
    (hS : IsSmoothEmbeddedSurface S) (hS' : IsSmoothEmbeddedSurface S') (hy' : y ∈ S')
    (hy : IsSurfaceRegularValue S S' f y) (hp : p ∈ S) (hfp : f p = y) :
    ∀ X ∈ tangentPlane S p, fderiv ℝ f p X = 0 → X = 0 := by
  let L := (fderiv ℝ f p : E₃ →ₗ[ℝ] E₃).domRestrict (tangentPlane S p)
  have hr : LinearMap.range L = tangentPlane S' y := by
    rw [LinearMap.range_domRestrict]
    exact hy p hp hfp
  have hd := L.finrank_range_add_finrank_ker
  rw [hr, hS.finrank_tangentPlane hp, hS'.finrank_tangentPlane hy'] at hd
  have hk : LinearMap.ker L = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
  intro X hX hzero
  have hx : (⟨X, hX⟩ : tangentPlane S p) ∈ LinearMap.ker L := hzero
  rw [hk] at hx
  have hxzero : (⟨X, hX⟩ : tangentPlane S p) = 0 := by simpa using hx
  exact congrArg Subtype.val hxzero

/-- A differential annihilates a limit of normalized secants along a level set. -/
theorem fderiv_eq_zero_of_tendsto_normalized_secant
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E₃ → F} {p u : E₃} {q : ℕ → E₃}
    (hf : DifferentiableAt ℝ f p) (hq : Tendsto q atTop (𝓝 p))
    (heq : ∀ᶠ k in atTop, f (q k) = f p)
    (hu : Tendsto (fun k => ‖q k - p‖⁻¹ • (q k - p)) atTop (𝓝 u)) :
    fderiv ℝ f p u = 0 := by
  have hrem := (hasFDerivAt_iff_tendsto.mp hf.hasFDerivAt).comp hq
  have hz : Tendsto (fun k => ‖fderiv ℝ f p (‖q k - p‖⁻¹ • (q k - p))‖)
      atTop (𝓝 0) := by
    apply hrem.congr'
    filter_upwards [heq] with k hk
    simp only [Function.comp_apply, hk, sub_self, zero_sub, norm_neg, map_smul,
      norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  have hl := ((fderiv ℝ f p).continuous.tendsto u).comp hu
  exact norm_eq_zero.mp (tendsto_nhds_unique hl.norm hz)

/-- A limit of normalized secants in a set belongs to its intrinsic tangent plane.
This uses only the intrinsic definition, so the set need not be a smooth surface. -/
theorem mem_tangentPlane_of_tendsto_normalized_secant
    {S : Set E₃} {p u : E₃} {q : ℕ → E₃}
    (hp : p ∈ S) (hqS : ∀ k, q k ∈ S) (hq : Tendsto q atTop (𝓝 p))
    (hu : Tendsto (fun k => ‖q k - p‖⁻¹ • (q k - p)) atTop (𝓝 u)) :
    u ∈ tangentPlane S p := by
  rw [mem_tangentPlane_iff]
  intro φ hφ hzero
  have hφp : φ p = 0 :=
    mem_of_mem_nhdsWithin (t := {x | φ x = 0}) hp hzero
  have hqWithin : Tendsto q atTop (𝓝[S] p) :=
    tendsto_nhdsWithin_iff.mpr ⟨hq, Eventually.of_forall hqS⟩
  apply fderiv_eq_zero_of_tendsto_normalized_secant hφ hq _ hu
  simpa only [hφp] using hqWithin.eventually hzero

/-- lem:regular-fiber-finite. -/
theorem finite_fiber_of_isSurfaceRegularValue {S S' : Set E₃} {f : E₃ → E₃} {y : E₃}
    (hS : IsSmoothEmbeddedSurface S) (hS' : IsSmoothEmbeddedSurface S') (hc : IsCompact S)
    (hmaps : MapsTo f S S') (hf : ∀ p ∈ S, DifferentiableAt ℝ f p)
    (hy : IsSurfaceRegularValue S S' f y) :
    {p ∈ S | f p = y}.Finite := by
  by_contra hinf
  obtain ⟨p, hp, hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf hc
    (show {p ∈ S | f p = y} ⊆ S from fun _ h => h.1)
  have hcl : p ∈ closure ({p ∈ S | f p = y} \ {p}) :=
    (accPt_principal_iff_clusterPt.mp hacc).mem_closure
  obtain ⟨q, hqmem, hq⟩ := mem_closure_iff_seq_limit.mp hcl
  have hqS (k : ℕ) : q k ∈ S := (hqmem k).1.1
  have hqf (k : ℕ) : f (q k) = y := (hqmem k).1.2
  have hqne (k : ℕ) : q k ≠ p := (hqmem k).2
  have hfp : f p = y := tendsto_nhds_unique ((hf p hp).continuousAt.tendsto.comp hq)
    (by simpa only [Function.comp_def, hqf] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => y) atTop (𝓝 y)))
  have hunit (k : ℕ) : ‖q k - p‖⁻¹ • (q k - p) ∈ Metric.sphere (0 : E₃) 1 := by
    simp [norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hqne k))]
  obtain ⟨u, huunit, r, hr, hu⟩ := (isCompact_sphere (0 : E₃) 1).tendsto_subseq hunit
  have hqr : Tendsto (q ∘ r) atTop (𝓝 p) := hq.comp hr.tendsto_atTop
  have huT : u ∈ tangentPlane S p := mem_tangentPlane_of_tendsto_normalized_secant
    hp (fun k => hqS (r k)) hqr hu
  have hdu : fderiv ℝ f p u = 0 := fderiv_eq_zero_of_tendsto_normalized_secant
    (hf p hp) hqr (Eventually.of_forall (fun k => (hqf (r k)).trans hfp.symm)) hu
  have huz := hy.injOn_tangentPlane hS hS' (hfp ▸ hmaps hp) hp hfp u huT hdu
  simp [huz] at huunit

end LiquidDrop
