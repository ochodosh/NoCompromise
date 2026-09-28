import NoCompromise.Topology.Transversality
import NoCompromise.Surface.RegularValue
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Compact transverse preimages and finite path intersections

The path argument uses normalized secants in the domain. The chain rule for
locally vanishing scalar functions puts their derivative images in the intrinsic
tangent plane. A nonzero vector spans the one-dimensional domain, contradicting
transversality if intersections accumulate.
-/

noncomputable section
open Set Filter Function
open scoped Topology

namespace LiquidDrop

/-- cor:transv-preimage, compactness (paths and disks). -/
theorem isCompact_transverse_preimage {k : ℕ} {S : Set E₃} (hc : IsCompact S)
    {f : EuclideanSpace ℝ (Fin k) → E₃} (hf : Continuous f) :
    IsCompact (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 ∩ f ⁻¹' S) :=
  (isCompact_closedBall _ _).inter_right (hc.isClosed.preimage hf)

private theorem derivative_image_mem_tangentPlane
    {k : ℕ} {S : Set E₃} {f : EuclideanSpace ℝ (Fin k) → E₃}
    {p u : EuclideanSpace ℝ (Fin k)} {q : ℕ → EuclideanSpace ℝ (Fin k)}
    (hf : DifferentiableAt ℝ f p) (hp : f p ∈ S) (hqS : ∀ n, f (q n) ∈ S)
    (hq : Tendsto q atTop (𝓝 p))
    (hu : Tendsto (fun n => ‖q n - p‖⁻¹ • (q n - p)) atTop (𝓝 u)) :
    fderiv ℝ f p u ∈ tangentPlane S (f p) := by
  rw [mem_tangentPlane_iff]
  intro φ hφ hzero
  have hφp : φ (f p) = 0 :=
    mem_of_mem_nhdsWithin (t := {x | φ x = 0}) hp hzero
  have hqWithin : Tendsto (f ∘ q) atTop (𝓝[S] (f p)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hf.continuousAt.tendsto.comp hq, Eventually.of_forall hqS⟩
  have heq : ∀ᶠ n in atTop, (φ ∘ f) (q n) = (φ ∘ f) p := by
    simpa only [Function.comp_apply, hφp] using hqWithin.eventually hzero
  have hd := hφ.hasFDerivAt.comp p hf.hasFDerivAt
  have hrem := (hasFDerivAt_iff_tendsto.mp hd).comp hq
  have hz : Tendsto
      (fun n => ‖((fderiv ℝ φ (f p)).comp (fderiv ℝ f p))
        (‖q n - p‖⁻¹ • (q n - p))‖) atTop (𝓝 0) := by
    apply hrem.congr'
    filter_upwards [heq] with n hn
    simp only [Function.comp_apply] at hn
    simp only [Function.comp_apply, hn, sub_self, zero_sub, norm_neg, map_smul,
      norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  have hl := (((fderiv ℝ φ (f p)).comp (fderiv ℝ f p)).continuous.tendsto u).comp hu
  exact norm_eq_zero.mp (tendsto_nhds_unique hl.norm hz)

/-- cor:transv-preimage, path case: finitely many intersections. -/
theorem finite_transverse_preimage_path {S : Set E₃} (hS : IsSmoothEmbeddedSurface S)
    (hc : IsCompact S) {f : EuclideanSpace ℝ (Fin 1) → E₃} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (htr : ∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1, TransverseAt S f p) :
    (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 ∩ f ⁻¹' S).Finite := by
  by_contra hinf
  obtain ⟨p, hp, hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf
    (isCompact_transverse_preimage hc hf.continuous) (Subset.refl _)
  have hcl : p ∈ closure
      ((Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 ∩ f ⁻¹' S) \ {p}) :=
    (accPt_principal_iff_clusterPt.mp hacc).mem_closure
  obtain ⟨q, hqmem, hq⟩ := mem_closure_iff_seq_limit.mp hcl
  have hqS (n : ℕ) : f (q n) ∈ S := (hqmem n).1.2
  have hqne (n : ℕ) : q n ≠ p := (hqmem n).2
  have hunit (n : ℕ) : ‖q n - p‖⁻¹ • (q n - p) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 := by
    simp [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hqne n))]
  obtain ⟨u, huunit, r, hr, hu⟩ :=
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 1)) 1).tendsto_subseq hunit
  have huT : fderiv ℝ f p u ∈ tangentPlane S (f p) :=
    derivative_image_mem_tangentPlane (hf.differentiable (by simp) p) hp.2
      (fun n => hqS (r n)) (hq.comp hr.tendsto_atTop) hu
  have hune : u ≠ 0 := by
    intro h
    simp [h] at huunit
  have hrange : LinearMap.range
      (fderiv ℝ f p : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] E₃) ≤ tangentPlane S (f p) := by
    rintro _ ⟨v, rfl⟩
    obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' (K := ℝ) u hune).mp (by simp) v
    change fderiv ℝ f p (c • u) ∈ tangentPlane S (f p)
    rw [map_smul]
    exact (tangentPlane S (f p)).smul_mem c huT
  have htop : tangentPlane S (f p) = ⊤ := by
    simpa only [sup_eq_right.mpr hrange] using htr p hp.1 hp.2
  have hdim := hS.finrank_tangentPlane hp.2
  rw [htop] at hdim
  norm_num [E₃] at hdim

end LiquidDrop
