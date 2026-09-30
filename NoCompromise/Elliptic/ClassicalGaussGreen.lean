module

public import NoCompromise.Elliptic.ClassicalCharts
public import NoCompromise.Elliptic.ClassicalPartition
public import NoCompromise.Sobolev.W11Smooth
public import NoCompromise.Sobolev.W11TraceBoundary
public import NoCompromise.Sobolev.C1Domain

@[expose] public section

/-!
# Classical C¹ Gauss–Green by a finite chart partition

Compact chart pieces obey the graph FTC formula. Their finite sum is the
original function on the closure, so their directional derivatives sum to the
original derivative inside the domain. The only geometric normal premise here
is agreement with the actual one-sided chart normals.
-/

noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped ENNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma integrable_boundary_pairing_of_contDiff_compact {D : Set AmbientSpace}
    (hD : IsOpen D) (hbD : Bornology.IsBounded D) (hC1 : HasC1Boundary D)
    {ν : AmbientSpace → AmbientSpace}
    (hνm : AEStronglyMeasurable ν ((hausdorffMeasure2 3).restrict (frontier D)))
    (hn : ∀ᵐ x ∂(hausdorffMeasure2 3).restrict (frontier D), ‖ν x‖ ≤ 1)
    {φ : AmbientSpace → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (v : AmbientSpace) :
    Integrable (fun x => φ x * inner ℝ v (ν x))
      ((hausdorffMeasure2 3).restrict (frontier D)) := by
  obtain ⟨_, _, ht⟩ := exists_global_w11_boundary_restriction_bound hD hbD hC1.hasLipschitzBoundary
  have hi := memLp_one_iff_integrable.mp
    (ht φ (gradient φ) (hasW11GradientOn_of_contDiff_compact hφ hcφ) hφ.continuous).1
  simpa only [inner_smul_left, conj_trivial, hausdorffMeasure2] using
    integrable_inner_of_bound (hi.smul_const v) hνm hn

theorem classical_directional_gauss_green {D : Set AmbientSpace}
    (hD : IsOpen D) (hbD : Bornology.IsBounded D) (hC1 : HasC1Boundary D)
    {ν : AmbientSpace → AmbientSpace}
    (hνm : AEStronglyMeasurable ν ((hausdorffMeasure2 3).restrict (frontier D)))
    (hn : ∀ᵐ x ∂(hausdorffMeasure2 3).restrict (frontier D), ‖ν x‖ ≤ 1)
    (hν : ∀ c : C1BoundaryChart, c.IsChartFor D →
      ∀ᵐ x ∂(hausdorffMeasure2 3).restrict (frontier D),
        x ∈ c.region → ν x = c.outwardNormal x)
    {φ : AmbientSpace → ℝ} (hφ : ContDiff ℝ 1 φ) (v : AmbientSpace) :
    (∫ x in D, fderiv ℝ φ x v) =
      ∫ x, φ x * inner ℝ v (ν x) ∂(hausdorffMeasure2 3).restrict (frontier D) := by
  classical
  obtain ⟨s, hopen, hbounded, hcover⟩ := exists_finite_c1_boundary_cover hD hbD hC1
  have hcover' : closure D ⊆ ⋃ i : ↥s, classicalBoundaryRegion D i.val := by
    simpa only [iUnion_subtype] using hcover
  obtain ⟨ζ, _, hζ, hsum, _⟩ := exists_finite_smooth_partition_of_bounded_open_cover
    hbD.isCompact_closure (fun i : ↥s => classicalBoundaryRegion D i.val)
    (fun i => hopen i.val) (fun i => hbounded i.val) hcover'
  let ψ (i : ↥s) (x : AmbientSpace) := ζ i x * φ x
  have hψ (i : ↥s) : ContDiff ℝ 1 (ψ i) := ((hζ i).1.of_le (by simp)).mul hφ
  have hcψ (i : ↥s) : HasCompactSupport (ψ i) := (hζ i).2.1.mul_right
  have hsψ (i : ↥s) : tsupport (ψ i) ⊆ classicalBoundaryRegion D i.val :=
    tsupport_mul_subset_left.trans (hζ i).2.2.1
  have hsumψ (x) (hx : x ∈ closure D) : ∑ i : ↥s, ψ i x = φ x := by
    simp only [ψ, ← Finset.sum_mul, hsum x hx, one_mul]
  have hvol (i : ↥s) : IntegrableOn (fun x => fderiv ℝ (ψ i) x v) D :=
    (Continuous.integrable_of_hasCompactSupport
      (((hψ i).continuous_fderiv one_ne_zero).clm_apply continuous_const)
      ((hcψ i).fderiv_apply ℝ v)).integrableOn
  have hsurf (i : ↥s) := integrable_boundary_pairing_of_contDiff_compact hD hbD hC1
    hνm hn (hψ i) (hcψ i) v
  have hpair (i : ↥s) : (∫ x in D, fderiv ℝ (ψ i) x v) =
      ∫ x, ψ i x * inner ℝ v (ν x) ∂(hausdorffMeasure2 3).restrict (frontier D) := by
    cases hi : i.val with
    | none =>
      have hs : tsupport (ψ i) ⊆ D := by simpa only [hi, classicalBoundaryRegion] using hsψ i
      rw [integral_directional_derivative_interior (hψ i) (hcψ i) hs v,
        boundary_pairing_eq_zero_of_interior_support hD hs ν v]
    | some c =>
      have hs : tsupport (ψ i) ⊆ c.val.region := by
        simpa only [hi, classicalBoundaryRegion] using hsψ i
      exact c.property.directional_pairing_boundary hD.measurableSet (hν c.val c.property)
        (hψ i) (hcψ i) hs v
  have hder (x) (hx : x ∈ D) : fderiv ℝ φ x v = ∑ i : ↥s, fderiv ℝ (ψ i) x v := by
    have heq : (fun y => ∑ i : ↥s, ψ i y) =ᶠ[𝓝 x] φ :=
      Filter.mem_of_superset (hD.mem_nhds hx) fun y hy => hsumψ y (subset_closure hy)
    have hh := congrArg (fun L : AmbientSpace →L[ℝ] ℝ => L v) (heq.fderiv_eq (𝕜 := ℝ))
    rw [fderiv_fun_sum (fun i _ => (hψ i).differentiable one_ne_zero x),
      sum_apply] at hh
    exact hh.symm
  calc
    _ = ∫ x in D, ∑ i : ↥s, fderiv ℝ (ψ i) x v :=
      setIntegral_congr_fun hD.measurableSet hder
    _ = ∑ i : ↥s, ∫ x in D, fderiv ℝ (ψ i) x v :=
      integral_finsetSum _ fun i _ => hvol i
    _ = ∑ i : ↥s, ∫ x, ψ i x * inner ℝ v (ν x)
        ∂(hausdorffMeasure2 3).restrict (frontier D) := Finset.sum_congr rfl fun i _ => hpair i
    _ = ∫ x, ∑ i : ↥s, ψ i x * inner ℝ v (ν x)
        ∂(hausdorffMeasure2 3).restrict (frontier D) :=
      (integral_finsetSum _ fun i _ => hsurf i).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with x hx
      rw [← Finset.sum_mul, hsumψ x (frontier_subset_closure hx)]

end LiquidDrop
