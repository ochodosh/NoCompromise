module

public import NoCompromise.Sobolev.H1TraceKernelLocal
public import NoCompromise.Sobolev.H1TraceKernelLocalization
public import NoCompromise.Sobolev.H1Extension

@[expose] public section

/-!
# The trace kernel is the actual H¹₀ space

Finite smooth localization reduces zero boundary trace to the interior and
single-chart results. A genuine bounded H¹ extension supplies the compact
global representative. No boundary approximation is assumed.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma H1Space.coeFn_finsetSum {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    {ι : Type*} (s : Finset ι) (u : ι → H1Space D) :
    ⇑(∑ i ∈ s, u i) =ᵐ[volume.restrict D] fun x => ∑ i ∈ s, u i x := by
  change ⇑(toLpCLM (∑ i ∈ s, u i)) =ᵐ[volume.restrict D] _
  rw [map_sum]
  exact Lp.coeFn_fun_finsetSum s (fun i => (u i).toLp)

theorem HasH1GradientOn.mem_h1Zero_of_domainTrace_zero {k : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D)
    (T : H1Space D →L[ℝ]
      Lp ℝ 2 ((Measure.euclideanHausdorffMeasure k).restrict (frontier D)))
    (hT : ∀ f G (hf : HasH1GradientOn f G D), Continuous f →
      T (H1Space.ofFunction f G hf) =ᵐ[(Measure.euclideanHausdorffMeasure k).restrict
        (frontier D)] f)
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : HasH1GradientOn f G univ) (hcf : HasCompactSupport f)
    (hzero : T (H1Space.ofFunction f G (hf.mono (subset_univ D))) = 0) :
    H1Space.ofFunction f G (hf.mono (subset_univ D)) ∈ h1ZeroSubmodule hD := by
  classical
  obtain ⟨s, hopen, hbounded, hcover⟩ := exists_finite_boundary_chart_cover hD hbD hL
  have hcover' : closure D ⊆ ⋃ i : ↥s, boundaryExtensionRegion D i.val := by
    simpa only [iUnion_subtype] using hcover
  obtain ⟨ζ, B, hζ, hsum, _⟩ := exists_finite_smooth_partition_of_bounded_open_cover
    hbD.isCompact_closure (fun i : ↥s => boundaryExtensionRegion D i.val)
    (fun i => hopen i.val) (fun i => hbounded i.val) hcover'
  have hbζ (i : ↥s) (x) : ‖ζ i x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg ((hζ i).2.2.2.1 x).1]
    exact ((hζ i).2.2.2.1 x).2
  have hcut (i : ↥s) : HasH1GradientOn (fun x => ζ i x * f x)
      (fun x => ζ i x • G x + f x • gradient (ζ i) x) univ :=
    (hf.mul_compact_cutoff MeasurableSet.univ ((hζ i).1.of_le (by simp))
      (hζ i).2.1 (subset_univ _) (hbζ i) (hζ i).2.2.2.2.2).1
  let u (i : ↥s) := H1Space.ofFunction (fun x => ζ i x * f x)
    (fun x => ζ i x • G x + f x • gradient (ζ i) x)
    ((hcut i).mono (subset_univ D))
  have hmem (i : ↥s) : u i ∈ h1ZeroSubmodule hD := by
    have hcp : HasCompactSupport (fun x => ζ i x * f x) := (hζ i).2.1.mul_right
    have hsp : tsupport (fun x => ζ i x * f x) ⊆ boundaryExtensionRegion D i.val :=
      tsupport_mul_subset_left.trans (hζ i).2.2.1
    cases hi : i.val with
    | none =>
      apply (hcut i).mem_h1Zero_of_compact_support hD hcp
      simpa only [hi, boundaryExtensionRegion] using hsp
    | some c =>
      apply (hcut i).mem_h1Zero_of_local_domainTrace_zero hD c.val c.property T hT hcp
        (by simpa only [hi, boundaryExtensionRegion] using hsp)
      exact hf.domainTrace_cutoff_eq_zero hD T hT hcf ((hζ i).1.of_le (by simp))
        (hζ i).2.1 zero_le_one (hζ i).2.2.2.2.1 (hbζ i) (hζ i).2.2.2.2.2 hzero
  have hsumMem : (∑ i, u i) ∈ h1ZeroSubmodule hD :=
    Submodule.sum_mem _ (fun i _ => hmem i)
  have heq : (∑ i, u i) = H1Space.ofFunction f G (hf.mono (subset_univ D)) := by
    apply H1Space.ext_ae hD
    have hall : ∀ᵐ x ∂volume.restrict D, ∀ i : ↥s, u i x = ζ i x * f x :=
      ae_all_iff.mpr (fun i => H1Space.coeFn_ofFunction _ _ ((hcut i).mono (subset_univ D)))
    filter_upwards [H1Space.coeFn_finsetSum Finset.univ u, hall,
      H1Space.coeFn_ofFunction _ _ (hf.mono (subset_univ D)),
      ae_restrict_mem hD.measurableSet] with x hx hi hy hxD
    rw [hx, hy]
    simp only [hi, ← Finset.sum_mul, hsum x (subset_closure hxD), one_mul]
  exact heq ▸ hsumMem

/-- Every class with zero actual trace belongs to the defining H¹ closure of
smooth compactly supported interior functions on a bounded Lipschitz domain. -/
theorem H1Space.mem_h1Zero_of_trace_zero {k : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D)
    (T : H1Space D →L[ℝ]
      Lp ℝ 2 ((Measure.euclideanHausdorffMeasure k).restrict (frontier D)))
    (hT : ∀ f G (hf : HasH1GradientOn f G D), Continuous f →
      T (ofFunction f G hf) =ᵐ[(Measure.euclideanHausdorffMeasure k).restrict (frontier D)] f)
    (u : H1Space D) (hzero : T u = 0) : u ∈ h1ZeroSubmodule hD := by
  obtain ⟨E, K, C, hK, _, hE⟩ := exists_h1_extension_linearMap hD hbD hL
  obtain ⟨G, hG, heq, hs, _⟩ := hE u u.gradientLp u.hasH1GradientOn
  have hcf : HasCompactSupport (E u) := hK.of_isClosed_subset (isClosed_tsupport _) hs
  have hclass : ofFunction (E u) G (hG.mono (subset_univ D)) = u := by
    apply ext_ae hD
    exact (coeFn_ofFunction _ _ _).trans (ae_restrict_of_forall_mem hD.measurableSet heq)
  have hm := hG.mem_h1Zero_of_domainTrace_zero hD hbD hL T hT hcf
    (by rwa [hclass])
  exact hclass ▸ hm

theorem trace_ker_eq_h1ZeroSubmodule {k : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D)
    (T : H1Space D →L[ℝ]
      Lp ℝ 2 ((Measure.euclideanHausdorffMeasure k).restrict (frontier D)))
    (hT : ∀ f G (hf : HasH1GradientOn f G D), Continuous f →
      T (H1Space.ofFunction f G hf) =ᵐ[(Measure.euclideanHausdorffMeasure k).restrict
        (frontier D)] f) : T.ker = h1ZeroSubmodule hD := by
  apply le_antisymm
  · intro u hu
    exact u.mem_h1Zero_of_trace_zero hD hbD hL T hT hu
  · exact h1ZeroSubmodule_le_trace_ker hD T hT

end LiquidDrop
