import NoCompromise.Elliptic.BoundaryHolderReflection
import NoCompromise.Sobolev.H1TraceKernelInward
import NoCompromise.Sobolev.H1TraceKernelFlat

/-!
# Genuine zero-boundary tests for flat reflection

Vanishing of the actual flat trace, together with compact support inside an
open neighborhood, gives membership in H¹₀ on its upper-halfspace intersection.
In particular the antisymmetric difference of a smooth test and its reflected
copy is an admissible test. No boundary test identity is assumed.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma boundary_holder_open_upper {k : ℕ} :
    IsOpen {x : EuclideanSpace ℝ (Fin (k + 1)) | 0 < x (Fin.last k)} :=
  isOpen_lt continuous_const (EuclideanSpace.proj (Fin.last k)).continuous

/-- A compact global H¹ function with zero actual flat trace is a genuine
zero-boundary test on every open neighborhood of its support, cut by the plane. -/
theorem HasH1GradientOn.boundary_mem_h1Zero_inter_upper {k : ℕ}
    {W : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hW : IsOpen W)
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : HasH1GradientOn f G univ) (hcf : HasCompactSupport f)
    (hsf : tsupport f ⊆ W) (hT : flatTraceFunction f G =ᵐ[volume] 0) :
    H1Space.ofFunction f G (hf.mono (subset_univ
      (W ∩ {x | 0 < x (Fin.last k)}))) ∈
      h1ZeroSubmodule (hW.inter boundary_holder_open_upper) := by
  let U := {x : EuclideanSpace ℝ (Fin (k + 1)) | 0 < x (Fin.last k)}
  have hU : IsOpen U := boundary_holder_open_upper
  have hcut : HasH1GradientOn (U.indicator f) (U.indicator G) univ := by
    simpa only [smoothEpigraph] using hf.indicator_upperHalfspace_of_flatTrace_zero hT
  have hs : tsupport (U.indicator f) ⊆ tsupport f :=
    closure_mono (by
      intro x hx
      by_contra hn
      exact hx (by simp only [Function.mem_support, not_not] at hn; simp [hn]))
  have hclosed : IsClosed {x : EuclideanSpace ℝ (Fin (k + 1)) |
      0 ≤ x (Fin.last k)} :=
    isClosed_le continuous_const (EuclideanSpace.proj (Fin.last k)).continuous
  have hp : ∀ x ∈ tsupport (U.indicator f), 0 ≤ x (Fin.last k) := by
    apply closure_minimal _ hclosed
    intro x hx
    have hxu : x ∈ U := by
      by_contra hn
      exact hx (indicator_of_notMem hn f)
    exact (show 0 < x (Fin.last k) from hxu).le
  have hc := hcf.of_isClosed_subset (isClosed_tsupport _) hs
  obtain ⟨a, ha, hsa⟩ := exists_inward_translations_of_compact (Fin.last k)
    hc hW (hs.trans hsf) hp
  have hmem := hcut.mem_h1Zero_of_inward_translations (hW.inter hU) hc ha
    (fun j x hx => hsa j x (tsupport_comp_subset_preimage (U.indicator f)
      (continuous_id.sub continuous_const) hx))
  have heq : H1Space.ofFunction (U.indicator f) (U.indicator G)
      (hcut.mono (subset_univ (W ∩ U))) =
        H1Space.ofFunction f G (hf.mono (subset_univ (W ∩ U))) := by
    apply H1Space.ext_ae (hW.inter hU)
    filter_upwards [H1Space.coeFn_ofFunction _ _ (hcut.mono (subset_univ (W ∩ U))),
      H1Space.coeFn_ofFunction _ _ (hf.mono (subset_univ (W ∩ U))),
      ae_restrict_mem (hW.inter hU).measurableSet] with x hx hy hxu
    rw [hx, hy, indicator_of_mem hxu.2]
  exact heq ▸ hmem

/-- Smooth compact functions which vanish on the plane are legitimate H¹₀ tests
on the upper part of a neighborhood containing their support. -/
theorem boundary_holder_smooth_test_mem_h1Zero {k : ℕ}
    {W : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hW : IsOpen W)
    {φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ W)
    (hz : ∀ x : EuclideanSpace ℝ (Fin k), φ (graphAppendN x 0) = 0) :
    ∃ h : HasH1GradientOn φ (gradient φ) univ,
      H1Space.ofFunction φ (gradient φ) (h.mono (subset_univ
        (W ∩ {x | 0 < x (Fin.last k)}))) ∈
        h1ZeroSubmodule (hW.inter boundary_holder_open_upper) := by
  have h : HasH1GradientOn φ (gradient φ) univ :=
    ⟨hasWeakGradientOn_of_contDiffOn isOpen_univ hφ.contDiffOn,
      hφ.continuous.memLp_of_hasCompactSupport hcφ,
      (continuous_gradient_of_contDiff hφ).memLp_of_hasCompactSupport
        (hcφ.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset φ))⟩
  refine ⟨h, h.boundary_mem_h1Zero_inter_upper hW hcφ hsφ ?_⟩
  exact Eventually.of_forall fun x => (flatTraceFunction_eq_restrict_of_contDiff hφ x).trans (hz x)

/-- Adapted antisymmetrization retains smoothness, compact support, and vanishing
on the flat boundary. -/
theorem boundary_holder_reflected_test {k : ℕ}
    (A : EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (k + 1)))
    (hn : inner ℝ (frozenSymmetricPart A (EuclideanSpace.single (Fin.last k) 1))
      (EuclideanSpace.single (Fin.last k) 1) ≠ 0)
    {W : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hW : IsOpen W)
    {φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ W)
    (hsR : boundaryFrozenReflection A (EuclideanSpace.single (Fin.last k) 1) ⁻¹'
      tsupport φ ⊆ W) :
    ∃ h : HasH1GradientOn
        (fun x => φ x - φ (boundaryFrozenReflection A (EuclideanSpace.single (Fin.last k) 1) x))
        (gradient (fun x => φ x -
          φ (boundaryFrozenReflection A (EuclideanSpace.single (Fin.last k) 1) x))) univ,
      H1Space.ofFunction _ _ (h.mono (subset_univ
        (W ∩ {x | 0 < x (Fin.last k)}))) ∈
        h1ZeroSubmodule (hW.inter boundary_holder_open_upper) := by
  let R := boundaryFrozenReflectionEquiv A (EuclideanSpace.single (Fin.last k) 1) hn
  apply boundary_holder_smooth_test_mem_h1Zero hW
    (hφ.sub (hφ.comp R.contDiff)) (hcφ.sub (hcφ.comp_homeomorph R.toHomeomorph))
  · exact (tsupport_sub _ _).trans (union_subset hsφ
      ((tsupport_comp_subset_preimage φ R.continuous).trans hsR))
  · intro x
    have hx : inner ℝ (EuclideanSpace.single (Fin.last k) (1 : ℝ))
        (graphAppendN x 0) = 0 := by
      simp only [EuclideanSpace.inner_single_left, graphAppendN_last, mul_zero]
    change φ (graphAppendN x 0) -
      φ (boundaryFrozenReflection A _ (graphAppendN x 0)) = 0
    rw [boundaryFrozenReflection_eq_self A _ _ hx, sub_self]

end LiquidDrop
