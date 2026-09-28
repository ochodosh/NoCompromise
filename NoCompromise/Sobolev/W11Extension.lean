import NoCompromise.Sobolev.W11ChartExtension
import NoCompromise.Sobolev.W11Algebra
import NoCompromise.Sobolev.H1ContinuousExtension

/-!
# W¹,¹ extension on bounded Lipschitz domains

A finite smooth partition assembles the actual chart reflections into a bounded
linear map on representatives. One fixed compact set contains every extension,
and the construction preserves continuity of continuous inputs.
-/

noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Finite partition assembly yields a linear W¹,¹ extension on representatives.
The support and bound depend only on the domain and the selected charts. -/
theorem exists_w11_extension_linearMap_preserving_continuity {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) :
    ∃ T : (EuclideanSpace ℝ (Fin n) → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin n) → ℝ),
    ∃ K : Set (EuclideanSpace ℝ (Fin n)), ∃ C : ℝ,
      IsCompact K ∧ 0 ≤ C ∧ (∀ f, Continuous f → Continuous (T f)) ∧
      ∀ f G, HasW11GradientOn f G D →
        ∃ H, HasW11GradientOn (T f) H univ ∧ EqOn (T f) f D ∧ tsupport (T f) ⊆ K ∧
          lpNorm (T f) 1 volume + lpNorm H 1 volume ≤
            C * (lpNorm f 1 (volume.restrict D) + lpNorm G 1 (volume.restrict D)) := by
  classical
  obtain ⟨s, hopen, hbounded, hcover⟩ := exists_finite_boundary_chart_cover hD hbD hL
  have hcover' : closure D ⊆ ⋃ i : ↥s, boundaryExtensionRegion D i.val := by
    simpa only [iUnion_subtype] using hcover
  obtain ⟨ζ, B, hζ, hsum, _⟩ := exists_finite_smooth_partition_of_bounded_open_cover
    hbD.isCompact_closure (fun i : ↥s => boundaryExtensionRegion D i.val)
    (fun i => hopen i.val) (fun i => hbounded i.val) hcover'
  let T := ∑ i : ↥s, boundaryExtensionPiece D i.val (ζ i)
  let K := ⋃ i : ↥s, tsupport (ζ i)
  let C := ∑ i : ↥s, w11BoundaryExtensionPieceBound i.val (B i)
  have hK : IsCompact K := isCompact_iUnion (fun i => (hζ i).2.1)
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ =>
    w11BoundaryExtensionPieceBound_nonneg i.val (hζ i).2.2.2.2.1
  have hcont (f) (hf : Continuous f) : Continuous (T f) := by
    have heq : T f = fun x => ∑ i : ↥s, boundaryExtensionPiece D i.val (ζ i) f x := by
      ext x
      simp only [T, LinearMap.sum_apply, Finset.sum_apply]
    rw [heq]
    exact continuous_finsetSum _ fun i _ =>
      continuous_boundaryExtensionPiece i.val (hζ i).1.continuous hf
  refine ⟨T, K, C, hK, hC, hcont, fun f G hf => ?_⟩
  have hpiece (i : ↥s) := w11_boundaryExtensionPiece hD i.val hf
    ((hζ i).1.of_le (by simp)) (hζ i).2.1 (hζ i).2.2.1
    (hζ i).2.2.2.1 (hζ i).2.2.2.2.1 (hζ i).2.2.2.2.2
  choose H hH hEq hSupport hBound using hpiece
  have hTeq : T f = fun x => ∑ i : ↥s, boundaryExtensionPiece D i.val (ζ i) f x := by
    ext x
    simp only [T, LinearMap.sum_apply, Finset.sum_apply]
  rw [hTeq]
  refine ⟨fun x => ∑ i : ↥s, H i x,
    HasW11GradientOn.finsetSum Finset.univ (fun i _ => hH i), ?_, ?_, ?_⟩
  · intro x hx
    calc
      _ = ∑ i : ↥s, ζ i x * f x := Finset.sum_congr rfl fun i _ => hEq i hx
      _ = (∑ i : ↥s, ζ i x) * f x := (Finset.sum_mul _ _ _).symm
      _ = f x := by rw [hsum x (subset_closure hx), one_mul]
  · apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hnot
    have hz (i : ↥s) : boundaryExtensionPiece D i.val (ζ i) f x = 0 := by
      by_contra hxne
      exact hnot (mem_iUnion.mpr ⟨i, hSupport i (subset_tsupport _ hxne)⟩)
    exact hx (by simp only [hz, Finset.sum_const_zero])
  · have hb := w11_lpNorm_finsetSum_le Finset.univ (fun i _ => hH i)
    simp only [Measure.restrict_univ] at hb
    apply hb.trans
    calc
      _ ≤ ∑ i : ↥s, w11BoundaryExtensionPieceBound i.val (B i) *
          (lpNorm f 1 (volume.restrict D) + lpNorm G 1 (volume.restrict D)) :=
        Finset.sum_le_sum fun i _ => hBound i
      _ = _ := (Finset.sum_mul _ _ _).symm

/-- A single domain constant bounds continuous global W¹,¹ extensions which agree
with continuous input representatives on the entire closure. -/
theorem exists_continuous_w11_extension_bound {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f G, HasW11GradientOn f G D → Continuous f →
      ∃ F H, Continuous F ∧ HasW11GradientOn F H univ ∧ EqOn F f (closure D) ∧
        lpNorm F 1 volume + lpNorm H 1 volume ≤
          C * (lpNorm f 1 (volume.restrict D) + lpNorm G 1 (volume.restrict D)) := by
  obtain ⟨T, K, C, _, hC, hcT, hT⟩ :=
    exists_w11_extension_linearMap_preserving_continuity hD hbD hL
  refine ⟨C, hC, fun f G hf hc => ?_⟩
  obtain ⟨H, hH, heq, _, hb⟩ := hT f G hf
  exact ⟨T f, H, hcT f hc, hH, heq.closure (hcT f hc) hc, hb⟩

end LiquidDrop
