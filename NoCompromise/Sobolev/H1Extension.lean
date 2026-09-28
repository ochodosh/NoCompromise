import NoCompromise.Sobolev.H1ChartExtension
import NoCompromise.Sobolev.H1Algebra

/-!
# Bounded linear H¹ extension on Lipschitz domains

A finite smooth partition assembles the cutoff reflection pieces into a linear
map on representatives. Quantitative H¹ bounds permit descent to the Hilbert
spaces of weak-gradient classes, with one fixed compact support for the image.
-/

noncomputable section

open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient Pointwise
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Finite partition assembly yields a linear H¹ extension on representatives.
The support and bound depend only on the domain and the selected charts. -/
theorem exists_h1_extension_linearMap {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) :
    ∃ T : (EuclideanSpace ℝ (Fin n) → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin n) → ℝ),
    ∃ K : Set (EuclideanSpace ℝ (Fin n)), ∃ C : ℝ,
      IsCompact K ∧ 0 ≤ C ∧ ∀ f G, HasH1GradientOn f G D →
        ∃ H, HasH1GradientOn (T f) H univ ∧ EqOn (T f) f D ∧ tsupport (T f) ⊆ K ∧
          lpNorm (T f) 2 volume + lpNorm H 2 volume ≤
            C * (lpNorm f 2 (volume.restrict D) + lpNorm G 2 (volume.restrict D)) := by
  classical
  obtain ⟨s, hopen, hbounded, hcover⟩ := exists_finite_boundary_chart_cover hD hbD hL
  have hcover' : closure D ⊆ ⋃ i : ↥s, boundaryExtensionRegion D i.val := by
    simpa only [iUnion_subtype] using hcover
  obtain ⟨ζ, B, hζ, hsum, _⟩ := exists_finite_smooth_partition_of_bounded_open_cover
    hbD.isCompact_closure (fun i : ↥s => boundaryExtensionRegion D i.val)
    (fun i => hopen i.val) (fun i => hbounded i.val) hcover'
  let T := ∑ i : ↥s, boundaryExtensionPiece D i.val (ζ i)
  let K := ⋃ i : ↥s, tsupport (ζ i)
  let C := ∑ i : ↥s, h1BoundaryExtensionPieceBound i.val (B i)
  have hK : IsCompact K := isCompact_iUnion (fun i => (hζ i).2.1)
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ =>
    h1BoundaryExtensionPieceBound_nonneg i.val (hζ i).2.2.2.2.1
  refine ⟨T, K, C, hK, hC, fun f G hf => ?_⟩
  have hpiece (i : ↥s) := h1_boundaryExtensionPiece hD i.val hf
    ((hζ i).1.of_le (by simp)) (hζ i).2.1 (hζ i).2.2.1
    (hζ i).2.2.2.1 (hζ i).2.2.2.2.1 (hζ i).2.2.2.2.2
  choose H hH hEq hSupport hBound using hpiece
  have hTeq : T f = fun x => ∑ i : ↥s, boundaryExtensionPiece D i.val (ζ i) f x := by
    ext x
    simp only [T, LinearMap.sum_apply, Finset.sum_apply]
  rw [hTeq]
  refine ⟨fun x => ∑ i : ↥s, H i x,
    HasH1GradientOn.finsetSum Finset.univ (fun i _ => hH i), ?_, ?_, ?_⟩
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
  · have hb := h1_lpNorm_finsetSum_le Finset.univ (fun i _ => hH i)
    simp only [Measure.restrict_univ] at hb
    apply hb.trans
    calc
      _ ≤ ∑ i : ↥s, h1BoundaryExtensionPieceBound i.val (B i) *
          (lpNorm f 2 (volume.restrict D) + lpNorm G 2 (volume.restrict D)) :=
        Finset.sum_le_sum fun i _ => hBound i
      _ = _ := (Finset.sum_mul _ _ _).symm

/-- All representatives produced by the extension have support inside one fixed
bounded open neighborhood of the closure of the original domain. -/
theorem exists_h1_extension_in_bounded_neighborhood {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) :
    ∃ T : (EuclideanSpace ℝ (Fin n) → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin n) → ℝ),
    ∃ W : Set (EuclideanSpace ℝ (Fin n)), ∃ C : ℝ,
      IsOpen W ∧ Bornology.IsBounded W ∧ closure D ⊆ W ∧ 0 ≤ C ∧
      ∀ f G, HasH1GradientOn f G D →
        ∃ H, HasH1GradientOn (T f) H univ ∧ EqOn (T f) f D ∧ tsupport (T f) ⊆ W ∧
          lpNorm (T f) 2 volume + lpNorm H 2 volume ≤
            C * (lpNorm f 2 (volume.restrict D) + lpNorm G 2 (volume.restrict D)) := by
  obtain ⟨T, K, C, hK, hC, hT⟩ := exists_h1_extension_linearMap hD hbD hL
  obtain ⟨R, _, hR⟩ := (hbD.closure.union hK.isBounded).exists_pos_norm_lt
  have hDK : closure D ∪ K ⊆ ball 0 R := by
    intro x hx
    simpa only [mem_ball, dist_zero_right] using hR x hx
  refine ⟨T, ball 0 R, C, isOpen_ball, isBounded_ball, fun x hx => hDK (Or.inl hx),
    hC, fun f G hf => ?_⟩
  obtain ⟨H, hH, heq, hs, hb⟩ := hT f G hf
  exact ⟨H, hH, heq, fun x hx => hDK (Or.inr (hs hx)), hb⟩

/-- Blueprint `lem:H1-extension-disk`: a bounded open set with Lipschitz boundary
has a bounded linear extension between the genuine H¹ Hilbert spaces. Each image
class has a compactly supported representative in one fixed bounded neighborhood.
The construction works in every finite dimension. -/
theorem exists_h1_extension {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) :
    ∃ E : H1Space D →L[ℝ] H1Space (univ : Set (EuclideanSpace ℝ (Fin n))),
    ∃ W : Set (EuclideanSpace ℝ (Fin n)), ∃ C : ℝ,
      IsOpen W ∧ Bornology.IsBounded W ∧ closure D ⊆ W ∧ 0 ≤ C ∧ ‖E‖ ≤ C ∧
      ∀ u : H1Space D,
        (⇑(E u) =ᵐ[volume.restrict D] u) ∧ ‖E u‖ ≤ C * ‖u‖ ∧
        ∃ f : EuclideanSpace ℝ (Fin n) → ℝ,
          IsH1On f univ ∧ HasCompactSupport f ∧ tsupport f ⊆ W ∧
          (⇑(E u) =ᵐ[volume] f) ∧ EqOn f u D := by
  obtain ⟨T, W, C, hoW, hbW, hDW, hC, hT⟩ :=
    exists_h1_extension_in_bounded_neighborhood hD hbD hL
  have hbound : ∀ f G, HasH1GradientOn f G D → ∃ H,
      HasH1GradientOn (T f) H univ ∧
        lpNorm (T f) 2 (volume.restrict univ) + lpNorm H 2 (volume.restrict univ) ≤
          C * (lpNorm f 2 (volume.restrict D) + lpNorm G 2 (volume.restrict D)) := by
    intro f G hf
    obtain ⟨H, hH, _, _, hb⟩ := hT f G hf
    exact ⟨H, hH, by simpa only [Measure.restrict_univ] using hb⟩
  let E := H1Space.liftBoundedLinearMap isOpen_univ T C hC hbound hD
  have hE : ‖E‖ ≤ 2 * C :=
    H1Space.norm_liftBoundedLinearMap_le isOpen_univ T C hC hbound hD
  refine ⟨E, W, 2 * C, hoW, hbW, hDW, by positivity, hE, fun u => ?_⟩
  obtain ⟨H, hH, heq, hs, _⟩ := hT u u.gradientLp u.hasH1GradientOn
  have hae : ⇑(E u) =ᵐ[volume] T u := by
    simpa only [Measure.restrict_univ] using
      H1Space.coeFn_liftBoundedLinearMap isOpen_univ T C hC hbound hD u
  have haeD : ⇑(E u) =ᵐ[volume.restrict D] T u := ae_restrict_of_ae hae
  refine ⟨haeD.trans (ae_restrict_of_forall_mem hD.measurableSet heq),
    (E.le_opNorm u).trans (mul_le_mul_of_nonneg_right hE (norm_nonneg u)),
    T u, ⟨H, hH⟩, ?_, hs, hae, heq⟩
  exact isCompact_of_isClosed_isBounded (isClosed_tsupport _) (hbW.subset hs)

end LiquidDrop
