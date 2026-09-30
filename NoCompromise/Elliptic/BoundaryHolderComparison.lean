module

public import NoCompromise.Elliptic.BoundaryHolderZeroSpace
public import NoCompromise.Elliptic.CampanatoComparisonFrozen

@[expose] public section

/-!
# Frozen comparison with the actual flat Dirichlet trace

The variational correction lies in the defining H¹₀ closure. Its flat trace
therefore vanishes by smooth approximation, so the constructed replacement
inherits the original solution's actual zero flat trace.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma boundary_hasZeroFlatTraceOn_of_h1Zero_difference {k : ℕ}
    {W : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hW : IsOpen W)
    (w h : H1Space (W ∩ {x | 0 < x (Fin.last k)}))
    (hTw : HasZeroFlatTraceOn w w.gradientLp W)
    (hbd : h - w ∈ h1ZeroSubmodule (hW.inter boundary_holder_open_upper)) :
    HasZeroFlatTraceOn h h.gradientLp W := by
  let d := w - h
  have hdz : d ∈ h1ZeroSubmodule (hW.inter boundary_holder_open_upper) := by
    simpa only [d, neg_sub] using
      (h1ZeroSubmodule (hW.inter boundary_holder_open_upper)).neg_mem hbd
  have hTd := d.hasH1GradientOn.hasZeroFlatTraceOn_of_mem_h1Zero hW
    (by
      rw [H1Space.ofFunction_coeFn (hW.inter boundary_holder_open_upper) d]
      exact hdz)
  have hT := HasZeroFlatTraceOn.sub hW.measurableSet w.hasH1GradientOn
    d.hasH1GradientOn hTw hTd
  apply hT.congr_ae hW.measurableSet
  · filter_upwards [H1Space.coeFn_sub w h] with x hx
    change w x - d x = h x
    rw [show d x = w x - h x from hx]
    ring
  · have hdG : d.gradientLp = w.gradientLp - h.gradientLp := by
      change H1Space.gradientCLM (w - h) = _
      rw [map_sub]
      rfl
    filter_upwards [Lp.coeFn_sub w.gradientLp h.gradientLp] with x hx
    change w.gradientLp x - d.gradientLp x = h.gradientLp x
    rw [hdG, hx]
    simp only [Pi.sub_apply, sub_sub_cancel]

/-- The actual frozen replacement retains zero trace and satisfies the full
squared-gradient comparison, on the upper part of any bounded open set. -/
theorem exists_boundary_campanato_comparison {k : ℕ}
    {W : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hW : IsOpen W)
    (hbW : Bornology.IsBounded W)
    (A : EuclideanSpace ℝ (Fin (k + 1)) →
      EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (k + 1)))
    (A₀ : EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (k + 1)))
    (G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1)))
    (G₀ : EuclideanSpace ℝ (Fin (k + 1)))
    (w : H1Space (W ∩ {x | 0 < x (Fin.last k)}))
    (hA : AEStronglyMeasurable A (volume.restrict (W ∩ {x | 0 < x (Fin.last k)})))
    {cap lam : ℝ} (hbA : ∀ᵐ x ∂volume.restrict (W ∩ {x | 0 < x (Fin.last k)}), ‖A x‖ ≤ cap)
    (hG : MemLp G 2 (volume.restrict (W ∩ {x | 0 < x (Fin.last k)})))
    (hlam : 0 < lam) (hell : ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A₀ ξ) ξ)
    (hw : IsWeakDivergenceEquationOn A w.gradientLp G (W ∩ {x | 0 < x (Fin.last k)}))
    (hTw : HasZeroFlatTraceOn w w.gradientLp W) :
    ∃ h : H1Space (W ∩ {x | 0 < x (Fin.last k)}),
      h - w ∈ h1ZeroSubmodule (hW.inter boundary_holder_open_upper) ∧
      HasZeroFlatTraceOn h h.gradientLp W ∧
      IsWeakDivergenceEquationOn (fun _ => A₀) h.gradientLp (fun _ => 0)
        (W ∩ {x | 0 < x (Fin.last k)}) ∧
      (∫ x in W ∩ {x | 0 < x (Fin.last k)}, ‖w.gradientLp x - h.gradientLp x‖ ^ 2) ≤
        (2 / lam ^ 2) *
          (∫ x in W ∩ {x | 0 < x (Fin.last k)}, ‖A x - A₀‖ ^ 2 * ‖w.gradientLp x‖ ^ 2) +
        (2 / lam ^ 2) * (∫ x in W ∩ {x | 0 < x (Fin.last k)}, ‖G x - G₀‖ ^ 2) := by
  obtain ⟨h, hbd, hh, he⟩ := exists_campanato_comparison (by omega)
    (hW.inter boundary_holder_open_upper) (hbW.subset inter_subset_left)
    A A₀ G G₀ w hA hbA hG hlam hell hw
  exact ⟨h, hbd, boundary_hasZeroFlatTraceOn_of_h1Zero_difference hW w h hTw hbd, hh, he⟩

end LiquidDrop
