module

public import NoCompromise.Sobolev.H1Extension
public import NoCompromise.Sobolev.PlanarGN
public import NoCompromise.Sobolev.LipschitzDomains

@[expose] public section

/-!
# Planar H¹ to L⁴ on bounded Lipschitz domains

The constructed H¹ extension and the whole-space square estimate give the
blueprint's planar Gagliardo–Nirenberg inequality, in particular on every disk.
-/

noncomputable section
open MeasureTheory Filter Metric Set
open scoped ENNReal NNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- A bounded open planar domain with Lipschitz boundary has the H¹ to L⁴
estimate, with one positive constant for every H¹ function on the domain. -/
theorem planar_gn_lipschitzDomain {D : Set (EuclideanSpace ℝ (Fin 2))}
    (hD : IsOpen D) (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) :
    ∃ C : ℝ, 0 < C ∧ ∀ f G, HasH1GradientOn f G D →
      MemLp f 4 (volume.restrict D) ∧
        lpNorm f 4 (volume.restrict D) ≤
          C * (lpNorm f 2 (volume.restrict D) + lpNorm G 2 (volume.restrict D)) := by
  obtain ⟨T, W, C, _, _, _, hC, hT⟩ :=
    exists_h1_extension_in_bounded_neighborhood hD hbD hL
  refine ⟨C + 1, by linarith, fun f G hf => ?_⟩
  obtain ⟨H, hH, heq, _, hb⟩ := hT f G hf
  apply planar_gn_of_h1_extension
  refine ⟨T f, H, hH, ae_restrict_of_forall_mem hD.measurableSet heq, ?_⟩
  exact hb.trans (mul_le_mul_of_nonneg_right (by linarith)
    (add_nonneg lpNorm_nonneg lpNorm_nonneg))

/-- Blueprint `lem:planar-GN`: the planar H¹ to L⁴ estimate on a positive-radius disk. -/
theorem planar_gn_disk (z : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ f G, HasH1GradientOn f G (ball z r) →
      MemLp f 4 (volume.restrict (ball z r)) ∧
        lpNorm f 4 (volume.restrict (ball z r)) ≤
          C * (lpNorm f 2 (volume.restrict (ball z r)) +
            lpNorm G 2 (volume.restrict (ball z r))) :=
  planar_gn_lipschitzDomain isOpen_ball isBounded_ball (hasLipschitzBoundary_ball z hr)

end LiquidDrop
