import NoCompromise.Surface.SurfaceChart
import NoCompromise.Surface.RegularValue
import NoCompromise.Area.Linear

/-!
# `cor:sard-charts` for the Gauss map of a compact embedded surface

Almost every point of `S²` (for `H²`) is a regular value of the unit normal `n`, from the
one-chart statement.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace LiquidDrop

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- `cor:sard-charts` for the Gauss map, globalized over a finite cover by projection charts,
from the one-chart statement `h_chart`. -/
theorem ae_isSurfaceRegularValue_gaussMap_of_chart {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S)
    (h_chart : ∀ (e : OpenPartialHomeomorph S E2) (P : E₃ →L[ℝ] E2) (q : E₃),
      (∀ x : S, e x = P ((x : E₃) - q)) →
      ContDiffOn ℝ 1 (fun y => (e.symm y : E₃)) e.target →
      ∀ {c : E2} {r : ℝ}, Metric.closedBall c r ⊆ e.target →
      hausdorffMeasure2 3 (n '' {p | ∃ u ∈ Metric.ball c r, (e.symm u : E₃) = p ∧
        (tangentPlane S p).map (fderiv ℝ n p : E₃ →ₗ[ℝ] E₃) ≠
          tangentPlane (Metric.sphere (0 : E₃) 1) (n p)}) = 0) :
    ∀ᵐ y ∂(hausdorffMeasure2 3).restrict (Metric.sphere (0 : E₃) 1),
      IsSurfaceRegularValue S (Metric.sphere (0 : E₃) 1) n y := by
  set Crit : Set E₃ := {p | p ∈ S ∧ (tangentPlane S p).map (fderiv ℝ n p : E₃ →ₗ[ℝ] E₃) ≠
    tangentPlane (Metric.sphere (0 : E₃) 1) (n p)} with hCrit
  have hloc : ∀ p ∈ S, ∃ V : Set E₃, IsOpen V ∧ p ∈ V ∧
      hausdorffMeasure2 3 (n '' (Crit ∩ V)) = 0 := by
    intro p hp
    obtain ⟨e, P, U, hU, hpU, hsrc, hps, he0, he, hψ⟩ := hS.exists_projection_chart hp 1
    have h0t : (0 : E2) ∈ e.target := he0 ▸ e.map_source hps
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp e.open_target 0 h0t
    have hB : Metric.closedBall (0 : E2) (ε / 2) ⊆ e.target :=
      (Metric.closedBall_subset_ball (by linarith)).trans hball
    have hPc : Continuous (fun x : E₃ => P (x - p)) :=
      P.continuous.comp (continuous_id.sub continuous_const)
    refine ⟨U ∩ (fun x => P (x - p)) ⁻¹' Metric.ball 0 (ε / 2),
      hU.inter (Metric.isOpen_ball.preimage hPc), ⟨hpU, by simp [half_pos hε]⟩, ?_⟩
    apply measure_mono_null _ (h_chart e P p he (by exact_mod_cast hψ) hB)
    apply image_mono
    rintro x ⟨⟨hxS, hxc⟩, hxU, hxb⟩
    have hxs : (⟨x, hxS⟩ : S) ∈ e.source := by rw [hsrc]; exact hxU
    refine ⟨e ⟨x, hxS⟩, ?_, ?_, hxc⟩
    · rw [he]; exact hxb
    · rw [e.left_inv hxs]
  choose! V hVo hpV hV0 using hloc
  obtain ⟨t, ht⟩ := hc.elim_nhds_subcover' (fun p _ => V p)
    (fun p hp => (hVo p hp).mem_nhds (hpV p hp))
  have hnull : hausdorffMeasure2 3 (n '' Crit) = 0 := by
    have hsub : n '' Crit ⊆ ⋃ x ∈ t, n '' (Crit ∩ V x) := by
      rintro _ ⟨p, hpC, rfl⟩
      have := ht hpC.1
      simp only [mem_iUnion] at this
      obtain ⟨x, hxt, hpx⟩ := this
      exact mem_biUnion hxt ⟨p, ⟨hpC, hpx⟩, rfl⟩
    apply measure_mono_null hsub
    exact (measure_biUnion_null_iff t.countable_toSet).mpr fun x _ => hV0 x x.2
  apply ae_restrict_of_ae
  apply measure_mono_null _ hnull
  intro y hy
  have hy' : ¬ IsSurfaceRegularValue S (Metric.sphere (0 : E₃) 1) n y := hy
  simp only [IsSurfaceRegularValue, not_forall] at hy'
  obtain ⟨p, hpS, hpy, hne⟩ := hy'
  exact ⟨p, ⟨hpS, hpy ▸ hne⟩, hpy⟩

end LiquidDrop
