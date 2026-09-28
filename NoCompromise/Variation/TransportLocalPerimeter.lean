import NoCompromise.Variation.TransportC1
import NoCompromise.Variation.TransportLocalCutoff
import NoCompromise.Variation.TransportLocalExtensionGlobal
import NoCompromise.BV.LocalToGlobal

/-!
# Local finiteness of perimeter under a C¹ diffeomorphism between open sets

First clause of blueprint `thm:transport-perimeter` on open domains: near each target
point, `Φ(E)` agrees with the image of a cut-off set under a global C¹ diffeomorphism.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

/-- Blueprint `thm:transport-perimeter`, local finiteness clause on open domains. -/
theorem hasLocallyFinitePerimeterIn_image_of_C1_diffeomorphism_on
    (Φ : OpenPartialHomeomorph AmbientSpace AmbientSpace)
    (hΦ : ContDiffOn ℝ 1 Φ Φ.source) (hΦi : ContDiffOn ℝ 1 Φ.symm Φ.target)
    {E : Set AmbientSpace} (hEU : E ⊆ Φ.source)
    (hE : HasLocallyFinitePerimeterIn E Φ.source) (hmE : NullMeasurableSet E volume) :
    HasLocallyFinitePerimeterIn (Φ '' E) Φ.target := by
  have hmI := nullMeasurableSet_image_of_C1_diffeomorphism_on Φ hΦ hEU hmE
  apply IsLocallyBVOn.hasLocallyFinitePerimeterIn
  refine isLocallyBVOn_of_local_variation
    ((locallyIntegrable_indicator_one hmI).locallyIntegrableOn _) ?_
  intro y hy
  set x₀ := Φ.symm y
  have hx₀ : x₀ ∈ Φ.source := Φ.map_target hy
  obtain ⟨r, hr, hsub, Ψ, hΨ, hΨi, hEq⟩ :=
    exists_local_C1_extension_of_C1_diffeomorphism_on Φ hΦ hΦi hx₀
  obtain ⟨E', hE', hmE', hEE'⟩ := exists_globalPerimeter_eq_on_ball Φ.open_source hE hmE hr hsub
  have hBs : ball x₀ r ⊆ Φ.source :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans hsub
  refine ⟨Ψ '' ball x₀ r, Ψ.isOpenMap _ isOpen_ball, ?_, ?_⟩
  · refine ⟨x₀, mem_ball_self hr, ?_⟩
    rw [hEq (mem_ball_self hr)]
    exact Φ.right_inv hy
  have hglob := hasLocallyFinitePerimeter_image_of_C1_diffeomorphism Ψ hΨ hΨi E' hE' hmE'
  have hcl : IsCompact (closure (Ψ '' ball x₀ r)) := by
    rw [← Ψ.image_closure]
    exact ((isCompact_closedBall x₀ r).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall).image Ψ.continuous
  have hfin := hglob _ (Ψ.isOpenMap _ isOpen_ball) hcl
  change perimeterIn (Φ '' E) (Ψ '' ball x₀ r) < ∞
  rw [perimeterIn_congr_ae (F := Ψ '' E') _ ?_]
  · exact hfin
  refine (ae_restrict_iff' (Ψ.isOpenMap _ isOpen_ball).measurableSet).mpr
    (Eventually.of_forall ?_)
  rintro z ⟨w, hw, rfl⟩
  apply propext
  constructor
  · rintro ⟨v, hv, hvw⟩
    have hvw' : v = w := by
      apply Φ.injOn (hEU hv) (hBs hw)
      rw [hvw, hEq hw]
    subst hvw'
    exact ⟨v, (hEE'.symm.subset ⟨hv, hw⟩).1, rfl⟩
  · rintro ⟨v, hv, hvw⟩
    have hvw' : v = w := Ψ.injective hvw
    subst hvw'
    exact ⟨v, (hEE'.subset ⟨hv, hw⟩).1, (hEq hw).symm⟩

end LiquidDrop
