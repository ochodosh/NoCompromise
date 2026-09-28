import NoCompromise.Stationary.Defs
import NoCompromise.Capacity.Translate
import NoCompromise.Energy.Scaling

/-!
# Stationary domains are translation invariant

A translate `a + Ω` of a stationary domain is stationary with the same volume and
multiplier. The intrinsic tangent plane and mean curvature of `Surface/Geometry.lean`
transport along `x ↦ x + b`, boundary charts transport by `C1BoundaryChart.translate`,
and the Coulomb potential is translation invariant (`coulombPotential_translate`).
-/

noncomputable section
open Set Filter
open scoped Topology
namespace LiquidDrop

/-- The intrinsic tangent plane of a pulled-back set, one inclusion. -/
lemma tangentPlane_le_preimage_add_right (S : Set AmbientSpace) (b p : AmbientSpace) :
    tangentPlane ((fun x => x + b) ⁻¹' S) p ≤ tangentPlane S (p + b) := by
  intro X hX
  rw [mem_tangentPlane_iff] at hX ⊢
  intro f hf hfz
  have hT : Tendsto (fun x => x + b) (𝓝[(fun x => x + b) ⁻¹' S] p) (𝓝[S] (p + b)) :=
    ((continuous_add_const b).continuousWithinAt).tendsto_nhdsWithin (mapsTo_preimage _ _)
  have hg : DifferentiableAt ℝ (fun x => f (x + b)) p :=
    hf.comp p ((differentiableAt_id).add_const b)
  have h := hX (fun x => f (x + b)) hg (hT.eventually hfz)
  rwa [fderiv_comp_add_right] at h

/-- The intrinsic tangent plane commutes with translation. -/
theorem tangentPlane_preimage_add_right (S : Set AmbientSpace) (b p : AmbientSpace) :
    tangentPlane ((fun x => x + b) ⁻¹' S) p = tangentPlane S (p + b) := by
  refine le_antisymm (tangentPlane_le_preimage_add_right S b p) ?_
  have h := tangentPlane_le_preimage_add_right ((fun x => x + b) ⁻¹' S) (-b) (p + b)
  have hS : (fun x => x + -b) ⁻¹' ((fun x => x + b) ⁻¹' S) = S := by
    ext x; simp
  rwa [hS, add_neg_cancel_right] at h

/-- The mean curvature commutes with translation, the normal field being translated too. -/
theorem meanCurvature_preimage_add_right (S : Set AmbientSpace)
    (n : AmbientSpace → AmbientSpace) (b p : AmbientSpace) :
    meanCurvature ((fun x => x + b) ⁻¹' S) (fun z => n (z + b)) p =
      meanCurvature S n (p + b) := by
  have hshape : shapeOperator (fun z => n (z + b)) p = shapeOperator n (p + b) := by
    simp only [shapeOperator, fderiv_comp_add_right]
  have key : ∀ (P Q : Submodule ℝ AmbientSpace) (L : AmbientSpace →L[ℝ] AmbientSpace), P = Q →
      LinearMap.trace ℝ P (P.orthogonalProjectionOnto ∘L L ∘L P.subtypeL).toLinearMap =
        LinearMap.trace ℝ Q (Q.orthogonalProjectionOnto ∘L L ∘L Q.subtypeL).toLinearMap := by
    rintro P Q L rfl
    rfl
  unfold meanCurvature tangentShapeOperator
  rw [hshape]
  exact key _ _ _ (tangentPlane_preimage_add_right S b p)

/-- The translate `a + Ω` as a pulled-back set. -/
lemma image_add_left_eq_preimage_add_right (Ω : Set AmbientSpace) (a : AmbientSpace) :
    (fun x => a + x) '' Ω = (fun x => x + -a) ⁻¹' Ω := by
  ext x
  simp [Set.image_add_left, add_comm]

namespace IsStationaryDomain

/-- Blueprint `def:stationary`: stationary domains are translation invariant, with the same
volume and the same multiplier. -/
theorem image_add_left {V lam : ℝ} {Ω : Set AmbientSpace}
    (h : IsStationaryDomain V lam Ω) (a : AmbientSpace) :
    IsStationaryDomain V lam ((fun x => a + x) '' Ω) := by
  have hpre := image_add_left_eq_preimage_add_right Ω a
  have hback : (fun x => x + a) ⁻¹' ((fun x => a + x) '' Ω) = Ω := by
    rw [hpre]; ext x; simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Homeomorph.addLeft a).isOpenMap _ h.isOpen
  · exact h.isConnected.image _ (continuous_const.add continuous_id).continuousOn
  · rw [hpre]
    exact (isBounded_preimage_add_right_iff Ω (-a)).2 h.isBounded
  · rw [volume_image_translate]
    exact h.volume_eq
  · intro p hp
    rw [hpre, frontier_preimage_add_right] at hp
    obtain ⟨c, hc, hpc, hk⟩ := h.boundary_C3 (p + -a) hp
    refine ⟨c.translate (-a), ?_, hpc, hk⟩
    rw [hpre]
    exact hc.translate (-a)
  · intro p hp c hc hpc hc2
    set q : AmbientSpace := p + -a with hqdef
    have hqa : q + a = p := by simp [hqdef]
    have haq : a + q = p := by rw [add_comm]; exact hqa
    have hq : q ∈ frontier Ω := by
      have h1 : q ∈ frontier ((fun x => x + a) ⁻¹' ((fun x => a + x) '' Ω)) := by
        rw [frontier_preimage_add_right]
        rw [mem_preimage, hqa]
        exact hp
      rwa [hback] at h1
    have hc' : (c.translate a).IsChartFor Ω := by
      have h1 := hc.translate a
      rwa [hback] at h1
    have hqc : q ∈ (c.translate a).region := by
      change q + a ∈ c.region
      rw [hqa]
      exact hpc
    have hEL := h.eulerLagrange q hq (c.translate a) hc' hqc hc2
    have hn : (c.translate a).outwardNormal = fun z => c.outwardNormal (z + a) := by
      funext z
      exact c.translate_outwardNormal a z
    have hfr : frontier Ω =
        (fun x => x + a) ⁻¹' frontier ((fun x => a + x) '' Ω) := by
      rw [← frontier_preimage_add_right, hback]
    rw [hn, hfr, meanCurvature_preimage_add_right, hqa] at hEL
    rw [← haq, coulombPotential_translate, haq]
    exact hEL

end IsStationaryDomain

end LiquidDrop

#print axioms LiquidDrop.IsStationaryDomain.image_add_left
