import NoCompromise.Elliptic.HopfC2Boundary
import NoCompromise.Elliptic.HopfDerivativeWithin

/-!
# The exterior Hopf sign

The outward normal of a C² domain is the actual normal of a chosen valid
rigid graph chart. Derivatives are taken within the closed exterior, so no
extension of the function through the boundary is imposed.
-/

noncomputable section
open Set Filter Metric
open scoped Topology
namespace LiquidDrop

def HasC2Boundary.outwardNormal {D : Set AmbientSpace} (hD : HasC2Boundary D)
    (p : AmbientSpace) : AmbientSpace := by
  classical
  exact if hp : p ∈ frontier D then (hD p hp).choose.outwardNormal p else 0

theorem hopf_exterior_chart {D : Set AmbientSpace} {c : C1BoundaryChart}
    (hc : c.IsChartFor D) (hC2 : ContDiff ℝ 2 c.height)
    {p : AmbientSpace} (hp : p ∈ frontier D) (hpr : p ∈ c.region)
    {u : AmbientSpace → ℝ} (hu : ContinuousOn u (closure (closure D)ᶜ))
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) (closure D)ᶜ)
    (hupper : ∀ x ∈ (closure D)ᶜ, u x < 1) (hup : u p = 1)
    {L : AmbientSpace →L[ℝ] ℝ}
    (hd : HasFDerivWithinAt u L (closure (closure D)ᶜ) p) :
    L (c.outwardNormal p) < 0 := by
  obtain ⟨R, hR, hball, hsp⟩ := hc.exists_exterior_tangent_ball hC2 hp hpr
  have hpcl : p ∈ closure (closure D)ᶜ := closure_mono hball (by
    rw [closure_ball _ hR.ne']
    exact sphere_subset_closedBall hsp)
  have hsub : (closure D)ᶜ ∪ {p} ⊆ closure (closure D)ᶜ :=
    union_subset subset_closure (singleton_subset_iff.mpr hpcl)
  have hvh : HasDistributionalLaplacianOn (fun x => 1 - u x) (fun _ => 0)
      (closure D)ᶜ := by
    simpa only [zero_sub, neg_zero] using
      (hasDistributionalLaplacianOn_const (closure D)ᶜ 1).sub hh
  have hvd : HasFDerivWithinAt (fun x => 1 - u x) (-L) (closure D)ᶜ p := by
    simpa only [zero_sub, Pi.sub_def] using
      (hasFDerivWithinAt_const (1 : ℝ) p (closure D)ᶜ).sub (hd.mono subset_closure)
  have hs := hopf_boundary_derivative_within hR hball hsp
    (continuousOn_const.sub (hu.mono hsub)) hvh
    (fun x hx => sub_pos.mpr (hupper x hx)) (by change 1 - u p = 0; rw [hup, sub_self]) hvd
  have heq : (1 / R) • (p - (p + R • c.outwardNormal p)) = -c.outwardNormal p := by
    simp [smul_neg, smul_smul, hR.ne']
  simpa only [heq, neg_apply, map_neg, neg_neg] using hs

/-- The exterior sign in the chosen genuine graph normal of a C² domain.
Only the upper bound `u<1` is needed; the blueprint's lower bound is stronger. -/
theorem hopf_exterior {D : Set AmbientSpace} (hD : HasC2Boundary D)
    {u : AmbientSpace → ℝ} (hu : ContinuousOn u (closure (closure D)ᶜ))
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) (closure D)ᶜ)
    (hupper : ∀ x ∈ (closure D)ᶜ, u x < 1)
    (hboundary : ∀ p ∈ frontier D, u p = 1)
    {L : AmbientSpace → AmbientSpace →L[ℝ] ℝ}
    (hd : ∀ p ∈ frontier D, HasFDerivWithinAt u (L p) (closure (closure D)ᶜ) p) :
    ∀ p ∈ frontier D, L p (hD.outwardNormal p) < 0 := by
  intro p hp
  obtain ⟨hc, hpr, hC2⟩ := (hD p hp).choose_spec
  have hs := hopf_exterior_chart hc hC2 hp hpr hu hh hupper (hboundary p hp) (hd p hp)
  simpa only [HasC2Boundary.outwardNormal, dite_eq_left hp] using hs

/-- Blueprint `cor:hopf-exterior`, with the C² boundary expressed in the
one-sided graph convention on `interior K`. The derivative within the closed
exterior covers the stated C¹ regularity up to the boundary. Compactness is
unnecessary for this local sign, and the result retains the regular-closed
hypothesis `K = closure (interior K)` exactly. -/
theorem hopf_exterior_regular_closed {K : Set AmbientSpace}
    (hregular : K = closure (interior K)) (hK : HasC2Boundary (interior K))
    {u : AmbientSpace → ℝ} (hu : ContinuousOn u (closure Kᶜ))
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hupper : ∀ x ∈ Kᶜ, u x < 1) (hboundary : ∀ p ∈ frontier K, u p = 1)
    {L : AmbientSpace → AmbientSpace →L[ℝ] ℝ}
    (hd : ∀ p ∈ frontier K, HasFDerivWithinAt u (L p) (closure Kᶜ) p) :
    ∀ p ∈ frontier K, L p (hK.outwardNormal p) < 0 := by
  have hf : frontier (interior K) = frontier K := by
    rw [← hK.hasC1Boundary.frontier_exterior, ← hregular, frontier_compl]
  rw [← hf]
  apply hopf_exterior hK
  · simpa only [← hregular] using hu
  · simpa only [← hregular] using hh
  · simpa only [← hregular] using hupper
  · simpa only [hf] using hboundary
  · simpa only [← hregular, hf] using hd

end LiquidDrop
