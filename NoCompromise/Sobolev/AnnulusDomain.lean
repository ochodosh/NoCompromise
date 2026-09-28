import NoCompromise.Sobolev.C1Domain
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Round annuli as admissible Sobolev domains

The inner and outer spheres have explicit C¹ one-sided graph charts. A round
annulus with strictly positive inner radius and strictly larger outer radius is
a bounded connected open C¹ domain in three-dimensional Euclidean space.
-/

noncomputable section
open MeasureTheory Set Filter Metric Topology
open scoped ENNReal NNReal Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The local spherical height above the tangent plane, in two base coordinates. -/
def sphericalBoundaryHeight (r : ℝ) (p : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  r - Real.sqrt (r ^ 2 - ‖p‖ ^ 2)

lemma contDiffOn_sphericalBoundaryHeight {r : ℝ} (hr : 0 < r) :
    ContDiffOn ℝ 1 (sphericalBoundaryHeight r) (ball 0 (r / 2)) := by
  apply contDiffOn_const.sub
  apply (contDiffOn_const.sub (contDiff_norm_sq ℝ).contDiffOn).sqrt
  intro p hp
  have hp' : ‖p‖ < r / 2 := by simpa using hp
  have hp0 := norm_nonneg p
  nlinarith

/-- In a tangent neighborhood, the two sides of a sphere are the two sides
of its explicit height graph. -/
lemma sphericalBoundaryHeight_side_iff {r : ℝ} (hr : 0 < r)
    {y : AmbientSpace} (hy : ‖y‖ < r / 2) :
    (‖y - r • EuclideanSpace.single (Fin.last 2) 1‖ < r ↔
      sphericalBoundaryHeight r (graphProjectionN 2 y) < y (Fin.last 2)) ∧
    (r < ‖y - r • EuclideanSpace.single (Fin.last 2) 1‖ ↔
      y (Fin.last 2) < sphericalBoundaryHeight r (graphProjectionN 2 y)) := by
  have hn := norm_sq_graphProjectionN y
  have hp0 := norm_nonneg (graphProjectionN 2 y)
  have hy0 := norm_nonneg y
  have hp : ‖graphProjectionN 2 y‖ ≤ r / 2 := by nlinarith [sq_nonneg (y (Fin.last 2))]
  have ht : y (Fin.last 2) < r / 2 :=
    (le_abs_self _).trans_lt ((PiLp.norm_apply_le y (Fin.last 2)).trans_lt hy)
  have hs : 0 ≤ r ^ 2 - ‖graphProjectionN 2 y‖ ^ 2 := by nlinarith
  have hsqrt := Real.sq_sqrt hs
  have hroot := sqrt_radius_sq_sub_norm_sq_ge_half hr hp
  have hnorm := norm_sq_graphProjectionN
    (y - r • EuclideanSpace.single (Fin.last 2) 1)
  have hproj : graphProjectionN 2 (y - r • EuclideanSpace.single (Fin.last 2) 1) =
      graphProjectionN 2 y := by
    ext i
    simp only [graphProjectionN_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      EuclideanSpace.single, PiLp.single_apply, Fin.castSucc_ne_last, ite_false,
      mul_zero, sub_zero]
  rw [hproj] at hnorm
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, EuclideanSpace.single, PiLp.single_apply,
    ite_true, mul_one] at hnorm
  have hnonneg := norm_nonneg (y - r • EuclideanSpace.single (Fin.last 2) 1)
  dsimp only [sphericalBoundaryHeight]
  constructor <;> constructor <;> intro hh <;> nlinarith

/-- Balls have geometric C¹ boundary in the one-sided graph convention. -/
theorem hasC1Boundary_ball (z : AmbientSpace) {r : ℝ} (hr : 0 < r) :
    HasC1Boundary (ball z r) := by
  apply hasC1Boundary_of_local_graphs
  intro x hx
  have hxnorm : ‖z - x‖ = r := by
    rw [frontier_ball z hr.ne'] at hx
    simpa only [mem_sphere, dist_eq_norm, norm_sub_rev] using hx
  obtain ⟨a, ha0, har⟩ := exists_affineIsometry_ball_placement (Fin.last 2) hr hxnorm
  let b : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace :=
    (LinearIsometryEquiv.neg ℝ).toAffineIsometryEquiv.trans a
  let f : EuclideanSpace ℝ (Fin 2) → ℝ := fun p => -sphericalBoundaryHeight r (-p)
  have hf : ContDiffOn ℝ 1 f (ball 0 (r / 2)) :=
    ((contDiffOn_sphericalBoundaryHeight hr).comp contDiffOn_id.neg
      (by intro p hp; simpa using hp)).neg
  refine ⟨b, f, ball 0 (r / 2), b '' ball 0 (r / 2), isOpen_ball, hf, ?_,
    b.toHomeomorph.isOpenMap _ isOpen_ball, ?_, ?_⟩
  · have hb0 : b 0 = x := by simpa [b] using ha0
    rw [← hb0, b.symm_apply_apply]
    simpa using (by linarith : (0 : ℝ) < r / 2)
  · refine ⟨0, by simpa using (by linarith : (0 : ℝ) < r / 2), ?_⟩
    simpa [b] using ha0
  · rintro w ⟨y, hy, rfl⟩
    rw [b.symm_apply_apply]
    have hy' : ‖-y‖ < r / 2 := by simpa using hy
    have hs := (sphericalBoundaryHeight_side_iff hr hy').1
    change dist (a (-y)) z < r ↔ _
    rw [← har, a.isometry.dist_eq, dist_eq_norm]
    dsimp only [f]
    simp only [map_neg, PiLp.neg_apply] at hs
    exact hs.trans (by constructor <;> intro ht <;> linarith)

/-- The exterior of a positive closed ball has geometric C¹ boundary. -/
theorem hasC1Boundary_closedBall_compl (z : AmbientSpace) {r : ℝ} (hr : 0 < r) :
    HasC1Boundary (closedBall z r)ᶜ := by
  apply hasC1Boundary_of_local_graphs
  intro x hx
  have hxnorm : ‖z - x‖ = r := by
    rw [frontier_compl, frontier_closedBall z hr.ne'] at hx
    simpa only [mem_sphere, dist_eq_norm, norm_sub_rev] using hx
  obtain ⟨a, ha0, har⟩ := exists_affineIsometry_ball_placement (Fin.last 2) hr hxnorm
  refine ⟨a, sphericalBoundaryHeight r, ball 0 (r / 2), a '' ball 0 (r / 2),
    isOpen_ball, contDiffOn_sphericalBoundaryHeight hr, ?_,
    a.toHomeomorph.isOpenMap _ isOpen_ball, ?_, ?_⟩
  · rw [← ha0, a.symm_apply_apply]
    simpa using (by linarith : (0 : ℝ) < r / 2)
  · exact ⟨0, by simpa using (by linarith : (0 : ℝ) < r / 2), ha0⟩
  · rintro w ⟨y, hy, rfl⟩
    rw [a.symm_apply_apply]
    change ¬ dist (a y) z ≤ r ↔ _
    rw [not_le, ← har, a.isometry.dist_eq, dist_eq_norm]
    exact (sphericalBoundaryHeight_side_iff hr (by simpa using hy)).2

/-- Transfer a local boundary chart across equality of domains in an open neighborhood. -/
lemma exists_c1BoundaryChart_of_local_eq {D E W : Set AmbientSpace}
    (hE : HasC1Boundary E) {x : AmbientSpace} (hx : x ∈ frontier E)
    (hW : IsOpen W) (hxW : x ∈ W)
    (heq : ∀ y ∈ W, y ∈ D ↔ y ∈ E) :
    ∃ c : C1BoundaryChart, c.IsChartFor D ∧ x ∈ c.region := by
  obtain ⟨c, hc, hxc⟩ := hE x hx
  let d : C1BoundaryChart := ⟨c.height, c.height_contDiff, c.placement,
    c.region ∩ W, c.isOpen_region.inter hW, c.bounded_region.subset inter_subset_left⟩
  refine ⟨d, ?_, hxc, hxW⟩
  intro y hy
  exact (heq y hy.2).trans (hc y hy.1)

/-- A round open annulus; the strict inequalities exclude both boundary spheres. -/
def roundAnnulus (z : AmbientSpace) (r R : ℝ) : Set AmbientSpace :=
  ball z R \ closedBall z r

@[simp] lemma mem_roundAnnulus {z x : AmbientSpace} {r R : ℝ} :
    x ∈ roundAnnulus z r R ↔ r < dist x z ∧ dist x z < R := by
  simp only [roundAnnulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le, and_comm]

lemma isOpen_roundAnnulus (z : AmbientSpace) (r R : ℝ) :
    IsOpen (roundAnnulus z r R) := isOpen_ball.sdiff isClosed_closedBall

lemma isBounded_roundAnnulus (z : AmbientSpace) (r R : ℝ) :
    Bornology.IsBounded (roundAnnulus z r R) := isBounded_ball.subset sdiff_subset

/-- Both boundary spheres of a positive annulus have correctly oriented C¹ charts. -/
theorem hasC1Boundary_roundAnnulus (z : AmbientSpace) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) : HasC1Boundary (roundAnnulus z r R) := by
  intro x hx
  have hR : 0 < R := hr.trans hrR
  have hx' : x ∈ frontier (ball z R ∩ (closedBall z r)ᶜ) := hx
  rcases frontier_inter_subset _ _ hx' with h | h
  · have hd : dist x z = R := by
      simpa only [frontier_ball z hR.ne', mem_sphere] using h.1
    refine exists_c1BoundaryChart_of_local_eq (W := (closedBall z r)ᶜ)
      (hasC1Boundary_ball z hR) h.1
      isClosed_closedBall.isOpen_compl (by simpa only [mem_compl_iff, mem_closedBall,
        not_le, hd] using hrR) ?_
    intro y hy
    simp only [roundAnnulus, Set.mem_sdiff, mem_compl_iff] at hy ⊢
    exact and_iff_left hy
  · have hb : x ∈ frontier (closedBall z r)ᶜ := h.2
    have hd : dist x z = r := by
      simpa only [frontier_compl, frontier_closedBall z hr.ne', mem_sphere] using hb
    refine exists_c1BoundaryChart_of_local_eq (W := ball z R)
      (hasC1Boundary_closedBall_compl z hr) hb
      isOpen_ball (by simpa only [mem_ball, hd] using hrR) ?_
    intro y hy
    simp only [roundAnnulus, Set.mem_sdiff, mem_compl_iff]
    exact and_iff_right hy

/-- A spatial round annulus is connected: it is the continuous image of a
sphere times an interval. The dimension is three, so the sphere is connected. -/
theorem isPreconnected_roundAnnulus (z : AmbientSpace) {r R : ℝ}
    (hr : 0 < r) : IsPreconnected (roundAnnulus z r R) := by
  let F : AmbientSpace × ℝ → AmbientSpace := fun p => z + p.2 • p.1
  have hF : Continuous F := continuous_const.add (continuous_snd.smul continuous_fst)
  have hdim : (1 : Cardinal) < Module.rank ℝ AmbientSpace := by
    rw [← Module.finrank_eq_rank]
    norm_num [AmbientSpace]
  have hpc := ((isPreconnected_sphere hdim (0 : AmbientSpace) 1).prod
    (isPreconnected_Ioo (a := r) (b := R))).image F hF.continuousOn
  have him : F '' (sphere (0 : AmbientSpace) 1 ×ˢ Ioo r R) = roundAnnulus z r R := by
    ext x
    constructor
    · rintro ⟨⟨p, t⟩, ⟨hp, ht⟩, rfl⟩
      have hp' : ‖p‖ = 1 := by simpa using hp
      have ht0 := hr.trans ht.1
      have hd : dist (F (p, t)) z = t := by
        simp [F, dist_eq_norm, norm_smul, abs_of_pos ht0, hp']
      exact mem_roundAnnulus.mpr (by simpa only [hd, mem_Ioo] using ht)
    · intro hx
      obtain ⟨hlt, hgt⟩ := mem_roundAnnulus.mp hx
      have ht0 : 0 < ‖x - z‖ := by simpa only [dist_eq_norm] using hr.trans hlt
      refine ⟨(‖x - z‖⁻¹ • (x - z), ‖x - z‖), ⟨?_, ?_⟩, ?_⟩
      · simp [norm_smul, ht0.ne']
      · simpa only [mem_Ioo, dist_eq_norm] using And.intro hlt hgt
      · simp [F, smul_smul, ht0.ne']
  rwa [him] at hpc

/-- Positive round annuli satisfy the exact geometric hypotheses of the
Poincaré and trace estimates. -/
theorem roundAnnulus_admissible (z : AmbientSpace) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) :
    IsOpen (roundAnnulus z r R) ∧ IsPreconnected (roundAnnulus z r R) ∧
      Bornology.IsBounded (roundAnnulus z r R) ∧ HasC1Boundary (roundAnnulus z r R) :=
  ⟨isOpen_roundAnnulus z r R, isPreconnected_roundAnnulus z hr,
    isBounded_roundAnnulus z r R, hasC1Boundary_roundAnnulus z hr hrR⟩

/-- Balls are also covered by the geometric C¹-domain endpoint. -/
theorem ball_admissible (z : AmbientSpace) {r : ℝ} (hr : 0 < r) :
    IsOpen (ball z r) ∧ IsPreconnected (ball z r) ∧
      Bornology.IsBounded (ball z r) ∧ HasC1Boundary (ball z r) :=
  ⟨isOpen_ball, isPreconnected_ball, isBounded_ball, hasC1Boundary_ball z hr⟩

lemma hasLipschitzBoundary_roundAnnulus (z : AmbientSpace) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) : HasLipschitzBoundary (roundAnnulus z r R) :=
  (hasC1Boundary_roundAnnulus z hr hrR).hasLipschitzBoundary

/-- Both Sobolev inequalities on a positive spatial round annulus. The trace
operator agrees with the actual boundary restriction of continuous representatives. -/
theorem exists_h1_poincare_trace_roundAnnulus (z : AmbientSpace) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) :
    ∃ T : H1Space (roundAnnulus z r R) →L[ℝ]
      Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier (roundAnnulus z r R))),
    ∃ C : ℝ, 0 < C ∧ ‖T‖ ≤ C ∧
      (∀ f G, HasH1GradientOn f G (roundAnnulus z r R) →
        lpNorm (fun x => f x - ⨍ y in roundAnnulus z r R, f y) 2
            (volume.restrict (roundAnnulus z r R)) ≤
          C * lpNorm G 2 (volume.restrict (roundAnnulus z r R))) ∧
      (∀ u : H1Space (roundAnnulus z r R), ‖T u‖ ≤ C *
        (lpNorm u 2 (volume.restrict (roundAnnulus z r R)) +
          lpNorm u.gradientLp 2 (volume.restrict (roundAnnulus z r R)))) ∧
      ∀ f G (hf : HasH1GradientOn f G (roundAnnulus z r R)), Continuous f →
        ∀ᵐ x ∂(hausdorffMeasure2 3).restrict (frontier (roundAnnulus z r R)),
          T (H1Space.ofFunction f G hf) x = f x := by
  obtain ⟨hO, hc, hb, hC1⟩ := roundAnnulus_admissible z hr hrR
  obtain ⟨T, C, hC, hTC, hP, hT, hrep, _⟩ :=
    exists_h1_poincare_trace_c1_domain hO hc hb hC1
  exact ⟨T, C, hC, hTC, hP, hT, hrep⟩

end LiquidDrop
