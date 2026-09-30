module

public import NoCompromise.Sobolev.LipschitzCubes
public import NoCompromise.Area.Linear

@[expose] public section

/-!
# Classical faces and boundary area of a coordinate cube

All surface measures in this file are normalized two-dimensional Hausdorff
measure. The proofs use affine isometries of the faces and ordinary Lebesgue
measure; no finite-perimeter structure theorem is used.
-/

noncomputable section
open MeasureTheory Set Metric Function
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The closed coordinate cube, in Euclidean coordinates. -/
def closedCoordinateCube (n : ℕ) (R : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i, |x i| ≤ R}

lemma closedCoordinateCube_eq_preimage (n : ℕ) (R : ℝ) :
    closedCoordinateCube n R = WithLp.ofLp ⁻¹'
      Icc (fun _ : Fin n => -R) (fun _ : Fin n => R) := by
  ext x
  simp only [closedCoordinateCube, mem_ofPred_eq, mem_preimage, mem_Icc, Pi.le_def,
    abs_le]
  exact forall_and

lemma isCompact_closedCoordinateCube (n : ℕ) (R : ℝ) :
    IsCompact (closedCoordinateCube n R) := by
  rw [closedCoordinateCube_eq_preimage]
  exact (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).isCompact_preimage.mpr isCompact_Icc

lemma closure_coordinateCube {n : ℕ} {R : ℝ} (hR : 0 < R) :
    closure (coordinateCube n R) = closedCoordinateCube n R := by
  let e := PiLp.homeomorph 2 (fun _ : Fin n => ℝ)
  have he : coordinateCube n R = e ⁻¹' (univ.pi fun _ => Ioo (-R) R) := by
    ext x
    change (∀ i, |x i| < R) ↔ (∀ i ∈ (univ : Set (Fin n)), -R < x i ∧ x i < R)
    simp only [mem_univ, true_implies, abs_lt]
  rw [he, ← e.preimage_closure, closure_pi_set]
  simp only [closure_Ioo (by linarith : -R ≠ R)]
  ext x
  change (∀ i ∈ (univ : Set (Fin n)), x i ∈ Icc (-R) R) ↔ (∀ i, |x i| ≤ R)
  simp only [mem_univ, true_implies, mem_Icc, abs_le]

lemma coordinateCube_ae_eq_closed (n : ℕ) (R : ℝ) :
    coordinateCube n R =ᵐ[volume] closedCoordinateCube n R := by
  have h := (PiLp.volume_preserving_ofLp (Fin n)).quasiMeasurePreserving.ae
    (Measure.univ_pi_Ioo_ae_eq_Icc (μ := fun _ : Fin n => volume)
      (f := fun _ => -R) (g := fun _ => R))
  filter_upwards [h] with x hx
  change (∀ i, |x i| < R) = (∀ i, |x i| ≤ R)
  change (WithLp.ofLp x ∈ univ.pi (fun _ => Ioo (-R) R)) =
    (WithLp.ofLp x ∈ Icc (fun _ => -R) (fun _ => R)) at hx
  simpa only [mem_pi, mem_univ, true_implies, mem_Ioo, mem_Icc,
    Pi.le_def, ← forall_and, ← abs_lt, ← abs_le] using hx

/-- Insert the fixed coordinate of a cube face. -/
def cubeFaceParam (i : Fin 3) (t : ℝ) (p : EuclideanSpace ℝ (Fin 2)) : AmbientSpace :=
  WithLp.toLp 2 (i.insertNth t (WithLp.ofLp p))

@[simp] lemma cubeFaceParam_same (i : Fin 3) (t : ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    cubeFaceParam i t p i = t := by
  change i.insertNth (α := fun _ => ℝ) t (fun j => p j) i = t
  simp

@[simp] lemma cubeFaceParam_succAbove (i : Fin 3) (t : ℝ)
    (p : EuclideanSpace ℝ (Fin 2)) (j : Fin 2) :
    cubeFaceParam i t p (i.succAbove j) = p j := by
  change i.insertNth (α := fun _ => ℝ) t (fun j => p j) (i.succAbove j) = p j
  simp

lemma isometry_cubeFaceParam (i : Fin 3) (t : ℝ) : Isometry (cubeFaceParam i t) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.real_norm_sq_eq]
  rw [Fin.sum_univ_succAbove _ i]
  simp [PiLp.sub_apply]

/-- A closed face, indexed by its fixed coordinate and its sign. -/
def cubeFace (R : ℝ) (j : Fin 3 × Bool) : Set AmbientSpace :=
  cubeFaceParam j.1 (if j.2 then R else -R) '' closedCoordinateCube 2 R

/-- The relative interior of a face. -/
def cubeOpenFace (R : ℝ) (j : Fin 3 × Bool) : Set AmbientSpace :=
  cubeFaceParam j.1 (if j.2 then R else -R) '' coordinateCube 2 R

lemma isCompact_cubeFace (R : ℝ) (j : Fin 3 × Bool) : IsCompact (cubeFace R j) :=
  (isCompact_closedCoordinateCube 2 R).image (isometry_cubeFaceParam _ _).continuous

lemma measurableSet_cubeOpenFace (R : ℝ) (j : Fin 3 × Bool) :
    MeasurableSet (cubeOpenFace R j) :=
  (isometry_cubeFaceParam _ _).isClosedEmbedding.measurableEmbedding.measurableSet_image'
    (isOpen_coordinateCube 2 R).measurableSet

lemma cubeFaceParam_preimage_closedCube {R : ℝ} (hR : 0 ≤ R) (j : Fin 3 × Bool) :
    cubeFaceParam j.1 (if j.2 then R else -R) ⁻¹' closedCoordinateCube 3 R =
      closedCoordinateCube 2 R := by
  ext p
  change (∀ i, |cubeFaceParam j.1 (if j.2 then R else -R) p i| ≤ R) ↔ ∀ i, |p i| ≤ R
  constructor
  · intro h i
    simpa using h (j.1.succAbove i)
  · intro h i
    by_cases hi : i = j.1
    · subst i
      simp only [cubeFaceParam_same]
      cases j.2 <;> simp [abs_of_nonneg hR]
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hi
      simpa using h k

lemma mem_cubeFace {R : ℝ} (hR : 0 ≤ R) (j : Fin 3 × Bool) (x : AmbientSpace) :
    x ∈ cubeFace R j ↔ x ∈ closedCoordinateCube 3 R ∧
      x j.1 = if j.2 then R else -R := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨by rwa [← cubeFaceParam_preimage_closedCube hR j] at hp,
      cubeFaceParam_same _ _ _⟩
  · rintro ⟨hx, hi⟩
    let p : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (fun k => x (j.1.succAbove k))
    refine ⟨p, (fun k => hx (j.1.succAbove k)), ?_⟩
    apply PiLp.ext
    intro k
    by_cases hk : k = j.1
    · subst k
      simpa using hi.symm
    · obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq hk
      simp [p]

lemma hausdorffMeasure2_cubeFaceParam (i : Fin 3) (t : ℝ)
    (A : Set (EuclideanSpace ℝ (Fin 2))) :
    hausdorffMeasure2 3 (cubeFaceParam i t '' A) = volume A :=
  ((isometry_cubeFaceParam i t).euclideanHausdorffMeasure_image A).trans
    (congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin 2)) => μ A) hausdorffMeasure2_plane)

lemma cubeFace_ae_eq_openFace (R : ℝ) (j : Fin 3 × Bool) :
    cubeFace R j =ᵐ[hausdorffMeasure2 3] cubeOpenFace R j := by
  have h := ae_eq_set.mp (coordinateCube_ae_eq_closed 2 R).symm
  apply ae_eq_set.mpr
  constructor
  · rw [cubeFace, cubeOpenFace, ← image_sdiff (isometry_cubeFaceParam _ _).injective,
      hausdorffMeasure2_cubeFaceParam]
    exact h.1
  · rw [cubeFace, cubeOpenFace, ← image_sdiff (isometry_cubeFaceParam _ _).injective,
      hausdorffMeasure2_cubeFaceParam]
    exact h.2

lemma mem_cubeOpenFace (R : ℝ) (j : Fin 3 × Bool) (x : AmbientSpace) :
    x ∈ cubeOpenFace R j ↔ (x j.1 = if j.2 then R else -R) ∧
      ∀ k, k ≠ j.1 → |x k| < R := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨cubeFaceParam_same _ _ _, fun k hk => ?_⟩
    obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq hk
    simpa using hp a
  · rintro ⟨hi, hx⟩
    let p : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (fun k => x (j.1.succAbove k))
    refine ⟨p, (fun k => hx _ (Fin.succAbove_ne _ _)), ?_⟩
    apply PiLp.ext
    intro k
    by_cases hk : k = j.1
    · subst k
      simpa using hi.symm
    · obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq hk
      simp [p]

lemma pairwiseDisjoint_cubeOpenFace {R : ℝ} (hR : 0 < R) :
    Pairwise (Disjoint on cubeOpenFace R) := by
  intro i j hij
  change Disjoint (cubeOpenFace R i) (cubeOpenFace R j)
  rw [disjoint_left]
  intro x hxi hxj
  rw [mem_cubeOpenFace] at hxi hxj
  by_cases hc : i.1 = j.1
  · have hs : i.2 ≠ j.2 := fun hs => hij (Prod.ext hc hs)
    have he := hxi.1.symm.trans ((congrArg (fun k => x k) hc).trans hxj.1)
    cases hi : i.2 <;> cases hj : j.2 <;> norm_num [hi, hj] at he hs <;> linarith
  · have h := hxj.2 i.1 hc
    rw [hxi.1] at h
    cases hi : i.2 <;> simp [hi, abs_of_pos hR] at h

lemma frontier_coordinateCube {R : ℝ} (hR : 0 < R) :
    frontier (coordinateCube 3 R) = ⋃ j : Fin 3 × Bool, cubeFace R j := by
  rw [(isOpen_coordinateCube 3 R).frontier_eq, closure_coordinateCube hR]
  ext x
  constructor
  · rintro ⟨hx, hn⟩
    change ¬ (∀ i, |x i| < R) at hn
    obtain ⟨i, hi⟩ := not_forall.mp hn
    have he : |x i| = R := le_antisymm (hx i) (le_of_not_gt hi)
    rcases (abs_eq (le_of_lt hR)).mp he with hp | hm
    · exact mem_iUnion.mpr ⟨(i, true), (mem_cubeFace hR.le _ _).mpr ⟨hx, hp⟩⟩
    · exact mem_iUnion.mpr ⟨(i, false), (mem_cubeFace hR.le _ _).mpr ⟨hx, hm⟩⟩
  · intro hx
    rcases mem_iUnion.mp hx with ⟨j, hj⟩
    rcases (mem_cubeFace hR.le j x).mp hj with ⟨hx, he⟩
    refine ⟨hx, fun hn => ?_⟩
    have h := hn j.1
    rw [he] at h
    cases hb : j.2 <;> simp [hb, abs_of_pos hR] at h

lemma map_volume_restrict_cubeFaceParam (i : Fin 3) (t : ℝ)
    {A : Set (EuclideanSpace ℝ (Fin 2))} (_hA : MeasurableSet A) :
    Measure.map (cubeFaceParam i t) (volume.restrict A) =
      (hausdorffMeasure2 3).restrict (cubeFaceParam i t '' A) := by
  ext S hS
  rw [Measure.map_apply (isometry_cubeFaceParam i t).continuous.measurable hS,
    Measure.restrict_apply ((isometry_cubeFaceParam i t).continuous.measurable hS),
    Measure.restrict_apply hS]
  have he : S ∩ cubeFaceParam i t '' A =
      cubeFaceParam i t '' (cubeFaceParam i t ⁻¹' S ∩ A) := by
    ext x
    constructor
    · rintro ⟨hx, p, hp, rfl⟩
      exact ⟨p, ⟨hx, hp⟩, rfl⟩
    · rintro ⟨p, ⟨hs, hp⟩, rfl⟩
      exact ⟨hs, ⟨p, hp, rfl⟩⟩
  rw [he, hausdorffMeasure2_cubeFaceParam]

lemma boundaryMeasure_coordinateCube {R : ℝ} (hR : 0 < R) :
    (hausdorffMeasure2 3).restrict (frontier (coordinateCube 3 R)) =
      ∑ j : Fin 3 × Bool, Measure.map (cubeFaceParam j.1 (if j.2 then R else -R))
        (volume.restrict (closedCoordinateCube 2 R)) := by
  have he : (⋃ j : Fin 3 × Bool, cubeFace R j) =ᵐ[hausdorffMeasure2 3]
      ⋃ j : Fin 3 × Bool, cubeOpenFace R j :=
    Filter.EventuallyEq.countable_iUnion fun j => cubeFace_ae_eq_openFace R j
  rw [frontier_coordinateCube hR, Measure.restrict_congr_set he,
    Measure.restrict_iUnion (pairwiseDisjoint_cubeOpenFace hR)
      (measurableSet_cubeOpenFace R), Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_volume_restrict_cubeFaceParam _ _ (isCompact_closedCoordinateCube 2 R).measurableSet]
  exact Measure.restrict_congr_set (cubeFace_ae_eq_openFace R j).symm

lemma hausdorffMeasure2_frontier_coordinateCube_lt_top {R : ℝ} (hR : 0 < R) :
    hausdorffMeasure2 3 (frontier (coordinateCube 3 R)) < ∞ := by
  have h : (hausdorffMeasure2 3).restrict (frontier (coordinateCube 3 R)) univ < ∞ := by
    rw [boundaryMeasure_coordinateCube hR, Measure.finsetSum_apply]
    apply ENNReal.sum_lt_top.mpr
    intro j _
    rw [Measure.map_apply (isometry_cubeFaceParam _ _).continuous.measurable MeasurableSet.univ]
    simpa using (isCompact_closedCoordinateCube 2 R).measure_lt_top (μ := volume)
  simpa using h

/-- The classical outward unit normal of one face. -/
def cubeFaceUnitNormal (j : Fin 3 × Bool) : AmbientSpace :=
  (if j.2 then (1 : ℝ) else -1) • EuclideanSpace.single j.1 1

lemma norm_cubeFaceUnitNormal (j : Fin 3 × Bool) : ‖cubeFaceUnitNormal j‖ = 1 := by
  cases hb : j.2 <;> simp [cubeFaceUnitNormal, hb]

/-- The outward normal on face interiors, set to zero on the edges and off the boundary. -/
def cubeOutwardNormal (R : ℝ) (x : AmbientSpace) : AmbientSpace :=
  ∑ j : Fin 3 × Bool, (cubeOpenFace R j).indicator (fun _ => cubeFaceUnitNormal j) x

lemma measurable_cubeOutwardNormal (R : ℝ) : Measurable (cubeOutwardNormal R) := by
  apply Finset.measurable_sum
  intro j _
  exact measurable_const.indicator (measurableSet_cubeOpenFace R j)

lemma cubeOutwardNormal_of_mem_openFace {R : ℝ} (hR : 0 < R)
    (j : Fin 3 × Bool) {x : AmbientSpace} (hx : x ∈ cubeOpenFace R j) :
    cubeOutwardNormal R x = cubeFaceUnitNormal j := by
  classical
  rw [cubeOutwardNormal, Finset.sum_eq_single j]
  · exact indicator_of_mem hx _
  · intro k _ hkj
    exact indicator_of_notMem (fun hk =>
      (pairwiseDisjoint_cubeOpenFace hR hkj).le_bot ⟨hk, hx⟩) _
  · simp

lemma norm_cubeOutwardNormal_le_one {R : ℝ} (hR : 0 < R) (x : AmbientSpace) :
    ‖cubeOutwardNormal R x‖ ≤ 1 := by
  classical
  by_cases hx : ∃ j, x ∈ cubeOpenFace R j
  · obtain ⟨j, hj⟩ := hx
    rw [cubeOutwardNormal_of_mem_openFace hR j hj, norm_cubeFaceUnitNormal]
  · have hz : cubeOutwardNormal R x = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      exact indicator_of_notMem (fun hj => hx ⟨j, hj⟩) _
    simp [hz]

lemma cubeOutwardNormal_ae_face {R : ℝ} (hR : 0 < R) (j : Fin 3 × Bool) :
    cubeOutwardNormal R =ᵐ[(hausdorffMeasure2 3).restrict (cubeFace R j)]
      fun _ => cubeFaceUnitNormal j := by
  have h := ae_restrict_mem (μ := hausdorffMeasure2 3) (isCompact_cubeFace R j).measurableSet
  filter_upwards [h, ae_restrict_of_ae (cubeFace_ae_eq_openFace R j)] with x hx he
  exact cubeOutwardNormal_of_mem_openFace hR j (Eq.mp he hx)

lemma norm_cubeOutwardNormal_ae {R : ℝ} (hR : 0 < R) :
    ∀ᵐ x ∂(hausdorffMeasure2 3).restrict (frontier (coordinateCube 3 R)),
      ‖cubeOutwardNormal R x‖ = 1 := by
  rw [frontier_coordinateCube hR, ae_restrict_iUnion_iff]
  intro j
  filter_upwards [cubeOutwardNormal_ae_face hR j] with x hx
  rw [hx, norm_cubeFaceUnitNormal]

lemma integral_cube_boundary_eq_faces {R : ℝ} (hR : 0 < R)
    {g : AmbientSpace → ℝ}
    (hg : Integrable g ((hausdorffMeasure2 3).restrict (frontier (coordinateCube 3 R)))) :
    (∫ x, g x ∂(hausdorffMeasure2 3).restrict (frontier (coordinateCube 3 R))) =
      ∑ j : Fin 3 × Bool, ∫ p in closedCoordinateCube 2 R,
        g (cubeFaceParam j.1 (if j.2 then R else -R) p) := by
  rw [boundaryMeasure_coordinateCube hR] at hg ⊢
  rw [← Measure.sum_fintype] at hg ⊢
  rw [integral_sum_measure hg, tsum_fintype]
  apply Finset.sum_congr rfl
  intro j _
  exact (isometry_cubeFaceParam _ _).isClosedEmbedding.measurableEmbedding.integral_map g

lemma integral_cube_face_flux {R : ℝ} (hR : 0 < R) (j : Fin 3 × Bool)
    (Z : AmbientSpace → AmbientSpace) :
    (∫ p in closedCoordinateCube 2 R,
      inner ℝ (Z (cubeFaceParam j.1 (if j.2 then R else -R) p))
        (cubeOutwardNormal R (cubeFaceParam j.1 (if j.2 then R else -R) p))) =
      ∫ p in closedCoordinateCube 2 R,
        (if j.2 then (1 : ℝ) else -1) *
          Z (cubeFaceParam j.1 (if j.2 then R else -R) p) j.1 := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (isCompact_closedCoordinateCube 2 R).measurableSet,
    ae_restrict_of_ae (coordinateCube_ae_eq_closed 2 R)] with p hp he
  have ho : p ∈ coordinateCube 2 R := Eq.mp he.symm hp
  rw [cubeOutwardNormal_of_mem_openFace hR j ⟨p, ho, rfl⟩]
  cases hb : j.2 <;> simp [cubeFaceUnitNormal, hb, EuclideanSpace.inner_single_right]

end LiquidDrop
