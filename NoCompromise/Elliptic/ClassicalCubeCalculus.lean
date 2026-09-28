import NoCompromise.Elliptic.ClassicalCubeGeometry
import NoCompromise.Sobolev.W11Pairing
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Classical divergence theorem on a cube

The rectangular fundamental theorem of calculus is transported through the
volume-preserving Euclidean coordinate equivalence. The six affine face
integrals are then identified with the Hausdorff boundary integral.
-/

noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped ENNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma integral_divergence_cube_eq_face_integrals {R : ℝ} (hR : 0 < R)
    {Z : AmbientSpace → AmbientSpace} (hZ : ContDiff ℝ 1 Z) :
    (∫ x in coordinateCube 3 R, divergenceN Z x) =
      ∑ i : Fin 3, ((∫ p in closedCoordinateCube 2 R, Z (cubeFaceParam i R p) i) -
        ∫ p in closedCoordinateCube 2 R, Z (cubeFaceParam i (-R) p) i) := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  let f (i : Fin 3) (x : Fin 3 → ℝ) := Z (e.symm x) i
  let f' (i : Fin 3) (x : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] ℝ :=
    (EuclideanSpace.proj i).comp ((fderiv ℝ Z (e.symm x)).comp e.symm.toContinuousLinearMap)
  have hd (x : Fin 3 → ℝ) (i : Fin 3) : HasFDerivAt (f i) (f' i x) x := by
    simpa only [f, f', Function.comp_def] using!
      (EuclideanSpace.proj i : AmbientSpace →L[ℝ] ℝ).hasFDerivAt.comp x
        (((hZ.differentiable one_ne_zero).differentiableAt.hasFDerivAt).comp x
          e.symm.hasFDerivAt)
  have hdiv (x : Fin 3 → ℝ) : (∑ i, f' i x (Pi.single i 1)) =
      divergenceN Z (e.symm x) := by
    simp only [f', ContinuousLinearMap.comp_apply, divergenceN]
    rfl
  have hc : Continuous (divergenceN Z) := by
    apply continuous_finsetSum
    intro i _
    exact (EuclideanSpace.proj i).continuous.comp
      ((hZ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have hraw := integral_divergence_of_hasFDerivAt_off_countable'
    (fun _ : Fin 3 => -R) (fun _ : Fin 3 => R) (fun _ => by linarith)
    f f' ∅ countable_empty (fun i =>
      (show Differentiable ℝ (f i) from fun x =>
        (hd x i).differentiableAt).continuous.continuousOn)
    (fun x _ i => hd x i)
    (by simpa only [hdiv, Function.comp_def] using!
      (hc.comp e.symm.continuous).integrableOn_Icc)
  have hbulk : (∫ x in coordinateCube 3 R, divergenceN Z x) =
      ∫ x in Icc (fun _ : Fin 3 => -R) (fun _ : Fin 3 => R), divergenceN Z (e.symm x) := by
    rw [setIntegral_congr_set (coordinateCube_ae_eq_closed 3 R),
      closedCoordinateCube_eq_preimage]
    simpa only [e, Function.comp_def, PiLp.continuousLinearEquiv_symm_apply,
      WithLp.toLp_ofLp] using
      (PiLp.volume_preserving_ofLp (Fin 3)).setIntegral_preimage_emb
        (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.measurableEmbedding
        (fun x => divergenceN Z (e.symm x))
        (Icc (fun _ : Fin 3 => -R) (fun _ : Fin 3 => R))
  simp_rw [hdiv] at hraw
  rw [hbulk]
  calc
    _ = _ := by exact hraw
    _ = _ := ?_
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  · rw [closedCoordinateCube_eq_preimage]
    exact ((PiLp.volume_preserving_ofLp (Fin 2)).setIntegral_preimage_emb
      (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.measurableEmbedding
      (fun p => f i (i.insertNth R p))
      (Icc (fun _ : Fin 2 => -R) (fun _ : Fin 2 => R))).symm
  · rw [closedCoordinateCube_eq_preimage]
    exact ((PiLp.volume_preserving_ofLp (Fin 2)).setIntegral_preimage_emb
      (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.measurableEmbedding
      (fun p => f i (i.insertNth (-R) p))
      (Icc (fun _ : Fin 2 => -R) (fun _ : Fin 2 => R))).symm

lemma integrable_cube_boundary_flux {R : ℝ} (hR : 0 < R)
    {Z : AmbientSpace → AmbientSpace} (hZ : Continuous Z) :
    Integrable (fun x => inner ℝ (Z x) (cubeOutwardNormal R x))
      ((hausdorffMeasure2 3).restrict (frontier (coordinateCube 3 R))) := by
  have hc : IsCompact (frontier (coordinateCube 3 R)) :=
    (isBounded_coordinateCube 3 R).isCompact_closure.of_isClosed_subset isClosed_frontier
      frontier_subset_closure
  have hi := hZ.continuousOn.integrableOn_of_subset_isCompact hc
    isClosed_frontier.measurableSet Subset.rfl
    (hausdorffMeasure2_frontier_coordinateCube_lt_top hR).ne
  exact integrable_inner_of_ae_bound hi (measurable_cubeOutwardNormal R).aestronglyMeasurable
    (Eventually.of_forall (norm_cubeOutwardNormal_le_one hR))

theorem classical_gauss_green_cube {R : ℝ} (hR : 0 < R)
    {Z : AmbientSpace → AmbientSpace} (hZ : ContDiff ℝ 1 Z) :
    (∫ x in coordinateCube 3 R, divergenceN Z x) =
      ∫ x, inner ℝ (Z x) (cubeOutwardNormal R x)
        ∂(hausdorffMeasure2 3).restrict (frontier (coordinateCube 3 R)) := by
  rw [integral_cube_boundary_eq_faces hR (integrable_cube_boundary_flux hR hZ.continuous)]
  simp_rw [integral_cube_face_flux hR]
  rw [integral_divergence_cube_eq_face_integrals hR hZ, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp [integral_neg, sub_eq_add_neg]

theorem classical_directional_gauss_green_cube {R : ℝ} (hR : 0 < R)
    {φ : AmbientSpace → ℝ} (hφ : ContDiff ℝ 1 φ) (v : AmbientSpace) :
    (∫ x in coordinateCube 3 R, fderiv ℝ φ x v) =
      ∫ x, φ x * inner ℝ v (cubeOutwardNormal R x)
        ∂(hausdorffMeasure2 3).restrict (frontier (coordinateCube 3 R)) := by
  have hdiv (x : AmbientSpace) : divergenceN (fun y => φ y • v) x =
      fderiv ℝ φ x v := by
    rw [divergenceN_smul hφ contDiff_const]
    simp [divergenceN, inner_gradient_left]
  simpa only [hdiv, real_inner_smul_left] using
    classical_gauss_green_cube (Z := fun y => φ y • v) hR
      (hφ.smul (contDiff_const (c := v)))

end LiquidDrop
