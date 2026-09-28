import NoCompromise.Elliptic.HarmonicDerivativeSobolev
import NoCompromise.Elliptic.HarmonicMeanValueLocal

/-! Ball-center independent harmonic derivative estimates, obtained by translating
the quantitative interior Sobolev estimates to the origin. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma poissonCoordinateDerivative_comp_add_left {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (z : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    poissonCoordinateDerivative i (fun x => u (z + x)) =
      fun x => poissonCoordinateDerivative i u (z + x) := by
  funext x
  simp only [poissonCoordinateDerivative, fderiv_comp_add_left]

lemma laplacianN_comp_add_left {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (z : EuclideanSpace ℝ (Fin n)) (x) :
    laplacianN (fun y => u (z + y)) x = laplacianN u (z + x) := by
  simp only [laplacianN, poissonCoordinateDerivative_comp_add_left]

lemma measurePreserving_add_left_ball {n : ℕ} (z : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    MeasurePreserving (fun x => z + x)
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin n)) r)) (volume.restrict (ball z r)) := by
  have he : (fun x => z + x) ⁻¹' ball z r = ball (0 : EuclideanSpace ℝ (Fin n)) r := by
    ext x
    simp only [mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero]
  have h := (measurePreserving_add_left volume z).restrict_preimage
    (s := ball z r) measurableSet_ball
  rwa [he] at h

lemma lpNorm_comp_add_left_ball {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (z : EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (hu : MemLp u 2 (volume.restrict (ball z r))) :
    lpNorm (fun x => u (z + x)) 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin n)) r)) =
      lpNorm u 2 (volume.restrict (ball z r)) := by
  have hm := measurePreserving_add_left_ball z r
  have hmc : AEStronglyMeasurable (fun x => u (z + x))
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin n)) r)) :=
    (hu.comp_measurePreserving hm).aestronglyMeasurable
  rw [← toReal_eLpNorm, ← toReal_eLpNorm]
  exact congrArg ENNReal.toReal (eLpNorm_comp_measurePreserving hu.aestronglyMeasurable hm)

/-- The classical harmonic equation gives the actual distributional equation
on each open region; only the test function has compact support. -/
lemma hasDistributionalLaplacianOn_zero_of_contDiff {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {U : Set (EuclideanSpace ℝ (Fin n))} (_hU : IsOpen U)
    (hh : ∀ x ∈ U, laplacianN u x = 0) :
    HasDistributionalLaplacianOn u (fun _ => 0) U := by
  refine ⟨hu.continuous.locallyIntegrable.locallyIntegrableOn U,
    continuous_const.locallyIntegrable.locallyIntegrableOn U, ?_⟩
  intro φ hφ hcφ hsφ
  have he : (∫ x in U, u x * laplacianN φ x) = ∫ x, u x * laplacianN φ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport
      (show x ∉ tsupport (laplacianN φ) from fun ht => hx (hsφ (tsupport_laplacianN_subset φ ht))),
      mul_zero]
  rw [he, sobolevChain_integral_laplacianN_comm (hu.of_le (by simp)) hφ hcφ]
  simp only [zero_mul, integral_zero]
  apply integral_eq_zero_of_ae
  filter_upwards [] with x
  change φ x * laplacianN u x = 0
  by_cases hx : x ∈ U
  · simp only [hh x hx, mul_zero]
  · rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hsφ ht)), zero_mul]

/-- Harmonic derivative constants are independent of the center of the ball.
The function need only be smooth on the open outer ball. -/
theorem harmonic_derivative_l2_bound {n k : ℕ} (hn : n < 4)
    {r R : ℝ} (hrR : r < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : EuclideanSpace ℝ (Fin n))
      (u : EuclideanSpace ℝ (Fin n) → ℝ),
      HasDistributionalLaplacianOn u (fun _ => 0) (ball z R) →
      MemLp u 2 (volume.restrict (ball z R)) → ContDiffOn ℝ (⊤ : ℕ∞) u (ball z R) →
      ∀ j ≤ k, ∀ x ∈ ball z r,
        ‖iteratedFDeriv ℝ j u x‖ ≤ C * lpNorm u 2 (volume.restrict (ball z R)) := by
  let s := (r + R) / 2
  have hrs : r < s := by dsimp [s]; linarith
  have hsR : s < R := by dsimp [s]; linarith
  obtain ⟨C, hC, hb⟩ := interior_harmonic_classical_derivative_bound (k := k) hn 0 hrs
  refine ⟨C, hC, fun z u h hu hc j hj x hx => ?_⟩
  obtain ⟨w, hw, he⟩ := exists_global_contDiff_eq_near_compact isOpen_ball
    (isCompact_closedBall z s) (closedBall_subset_ball hsR) hc
  have hae : w =ᵐ[volume.restrict (ball z s)] u := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    exact (he y (ball_subset_closedBall hy)).self_of_nhds
  have huS := hu.mono_measure (Measure.restrict_mono (ball_subset_ball hsR.le) le_rfl)
  have hwS := huS.ae_eq hae.symm
  have hws := (h.mono (ball_subset_ball hsR.le)).congr_ae hae.symm EventuallyEq.rfl
  have hwlap := hws.laplacianN_eq_zero isOpen_ball (hw.of_le (by simp))
  let v := fun y => w (z + y)
  have hv : ContDiff ℝ (⊤ : ℕ∞) v := hw.comp (contDiff_const.add contDiff_id)
  have hvH : HasDistributionalLaplacianOn v (fun _ => 0) (ball 0 s) :=
    hasDistributionalLaplacianOn_zero_of_contDiff hv isOpen_ball (by
      intro y hy
      rw [show laplacianN v y = laplacianN w (z + y) from laplacianN_comp_add_left w z y]
      exact hwlap (by simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hy))
  have hvL : MemLp v 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin n)) s)) :=
    hwS.comp_measurePreserving (measurePreserving_add_left_ball z s)
  have hxb : x - z ∈ ball (0 : EuclideanSpace ℝ (Fin n)) r := by
    simpa only [mem_ball, dist_eq_norm, sub_zero] using hx
  have hbx := hb v v hvH hvL (hv.of_le (by simp)) EventuallyEq.rfl j hj (x - z) hxb
  have hdx : iteratedFDeriv ℝ j v (x - z) = iteratedFDeriv ℝ j u x := by
    rw [show iteratedFDeriv ℝ j v (x - z) = iteratedFDeriv ℝ j w (z + (x - z)) from
      iteratedFDeriv_comp_add_left j z (x - z)]
    rw [show z + (x - z) = x by abel]
    have ht := (he x (ball_subset_closedBall ((ball_subset_ball hrs.le) hx))).iteratedFDeriv ℝ j
    exact ht.self_of_nhds
  rw [hdx, show lpNorm v 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin n)) s)) =
    lpNorm w 2 (volume.restrict (ball z s)) from lpNorm_comp_add_left_ball z s hwS] at hbx
  have heNorm : lpNorm w 2 (volume.restrict (ball z s)) = lpNorm u 2 (volume.restrict (ball z s)) :=
    by
      rw [← toReal_eLpNorm, ← toReal_eLpNorm, eLpNorm_congr_ae hae]
  rw [heNorm] at hbx
  exact hbx.trans (mul_le_mul_of_nonneg_left
    (poisson_lpNorm_mono_measure hu (Measure.restrict_mono (ball_subset_ball hsR.le) le_rfl)) hC.le)

end LiquidDrop
