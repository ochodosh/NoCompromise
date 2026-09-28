import NoCompromise.Elliptic.SobolevChainLocal
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Smooth representatives of distributionally harmonic functions

Repeated weak elliptic regularity produces compatible classical representatives.
The distributional equation is then identified with the pointwise Laplacian.
-/

noncomputable section

open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient

namespace LiquidDrop

/-- Smoothness of a representative follows from arbitrarily high weak Sobolev order. -/
theorem interior_all_sobolev_contDiff {n : ℕ} (hn : n < 4)
    (z : EuclideanSpace ℝ (Fin n)) {r R : ℝ} (hrR : r < R)
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ∀ k, HasSobolevOrderOn k u (ball z R)) :
    ∃ w : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ (⊤ : ℕ∞) w ∧
      w =ᵐ[volume.restrict (ball z r)] u := by
  let s := (r + R) / 2
  have hrs : r < s := by dsimp [s]; linarith
  have hsR : s < R := by dsimp [s]; linarith
  obtain ⟨w, hw, hweq⟩ := interior_sobolevOrder_two_continuous hn z hsR (hu 2)
  have hcw : ContDiffOn ℝ (⊤ : ℕ∞) w (ball z s) := by
    apply contDiffOn_infty.mpr
    intro k
    obtain ⟨v, hv, hveq⟩ := interior_sobolev_contDiff hn z hsR (hu (k + 2))
    have heq := Measure.eqOn_open_of_ae_eq (hweq.trans hveq.symm) isOpen_ball
      hw.continuousOn hv.continuous.continuousOn
    exact hv.contDiffOn.congr heq
  obtain ⟨η, hη, _, hsη, hone, _⟩ := exists_smooth_cutoff_one_near_compact
    (isCompact_closedBall z r) isOpen_ball (closedBall_subset_ball hrs)
  refine ⟨fun x => η x * w x, sobolevChain_contDiff_cutoff isOpen_ball hcw hη hsη, ?_⟩
  have heq := ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hrs.le) hweq
  filter_upwards [heq, ae_restrict_mem measurableSet_ball] with x hx hxr
  have hηx : η x = 1 := (hone.filter_mono
    (nhds_le_nhdsSet (mem_closedBall.mpr (mem_ball.mp hxr).le))).self_of_nhds
  rw [hηx, one_mul, hx]

/-- The distributional Laplacian relation is independent of null changes of representatives. -/
theorem HasDistributionalLaplacianOn.congr_ae {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {u v f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (h : HasDistributionalLaplacianOn u f U)
    (huv : u =ᵐ[volume.restrict U] v) (hfg : f =ᵐ[volume.restrict U] g) :
    HasDistributionalLaplacianOn v g U := by
  refine ⟨(locallyIntegrableOn_congr huv).mp h.locallyIntegrable_function,
    (locallyIntegrableOn_congr hfg).mp h.locallyIntegrable_source, ?_⟩
  intro φ hφ hcφ hsφ
  calc
    (∫ x in U, v x * laplacianN φ x) = ∫ x in U, u x * laplacianN φ x :=
      integral_congr_ae (huv.mono fun x hx => by simp only [hx])
    _ = ∫ x in U, f x * φ x := h.test_eq φ hφ hcφ hsφ
    _ = ∫ x in U, g x * φ x := integral_congr_ae (hfg.mono fun x hx => by simp only [hx])

/-- Green's second identity against a compact smooth scalar test. -/
lemma sobolevChain_integral_laplacianN_comm {n : ℕ}
    {u φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 2 u) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcφ : HasCompactSupport φ) :
    (∫ x, u x * laplacianN φ x) = ∫ x, φ x * laplacianN u x := by
  classical
  have hdu i := ContDiff.poissonCoordinateDerivative (r := 1) hu i
  have hdφ i := poissonCoordinateDerivative_smooth hφ i
  have hcdφ i := HasCompactSupport.poissonCoordinateDerivative hcφ i
  have hddu i := ContDiff.poissonCoordinateDerivative (r := 0) (hdu i) i
  have hddφ i := poissonCoordinateDerivative_smooth (hdφ i) i
  have hi₁ i : Integrable (fun x => u x *
      poissonCoordinateDerivative i (poissonCoordinateDerivative i φ) x) :=
    (hu.continuous.mul (hddφ i).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.poissonCoordinateDerivative (hcdφ i) i).mul_left
  have hi₂ i : Integrable (fun x => φ x *
      poissonCoordinateDerivative i (poissonCoordinateDerivative i u) x) :=
    (hφ.continuous.mul (hddu i).continuous).integrable_of_hasCompactSupport hcφ.mul_right
  simp only [laplacianN, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hi₁ i), integral_finsetSum _ (fun i _ => hi₂ i)]
  apply Finset.sum_congr rfl
  intro i _
  have h₁ := integral_mul_poissonCoordinateDerivative (hu.of_le (by norm_num))
    ((hdφ i).of_le (by simp)) (hcdφ i) i
  have h₂ := integral_mul_poissonCoordinateDerivative (hdu i) (hφ.of_le (by simp)) hcφ i
  rw [h₁]
  rw [show (fun x => poissonCoordinateDerivative i φ x * poissonCoordinateDerivative i u x) =
    (fun x => poissonCoordinateDerivative i u x * poissonCoordinateDerivative i φ x) by
      ext x; exact mul_comm _ _, h₂, neg_neg]

/-- A smooth distributionally harmonic function has zero classical Laplacian pointwise. -/
theorem HasDistributionalLaplacianOn.laplacianN_eq_zero {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (h : HasDistributionalLaplacianOn u (fun _ => 0) U) (hu : ContDiff ℝ 2 u) :
    EqOn (laplacianN u) (fun _ => 0) U := by
  have hc := continuous_laplacianN hu
  have hz : ∀ᵐ x ∂volume, x ∈ U → laplacianN u x = 0 := by
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hc.locallyIntegrable.locallyIntegrableOn U)
    intro φ hφ hcφ hsφ
    change (∫ x, φ x * laplacianN u x) = 0
    rw [← sobolevChain_integral_laplacianN_comm hu hφ hcφ]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := U)
      (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport
          (fun ht => hx (hsφ ((tsupport_laplacianN_subset φ) ht))), mul_zero])]
    simpa using h.test_eq φ hφ hcφ hsφ
  exact Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hU.measurableSet).mpr hz) hU
    hc.continuousOn continuousOn_const

/-- Actual smooth harmonic representatives on smaller balls, starting only from L² and Δu=0. -/
theorem interior_harmonic_smooth {n : ℕ} (hn : n < 4)
    (z : EuclideanSpace ℝ (Fin n)) {r R : ℝ} (hrR : r < R)
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (h : HasDistributionalLaplacianOn u (fun _ => 0) (ball z R))
    (hu : MemLp u 2 (volume.restrict (ball z R))) :
    ∃ w : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ (⊤ : ℕ∞) w ∧
      w =ᵐ[volume.restrict (ball z r)] u ∧ ∀ x ∈ ball z r, laplacianN w x = 0 := by
  let s := (r + R) / 2
  have hrs : r < s := by dsimp [s]; linarith
  have hsR : s < R := by dsimp [s]; linarith
  obtain ⟨w, hw, hweq⟩ := interior_all_sobolev_contDiff hn z hrs
    (fun k => interior_harmonic_sobolev_order k z hsR h hu)
  refine ⟨w, hw, hweq, ?_⟩
  have hwlap := (h.mono (ball_subset_ball hrR.le)).congr_ae hweq.symm EventuallyEq.rfl
  exact hwlap.laplacianN_eq_zero isOpen_ball (hw.of_le (by simp))

end LiquidDrop
