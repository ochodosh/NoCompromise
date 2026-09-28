import NoCompromise.Elliptic.HarmonicMeanValue
import NoCompromise.BV.StrictApprox

/-!
# Classical harmonic functions are smooth

A function of class `C²` on an open set `U ⊆ ℝⁿ`, `n ≤ 3`, with vanishing pointwise Laplacian
there, satisfies the distributional equation `Δu = 0` on `U` (Green's second identity after a
cutoff equal to one near the support of the test function), hence is `C^∞` on `U` by the
mean-value regularity `HasDistributionalLaplacianOn.contDiffOn_of_continuous`.

In chapter 31 this is the supporting fact that the capacitary potential, harmonic off `K`, is
smooth near its levels (`lem:K-gauss-bonnet-input`, `lem:K-slab-H`, `lem:K-slab-F`).
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace LiquidDrop

/-- The classical harmonic equation on an open set gives the distributional one. -/
theorem hasDistributionalLaplacianOn_zero_of_contDiffOn {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (hh : ∀ x ∈ U, laplacianN u x = 0) :
    HasDistributionalLaplacianOn u (fun _ => 0) U := by
  refine ⟨hu.continuousOn.locallyIntegrableOn hU.measurableSet,
    continuous_const.locallyIntegrable.locallyIntegrableOn U, ?_⟩
  intro φ hφ hcφ hsφ
  obtain ⟨η, hη, _, hsη, hone, _⟩ := exists_smooth_cutoff_one_near_compact hcφ hU hsφ
  let v : EuclideanSpace ℝ (Fin n) → ℝ := fun x => η x * u x
  have hv : ContDiff ℝ 2 v := sobolevChain_contDiff_cutoff hU hu (hη.of_le (by simp)) hsη
  have hnear (x) (hx : x ∈ tsupport φ) : v =ᶠ[𝓝 x] u := by
    filter_upwards [hone.filter_mono (nhds_le_nhdsSet hx)] with y hy
    simp only [v, hy, one_mul]
  have he : (∫ x in U, u x * laplacianN φ x) = ∫ x, v x * laplacianN φ x := by
    calc (∫ x in U, u x * laplacianN φ x) = ∫ x in U, v x * laplacianN φ x := by
          apply setIntegral_congr_fun hU.measurableSet
          intro x _
          by_cases hx : x ∈ tsupport φ
          · simp only [(hnear x hx).self_of_nhds]
          · have hz : laplacianN φ x = 0 := image_eq_zero_of_notMem_tsupport
              (fun ht => hx (tsupport_laplacianN_subset φ ht))
            simp only [hz, mul_zero]
      _ = ∫ x, v x * laplacianN φ x := by
          apply setIntegral_eq_integral_of_forall_compl_eq_zero
          intro x hx
          have hz : laplacianN φ x = 0 := image_eq_zero_of_notMem_tsupport
            (fun ht => hx (hsφ (tsupport_laplacianN_subset φ ht)))
          simp only [hz, mul_zero]
  rw [he, sobolevChain_integral_laplacianN_comm hv hφ hcφ]
  simp only [zero_mul, integral_zero]
  apply integral_eq_zero_of_ae
  filter_upwards [] with x
  change φ x * laplacianN v x = 0
  by_cases hx : x ∈ tsupport φ
  · rw [laplacianN_congr_nhds (hnear x hx), hh x (hsφ hx), mul_zero]
  · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]

/-- A `C²` function with vanishing Laplacian on an open subset of `ℝⁿ`, `n ≤ 3`, is smooth. -/
theorem contDiffOn_top_of_harmonic {n : ℕ} (hn : n < 4)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (hh : ∀ x ∈ U, laplacianN u x = 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) u U :=
  (hasDistributionalLaplacianOn_zero_of_contDiffOn hU hu hh).contDiffOn_of_continuous hn hU
    hu.continuousOn

end LiquidDrop
