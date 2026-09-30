module

public import NoCompromise.Elliptic.NewtonianKernel

@[expose] public section

/-!
# Linear operations on distributional Poisson equations

The singular Newtonian identity also gives actual harmonicity of the reciprocal
distance kernel on every domain avoiding its center.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma HasDistributionalLaplacianOn.integrable_test_function {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {u f φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (h : HasDistributionalLaplacianOn u f U) (hφ : ContDiff ℝ 2 φ)
    (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ U) :
    Integrable (fun x => u x * laplacianN φ x) := by
  simpa only [mul_comm] using integrable_mul_compact_factor h.locallyIntegrable_function
    (continuous_laplacianN hφ)
    (hcφ.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacianN_subset φ))
    ((tsupport_laplacianN_subset φ).trans hsφ)

theorem HasDistributionalLaplacianOn.add {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {u v f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (h : HasDistributionalLaplacianOn u f U) (hv : HasDistributionalLaplacianOn v g U) :
    HasDistributionalLaplacianOn (fun x => u x + v x) (fun x => f x + g x) U := by
  refine ⟨h.locallyIntegrable_function.add hv.locallyIntegrable_function,
    h.locallyIntegrable_source.add hv.locallyIntegrable_source, ?_⟩
  intro φ hφ hcφ hsφ
  have hiu := h.integrable_test_function (hφ.of_le (by simp)) hcφ hsφ
  have hiv := hv.integrable_test_function (hφ.of_le (by simp)) hcφ hsφ
  have hif : Integrable (fun x => f x * φ x) := by
    simpa only [mul_comm] using integrable_mul_compact_factor h.locallyIntegrable_source
      hφ.continuous hcφ hsφ
  have hig : Integrable (fun x => g x * φ x) := by
    simpa only [mul_comm] using integrable_mul_compact_factor hv.locallyIntegrable_source
      hφ.continuous hcφ hsφ
  simp_rw [add_mul]
  rw [integral_add hiu.integrableOn hiv.integrableOn,
    integral_add hif.integrableOn hig.integrableOn,
    h.test_eq φ hφ hcφ hsφ, hv.test_eq φ hφ hcφ hsφ]

theorem HasDistributionalLaplacianOn.const_mul {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {u f : EuclideanSpace ℝ (Fin n) → ℝ}
    (h : HasDistributionalLaplacianOn u f U) (a : ℝ) :
    HasDistributionalLaplacianOn (fun x => a * u x) (fun x => a * f x) U := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Pi.smul_def, smul_eq_mul] using h.locallyIntegrable_function.smul a
  · simpa only [Pi.smul_def, smul_eq_mul] using h.locallyIntegrable_source.smul a
  · intro φ hφ hcφ hsφ
    simp_rw [mul_assoc]
    rw [integral_const_mul, integral_const_mul, h.test_eq φ hφ hcφ hsφ]

theorem HasDistributionalLaplacianOn.sub {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {u v f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (h : HasDistributionalLaplacianOn u f U) (hv : HasDistributionalLaplacianOn v g U) :
    HasDistributionalLaplacianOn (fun x => u x - v x) (fun x => f x - g x) U := by
  simpa only [neg_one_mul, ← sub_eq_add_neg] using h.add (hv.const_mul (-1))

theorem hasDistributionalLaplacianOn_const {n : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin n))) (a : ℝ) :
    HasDistributionalLaplacianOn (fun _ => a) (fun _ => 0) U := by
  refine ⟨locallyIntegrableOn_const a, locallyIntegrableOn_const 0, ?_⟩
  intro φ hφ hcφ hsφ
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport
      (fun ht => hx (hsφ (tsupport_laplacianN_subset φ ht))), mul_zero])]
  rw [integral_newtonian_laplacian_comm contDiff_const (hφ.of_le (by simp)) hcφ]
  have hd (i : Fin n) : poissonCoordinateDerivative i (fun _ => a) =
      fun _ : EuclideanSpace ℝ (Fin n) => 0 := by
    funext x
    simp [poissonCoordinateDerivative]
  simp [laplacianN, hd, poissonCoordinateDerivative]

lemma locallyIntegrable_newtonKernel_sub (q : EuclideanSpace ℝ (Fin 3)) :
    LocallyIntegrable (fun x => ‖x - q‖⁻¹) := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  simpa only [norm_sub_rev] using integrableOn_coulombKernel K hK.measure_lt_top q

theorem hasDistributionalLaplacianOn_newtonKernel_away
    (q : EuclideanSpace ℝ (Fin 3)) {U : Set (EuclideanSpace ℝ (Fin 3))} (hq : q ∉ U) :
    HasDistributionalLaplacianOn (fun x => ‖x - q‖⁻¹) (fun _ => 0) U := by
  refine ⟨(locallyIntegrable_newtonKernel_sub q).locallyIntegrableOn U,
    locallyIntegrableOn_const 0, ?_⟩
  intro φ hφ hcφ hsφ
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport
      (fun ht => hx (hsφ (tsupport_laplacianN_subset φ ht))), mul_zero]),
    integral_newtonKernel_sub_mul_laplacianN hφ hcφ q]
  have hφq : φ q = 0 := image_eq_zero_of_notMem_tsupport (fun h => hq (hsφ h))
  simp only [hφq, mul_zero, neg_zero, zero_mul, integral_zero]

end LiquidDrop
