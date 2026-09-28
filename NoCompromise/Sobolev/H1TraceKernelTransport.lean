import NoCompromise.Sobolev.H1TraceKernelOperators
import NoCompromise.Sobolev.H1TraceKernelApprox
import NoCompromise.Sobolev.H1TraceChart

/-!
# Interior approximation transported through Lipschitz charts

Strong H¹ approximations with compact interior support remain valid after a
bi-Lipschitz change of coordinates, even when the transformed functions are
not smooth. Interior mollification supplies the defining smooth tests.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

theorem HasH1GradientOn.mem_h1Zero_of_homeomorph_approximation {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (e : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
    {C K : ℝ≥0} (he : LipschitzWith C e) (hi : LipschitzWith K e.symm)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G univ)
    {v : ℕ → EuclideanSpace ℝ (Fin n) → ℝ}
    {H : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hv : ∀ j, HasH1GradientOn (v j) (H j) univ)
    (hcv : ∀ j, HasCompactSupport (v j)) (hsv : ∀ j, tsupport (v j) ⊆ e ⁻¹' D)
    (hconv : Tendsto (fun j => H1Space.ofFunction (v j) (H j) (hv j)) atTop
      (𝓝 (H1Space.ofFunction f G hf))) :
    H1Space.ofFunction (f ∘ e.symm)
      (fun x => (fderiv ℝ e.symm x).adjoint (G (e.symm x)))
      ((hf.comp_homeomorph e.symm hi he).1.mono (subset_univ D)) ∈ h1ZeroSubmodule hD := by
  let A := (H1Space.restrictionCLM isOpen_univ hD (subset_univ D)).comp
    (H1Space.chartPullbackCLM e.symm hi he)
  have ht := (A.continuous.tendsto _).comp hconv
  have hA (g : EuclideanSpace ℝ (Fin n) → ℝ)
      (J : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (hg : HasH1GradientOn g J univ) :
      A (H1Space.ofFunction g J hg) = H1Space.ofFunction (g ∘ e.symm)
        (fun x => (fderiv ℝ e.symm x).adjoint (J (e.symm x)))
        ((hg.comp_homeomorph e.symm hi he).1.mono (subset_univ D)) := by
    dsimp only [A, ContinuousLinearMap.comp_apply]
    rw [H1Space.chartPullbackCLM_ofFunction e.symm hi he hg,
      H1Space.restrictionCLM_ofFunction]
  simp only [Function.comp_def, hA] at ht
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto ht
  apply Eventually.of_forall
  intro j
  apply (hv j |>.comp_homeomorph e.symm hi he).1.mem_h1Zero_of_compact_support hD
    ((hcv j).comp_homeomorph e.symm)
  intro x hx
  have hpre := tsupport_comp_subset_preimage (v j) e.symm.continuous hx
  have h := hsv j hpre
  simpa only [mem_preimage, e.apply_symm_apply] using h

theorem HasH1GradientOn.mem_h1Zero_of_translated_homeomorph {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (e : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
    {C K : ℝ≥0} (he : LipschitzWith C e) (hi : LipschitzWith K e.symm)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G univ) (hcf : HasCompactSupport f)
    {a : ℕ → EuclideanSpace ℝ (Fin n)} (ha : Tendsto a atTop (𝓝 0))
    (hs : ∀ j, tsupport (fun x => f (x - a j)) ⊆ e ⁻¹' D) :
    H1Space.ofFunction (f ∘ e.symm)
      (fun x => (fderiv ℝ e.symm x).adjoint (G (e.symm x)))
      ((hf.comp_homeomorph e.symm hi he).1.mono (subset_univ D)) ∈ h1ZeroSubmodule hD := by
  have hv (j : ℕ) : HasH1GradientOn (fun x => f (x - a j)) (fun x => G (x - a j)) univ := by
    simpa only [sub_eq_add_neg] using
      hf.translate isOpen_univ isOpen_univ (-a j) (fun _ _ => mem_univ _)
  have hmf : MemLp f 2 volume := by simpa only [Measure.restrict_univ] using hf.memLp_function
  have hmG : MemLp G 2 volume := by simpa only [Measure.restrict_univ] using hf.memLp_gradient
  apply hf.mem_h1Zero_of_homeomorph_approximation hD e he hi hv
    (fun j => hcf.comp_homeomorph (Homeomorph.subRight (a j))) hs
  exact H1Space.tendsto_ofFunction_restrict isOpen_univ hf hv
    (tendsto_lpNorm_sub_of_eLpNorm
      (fun j => hmf.comp_measurePreserving (measurePreserving_sub_right volume (a j))) hmf
      ((tendsto_eLpNorm_translate_sub_zero (by norm_num) hmf).comp ha))
    (tendsto_lpNorm_sub_of_eLpNorm
      (fun j => hmG.comp_measurePreserving (measurePreserving_sub_right volume (a j))) hmG
      ((tendsto_eLpNorm_translate_sub_zero (by norm_num) hmG).comp ha))

end LiquidDrop
