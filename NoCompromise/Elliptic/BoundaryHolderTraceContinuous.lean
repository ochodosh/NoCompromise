import NoCompromise.Elliptic.BoundaryHolderTraceAlgebra
import NoCompromise.Elliptic.InteriorH2H1

/-!
# Continuity of the actual localized trace

A compact cutoff gives an L² trace bound using only H¹ data on the upper part
of its neighborhood. This is the continuity needed to pass genuine H¹₀
approximations to zero flat trace.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma boundary_lpNorm_indicator {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} {D : Set X} (hD : MeasurableSet D) {f : X → E}
    (hf : MemLp f 2 (μ.restrict D)) : lpNorm (D.indicator f) 2 μ = lpNorm f 2 (μ.restrict D) := by
  have hm := (memLp_indicator_iff_restrict hD).mpr hf
  rw [← toReal_eLpNorm, ← toReal_eLpNorm,
    eLpNorm_indicator_eq_eLpNorm_restrict hD]

lemma boundaryLocalizedFlatTrace_lpNorm_le {k : ℕ}
    {W : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hW : MeasurableSet W)
    {f ζ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : MemLp f 2 (volume.restrict (W ∩ {x | 0 < x (Fin.last k)})))
    (hG : MemLp G 2 (volume.restrict (W ∩ {x | 0 < x (Fin.last k)})))
    (hζ : ContDiff ℝ 1 ζ) (hcζ : HasCompactSupport ζ) (hsζ : tsupport ζ ⊆ W)
    {C : ℝ} (hC : 0 ≤ C) (hbζ : ∀ x, ‖ζ x‖ ≤ C) (hbg : ∀ x, ‖gradient ζ x‖ ≤ C) :
    MemLp (boundaryLocalizedFlatTrace f G ζ) 2 volume ∧
      lpNorm (boundaryLocalizedFlatTrace f G ζ) 2 volume ≤
        2 * C * (lpNorm f 2 (volume.restrict (W ∩ {x | 0 < x (Fin.last k)})) +
          lpNorm G 2 (volume.restrict (W ∩ {x | 0 < x (Fin.last k)}))) := by
  let U := {x : EuclideanSpace ℝ (Fin (k + 1)) | 0 < x (Fin.last k)}
  let D := W ∩ U
  let f₀ := U.indicator (fun x => ζ x * f x)
  let G₀ := U.indicator (fun x => ζ x • G x + f x • gradient ζ x)
  let S := fun x => ‖D.indicator f x‖ + ‖D.indicator G x‖
  have hD : MeasurableSet D := hW.inter boundary_holder_open_upper.measurableSet
  have hmf := (memLp_indicator_iff_restrict hD).mpr hf
  have hmG := (memLp_indicator_iff_restrict hD).mpr hG
  have hS : MemLp S 2 volume := hmf.norm.add hmG.norm
  obtain ⟨hmf₀, hmG₀⟩ := boundary_cutoff_memLp_upper hW hf hG hζ hcζ hsζ
  have hz (x) (hx : x ∉ W) : ζ x = 0 ∧ gradient ζ x = 0 :=
    ⟨image_eq_zero_of_notMem_tsupport (fun ht => hx (hsζ ht)),
      gradient_eq_zero_of_notMem_tsupport (fun ht => hx (hsζ ht))⟩
  have hbF (x) : ‖f₀ x‖ ≤ C * ‖S x‖ := by
    by_cases hxU : x ∈ U
    · by_cases hxW : x ∈ W
      · simp only [f₀, S, D, indicator_of_mem hxU,
          indicator_of_mem (show x ∈ W ∩ U from ⟨hxW, hxU⟩),
          Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)), norm_mul]
        nlinarith [mul_le_mul_of_nonneg_right (hbζ x) (norm_nonneg (f x)),
          mul_nonneg hC (norm_nonneg (G x))]
      · simp [f₀, S, D, hxU, hxW, (hz x hxW).1]
    · simp [f₀, S, D, hxU]
  have hbG (x) : ‖G₀ x‖ ≤ C * ‖S x‖ := by
    by_cases hxU : x ∈ U
    · by_cases hxW : x ∈ W
      · simp only [G₀, S, D, indicator_of_mem hxU,
          indicator_of_mem (show x ∈ W ∩ U from ⟨hxW, hxU⟩),
          Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
        calc
          _ ≤ ‖ζ x‖ * ‖G x‖ + ‖f x‖ * ‖gradient ζ x‖ := by
            simpa only [norm_smul] using norm_add_le (ζ x • G x) (f x • gradient ζ x)
          _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right (hbζ x) (norm_nonneg (G x)),
            mul_le_mul_of_nonneg_left (hbg x) (norm_nonneg (f x))]
      · simp [G₀, S, D, hxU, hxW, (hz x hxW).1, (hz x hxW).2]
    · simp [G₀, S, D, hxU]
  have hbS : lpNorm S 2 volume ≤ lpNorm f 2 (volume.restrict D) +
      lpNorm G 2 (volume.restrict D) := by
    calc
      _ ≤ lpNorm (fun x => ‖D.indicator f x‖) 2 volume +
          lpNorm (fun x => ‖D.indicator G x‖) 2 volume :=
        lpNorm_add_le hmf.norm (by norm_num)
      _ = _ := by
        rw [lpNorm_norm hmf.aestronglyMeasurable, lpNorm_norm hmG.aestronglyMeasurable,
          boundary_lpNorm_indicator hD hf, boundary_lpNorm_indicator hD hG]
  have ht := memLp_flatTraceFunction hmf₀ hmG₀
  have he := boundaryLocalizedFlatTrace_indicator f ζ G
  have hm := ht.1.ae_eq he.symm
  refine ⟨hm, ?_⟩
  have heq : lpNorm (boundaryLocalizedFlatTrace f G ζ) 2 volume =
      lpNorm (flatTraceFunction f₀ G₀) 2 volume := by
    rw [← toReal_eLpNorm, ← toReal_eLpNorm, eLpNorm_congr_ae he]
  rw [heq]
  calc
    _ ≤ lpNorm f₀ 2 volume + lpNorm G₀ 2 volume := ht.2
    _ ≤ C * lpNorm S 2 volume + C * lpNorm S 2 volume :=
      add_le_add (poisson_lpNorm_le_mul_of_norm_le hS hC hbF)
        (poisson_lpNorm_le_mul_of_norm_le hS hC hbG)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hbS hC]

/-- Strong H¹ convergence on the upper domain gives strong L² convergence of
its actual localized traces. -/
theorem tendsto_boundaryLocalizedFlatTrace {k : ℕ} {ι : Type*} {l : Filter ι}
    {W : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hW : MeasurableSet W)
    {f ζ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    {f' : ι → EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G' : ι → EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : HasH1GradientOn f G (W ∩ {x | 0 < x (Fin.last k)}))
    (hf' : ∀ j, HasH1GradientOn (f' j) (G' j) (W ∩ {x | 0 < x (Fin.last k)}))
    (hζ : ContDiff ℝ 1 ζ) (hcζ : HasCompactSupport ζ) (hsζ : tsupport ζ ⊆ W)
    (htf : Tendsto (fun j => lpNorm (f' j - f) 2
      (volume.restrict (W ∩ {x | 0 < x (Fin.last k)}))) l (𝓝 0))
    (htG : Tendsto (fun j => lpNorm (G' j - G) 2
      (volume.restrict (W ∩ {x | 0 < x (Fin.last k)}))) l (𝓝 0)) :
    Tendsto (fun j => lpNorm
      (boundaryLocalizedFlatTrace (f' j) (G' j) ζ - boundaryLocalizedFlatTrace f G ζ)
      2 volume) l (𝓝 0) := by
  obtain ⟨B, hB⟩ := hcζ.exists_bound_of_continuous hζ.continuous
  have hcgrad : HasCompactSupport (gradient ζ) :=
    hcζ.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset ζ)
  obtain ⟨C, hC⟩ := hcgrad.exists_bound_of_continuous (continuous_gradient_of_contDiff hζ)
  let M := max 0 (max B C)
  have hM : 0 ≤ M := le_max_left _ _
  have hBM (x) : ‖ζ x‖ ≤ M := (hB x).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hCM (x) : ‖gradient ζ x‖ ≤ M :=
    (hC x).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hbase := boundaryLocalizedFlatTrace_lpNorm_le hW hf.memLp_function
    hf.memLp_gradient hζ hcζ hsζ hM hBM hCM
  have hbound (j) : lpNorm
      (boundaryLocalizedFlatTrace (f' j) (G' j) ζ - boundaryLocalizedFlatTrace f G ζ) 2 volume ≤
      2 * M * (lpNorm (f' j - f) 2 (volume.restrict (W ∩ {x | 0 < x (Fin.last k)})) +
        lpNorm (G' j - G) 2 (volume.restrict (W ∩ {x | 0 < x (Fin.last k)}))) := by
    have hj := boundaryLocalizedFlatTrace_lpNorm_le hW (hf' j).memLp_function
      (hf' j).memLp_gradient hζ hcζ hsζ hM hBM hCM
    have hd := boundaryLocalizedFlatTrace_lpNorm_le hW ((hf' j).sub hf).memLp_function
      ((hf' j).sub hf).memLp_gradient hζ hcζ hsζ hM hBM hCM
    have he := boundaryLocalizedFlatTrace_sub_ae hW (hf' j) hf hζ hcζ hsζ
    have hnorm := congrArg ENNReal.toReal (eLpNorm_congr_ae (p := 2) he)
    have hdm : MemLp (boundaryLocalizedFlatTrace (f' j - f) (G' j - G) ζ) 2 volume := hd.1
    rw [toReal_eLpNorm, toReal_eLpNorm] at hnorm
    exact hnorm.symm.trans_le hd.2
  apply squeeze_zero (fun _ => lpNorm_nonneg) hbound
  simpa only [zero_add, mul_zero] using (htf.add htG).const_mul (2 * M)

end LiquidDrop
