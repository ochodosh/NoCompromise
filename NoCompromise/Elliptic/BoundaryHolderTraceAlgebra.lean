module

public import NoCompromise.Elliptic.BoundaryHolderTrace
public import NoCompromise.Elliptic.FrozenDecayAffine

@[expose] public section

/-!
# Linearity of the localized flat trace

All trace subtractions are justified by actual L² upper-domain data. In
particular subtracting a normal affine function preserves the zero flat trace.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma boundary_cutoff_memLp_upper {k : ℕ}
    {W : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hW : MeasurableSet W)
    {f ζ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : MemLp f 2 (volume.restrict (W ∩ {x | 0 < x (Fin.last k)})))
    (hG : MemLp G 2 (volume.restrict (W ∩ {x | 0 < x (Fin.last k)})))
    (hζ : ContDiff ℝ 1 ζ) (hcζ : HasCompactSupport ζ) (hsζ : tsupport ζ ⊆ W) :
    MemLp ({x | 0 < x (Fin.last k)}.indicator (fun x => ζ x * f x)) 2 volume ∧
    MemLp ({x | 0 < x (Fin.last k)}.indicator
      (fun x => ζ x • G x + f x • gradient ζ x)) 2 volume := by
  let U := {x : EuclideanSpace ℝ (Fin (k + 1)) | 0 < x (Fin.last k)}
  let D := W ∩ U
  have hU : MeasurableSet U := boundary_holder_open_upper.measurableSet
  have hD : MeasurableSet D := hW.inter hU
  have hmf : MemLp (D.indicator f) 2 volume := (memLp_indicator_iff_restrict hD).mpr hf
  have hmG : MemLp (D.indicator G) 2 volume := (memLp_indicator_iff_restrict hD).mpr hG
  obtain ⟨B, hB⟩ := hcζ.exists_bound_of_continuous hζ.continuous
  have hcgrad : HasCompactSupport (gradient ζ) :=
    hcζ.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset ζ)
  have hgrad := continuous_gradient_of_contDiff hζ
  obtain ⟨C, hC⟩ := hcgrad.exists_bound_of_continuous hgrad
  have hmul : MemLp (fun x => ζ x * D.indicator f x) 2 volume :=
    hmf.of_le_mul (c := B) (hζ.continuous.aestronglyMeasurable.mul hmf.aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _))
  have hsmul : MemLp (fun x => ζ x • D.indicator G x) 2 volume :=
    hmG.of_le_mul (c := B) (hζ.continuous.aestronglyMeasurable.smul hmG.aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _))
  have hgradmul : MemLp (fun x => D.indicator f x • gradient ζ x) 2 volume :=
    hmf.of_le_mul (c := C) (hmf.aestronglyMeasurable.smul hgrad.aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        rw [norm_smul, mul_comm C]
        exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _))
  have hz (x) (hx : x ∉ W) : ζ x = 0 ∧ gradient ζ x = 0 :=
    ⟨image_eq_zero_of_notMem_tsupport (fun ht => hx (hsζ ht)),
      gradient_eq_zero_of_notMem_tsupport (fun ht => hx (hsζ ht))⟩
  have hef : U.indicator (fun x => ζ x * f x) = fun x => ζ x * D.indicator f x := by
    funext x
    by_cases hxU : x ∈ U <;> by_cases hxW : x ∈ W
    · simp [D, hxU, hxW]
    · simp [D, hxU, hxW, (hz x hxW).1]
    · simp [D, hxU, hxW]
    · simp [D, hxU, hxW]
  have heG : U.indicator (fun x => ζ x • G x + f x • gradient ζ x) =
      fun x => ζ x • D.indicator G x + D.indicator f x • gradient ζ x := by
    funext x
    by_cases hxU : x ∈ U <;> by_cases hxW : x ∈ W
    · simp [D, hxU, hxW]
    · simp [D, hxU, hxW, (hz x hxW).1, (hz x hxW).2]
    · simp [D, hxU, hxW]
    · simp [D, hxU, hxW]
  exact ⟨hef ▸ hmul, heG ▸ hsmul.add hgradmul⟩

lemma boundaryLocalizedFlatTrace_indicator {k : ℕ}
    (f ζ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))) :
    boundaryLocalizedFlatTrace f G ζ =ᵐ[volume]
      flatTraceFunction ({x | 0 < x (Fin.last k)}.indicator (fun x => ζ x * f x))
        ({x | 0 < x (Fin.last k)}.indicator (fun x => ζ x • G x + f x • gradient ζ x)) := by
  apply flatTraceFunction_congr_ae_on_slab
  · filter_upwards [ae_restrict_mem (measurableSet_flatTraceSlab k)] with x hx
    simp only [indicator_apply, mem_ofPred_eq, hx.1, ↓reduceIte]
  · filter_upwards [ae_restrict_mem (measurableSet_flatTraceSlab k)] with x hx
    simp only [indicator_apply, mem_ofPred_eq, hx.1, ↓reduceIte]

lemma boundaryLocalizedFlatTrace_sub_ae {k : ℕ}
    {W : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hW : MeasurableSet W)
    {f g ζ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G H : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : HasH1GradientOn f G (W ∩ {x | 0 < x (Fin.last k)}))
    (hg : HasH1GradientOn g H (W ∩ {x | 0 < x (Fin.last k)}))
    (hζ : ContDiff ℝ 1 ζ) (hcζ : HasCompactSupport ζ) (hsζ : tsupport ζ ⊆ W) :
    boundaryLocalizedFlatTrace (f - g) (G - H) ζ =ᵐ[volume]
      boundaryLocalizedFlatTrace f G ζ - boundaryLocalizedFlatTrace g H ζ := by
  let U := {x : EuclideanSpace ℝ (Fin (k + 1)) | 0 < x (Fin.last k)}
  obtain ⟨hmf, hmG⟩ := boundary_cutoff_memLp_upper hW hf.memLp_function hf.memLp_gradient hζ hcζ hsζ
  obtain ⟨hmg, hmH⟩ := boundary_cutoff_memLp_upper hW hg.memLp_function hg.memLp_gradient hζ hcζ hsζ
  have heF : U.indicator (fun x => ζ x * (f - g) x) =
      U.indicator (fun x => ζ x * f x) - U.indicator (fun x => ζ x * g x) := by
    funext x
    by_cases hx : x ∈ U <;> simp [hx, mul_sub]
  have heG : U.indicator (fun x => ζ x • (G - H) x + (f - g) x • gradient ζ x) =
      U.indicator (fun x => ζ x • G x + f x • gradient ζ x) -
        U.indicator (fun x => ζ x • H x + g x • gradient ζ x) := by
    funext x
    by_cases hx : x ∈ U
    · simp only [indicator_of_mem hx, Pi.sub_apply]
      module
    · simp [hx]
  have he := (boundaryLocalizedFlatTrace_indicator (f - g) ζ (G - H))
  rw [heF, heG] at he
  exact he.trans ((flatTraceFunction_sub_ae hmf hmG hmg hmH).trans
    ((boundaryLocalizedFlatTrace_indicator f ζ G).symm.sub
      (boundaryLocalizedFlatTrace_indicator g ζ H).symm))

lemma HasZeroFlatTraceOn.sub {k : ℕ}
    {W : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hW : MeasurableSet W)
    {f g : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G H : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : HasH1GradientOn f G (W ∩ {x | 0 < x (Fin.last k)}))
    (hg : HasH1GradientOn g H (W ∩ {x | 0 < x (Fin.last k)}))
    (hTf : HasZeroFlatTraceOn f G W) (hTg : HasZeroFlatTraceOn g H W) :
    HasZeroFlatTraceOn (f - g) (G - H) W := by
  intro ζ hζ hcζ hsζ
  have he := boundaryLocalizedFlatTrace_sub_ae hW hf hg (hζ.of_le (by simp)) hcζ hsζ
  filter_upwards [he, hTf ζ hζ hcζ hsζ, hTg ζ hζ hcζ hsζ] with x hx hy hz
  simpa only [Pi.sub_apply, hy, hz, Pi.zero_apply, sub_self] using hx

lemma hasZeroFlatTraceOn_normal_affine {k : ℕ} (c : ℝ)
    (W : Set (EuclideanSpace ℝ (Fin (k + 1)))) :
    HasZeroFlatTraceOn
      (fun x => inner ℝ (c • EuclideanSpace.single (Fin.last k) (1 : ℝ)) x)
      (fun _ => c • EuclideanSpace.single (Fin.last k) (1 : ℝ)) W := by
  have he : gradient (fun x => inner ℝ (c • EuclideanSpace.single (Fin.last k) (1 : ℝ)) x) =
      fun _ => c • EuclideanSpace.single (Fin.last k) (1 : ℝ) :=
    funext (frozen_gradient_inner _)
  rw [← he]
  apply hasZeroFlatTraceOn_of_contDiff (innerSL ℝ _).contDiff
  intro x _
  change inner ℝ (c • EuclideanSpace.single (Fin.last k) (1 : ℝ)) (graphAppendN x 0) = 0
  simp only [real_inner_smul_left, EuclideanSpace.inner_single_left, graphAppendN_last,
    mul_zero]

lemma HasZeroFlatTraceOn.sub_normal_affine {k : ℕ}
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : HasH1GradientOn f G (ball 0 1 ∩ {x | 0 < x (Fin.last k)}))
    (hT : HasZeroFlatTraceOn f G (ball 0 1)) (c : ℝ) :
    HasZeroFlatTraceOn
      (fun x => f x - inner ℝ (c • EuclideanSpace.single (Fin.last k) (1 : ℝ)) x)
      (fun x => G x - c • EuclideanSpace.single (Fin.last k) (1 : ℝ)) (ball 0 1) :=
  HasZeroFlatTraceOn.sub isOpen_ball.measurableSet hf
    ((frozen_hasH1GradientOn_inner_ball _).mono inter_subset_left)
    hT (hasZeroFlatTraceOn_normal_affine c _)

end LiquidDrop
