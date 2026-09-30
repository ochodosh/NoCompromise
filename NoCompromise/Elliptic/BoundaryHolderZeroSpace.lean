module

public import NoCompromise.Elliptic.BoundaryHolderTraceContinuous
public import NoCompromise.Sobolev.H1PositivePartTests

@[expose] public section

/-!
# Genuine H¹₀ corrections preserve the flat Dirichlet trace

Smooth interior approximations converge in the actual H¹ space. The proved
localized trace continuity passes their zero classical restrictions to the
specified weak representative.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Membership in the actual H¹₀ closure implies the actual localized zero flat
trace on the upper part of any open neighborhood. -/
theorem HasH1GradientOn.hasZeroFlatTraceOn_of_mem_h1Zero {k : ℕ}
    {W : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hW : IsOpen W)
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : HasH1GradientOn f G (W ∩ {x | 0 < x (Fin.last k)}))
    (hz : H1Space.ofFunction f G hf ∈ h1ZeroSubmodule
      (hW.inter boundary_holder_open_upper)) : HasZeroFlatTraceOn f G W := by
  let D := W ∩ {x : EuclideanSpace ℝ (Fin (k + 1)) | 0 < x (Fin.last k)}
  have hD : IsOpen D := hW.inter boundary_holder_open_upper
  let u : H1ZeroSpace hD := ⟨H1Space.ofFunction f G hf, hz⟩
  obtain ⟨p, hp⟩ := H1ZeroSpace.exists_smooth_interior_approximation hD u
  have hpH (j : ℕ) : HasH1GradientOn (p j) (gradient (p j).val) D :=
    h1ZeroTestFunctions.hasH1GradientOn (p j) hD
  have hpf : Tendsto (fun j => (hpH j).memLp_function.toLp (p j)) atTop
      (𝓝 (hf.memLp_function.toLp f)) :=
    (H1Space.toLpCLM.continuous.tendsto u.val).comp hp
  have hpG : Tendsto (fun j => (hpH j).memLp_gradient.toLp (gradient (p j).val)) atTop
      (𝓝 (hf.memLp_gradient.toLp G)) :=
    (H1Space.gradientCLM.continuous.tendsto u.val).comp hp
  have hcf : Tendsto (fun j => lpNorm (fun x => (p j).val x - f x) 2 (volume.restrict D))
      atTop (𝓝 0) := tendsto_lpNorm_sub_of_eLpNorm (fun j => (hpH j).memLp_function)
    hf.memLp_function ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun j => (p j).val)
      (fun j => (hpH j).memLp_function) f hf.memLp_function).mp hpf)
  have hcG : Tendsto (fun j => lpNorm (fun x => gradient (p j).val x - G x) 2 (volume.restrict D))
      atTop (𝓝 0) := tendsto_lpNorm_sub_of_eLpNorm (fun j => (hpH j).memLp_gradient)
    hf.memLp_gradient ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun j => gradient (p j).val)
      (fun j => (hpH j).memLp_gradient) G hf.memLp_gradient).mp hpG)
  have hTp (j : ℕ) : HasZeroFlatTraceOn (p j) (gradient (p j).val) W := by
    apply hasZeroFlatTraceOn_of_contDiff ((p j).property.1.of_le (by simp))
    intro x _
    apply image_eq_zero_of_notMem_tsupport
    intro hx
    have hh := ((p j).property.2.2 hx).2
    change 0 < (graphAppendN x 0) (Fin.last k) at hh
    simp only [graphAppendN_last, lt_self_iff_false] at hh
  intro ζ hζ hcζ hsζ
  have hζ1 : ContDiff ℝ 1 ζ := hζ.of_le (by simp)
  obtain ⟨hmf, hmG⟩ := boundary_cutoff_memLp_upper hW.measurableSet hf.memLp_function
    hf.memLp_gradient hζ1 hcζ hsζ
  have hm : MemLp (boundaryLocalizedFlatTrace f G ζ) 2 volume :=
    (memLp_flatTraceFunction hmf hmG).1.ae_eq (boundaryLocalizedFlatTrace_indicator f ζ G).symm
  have ht := tendsto_boundaryLocalizedFlatTrace hW.measurableSet hf hpH hζ1 hcζ hsζ hcf hcG
  have heq (j : ℕ) : lpNorm (boundaryLocalizedFlatTrace (p j) (gradient (p j).val) ζ -
      boundaryLocalizedFlatTrace f G ζ) 2 volume = lpNorm (boundaryLocalizedFlatTrace f G ζ)
        2 volume := by
    have he : boundaryLocalizedFlatTrace (p j) (gradient (p j).val) ζ -
        boundaryLocalizedFlatTrace f G ζ =ᵐ[volume] -boundaryLocalizedFlatTrace f G ζ := by
      filter_upwards [hTp j ζ hζ hcζ hsζ] with x hx
      simp only [Pi.sub_apply, Pi.neg_apply, hx, Pi.zero_apply, zero_sub]
    have hmd := hm.neg.ae_eq he.symm
    rw [← toReal_eLpNorm, ← toReal_eLpNorm, eLpNorm_congr_ae he, eLpNorm_neg]
  have hnorm : lpNorm (boundaryLocalizedFlatTrace f G ζ) 2 volume = 0 :=
    tendsto_nhds_unique tendsto_const_nhds (ht.congr (fun j => heq j))
  exact (lpNorm_eq_zero hm (by norm_num)).mp hnorm

end LiquidDrop
