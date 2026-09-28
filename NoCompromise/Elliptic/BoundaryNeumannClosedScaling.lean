import NoCompromise.Elliptic.BoundaryNeumannQuotientScaling
import NoCompromise.Elliptic.BoundaryNeumannQuotientHolder
import NoCompromise.Elliptic.NondivSchauderScalingNorm

/-!
# Rescaling closed conormal data to the unit half ball

Closed conormal data on the closed half ball of radius `r ≤ 1` become closed data on the
closed unit half ball after composing with `x ↦ r x` (flux and datum multiplied by `r`),
with the same ellipticity, coefficient bound and C¹,α norm bounds. This is the step that
lets the fixed-radius theorems (`boundary_neumann_c2_holder`) be applied at every scale.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

lemma boundary_neumann_scaling_mapsTo_halfBall {r : ℝ} (hr : 0 < r) :
    MapsTo (frozenBallScaling (0 : EuclideanSpace ℝ (Fin 3)) hr)
      (boundaryHalfBall 1) (boundaryHalfBall r) := by
  intro x hx
  refine ⟨?_, ?_⟩
  · simpa only [mul_one] using (frozenBallScaling_mem_ball_iff 0 x hr 1).mpr hx.1
  · change 0 < (0 + r • x) (Fin.last 2)
    simpa only [zero_add, PiLp.smul_apply, smul_eq_mul] using mul_pos hr hx.2

lemma boundary_neumann_scaling_mapsTo_closure {r : ℝ} (hr : 0 < r) :
    MapsTo (frozenBallScaling (0 : EuclideanSpace ℝ (Fin 3)) hr)
      (closure (boundaryHalfBall 1)) (closure (boundaryHalfBall r)) :=
  (boundary_neumann_scaling_mapsTo_halfBall hr).closure (frozenBallScaling 0 hr).continuous

lemma boundary_neumann_scaling_last {r : ℝ} (hr : 0 < r) (x : EuclideanSpace ℝ (Fin 3)) :
    frozenBallScaling (0 : EuclideanSpace ℝ (Fin 3)) hr x (Fin.last 2) =
      r * x (Fin.last 2) := by
  simp [frozenBallScaling_apply]

lemma boundary_neumann_scaling_norm_sub_le {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (x y : EuclideanSpace ℝ (Fin 3)) :
    ‖frozenBallScaling (0 : EuclideanSpace ℝ (Fin 3)) hr x - frozenBallScaling 0 hr y‖ ≤
      ‖x - y‖ := by
  have heq : ‖frozenBallScaling (0 : EuclideanSpace ℝ (Fin 3)) hr x -
      frozenBallScaling 0 hr y‖ = r * ‖x - y‖ := by
    simpa only [dist_eq_norm] using quasilinear_ballScaling_dist 0 x y hr
  rw [heq]
  exact (mul_le_mul_of_nonneg_right hr1 (norm_nonneg _)).trans_eq (one_mul _)

/-- The chain rule for the scaling holds at every point, without any differentiability
assumption (both sides vanish at non-differentiability points). -/
lemma boundary_neumann_fderiv_comp_scaling {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {r : ℝ} (hr : 0 < r)
    (f : EuclideanSpace ℝ (Fin 3) → F) (x : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (f ∘ frozenBallScaling 0 hr) x = r • fderiv ℝ f (frozenBallScaling 0 hr x) := by
  by_cases hf : DifferentiableAt ℝ f (frozenBallScaling 0 hr x)
  · exact nondiv_fderiv_comp_ballScaling 0 x hr hf
  · have hc : ¬ DifferentiableAt ℝ (f ∘ frozenBallScaling 0 hr) x := by
      intro hd
      apply hf
      have hs : DifferentiableAt ℝ (frozenBallScaling (0 : EuclideanSpace ℝ (Fin 3)) hr).symm
          (frozenBallScaling 0 hr x) := by
        rw [frozenBallScaling_symm_coe]
        exact (differentiableAt_id.sub_const (0 : EuclideanSpace ℝ (Fin 3))).const_smul r⁻¹
      have hcomp := (((frozenBallScaling (0 : EuclideanSpace ℝ (Fin 3)) hr).symm_apply_apply
        x).symm ▸ hd).comp (frozenBallScaling 0 hr x) hs
      have he : (f ∘ frozenBallScaling 0 hr) ∘ (frozenBallScaling 0 hr).symm = f := by
        funext y
        simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
      rwa [he] at hcomp
    rw [fderiv_zero_of_not_differentiableAt hc, fderiv_zero_of_not_differentiableAt hf,
      smul_zero]

lemma boundary_neumann_gradient_comp_scaling {r : ℝ} (hr : 0 < r)
    (f : EuclideanSpace ℝ (Fin 3) → ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    gradient (f ∘ frozenBallScaling 0 hr) x = r • gradient f (frozenBallScaling 0 hr x) := by
  simp only [gradient, boundary_neumann_fderiv_comp_scaling hr f x, map_smulₛₗ,
    starRingEnd_apply, star_trivial]

/-- C¹,α regularity on the closed half ball of radius `r ≤ 1` transfers to the closed unit
half ball under the scaling, without increasing the norm. -/
theorem boundary_neumann_c1Holder_comp_scaling {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {α r : ℝ} (hα : 0 ≤ α)
    (hr : 0 < r) (hr1 : r ≤ 1) {f : EuclideanSpace ℝ (Fin 3) → F}
    (hf : HasC1HolderOn α f (closure (boundaryHalfBall r))) :
    HasC1HolderOn α (f ∘ frozenBallScaling 0 hr) (closure (boundaryHalfBall 1)) ∧
      nondivC1HolderNorm α (f ∘ frozenBallScaling 0 hr) (closure (boundaryHalfBall 1)) ≤
        nondivC1HolderNorm α f (closure (boundaryHalfBall r)) := by
  let e := frozenBallScaling (0 : EuclideanSpace ℝ (Fin 3)) hr
  have hm := boundary_neumann_scaling_mapsTo_closure hr
  have hd (x) (_ : x ∈ closure (boundaryHalfBall 1)) (y)
      (_ : y ∈ closure (boundaryHalfBall 1)) : ‖e x - e y‖ ≤ ‖x - y‖ :=
    boundary_neumann_scaling_norm_sub_le hr hr1 x y
  obtain ⟨hfc, hfcb⟩ := nondiv_holder_comp_contraction hα hf.function_holder hm hd
  obtain ⟨hDc, hDcb⟩ := nondiv_holder_comp_contraction hα hf.derivative_holder hm hd
  obtain ⟨hDs, hDsb⟩ := nondiv_holder_const_smul hDc r
  have heq : EqOn (fderiv ℝ (f ∘ e)) (fun x => r • fderiv ℝ f (e x))
      (closure (boundaryHalfBall 1)) :=
    fun x _ => boundary_neumann_fderiv_comp_scaling hr f x
  have hec : ContDiff ℝ 1 e := contDiff_const.add (contDiff_id.const_smul r)
  refine ⟨⟨hf.contDiff.comp hec.contDiffOn hm, hfc, (nondiv_holder_congr heq).1.mpr hDs⟩, ?_⟩
  unfold nondivC1HolderNorm
  rw [(nondiv_holder_congr heq).2]
  apply add_le_add hfcb
  apply hDsb.trans
  rw [Real.norm_of_nonneg hr.le]
  exact (mul_le_mul_of_nonneg_left hDcb hr.le).trans
    ((mul_le_mul_of_nonneg_right hr1 hf.derivative_holder.norm_nonneg).trans_eq (one_mul _))

/-- Multiplying by a constant of modulus at most one preserves C¹,α without increasing
the norm. -/
theorem boundary_neumann_c1Holder_const_smul {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {α : ℝ} {U : Set E}
    {f : E → F} (hf : HasC1HolderOn α f U) {c : ℝ} (hc : |c| ≤ 1) :
    HasC1HolderOn α (fun x => c • f x) U ∧
      nondivC1HolderNorm α (fun x => c • f x) U ≤ nondivC1HolderNorm α f U := by
  obtain ⟨h0, h0b⟩ := nondiv_holder_const_smul hf.function_holder c
  obtain ⟨h1, h1b⟩ := nondiv_holder_const_smul hf.derivative_holder c
  have heq : fderiv ℝ (fun x => c • f x) = fun x => c • fderiv ℝ f x := by
    have h := fderiv_const_smul_field (𝕜 := ℝ) (f := f) c
    simpa only [Pi.smul_def] using h
  have hc' : ‖c‖ ≤ 1 := by rwa [Real.norm_eq_abs]
  refine ⟨⟨hf.contDiff.const_smul c, h0, heq ▸ h1⟩, ?_⟩
  unfold nondivC1HolderNorm
  rw [heq]
  exact add_le_add
    (h0b.trans ((mul_le_mul_of_nonneg_right hc' hf.function_holder.norm_nonneg).trans_eq
      (one_mul _)))
    (h1b.trans ((mul_le_mul_of_nonneg_right hc' hf.derivative_holder.norm_nonneg).trans_eq
      (one_mul _)))

/-- Closed conormal data on the closed half ball of radius `r ∈ (0, 1]` rescale to closed
conormal data on the closed unit half ball, with the same constants. -/
theorem boundary_neumann_closed_data_of_scaling {α lam cap M N r : ℝ} (hα : 0 ≤ α)
    (hr : 0 < r) (hr1 : r ≤ 1)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hA : HasC1HolderOn α A (closure (boundaryHalfBall r)))
    (hH : HasC1HolderOn α H (closure (boundaryHalfBall r)))
    (hw : HasC1HolderOn α w (closure (boundaryHalfBall r)))
    (hAM : nondivC1HolderNorm α A (closure (boundaryHalfBall r)) ≤ M)
    (hN : nondivC1HolderNorm α w (closure (boundaryHalfBall r)) +
      nondivC1HolderNorm α H (closure (boundaryHalfBall r)) ≤ N)
    (hcap : ∀ x ∈ closure (boundaryHalfBall r), ‖A x‖ ≤ cap)
    (hell : ∀ x ∈ closure (boundaryHalfBall r), ∀ v,
      lam * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    (hcross : ∀ x ∈ closure (boundaryHalfBall r), x (Fin.last 2) = 0 →
      ∀ j : Fin 3, j ≠ Fin.last 2 →
        A x (EuclideanSpace.single j 1) (Fin.last 2) = 0 ∧
        A x (EuclideanSpace.single (Fin.last 2) 1) j = 0)
    (hH0 : ∀ x ∈ closure (boundaryHalfBall r), x (Fin.last 2) = 0 →
      H x (Fin.last 2) = 0)
    (hw0 : ∀ x ∈ closure (boundaryHalfBall r), x (Fin.last 2) = 0 →
      gradient w x (Fin.last 2) = 0)
    (heq : IsBoundaryNeumannEquationOn A (gradient w) H r) :
    BoundaryNeumannClosedData α lam cap M N (A ∘ frozenBallScaling 0 hr)
      (fun x => r • H (frozenBallScaling 0 hr x)) (w ∘ frozenBallScaling 0 hr) := by
  have hm := boundary_neumann_scaling_mapsTo_closure hr
  have hr1' : |r| ≤ 1 := by rwa [abs_of_pos hr]
  obtain ⟨hAs, hAsb⟩ := boundary_neumann_c1Holder_comp_scaling hα hr hr1 hA
  obtain ⟨hHs, hHsb⟩ := boundary_neumann_c1Holder_comp_scaling hα hr hr1 hH
  obtain ⟨hHr, hHrb⟩ := boundary_neumann_c1Holder_const_smul hHs hr1'
  obtain ⟨hws, hwsb⟩ := boundary_neumann_c1Holder_comp_scaling hα hr hr1 hw
  have hlast (x : EuclideanSpace ℝ (Fin 3)) (hx : x (Fin.last 2) = 0) :
      frozenBallScaling (0 : EuclideanSpace ℝ (Fin 3)) hr x (Fin.last 2) = 0 := by
    rw [boundary_neumann_scaling_last, hx, mul_zero]
  refine
    { coefficient := hAs
      source := hHr
      solution := hws
      coefficient_norm := hAsb.trans hAM
      norm_bound := ?_
      coefficient_bound := fun x hx => hcap _ (hm hx)
      elliptic := fun x hx v => hell _ (hm hx) v
      cross_zero := fun x hx hx0 j hj => hcross _ (hm hx) (hlast x hx0) j hj
      source_normal_zero := ?_
      solution_normal_zero := ?_
      equation := ?_ }
  · have hHr' : nondivC1HolderNorm α (fun x => r • H (frozenBallScaling 0 hr x))
        (closure (boundaryHalfBall 1)) ≤ nondivC1HolderNorm α H (closure (boundaryHalfBall r)) :=
      hHrb.trans hHsb
    linarith
  · intro x hx hx0
    simp only [PiLp.smul_apply, smul_eq_mul, hH0 _ (hm hx) (hlast x hx0), mul_zero]
  · intro x hx hx0
    rw [boundary_neumann_gradient_comp_scaling hr w x, PiLp.smul_apply,
      hw0 _ (hm hx) (hlast x hx0), smul_zero]
  · have hg : gradient (w ∘ frozenBallScaling 0 hr) =
        fun x => r • gradient w (frozenBallScaling 0 hr x) :=
      funext (boundary_neumann_gradient_comp_scaling hr w)
    rw [hg]
    exact heq.comp_scaling hr

end LiquidDrop
