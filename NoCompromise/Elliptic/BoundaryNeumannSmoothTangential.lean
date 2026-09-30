module

public import NoCompromise.Elliptic.BoundaryNeumannSmoothFlux

@[expose] public section

/-!
# The differentiated homogeneous Neumann problem

The first iteration milestone uses an actual C² extension of the solution to an
open neighborhood of the closed half ball. All derivatives on the face are
ambient Fréchet derivatives of that extension. The coefficient and source need
only C¹ regularity for the differentiated weak identity.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- The exact vector datum after differentiating tangentially, with unshifted
principal coefficient. -/
def boundaryNeumannSmoothDatum
    (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3))
    (F H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (i : Fin 3) (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  fderiv ℝ H x (EuclideanSpace.single i 1) -
    fderiv ℝ A x (EuclideanSpace.single i 1) (F x)

/-- The actual shifted-gradient quotient datum converges to the differentiated
datum; no shift remains in the limit. -/
lemma boundary_neumann_smooth_datum_tendsto
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {F H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {x : EuclideanSpace ℝ (Fin 3)}
    (hA : DifferentiableAt ℝ A x) (hF : ContinuousAt F x)
    (hH : DifferentiableAt ℝ H x) (i : Fin 3) :
    Tendsto (fun s : ℝ => boundaryNeumannQuotientDatum A F H i s x) (𝓝[≠] 0)
      (𝓝 (boundaryNeumannSmoothDatum A F H i x)) := by
  have ht : Tendsto (fun s : ℝ => x + s • EuclideanSpace.single i (1 : ℝ))
      (𝓝[≠] 0) (𝓝 x) := by
    simpa only [zero_smul, add_zero] using
      (tendsto_const_nhds.add ((tendsto_id.mono_left nhdsWithin_le_nhds).smul
        tendsto_const_nhds) :
        Tendsto (fun s : ℝ => x + s • EuclideanSpace.single i (1 : ℝ))
          (𝓝[≠] 0) (𝓝 (x + (0 : ℝ) • EuclideanSpace.single i 1)))
  have hp := (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp
    ((boundary_neumann_smooth_quotient_tendsto hA i).prodMk_nhds (hF.tendsto.comp ht))
  exact (boundary_neumann_smooth_quotient_tendsto hH i).sub hp

/-- A vanishing normal component remains zero after a tangential derivative on
every smaller closed flat face. -/
lemma boundary_neumann_smooth_normal_derivative_zero {R r : ℝ} (hrR : r < R)
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    (hRU : closure (boundaryHalfBall R) ⊆ U)
    {F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hF : ContDiffOn ℝ 1 F U)
    (hzero : ∀ x ∈ closure (boundaryHalfBall R), x (Fin.last 2) = 0 →
      F x (Fin.last 2) = 0)
    {i : Fin 3} (hi : i ≠ Fin.last 2)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ closure (boundaryHalfBall r))
    (hflat : x (Fin.last 2) = 0) :
    fderiv ℝ F x (EuclideanSpace.single i 1) (Fin.last 2) = 0 := by
  have hxR := closure_mono (boundaryHalfBall_mono hrR.le) hx
  have ht := (EuclideanSpace.proj (Fin.last 2)).continuous.continuousAt.tendsto.comp
    (boundary_neumann_smooth_quotient_tendsto
      ((hF.contDiffAt (hU.mem_nhds (hRU hxR))).differentiableAt one_ne_zero) i)
  have hs : ∀ᶠ s : ℝ in 𝓝[≠] 0, |s| ≤ R - r := by
    have ht : ∀ᶠ s : ℝ in 𝓝[≠] 0, s ∈ ball 0 (R - r) :=
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ (sub_pos.mpr hrR))
    exact ht.mono fun s hs => (by simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs]
      using hs : |s| < R - r).le
  have he : ∀ᶠ s : ℝ in 𝓝[≠] 0,
      (EuclideanSpace.proj (Fin.last 2)) (coordinateDifferenceQuotient i s F x) = 0 := by
    filter_upwards [hs] with s hs
    have hxshift : x + s • EuclideanSpace.single i 1 ∈ closure (boundaryHalfBall R) := by
      simpa only [one_smul] using boundary_nondiv_closed_segment hi hs hx (t := 1) (by simp)
    change coordinateDifferenceQuotient i s F x (Fin.last 2) = 0
    simp only [coordinateDifferenceQuotient, PiLp.smul_apply, PiLp.sub_apply,
      hzero x hxR hflat,
      hzero _ hxshift ((boundary_neumann_tangential_last hi s x).trans hflat),
      sub_self, smul_zero]
  exact tendsto_nhds_unique (ht.congr' he) tendsto_const_nhds

/-- Differentiating the conormal equation and both face conditions, first for
an arbitrary C¹ vector field `F`. Only the normal row of cross coefficients is
needed; assuming both cross rows vanish is therefore also sufficient. -/
theorem boundary_neumann_smooth_vector_equation {R r : ℝ} (hrR : r < R)
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    (hRU : closure (boundaryHalfBall R) ⊆ U)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {F H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hA : ContDiffOn ℝ 1 A U) (hF : ContDiffOn ℝ 1 F U) (hH : ContDiffOn ℝ 1 H U)
    (he : IsBoundaryNeumannEquationOn A F H R)
    (hcross : ∀ x ∈ closure (boundaryHalfBall R), x (Fin.last 2) = 0 →
      ∀ j : Fin 3, j ≠ Fin.last 2 → A x (EuclideanSpace.single j 1) (Fin.last 2) = 0)
    (hHzero : ∀ x ∈ closure (boundaryHalfBall R), x (Fin.last 2) = 0 → H x (Fin.last 2) = 0)
    (hFzero : ∀ x ∈ closure (boundaryHalfBall R), x (Fin.last 2) = 0 → F x (Fin.last 2) = 0)
    {i : Fin 3} (hi : i ≠ Fin.last 2) :
    IsBoundaryNeumannEquationOn A (fun x => fderiv ℝ F x (EuclideanSpace.single i 1))
      (boundaryNeumannSmoothDatum A F H i) r ∧
    (∀ x ∈ closure (boundaryHalfBall r), x (Fin.last 2) = 0 →
      boundaryNeumannSmoothDatum A F H i x (Fin.last 2) = 0) ∧
    ∀ x ∈ closure (boundaryHalfBall r), x (Fin.last 2) = 0 →
      fderiv ℝ F x (EuclideanSpace.single i 1) (Fin.last 2) = 0 := by
  have hsub := closure_mono (boundaryHalfBall_mono hrR.le)
  have hdA (x) (hx : x ∈ U) := (hA.contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero
  have hdF (x) (hx : x ∈ U) := (hF.contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero
  have hdH (x) (hx : x ∈ U) := (hH.contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero
  refine ⟨?_, ?_, fun x hx hf =>
    boundary_neumann_smooth_normal_derivative_zero hrR hU hRU hF hFzero hi hx hf⟩
  · have hflux := boundary_neumann_smooth_flux_derivative hrR hU hRU
      ((hA.clm_apply hF).sub hH) he hi
    intro φ hφ hcφ hsφ
    rw [← hflux φ hφ hcφ hsφ]
    apply setIntegral_congr_fun (isOpen_boundaryHalfBall r).measurableSet
    intro x hx
    have hxU := hRU (hsub (subset_closure hx))
    have hd : HasFDerivAt (fun y => A y (F y) - H y)
        ((A x).comp (fderiv ℝ F x) + (fderiv ℝ A x).flip (F x) - fderiv ℝ H x) x :=
      ((hdA x hxU).hasFDerivAt.clm_apply (hdF x hxU).hasFDerivAt).sub
        (hdH x hxU).hasFDerivAt
    dsimp only
    rw [hd.fderiv]
    congr 1
    simp only [boundaryNeumannSmoothDatum, sub_apply, add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
    abel
  · intro x hx hflat
    have ht := (EuclideanSpace.proj (Fin.last 2)).continuous.continuousAt.tendsto.comp
      (boundary_neumann_smooth_datum_tendsto (hdA x (hRU (hsub hx)))
        (hdF x (hRU (hsub hx))).continuousAt (hdH x (hRU (hsub hx))) i)
    have hs : ∀ᶠ s : ℝ in 𝓝[≠] 0, |s| ≤ R - r := by
      have ht : ∀ᶠ s : ℝ in 𝓝[≠] 0, s ∈ ball 0 (R - r) :=
        mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ (sub_pos.mpr hrR))
      exact ht.mono fun s hs => (by simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs]
        using hs : |s| < R - r).le
    have hz : ∀ᶠ s : ℝ in 𝓝[≠] 0,
        (EuclideanSpace.proj (Fin.last 2)) (boundaryNeumannQuotientDatum A F H i s x) = 0 := by
      filter_upwards [hs] with s hs
      exact (boundary_neumann_quotient_equation hi hs (hA.continuousOn.mono hRU)
        (hF.continuousOn.mono hRU) (hH.continuousOn.mono hRU) he hcross hHzero hFzero).2
          x hx hflat
    exact tendsto_nhds_unique (ht.congr' hz) tendsto_const_nhds

/-- C² symmetry identifies the derivative of the gradient with the gradient of
the coordinate derivative, including at face points lying in the open extension
domain. -/
lemma boundary_neumann_smooth_gradient_coordinate
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    {w : EuclideanSpace ℝ (Fin 3) → ℝ} (hw : ContDiffOn ℝ 2 w U)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ U) (i : Fin 3) :
    gradient (fun y => fderiv ℝ w y (EuclideanSpace.single i 1)) x =
      fderiv ℝ (gradient w) x (EuclideanSpace.single i 1) := by
  have hDw : ContDiffOn ℝ 1 (fderiv ℝ w) U := hw.fderiv_of_isOpen hU (by norm_num)
  have hGw : ContDiffOn ℝ 1 (gradient w) U :=
    (toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm.toContinuousLinearEquiv.contDiff
      |>.comp_contDiffOn hDw
  have hdG := (hGw.contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero
  ext j
  rw [gradient_apply_eq_fderiv_single]
  have hp : fderiv ℝ (fun y => fderiv ℝ w y (EuclideanSpace.single j 1)) x =
      (EuclideanSpace.proj j).comp (fderiv ℝ (gradient w) x) := by
    have he : (fun y => fderiv ℝ w y (EuclideanSpace.single j 1)) =
        (EuclideanSpace.proj j) ∘ gradient w :=
      funext fun y => (gradient_apply_eq_fderiv_single w y j).symm
    rw [he, ((EuclideanSpace.proj j).hasFDerivAt.comp x hdG.hasFDerivAt).fderiv]
  change _ = ((EuclideanSpace.proj j).comp (fderiv ℝ (gradient w) x))
    (EuclideanSpace.single i 1)
  rw [← hp, nondiv_fderiv_coordinate_eq hU hw i hx, nondiv_fderiv_coordinate_eq hU hw j hx]
  exact ((hw.contDiffAt (hU.mem_nhds hx)).isSymmSndFDerivAt (by norm_num)).eq _ _

/-- Milestone 1: `v = ∂ᵢw` solves the differentiated homogeneous conormal problem
on every smaller half ball, and its normal derivative and normal datum vanish
on the entire smaller closed flat face. Here `w` itself is the chosen ambient
C² extension. Both rows of cross coefficients are explicitly assumed zero. -/
theorem boundary_neumann_smooth_tangential_equation {R r : ℝ} (hrR : r < R)
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    (hRU : closure (boundaryHalfBall R) ⊆ U)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hA : ContDiffOn ℝ 2 A U) (hH : ContDiffOn ℝ 2 H U) (hw : ContDiffOn ℝ 2 w U)
    (he : IsBoundaryNeumannEquationOn A (gradient w) H R)
    (hcross : ∀ x ∈ closure (boundaryHalfBall R), x (Fin.last 2) = 0 →
      ∀ j : Fin 3, j ≠ Fin.last 2 →
        A x (EuclideanSpace.single j 1) (Fin.last 2) = 0 ∧
        A x (EuclideanSpace.single (Fin.last 2) 1) j = 0)
    (hHzero : ∀ x ∈ closure (boundaryHalfBall R), x (Fin.last 2) = 0 → H x (Fin.last 2) = 0)
    (hwzero : ∀ x ∈ closure (boundaryHalfBall R), x (Fin.last 2) = 0 →
      gradient w x (Fin.last 2) = 0)
    {i : Fin 3} (hi : i ≠ Fin.last 2) :
    IsBoundaryNeumannEquationOn A
      (gradient (fun x => fderiv ℝ w x (EuclideanSpace.single i 1)))
      (boundaryNeumannSmoothDatum A (gradient w) H i) r ∧
    (∀ x ∈ closure (boundaryHalfBall r), x (Fin.last 2) = 0 →
      boundaryNeumannSmoothDatum A (gradient w) H i x (Fin.last 2) = 0) ∧
    ∀ x ∈ closure (boundaryHalfBall r), x (Fin.last 2) = 0 →
      gradient (fun y => fderiv ℝ w y (EuclideanSpace.single i 1)) x (Fin.last 2) = 0 := by
  have hDw : ContDiffOn ℝ 1 (fderiv ℝ w) U := hw.fderiv_of_isOpen hU (by norm_num)
  have hGw : ContDiffOn ℝ 1 (gradient w) U :=
    (toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm.toContinuousLinearEquiv.contDiff
      |>.comp_contDiffOn hDw
  obtain ⟨heq, hdatum, hnormal⟩ := boundary_neumann_smooth_vector_equation hrR hU hRU
    (hA.of_le (by norm_num)) hGw (hH.of_le (by norm_num)) he
    (fun x hx hf j hj => (hcross x hx hf j hj).1) hHzero hwzero hi
  have hsub := closure_mono (boundaryHalfBall_mono hrR.le)
  refine ⟨?_, hdatum, ?_⟩
  · intro φ hφ hcφ hsφ
    rw [← heq φ hφ hcφ hsφ]
    apply setIntegral_congr_fun (isOpen_boundaryHalfBall r).measurableSet
    intro x hx
    dsimp only
    rw [boundary_neumann_smooth_gradient_coordinate hU hw (hRU (hsub (subset_closure hx))) i]
  · intro x hx hf
    rw [boundary_neumann_smooth_gradient_coordinate hU hw (hRU (hsub hx)) i]
    exact hnormal x hx hf

/-- The differentiated problem directly from the existing closed Neumann data.
The coefficient and source are C² on an open neighborhood of the closed unit
half ball, while the C² extension hypothesis for the solution is needed only
near the closed radius `R` half ball. No ellipticity is used in this step. -/
theorem BoundaryNeumannClosedData.smooth_tangential_equation
    {α lam cap M N R r : ℝ} (hrR : r < R) (hR : R ≤ 1)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    (d : BoundaryNeumannClosedData α lam cap M N A H w)
    {U W : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U) (hW : IsOpen W)
    (h1U : closure (boundaryHalfBall 1) ⊆ U)
    (hRW : closure (boundaryHalfBall R) ⊆ W)
    (hA : ContDiffOn ℝ 2 A U) (hH : ContDiffOn ℝ 2 H U) (hw : ContDiffOn ℝ 2 w W)
    {i : Fin 3} (hi : i ≠ Fin.last 2) :
    IsBoundaryNeumannEquationOn A
      (gradient (fun x => fderiv ℝ w x (EuclideanSpace.single i 1)))
      (boundaryNeumannSmoothDatum A (gradient w) H i) r ∧
    (∀ x ∈ closure (boundaryHalfBall r), x (Fin.last 2) = 0 →
      boundaryNeumannSmoothDatum A (gradient w) H i x (Fin.last 2) = 0) ∧
    ∀ x ∈ closure (boundaryHalfBall r), x (Fin.last 2) = 0 →
      gradient (fun y => fderiv ℝ w y (EuclideanSpace.single i 1)) x (Fin.last 2) = 0 := by
  have hsub := closure_mono (boundaryHalfBall_mono hR)
  have he : IsBoundaryNeumannEquationOn A (gradient w) H R := by
    intro φ hφ hcφ hsφ
    have ht := boundary_neumann_flux_translate hi
      (show |(0 : ℝ)| ≤ 1 - R by simpa only [abs_zero] using sub_nonneg.mpr hR)
      d.equation hφ hcφ hsφ
    simpa only [zero_smul, add_zero] using ht
  exact boundary_neumann_smooth_tangential_equation hrR (hU.inter hW)
    (fun x hx => ⟨h1U (hsub hx), hRW hx⟩)
    (hA.mono inter_subset_left) (hH.mono inter_subset_left) (hw.mono inter_subset_right) he
    (fun x hx hf => d.cross_zero x (hsub hx) hf)
    (fun x hx hf => d.source_normal_zero x (hsub hx) hf)
    (fun x hx hf => d.solution_normal_zero x (hsub hx) hf) hi

end LiquidDrop
