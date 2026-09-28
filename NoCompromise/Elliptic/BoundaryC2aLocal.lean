import NoCompromise.Elliptic.BoundaryC2aH1
import NoCompromise.Elliptic.BoundaryC2aTrace
import NoCompromise.Elliptic.BoundaryHolderHalfScaling
import NoCompromise.Elliptic.BoundaryHolderTranslate
import NoCompromise.Elliptic.NondivSchauderScalingNorm

/-!
# Local boundary C²,α near flat points: the rescaling step of `thm:boundary-C2a`

The similarity `e y = p + r • y` carries the closed unit half ball into the fixed slab on
which the C¹,α representative lives. This file records the scaling facts used to transfer
the C²,α estimate on the unit half ball back to `e '' boundaryNondivC2Slab`:

* the derivative of `f ∘ e` is `r • (fderiv f) ∘ e` with no differentiability hypothesis;
* C¹,α membership and norms do not grow under `f ↦ f ∘ e` for `r ≤ 1`, on any pair of
  sets mapped into each other;
* the iterated coordinate derivatives of `w ∘ e⁻¹` at `e y` are `r⁻² ` times those of `w`
  at `y`, and C² regularity transfers along `e`.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- The derivative of `f ∘ e` for the similarity `e y = c + r • y`, with no differentiability
hypothesis on `f` (both sides vanish when `f` is not differentiable at `e x`). -/
lemma boundary_c2a_fderiv_comp_scaling {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r)
    (f : EuclideanSpace ℝ (Fin n) → F) :
    fderiv ℝ (f ∘ frozenBallScaling c hr) x = r • fderiv ℝ f (frozenBallScaling c hr x) := by
  by_cases hf : DifferentiableAt ℝ f (frozenBallScaling c hr x)
  · exact nondiv_fderiv_comp_ballScaling c x hr hf
  · have hnd : ¬ DifferentiableAt ℝ (f ∘ frozenBallScaling c hr) x := by
      intro h
      apply hf
      have hs : DifferentiableAt ℝ (⇑(frozenBallScaling c hr).symm)
          (frozenBallScaling c hr x) := by
        rw [frozenBallScaling_symm_coe]
        fun_prop
      have h' : DifferentiableAt ℝ (f ∘ frozenBallScaling c hr)
          ((frozenBallScaling c hr).symm (frozenBallScaling c hr x)) := by
        rw [Homeomorph.symm_apply_apply]
        exact h
      have hc := h'.comp (frozenBallScaling c hr x) hs
      have heq : (f ∘ frozenBallScaling c hr) ∘ (frozenBallScaling c hr).symm = f := by
        funext z
        simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
      rwa [heq] at hc
    rw [fderiv_zero_of_not_differentiableAt hnd, fderiv_zero_of_not_differentiableAt hf,
      smul_zero]

/-- C¹,α membership and norm do not grow under a contracting similarity mapping `V` into `S`.
No differentiability beyond the C¹,α hypothesis on `S` is needed: the derivative formula for
`f ∘ e` holds everywhere. -/
theorem boundary_c2a_c1Holder_comp_scaling {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ} (hα : 0 ≤ α) (c : EuclideanSpace ℝ (Fin n)) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) {f : EuclideanSpace ℝ (Fin n) → F}
    {S V : Set (EuclideanSpace ℝ (Fin n))}
    (hf : HasC1HolderOn α f S) (hm : MapsTo (frozenBallScaling c hr) V S) :
    HasC1HolderOn α (f ∘ frozenBallScaling c hr) V ∧
      nondivC1HolderNorm α (f ∘ frozenBallScaling c hr) V ≤ nondivC1HolderNorm α f S := by
  let e := frozenBallScaling c hr
  have hd (x) (_ : x ∈ V) (y) (_ : y ∈ V) : ‖e x - e y‖ ≤ ‖x - y‖ := by
    have heq : ‖e x - e y‖ = r * ‖x - y‖ := by
      simpa only [dist_eq_norm] using quasilinear_ballScaling_dist c x y hr
    rw [heq]
    exact (mul_le_mul_of_nonneg_right hr1 (norm_nonneg _)).trans_eq (one_mul _)
  obtain ⟨hfc, hfcb⟩ := nondiv_holder_comp_contraction hα hf.function_holder hm hd
  obtain ⟨hDc, hDcb⟩ := nondiv_holder_comp_contraction hα hf.derivative_holder hm hd
  obtain ⟨hDs, hDsb⟩ := nondiv_holder_const_smul hDc r
  have heq : EqOn (fderiv ℝ (f ∘ e)) (fun x => r • fderiv ℝ f (e x)) V := by
    intro x _
    exact boundary_c2a_fderiv_comp_scaling c x hr f
  have hec : ContDiff ℝ 1 e := contDiff_const.add (contDiff_id.const_smul r)
  refine ⟨⟨hf.contDiff.comp hec.contDiffOn hm, hfc, (nondiv_holder_congr heq).1.mpr hDs⟩, ?_⟩
  unfold nondivC1HolderNorm
  rw [(nondiv_holder_congr heq).2]
  apply add_le_add hfcb
  apply hDsb.trans
  rw [Real.norm_of_nonneg hr.le]
  exact (mul_le_mul_of_nonneg_left hDcb hr.le).trans
    ((mul_le_mul_of_nonneg_right hr1 hf.derivative_holder.norm_nonneg).trans_eq (one_mul _))

/-- The inverse of a ball similarity is again a ball similarity. -/
lemma boundary_c2a_scaling_symm_eq {n : ℕ} (c : EuclideanSpace ℝ (Fin n)) {r : ℝ}
    (hr : 0 < r) :
    ⇑(frozenBallScaling c hr).symm = ⇑(frozenBallScaling (-(r⁻¹ • c)) (inv_pos.mpr hr)) := by
  funext x
  rw [frozenBallScaling_symm_apply, frozenBallScaling_apply, smul_sub]
  abel

/-- Iterated coordinate derivatives scale by `r⁻²` under `w ↦ w ∘ e⁻¹`. The identity holds
for every `w`, with no regularity hypothesis. -/
theorem boundary_c2a_entry_comp_scaling (c y : EuclideanSpace ℝ (Fin 3)) {r : ℝ}
    (hr : 0 < r) (w : EuclideanSpace ℝ (Fin 3) → ℝ) (i j : Fin 3) :
    boundaryNeumannC2Entry (w ∘ (frozenBallScaling c hr).symm) (frozenBallScaling c hr y) i j =
      r⁻¹ ^ 2 * boundaryNeumannC2Entry w y i j := by
  have hs := boundary_c2a_scaling_symm_eq c hr
  set e' := frozenBallScaling (-(r⁻¹ • c)) (inv_pos.mpr hr)
  have hy : e' (frozenBallScaling c hr y) = y := by
    rw [← hs, Homeomorph.symm_apply_apply]
  unfold boundaryNeumannC2Entry
  rw [hs]
  have h1 : (fun z => fderiv ℝ (w ∘ e') z (EuclideanSpace.single j 1)) =
      r⁻¹ • ((fun u => fderiv ℝ w u (EuclideanSpace.single j 1)) ∘ e') := by
    funext z
    rw [boundary_c2a_fderiv_comp_scaling]
    rfl
  rw [h1, fderiv_const_smul_field, Pi.smul_apply, boundary_c2a_fderiv_comp_scaling, hy]
  simp only [smul_apply, smul_eq_mul]
  ring

/-- C² regularity transfers along a ball similarity. -/
theorem boundary_c2a_contDiffOn_comp_scaling_symm {k : ℕ∞} (c : EuclideanSpace ℝ (Fin 3))
    {r : ℝ} (hr : 0 < r) {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    {S : Set (EuclideanSpace ℝ (Fin 3))} (hw : ContDiffOn ℝ k w S) :
    ContDiffOn ℝ k (w ∘ (frozenBallScaling c hr).symm) (frozenBallScaling c hr '' S) := by
  have hsym : ContDiff ℝ k (frozenBallScaling c hr).symm := by
    rw [frozenBallScaling_symm_coe]
    exact (contDiff_id.sub contDiff_const).const_smul r⁻¹
  apply hw.comp hsym.contDiffOn
  rintro _ ⟨y, hy, rfl⟩
  simpa only [mem_preimage, Homeomorph.symm_apply_apply] using hy

/-- The gradient of `v ∘ e` for the similarity `e y = c + r • y`, with no hypothesis on `v`. -/
lemma boundary_c2a_gradient_comp_scaling (c y : EuclideanSpace ℝ (Fin 3)) {r : ℝ}
    (hr : 0 < r) (v : EuclideanSpace ℝ (Fin 3) → ℝ) :
    gradient (v ∘ frozenBallScaling c hr) y = r • gradient v (frozenBallScaling c hr y) := by
  simp [gradient, boundary_c2a_fderiv_comp_scaling]

/-- The rescaled weak equation. If `u` solves `div(A∇u) = div G` weakly on the unit half ball,
`v` is a C¹ representative on an open `W` whose gradient agrees a.e. with the weak gradient `F`
on `W ∩ {x₃ > 0}`, and the similarity `e y = p + r • y` maps the half ball into
`W ∩ boundaryHalfBall 1`, then `w = v ∘ e` solves `div((A ∘ e)∇w) = div(r • G ∘ e)` against
smooth compactly supported tests, in the split form used by `boundary_c2a_holder_trace`. -/
theorem IsWeakDivergenceEquationOn.boundary_c2a_rescale
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    {F G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} {W : Set (EuclideanSpace ℝ (Fin 3))}
    (p : EuclideanSpace ℝ (Fin 3)) {r : ℝ} (hr : 0 < r)
    (hw : IsWeakDivergenceEquationOn A F G (boundaryHalfBall 1))
    (hW : IsOpen W) (hv : ContDiffOn ℝ 1 v W)
    (hgv : gradient v =ᵐ[volume.restrict (W ∩ {x | 0 < x (Fin.last 2)})] F)
    (hsub : frozenBallScaling p hr '' boundaryHalfBall 1 ⊆ W ∩ boundaryHalfBall 1)
    (hA : ContinuousOn A (closure (boundaryHalfBall 1)))
    (hG : ContinuousOn G (closure (boundaryHalfBall 1))) :
    ∀ ψ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ boundaryHalfBall 1 →
      (∫ y, inner ℝ ((A ∘ frozenBallScaling p hr) y
          (gradient (v ∘ frozenBallScaling p hr) y)) (gradient ψ y)) =
        ∫ y, inner ℝ (r • G (frozenBallScaling p hr y)) (gradient ψ y) := by
  set e := frozenBallScaling p hr with he_def
  set U' := W ∩ boundaryHalfBall 1
  have hU'o : IsOpen U' := hW.inter (isOpen_boundaryHalfBall 1)
  have h1 : IsWeakDivergenceEquationOn A F G U' := hw.mono inter_subset_right
  have hae : F =ᵐ[volume.restrict U'] gradient v := by
    have hss : U' ⊆ W ∩ {x | 0 < x (Fin.last 2)} := fun x hx => ⟨hx.1, hx.2.2⟩
    exact (ae_restrict_of_ae_restrict_of_subset hss hgv).mono fun x hx => hx.symm
  have h2 : IsWeakDivergenceEquationOn A (gradient v) G U' :=
    h1.congr_gradient_ae hU'o.measurableSet hae
  have hmap : ∀ x ∈ boundaryHalfBall r, x + p ∈ U' := by
    intro x hx
    have hy : r⁻¹ • x ∈ boundaryHalfBall 1 := by
      obtain ⟨hx1, hx2⟩ := hx
      refine ⟨?_, ?_⟩
      · rw [mem_ball_zero_iff] at hx1 ⊢
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
        calc r⁻¹ * ‖x‖ < r⁻¹ * r := mul_lt_mul_of_pos_left hx1 (inv_pos.mpr hr)
          _ = 1 := inv_mul_cancel₀ hr.ne'
      · change 0 < x (Fin.last 2) at hx2
        change 0 < (r⁻¹ • x) (Fin.last 2)
        rw [PiLp.smul_apply, smul_eq_mul]
        exact mul_pos (inv_pos.mpr hr) hx2
    have hmem := hsub ⟨_, hy, rfl⟩
    have heq : e (r⁻¹ • x) = x + p := by
      rw [he_def, frozenBallScaling_apply, smul_smul, mul_inv_cancel₀ hr.ne', one_smul,
        add_comm]
    rwa [heq] at hmem
  have h3 := (h2.boundary_translate p hmap).boundary_comp_scaling hr
  have hEq : ∀ y, frozenBallScaling 0 hr y + p = e y := by
    intro y
    rw [frozenBallScaling_apply, he_def, frozenBallScaling_apply, zero_add, add_comm]
  have h4 : IsWeakDivergenceEquationOn (A ∘ e) (gradient (v ∘ e)) (fun y => r • G (e y))
      (boundaryHalfBall 1) := by
    intro ψ hψ hcψ hsψ
    rw [← h3 ψ hψ hcψ hsψ]
    congr 1
    funext y
    simp only [Function.comp_apply, hEq, he_def, boundary_c2a_gradient_comp_scaling]
  intro ψ hψ hcψ hsψ
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by exact_mod_cast le_top)
  have h5 := h4 ψ hψ1 hcψ hsψ
  have hgψ : Continuous (gradient ψ) := continuous_gradient_of_contDiff hψ1
  have hsupp : ∀ g : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      Function.support (fun y => inner ℝ (g y) (gradient ψ y)) ⊆ tsupport ψ := by
    intro g y hy
    by_contra hn
    apply hy
    have h0 : fderiv ℝ ψ y = 0 := by
      by_contra h0
      exact hn (support_fderiv_subset ℝ (f := ψ) h0)
    have hg0 : gradient ψ y = 0 := by simp [gradient, h0]
    simp only [hg0, inner_zero_right]
  have hint : ∀ g : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      ContinuousOn g (boundaryHalfBall 1) →
      Integrable (fun y => inner ℝ (g y) (gradient ψ y)) := by
    intro g hg
    have hc : ContinuousOn (fun y => inner ℝ (g y) (gradient ψ y)) (tsupport ψ) :=
      (hg.mono hsψ).inner hgψ.continuousOn
    exact (integrableOn_iff_integrable_of_support_subset (hsupp g)).mp
      (hc.integrableOn_compact hcψ)
  have hec : Continuous e := (frozenBallScaling p hr).continuous
  have hmaps : MapsTo e (boundaryHalfBall 1) (boundaryHalfBall 1) :=
    fun y hy => (hsub ⟨y, hy, rfl⟩).2
  have hmapsW : MapsTo e (boundaryHalfBall 1) W := fun y hy => (hsub ⟨y, hy, rfl⟩).1
  have hAe : ContinuousOn (A ∘ e) (boundaryHalfBall 1) :=
    (hA.mono subset_closure).comp hec.continuousOn hmaps
  have hgradv : ContinuousOn (gradient v) W := by
    have hd := hv.continuousOn_fderiv_of_isOpen hW le_rfl
    exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm.continuous.comp_continuousOn
      hd
  have hgw : ContinuousOn (gradient (v ∘ e)) (boundaryHalfBall 1) := by
    have hfun : gradient (v ∘ e) = fun y => r • gradient v (e y) := by
      funext y
      rw [he_def]
      exact boundary_c2a_gradient_comp_scaling p y hr v
    rw [hfun]
    exact (hgradv.comp hec.continuousOn hmapsW).const_smul r
  have hGe : ContinuousOn (fun y => r • G (e y)) (boundaryHalfBall 1) :=
    ((hG.mono subset_closure).comp hec.continuousOn hmaps).const_smul r
  have i1 := hint _ (hAe.clm_apply hgw)
  have i2 := hint _ hGe
  simp_rw [inner_sub_left] at h5
  rw [integral_sub i1 i2, sub_eq_zero] at h5
  exact h5

lemma boundary_c2a_local_radius_pos : (0 : ℝ) < 1 / 2097152 := by norm_num

/-- For a flat point `p` with `‖p‖ ≤ 1/2`, the similarity `y ↦ p + 2⁻²¹ • y` maps the unit
half ball into itself. -/
lemma boundary_c2a_scaling_maps_halfBall {p : EuclideanSpace ℝ (Fin 3)}
    (hp3 : p (Fin.last 2) = 0) (hp : ‖p‖ ≤ 1 / 2) :
    MapsTo (frozenBallScaling p boundary_c2a_local_radius_pos) (boundaryHalfBall 1)
      (boundaryHalfBall 1) := by
  intro y hy
  obtain ⟨hy1, hy2⟩ := hy
  rw [mem_ball_zero_iff] at hy1
  change 0 < y (Fin.last 2) at hy2
  refine ⟨?_, ?_⟩
  · rw [mem_ball_zero_iff, frozenBallScaling_apply]
    calc ‖p + (1 / 2097152 : ℝ) • y‖ ≤ ‖p‖ + ‖(1 / 2097152 : ℝ) • y‖ := norm_add_le _ _
      _ = ‖p‖ + 1 / 2097152 * ‖y‖ := by
          rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
      _ < 1 := by nlinarith [norm_nonneg y]
  · change 0 < (frozenBallScaling p boundary_c2a_local_radius_pos y) (Fin.last 2)
    rw [frozenBallScaling_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hp3]
    positivity

/-- The similarity `y ↦ p + 2⁻²¹ • y` maps the closed unit half ball into the slab carrying the
C¹,α representative, and into the closed unit half ball. -/
lemma boundary_c2a_scaling_maps_slab {p : EuclideanSpace ℝ (Fin 3)}
    (hp3 : p (Fin.last 2) = 0) (hp : ‖p‖ ≤ 1 / 2) :
    MapsTo (frozenBallScaling p boundary_c2a_local_radius_pos) (closure (boundaryHalfBall 1))
      (boundaryC1Slab ∩ closure (boundaryHalfBall 1)) := by
  set e := frozenBallScaling p boundary_c2a_local_radius_pos
  have hsub : closure (boundaryHalfBall 1) ⊆ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    closure_minimal (inter_subset_left.trans ball_subset_closedBall) isClosed_closedBall
  intro y hy
  refine ⟨?_, ?_⟩
  · have hy1 : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.mp (hsub hy)
    have hy3 : |y (Fin.last 2)| ≤ ‖y‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le y (Fin.last 2)
    refine ⟨?_, ?_⟩
    · rw [mem_preimage, mem_ball_zero_iff]
      have hproj : ‖graphProjectionN 2 (e y)‖ ≤ ‖e y‖ := by
        have h := norm_sq_graphProjectionN (e y)
        nlinarith [norm_nonneg (e y), norm_nonneg (graphProjectionN 2 (e y)),
          sq_nonneg ((e y) (Fin.last 2))]
      calc ‖graphProjectionN 2 (e y)‖ ≤ ‖e y‖ := hproj
        _ ≤ ‖p‖ + ‖(1 / 2097152 : ℝ) • y‖ := by
            rw [frozenBallScaling_apply]
            exact norm_add_le _ _
        _ = ‖p‖ + 1 / 2097152 * ‖y‖ := by
            rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
        _ < 5 / 8 := by nlinarith [norm_nonneg y]
    · change |(e y) (Fin.last 2)| < 1 / 1048576
      rw [frozenBallScaling_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hp3,
        zero_add, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2097152)]
      nlinarith [abs_nonneg (y (Fin.last 2))]
  · have hc : Continuous e := (frozenBallScaling p boundary_c2a_local_radius_pos).continuous
    exact closure_mono (image_subset_iff.mpr (boundary_c2a_scaling_maps_halfBall hp3 hp))
      (image_closure_subset_closure_image hc ⟨y, hy, rfl⟩)

/-- A function C² on an open neighbourhood of the closed unit ball agrees, on a smaller open
neighbourhood, with a globally C² function (multiply by a smooth bump). This supplies the global
`ContDiff ℝ 1 φ` hypothesis of `boundary_c1_holder_slab_trace` from local data. -/
lemma boundary_c2a_exists_global_extension {φ : EuclideanSpace ℝ (Fin 3) → ℝ}
    {V : Set (EuclideanSpace ℝ (Fin 3))} (hV : IsOpen V)
    (hK : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 ⊆ V) (hφ : ContDiffOn ℝ 2 φ V) :
    ∃ φ' : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 2 φ' ∧
      ∃ O : Set (EuclideanSpace ℝ (Fin 3)), IsOpen O ∧
        closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 ⊆ O ∧ EqOn φ' φ O := by
  obtain ⟨δ, hδ, hδV⟩ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1).exists_thickening_subset_open hV hK
  rw [thickening_closedBall hδ zero_le_one, add_comm] at hδV
  let χ : ContDiffBump (0 : EuclideanSpace ℝ (Fin 3)) :=
    ⟨1 + δ / 3, 1 + δ / 2, by positivity, by linarith⟩
  refine ⟨fun x => χ x * φ x, ?_, ball 0 (1 + δ / 3), isOpen_ball, ?_, ?_⟩
  · refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hx : x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) (1 + δ)
    · exact (χ.contDiff.contDiffAt).mul (hφ.contDiffAt (hV.mem_nhds (hδV hx)))
    · have hO : IsOpen (closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 + δ / 2))ᶜ :=
        isClosed_closedBall.isOpen_compl
      have hxO : x ∈ (closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 + δ / 2))ᶜ := by
        intro hc
        apply hx
        rw [mem_ball]
        rw [mem_closedBall] at hc
        linarith
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [hO.mem_nhds hxO] with y hy
      have hy' : χ.rOut ≤ dist y 0 := by
        rw [mem_compl_iff, mem_closedBall, not_le] at hy
        exact hy.le
      rw [χ.zero_of_le_dist hy', zero_mul]
  · exact closedBall_subset_ball (by linarith)
  · intro x hx
    have hx' : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) χ.rIn := ball_subset_closedBall hx
    change χ x * φ x = φ x
    rw [χ.one_of_mem_closedBall hx', one_mul]

/-- Finite Hölder norm from pointwise bounds. -/
lemma boundary_c2a_holder_of_bounds {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {α A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) {f : E → F} {U : Set E}
    (hf : ∀ x ∈ U, ‖f x‖ ≤ A) (hh : ∀ x ∈ U, ∀ y ∈ U, ‖f x - f y‖ ≤ B * ‖x - y‖ ^ α) :
    HasFiniteHolderNormOn α f U ∧ holderNorm α f U ≤ A + B := by
  have hq : ∀ x ∈ U, ∀ y ∈ U, ‖f x - f y‖ / ‖x - y‖ ^ α ≤ B := by
    intro x hx y hy
    by_cases he : x = y
    · subst he
      simp [hB]
    · rw [div_le_iff₀ (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr he)) α)]
      exact hh x hx y hy
  exact ⟨HasFiniteHolderNormOn.of_bounds hA hB hf hq, holderNorm_le hA hB hf hq⟩

/-- The similarity `y ↦ p + 2⁻²¹ • y` maps the closed unit ball into the C¹ slab. -/
lemma boundary_c2a_scaling_maps_closedBall_slab {p : EuclideanSpace ℝ (Fin 3)}
    (hp3 : p (Fin.last 2) = 0) (hp : ‖p‖ ≤ 1 / 2) :
    MapsTo (frozenBallScaling p boundary_c2a_local_radius_pos) (closedBall 0 1)
      boundaryC1Slab := by
  set e := frozenBallScaling p boundary_c2a_local_radius_pos
  intro y hy
  have hy1 : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.mp hy
  have hy3 : |y (Fin.last 2)| ≤ ‖y‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le y (Fin.last 2)
  refine ⟨?_, ?_⟩
  · rw [mem_preimage, mem_ball_zero_iff]
    have hproj : ‖graphProjectionN 2 (e y)‖ ≤ ‖e y‖ := by
      have h := norm_sq_graphProjectionN (e y)
      nlinarith [norm_nonneg (e y), norm_nonneg (graphProjectionN 2 (e y)),
        sq_nonneg ((e y) (Fin.last 2))]
    calc ‖graphProjectionN 2 (e y)‖ ≤ ‖e y‖ := hproj
      _ ≤ ‖p‖ + ‖(1 / 2097152 : ℝ) • y‖ := by
          rw [frozenBallScaling_apply]
          exact norm_add_le _ _
      _ = ‖p‖ + 1 / 2097152 * ‖y‖ := by
          rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
      _ < 5 / 8 := by nlinarith [norm_nonneg y]
  · change |(e y) (Fin.last 2)| < 1 / 1048576
    rw [frozenBallScaling_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hp3,
      zero_add, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2097152)]
    nlinarith [abs_nonneg (y (Fin.last 2))]

/-- The rescaled C¹ representative `w = v ∘ e` is C¹,α on the closed unit half ball, with norm
bounded by the sup of the trace, the gradient bound and the gradient Hölder constant. -/
theorem boundary_c2a_rescaled_c1Holder {α C P N₀ : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hC : 0 ≤ C) (hP : 0 ≤ P) (hN₀ : 0 ≤ N₀)
    {v φ : EuclideanSpace ℝ (Fin 3) → ℝ} {W : Set (EuclideanSpace ℝ (Fin 3))}
    {p : EuclideanSpace ℝ (Fin 3)} (hp3 : p (Fin.last 2) = 0) (hp : ‖p‖ ≤ 1 / 2)
    (hW : IsOpen W) (hslab : boundaryC1Slab ⊆ W) (hv : ContDiffOn ℝ 1 v W)
    (hvP : ∀ x ∈ W, ‖gradient v x‖ ≤ P)
    (hvC : ∀ x ∈ W, ∀ y ∈ W, ‖gradient v x - gradient v y‖ ≤ C * dist x y ^ α)
    (htr : ∀ x ∈ W, x (Fin.last 2) = 0 → v x = φ x)
    (hφ : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, |φ x| ≤ N₀) :
    HasC1HolderOn α (v ∘ frozenBallScaling p boundary_c2a_local_radius_pos)
        (closure (boundaryHalfBall 1)) ∧
      nondivC1HolderNorm α (v ∘ frozenBallScaling p boundary_c2a_local_radius_pos)
        (closure (boundaryHalfBall 1)) ≤ (N₀ + P + 2 * P) + (P + C) := by
  set r : ℝ := 1 / 2097152 with hr_def
  set e := frozenBallScaling p boundary_c2a_local_radius_pos
  set U := closure (boundaryHalfBall 1)
  have hr0 : 0 < r := boundary_c2a_local_radius_pos
  have hr1 : r ≤ 1 := by norm_num [hr_def]
  have hsub : U ⊆ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    closure_minimal (inter_subset_left.trans ball_subset_closedBall) isClosed_closedBall
  have hmB : MapsTo e (closedBall 0 1) W := fun y hy =>
    hslab (boundary_c2a_scaling_maps_closedBall_slab hp3 hp hy)
  have hdv : ∀ x ∈ W, DifferentiableAt ℝ v x := fun x hx =>
    (hv.contDiffAt (hW.mem_nhds hx)).differentiableAt one_ne_zero
  have hnorm : ∀ x, ‖fderiv ℝ v x‖ = ‖gradient v x‖ := by
    intro x
    change ‖fderiv ℝ v x‖ = ‖(InnerProductSpace.toDual ℝ _).symm (fderiv ℝ v x)‖
    rw [LinearIsometryEquiv.norm_map]
  have hnorm2 : ∀ x y, ‖fderiv ℝ v x - fderiv ℝ v y‖ = ‖gradient v x - gradient v y‖ := by
    intro x y
    change ‖fderiv ℝ v x - fderiv ℝ v y‖ = ‖(InnerProductSpace.toDual ℝ _).symm (fderiv ℝ v x) -
      (InnerProductSpace.toDual ℝ _).symm (fderiv ℝ v y)‖
    rw [← map_sub, LinearIsometryEquiv.norm_map]
  have hfd : ∀ y, fderiv ℝ (v ∘ e) y = r • fderiv ℝ v (e y) := fun y =>
    boundary_c2a_fderiv_comp_scaling p y boundary_c2a_local_radius_pos v
  have hec : ContDiff ℝ 1 e := contDiff_const.add (contDiff_id.const_smul r)
  have hdw : ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, DifferentiableAt ℝ (v ∘ e) y :=
    fun y hy => (hdv _ (hmB hy)).comp y (hec.differentiable one_ne_zero y)
  have hbw : ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, ‖fderiv ℝ (v ∘ e) y‖ ≤ r * P := by
    intro y hy
    rw [hfd, norm_smul, Real.norm_of_nonneg hr0.le, hnorm]
    exact mul_le_mul_of_nonneg_left (hvP _ (hmB hy)) hr0.le
  have hmvt : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1,
      ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1,
      ‖(v ∘ e) x - (v ∘ e) y‖ ≤ r * P * ‖x - y‖ := fun x hx y hy =>
    (convex_closedBall 0 1).norm_image_sub_le_of_norm_fderiv_le hdw hbw hy hx
  have h0 : (0 : EuclideanSpace ℝ (Fin 3)) ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    mem_closedBall_self zero_le_one
  have he0 : e 0 = p := by rw [frozenBallScaling_apply, smul_zero, add_zero]
  have hw0 : |(v ∘ e) 0| ≤ N₀ := by
    have hpW : e 0 ∈ W := hmB h0
    rw [he0] at hpW
    rw [Function.comp_apply, he0, htr p hpW hp3]
    exact hφ p (mem_closedBall_zero_iff.mpr (hp.trans (by norm_num)))
  have hfun : ∀ x ∈ U, ‖(v ∘ e) x‖ ≤ N₀ + P := by
    intro x hx
    have hxB := hsub hx
    have h1 := hmvt x hxB 0 h0
    rw [sub_zero] at h1
    have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hxB
    have h2 : r * P * ‖x‖ ≤ P := by
      calc r * P * ‖x‖ ≤ 1 * P * 1 := by gcongr
        _ = P := by ring
    rw [Real.norm_eq_abs] at h1 ⊢
    have := abs_sub_abs_le_abs_sub ((v ∘ e) x) ((v ∘ e) 0)
    linarith
  have hkey : ∀ d : ℝ, 0 ≤ d → d ≤ 2 → d ≤ 2 * d ^ α := by
    intro d hd0 hd2
    rcases eq_or_lt_of_le hd0 with h | h
    · rw [← h]
      positivity
    · have h1 : d = d ^ α * d ^ (1 - α) := by
        rw [← Real.rpow_add h, add_sub_cancel, Real.rpow_one]
      have h2 : d ^ (1 - α) ≤ 2 := by
        calc d ^ (1 - α) ≤ 2 ^ (1 - α) := Real.rpow_le_rpow h.le hd2 (by linarith)
          _ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 2 := Real.rpow_one 2
      calc d = d ^ α * d ^ (1 - α) := h1
        _ ≤ d ^ α * 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 2 * d ^ α := mul_comm _ _
  have hfunH : ∀ x ∈ U, ∀ y ∈ U, ‖(v ∘ e) x - (v ∘ e) y‖ ≤ 2 * P * ‖x - y‖ ^ α := by
    intro x hx y hy
    have hxB := hsub hx
    have hyB := hsub hy
    have hd2 : ‖x - y‖ ≤ 2 := by
      have := norm_sub_le x y
      have := mem_closedBall_zero_iff.mp hxB
      have := mem_closedBall_zero_iff.mp hyB
      linarith
    calc ‖(v ∘ e) x - (v ∘ e) y‖ ≤ r * P * ‖x - y‖ := hmvt x hxB y hyB
      _ ≤ 1 * P * (2 * ‖x - y‖ ^ α) := by
          gcongr
          exact hkey _ (norm_nonneg _) hd2
      _ = 2 * P * ‖x - y‖ ^ α := by ring
  have hder : ∀ x ∈ U, ‖fderiv ℝ (v ∘ e) x‖ ≤ P := fun x hx =>
    (hbw x (hsub hx)).trans ((mul_le_mul_of_nonneg_right hr1 hP).trans_eq (one_mul P))
  have hderH : ∀ x ∈ U, ∀ y ∈ U,
      ‖fderiv ℝ (v ∘ e) x - fderiv ℝ (v ∘ e) y‖ ≤ C * ‖x - y‖ ^ α := by
    intro x hx y hy
    rw [hfd, hfd, ← smul_sub, norm_smul, Real.norm_of_nonneg hr0.le, hnorm2]
    have hdist : dist (e x) (e y) ≤ ‖x - y‖ := by
      rw [quasilinear_ballScaling_dist p x y hr0, dist_eq_norm]
      exact (mul_le_mul_of_nonneg_right hr1 (norm_nonneg _)).trans_eq (one_mul _)
    calc r * ‖gradient v (e x) - gradient v (e y)‖ ≤ 1 * (C * dist (e x) (e y) ^ α) :=
          mul_le_mul hr1 (hvC _ (hmB (hsub hx)) _ (hmB (hsub hy))) (norm_nonneg _) zero_le_one
      _ ≤ C * ‖x - y‖ ^ α := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow dist_nonneg hdist hα.le) hC
  obtain ⟨hF1, hF2⟩ := boundary_c2a_holder_of_bounds (by positivity) (by positivity) hfun hfunH
  obtain ⟨hD1, hD2⟩ := boundary_c2a_holder_of_bounds hP hC hder hderH
  refine ⟨⟨hv.comp hec.contDiffOn (fun y hy => hmB (hsub hy)), hF1, hD1⟩, ?_⟩
  exact add_le_add hF2 hD2

/-- Multiplying by a constant in `[0, 1]` preserves C¹,α and does not increase the norm. -/
lemma boundary_c2a_c1Holder_const_smul {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {α : ℝ} {g : E → F} {S : Set E}
    (hg : HasC1HolderOn α g S) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    HasC1HolderOn α (fun y => c • g y) S ∧
      nondivC1HolderNorm α (fun y => c • g y) S ≤ nondivC1HolderNorm α g S := by
  have hfd : fderiv ℝ (fun y => c • g y) = fun y => c • fderiv ℝ g y := by
    funext y
    exact congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := g) c) y
  obtain ⟨h1, h1b⟩ := nondiv_holder_const_smul hg.function_holder c
  obtain ⟨h2, h2b⟩ := nondiv_holder_const_smul hg.derivative_holder c
  rw [Real.norm_of_nonneg hc] at h1b h2b
  refine ⟨⟨hg.contDiff.const_smul c, h1, by rw [hfd]; exact h2⟩, ?_⟩
  unfold nondivC1HolderNorm
  rw [hfd]
  have hn1 := hg.function_holder.norm_nonneg
  have hn2 := hg.derivative_holder.norm_nonneg
  calc _ ≤ c * holderNorm α g S + c * holderNorm α (fderiv ℝ g) S := add_le_add h1b h2b
    _ ≤ 1 * holderNorm α g S + 1 * holderNorm α (fderiv ℝ g) S :=
        add_le_add (mul_le_mul_of_nonneg_right hc1 hn1) (mul_le_mul_of_nonneg_right hc1 hn2)
    _ = holderNorm α g S + holderNorm α (fderiv ℝ g) S := by ring

end LiquidDrop
