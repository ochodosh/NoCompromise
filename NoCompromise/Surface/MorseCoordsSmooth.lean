import NoCompromise.Surface.MorseCoordsPlanar
import NoCompromise.Surface.MorseRadialIntegral

/-!
# The planar Morse lemma `lem:morse-coords` with smooth coordinates

`lem:morse-coords` as stated in the TeX: a function smooth near `0` in the plane, with
`g(0) = 0`, `Dg(0) = 0` and nondegenerate Hessian of index `λ`, is the model form
`eq:morse-normal-form` of index `λ` in smooth local coordinates (a chart which is `C^∞`
with `C^∞` inverse).

The route is that of the C¹ version in `NoCompromise.Surface.MorseCoordsPlanar`: the
coefficient field `morseB` of `eq:morse-B` is now smooth, hence so is the
completion-of-squares map, and a C¹ chart with C¹ inverse whose forward map is `C^∞` has a
`C^∞` inverse (the inverse function theorem in the form `OpenPartialHomeomorph.contDiffAt_symm`).
Smoothness of `morseB` is `contDiffOn_radial_integral` (`NoCompromise.Surface.MorseRadialIntegral`)
applied to the Hessian field with weight `1 - t`.
-/

noncomputable section

open Set Filter Metric
open scoped Topology

namespace LiquidDrop

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- `1 ≤ ∞` for the smoothness orders used in `lem:morse-coords`. -/
theorem one_le_smooth_order : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  WithTop.coe_le_coe.mpr le_top

/-- Inverse function theorem step of `lem:morse-coords`: if an open partial homeomorphism is
`C^n` (`n ≥ 1`) on its source and its inverse is C¹ on its target, then the inverse is `C^n`
on its target. The derivatives of the map and of its inverse are mutually inverse by the
chain rule, so `OpenPartialHomeomorph.contDiffAt_symm` applies at every point. -/
theorem contDiffOn_symm_of_contDiffOn_one {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : OpenPartialHomeomorph E F) {n : WithTop ℕ∞} (hn : n ≠ 0)
    (he : ContDiffOn ℝ n e e.source) (he1 : ContDiffOn ℝ 1 e.symm e.target) :
    ContDiffOn ℝ n e.symm e.target := by
  intro y hy
  have hx : e.symm y ∈ e.source := e.map_target hy
  have heC : ContDiffAt ℝ n e (e.symm y) := he.contDiffAt (e.open_source.mem_nhds hx)
  have hdiff : HasFDerivAt e (fderiv ℝ e (e.symm y)) (e.symm y) :=
    (heC.differentiableAt hn).hasFDerivAt
  have hsd : HasFDerivAt e.symm (fderiv ℝ e.symm y) y :=
    ((he1.contDiffAt (e.open_target.mem_nhds hy)).differentiableAt one_ne_zero).hasFDerivAt
  have hsd' : HasFDerivAt e.symm (fderiv ℝ e.symm y) (e (e.symm y)) := by
    rw [e.right_inv hy]; exact hsd
  have h1 : (fderiv ℝ e.symm y).comp (fderiv ℝ e (e.symm y)) = ContinuousLinearMap.id ℝ E := by
    have hcomp := hsd'.comp (e.symm y) hdiff
    have heq : e.symm ∘ e =ᶠ[𝓝 (e.symm y)] id := by
      filter_upwards [e.open_source.mem_nhds hx] with z hz using e.left_inv hz
    exact hcomp.unique ((hasFDerivAt_id _).congr_of_eventuallyEq heq)
  have h2 : (fderiv ℝ e (e.symm y)).comp (fderiv ℝ e.symm y) = ContinuousLinearMap.id ℝ F := by
    have hcomp := hdiff.comp y hsd
    have heq : e ∘ e.symm =ᶠ[𝓝 y] id := by
      filter_upwards [e.open_target.mem_nhds hy] with z hz using e.right_inv hz
    exact hcomp.unique ((hasFDerivAt_id _).congr_of_eventuallyEq heq)
  let A : E ≃L[ℝ] F := ContinuousLinearEquiv.equivOfInverse' _ _ h2 h1
  exact (e.contDiffAt_symm (f₀' := A) hy hdiff heC).contDiffWithinAt

/-- Restricting a C¹ chart with C¹ inverse to an open set on which the forward map is `C^n`
gives a chart which is `C^n` with `C^n` inverse (`lem:morse-coords`). -/
theorem exists_smoothChart_restrOpen {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : OpenPartialHomeomorph E F) {n : WithTop ℕ∞} (hn : n ≠ 0)
    (he1 : ContDiffOn ℝ 1 e.symm e.target) {W : Set E} (hW : IsOpen W)
    (heW : ContDiffOn ℝ n e W) :
    (e.restrOpen W hW).source = e.source ∩ W ∧ ⇑(e.restrOpen W hW) = e ∧
      ContDiffOn ℝ n (e.restrOpen W hW) (e.restrOpen W hW).source ∧
      ContDiffOn ℝ n (e.restrOpen W hW).symm (e.restrOpen W hW).target := by
  have hs : ContDiffOn ℝ n (e.restrOpen W hW) (e.restrOpen W hW).source := by
    rw [OpenPartialHomeomorph.coe_restrOpen, OpenPartialHomeomorph.restrOpen_source]
    exact heW.mono inter_subset_right
  have ht : (e.restrOpen W hW).target ⊆ e.target := fun y hy => hy.1
  refine ⟨rfl, rfl, hs, ?_⟩
  apply contDiffOn_symm_of_contDiffOn_one _ hn hs
  rw [OpenPartialHomeomorph.coe_restrOpen_symm]
  exact he1.mono ht

/-- The square-root chart of `lem:morse-coords` is `C^n` at any point where its coefficients
are `C^n` and its two pivots are nonzero. -/
theorem contDiffAt_morseSquareChart_at {n : ℕ∞} {a b d : E2 → ℝ} {x : E2}
    (ha : ContDiffAt ℝ n a x) (hb : ContDiffAt ℝ n b x) (hd : ContDiffAt ℝ n d x)
    (ha0 : a x ≠ 0) (hs0 : d x - b x ^ 2 / a x ≠ 0) :
    ContDiffAt ℝ n (morseSquareChart a b d) x := by
  have haS := (ha.abs ha0).sqrt (abs_ne_zero.mpr ha0)
  have hs := hd.sub ((hb.pow 2).div ha ha0)
  have hsS := (hs.abs hs0).sqrt (abs_ne_zero.mpr hs0)
  apply (contDiffAt_piLp 2).mpr
  intro i
  fin_cases i
  · exact haS.mul ((contDiffAt_piLp_apply 2).add
      ((hb.div ha ha0).mul (contDiffAt_piLp_apply 2)))
  · exact hsS.mul (contDiffAt_piLp_apply 2)

/-- The completion-of-squares map of `lem:morse-coords` supplies a local diffeomorphism which
is `C^∞` with `C^∞` inverse, with source inside `W`, whenever its coefficient functions are
`C^∞` on the open neighbourhood `W` of the origin and its two pivots at the origin are
nonzero. -/
theorem exists_morseSquareChart_smooth {a b d : E2 → ℝ} {W : Set E2} (hW : IsOpen W)
    (h0W : (0 : E2) ∈ W) (ha : ContDiffOn ℝ (⊤ : ℕ∞) a W) (hb : ContDiffOn ℝ (⊤ : ℕ∞) b W)
    (hd : ContDiffOn ℝ (⊤ : ℕ∞) d W) (ha0 : a 0 ≠ 0) (hs0 : d 0 - b 0 ^ 2 / a 0 ≠ 0) :
    ∃ e : OpenPartialHomeomorph E2 E2, (0 : E2) ∈ e.source ∧ e 0 = 0 ∧ e.source ⊆ W ∧
      ContDiffOn ℝ (⊤ : ℕ∞) e e.source ∧ ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target ∧
      (e : E2 → E2) = morseSquareChart a b d := by
  have hW0 := hW.mem_nhds h0W
  obtain ⟨e₁, h0, he0, -, h1iC, hcoe⟩ := exists_morseSquareChart
    ((ha.contDiffAt hW0).of_le one_le_smooth_order)
    ((hb.contDiffAt hW0).of_le one_le_smooth_order)
    ((hd.contDiffAt hW0).of_le one_le_smooth_order) ha0 hs0
  let W₁ : Set E2 := W ∩ a ⁻¹' {0}ᶜ
  have hW₁ : IsOpen W₁ := ha.continuousOn.isOpen_inter_preimage hW isOpen_compl_singleton
  let s : E2 → ℝ := fun x => d x - b x ^ 2 / a x
  have hsc : ContinuousOn s W₁ :=
    (hd.continuousOn.mono inter_subset_left).sub
      (((hb.continuousOn.mono inter_subset_left).pow 2).div
        (ha.continuousOn.mono inter_subset_left) fun x hx => hx.2)
  let W₂ : Set E2 := W₁ ∩ s ⁻¹' {0}ᶜ
  have hW₂ : IsOpen W₂ := hsc.isOpen_inter_preimage hW₁ isOpen_compl_singleton
  have h0W₂ : (0 : E2) ∈ W₂ := ⟨⟨h0W, ha0⟩, hs0⟩
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞) e₁ W₂ := by
    rw [hcoe]
    intro x hx
    have hxW : W ∈ 𝓝 x := hW.mem_nhds hx.1.1
    exact (contDiffAt_morseSquareChart_at (ha.contDiffAt hxW) (hb.contDiffAt hxW)
      (hd.contDiffAt hxW) hx.1.2 hx.2).contDiffWithinAt
  obtain ⟨hsrc, hcoe', hC, hiC⟩ :=
    exists_smoothChart_restrOpen e₁ (by simp) h1iC hW₂ hsm
  refine ⟨e₁.restrOpen W₂ hW₂, ?_, ?_, ?_, hC, hiC, ?_⟩
  · rw [hsrc]; exact ⟨h0, h0W₂⟩
  · rw [hcoe']; exact he0
  · rw [hsrc]; exact fun x hx => hx.2.1.1
  · rw [hcoe', hcoe]

/-- A pair of `C^∞` conditions for an open partial homeomorphism of the plane and its
inverse: smooth local coordinates in `lem:morse-coords`. -/
def IsMorseSmoothChart (e : OpenPartialHomeomorph E2 E2) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) e e.source ∧ ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target

/-- Composition preserves smooth charts (`lem:morse-coords`). -/
theorem IsMorseSmoothChart.trans {e₁ e₂ : OpenPartialHomeomorph E2 E2}
    (h1 : IsMorseSmoothChart e₁) (h2 : IsMorseSmoothChart e₂) :
    IsMorseSmoothChart (e₁.trans e₂) := by
  refine ⟨?_, ?_⟩
  · rw [OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_source]
    exact h2.1.comp (h1.1.mono inter_subset_left) (fun x hx => hx.2)
  · rw [OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.trans_target]
    exact h1.2.comp (h2.2.mono inter_subset_left) (fun x hx => hx.2)

/-- A continuous linear isomorphism is a smooth chart (`lem:morse-coords`). -/
theorem isMorseSmoothChart_linearEquiv (L : E2 ≃L[ℝ] E2) :
    IsMorseSmoothChart L.toHomeomorph.toOpenPartialHomeomorph := by
  refine ⟨?_, ?_⟩
  · simpa using L.contDiff.contDiffOn
  · simpa using L.symm.contDiff.contDiffOn

/-- The identity on an open set is a smooth chart (`lem:morse-coords`). -/
theorem isMorseSmoothChart_ofSet {W : Set E2} (hW : IsOpen W) :
    IsMorseSmoothChart (OpenPartialHomeomorph.ofSet W hW) := by
  refine ⟨?_, ?_⟩
  · simpa using contDiffOn_id
  · simpa using contDiffOn_id

/-- Assembly of the smooth chart in `lem:morse-coords` from a linear change of coordinates
`L`, a smooth chart `eφ`, an open set `W` and a final linear map `P`. The source of the
assembled chart lies in any set `U` containing `L '' W`. -/
theorem morse_chart_assembly_smooth {g : E2 → ℝ} {k : ℕ} (L P : E2 ≃L[ℝ] E2)
    (eφ : OpenPartialHomeomorph E2 E2) (h0φ : (0 : E2) ∈ eφ.source) (heφ0 : eφ 0 = 0)
    (hφ : IsMorseSmoothChart eφ) {W U : Set E2} (hWo : IsOpen W) (hW0 : (0 : E2) ∈ W)
    (hWU : ∀ u ∈ W, L u ∈ U)
    (hform : ∀ u ∈ W, u ∈ eφ.source → g (L u) = morseModel k (P (eφ u))) :
    ∃ e : OpenPartialHomeomorph E2 E2, (0 : E2) ∈ e.source ∧ e 0 = 0 ∧ e.source ⊆ U ∧
      ContDiffOn ℝ (⊤ : ℕ∞) e e.source ∧ ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target ∧
      ∀ x ∈ e.source, g x = morseModel k (e x) := by
  let e := ((L.symm.toHomeomorph.toOpenPartialHomeomorph.trans
    (OpenPartialHomeomorph.ofSet W hWo)).trans eφ).trans P.toHomeomorph.toOpenPartialHomeomorph
  have hC : IsMorseSmoothChart e :=
    (((isMorseSmoothChart_linearEquiv _).trans (isMorseSmoothChart_ofSet hWo)).trans hφ).trans
      (isMorseSmoothChart_linearEquiv _)
  have happ : ∀ x, e x = P (eφ (L.symm x)) := fun x => rfl
  have hsrc : ∀ x ∈ e.source, L.symm x ∈ W ∧ L.symm x ∈ eφ.source := by
    intro x hx
    simp only [e, mfld_simps] at hx
    exact ⟨hx.1, hx.2⟩
  refine ⟨e, ?_, ?_, ?_, hC.1, hC.2, ?_⟩
  · simp only [e, mfld_simps]
    simpa using ⟨hW0, h0φ⟩
  · rw [happ]
    simp [heφ0]
  · intro x hx
    simpa using hWU _ (hsrc x hx).1
  · intro x hx
    obtain ⟨h1, h2⟩ := hsrc x hx
    have := hform _ h1 h2
    rw [happ]
    simpa using this

set_option maxHeartbeats 1600000 in
-- The assembly repeats the long case analysis of `exists_morse_coords`.
/-- `lem:morse-coords` with smooth coordinates, given smoothness of the coefficient field
`morseB g` of `eq:morse-B` on the open neighbourhood `U` of the origin on which `g` is smooth:
there is a chart which is `C^∞` with `C^∞` inverse, with source in `U`, sending the origin to
itself, in which `g` is the model form `eq:morse-normal-form` of the index of its Hessian. -/
theorem exists_morse_coords_smooth_of_morseB {g : E2 → ℝ} {U : Set E2} (hU : IsOpen U)
    (h0U : (0 : E2) ∈ U) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U)
    (hBs : ContDiffOn ℝ (⊤ : ℕ∞) (morseB g) U) (h0 : g 0 = 0) (hd : fderiv ℝ g 0 = 0)
    (hnd : IsNondegenerateForm (fun v w : E2 => fderiv ℝ (fderiv ℝ g) 0 v w)) :
    ∃ e : OpenPartialHomeomorph E2 E2, (0 : E2) ∈ e.source ∧ e 0 = 0 ∧ e.source ⊆ U ∧
      ContDiffOn ℝ (⊤ : ℕ∞) e e.source ∧ ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target ∧
      ∀ x ∈ e.source,
        g x = morseModel (formIndex (fun v w : E2 => fderiv ℝ (fderiv ℝ g) 0 v w)) (e x) := by
  have hg3 : ContDiffAt ℝ 3 g 0 :=
    (hg.contDiffAt (hU.mem_nhds h0U)).of_le
      (show ((3 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from
        WithTop.coe_le_coe.mpr le_top)
  obtain ⟨R, hR, -, hB0, hBx⟩ := exists_morseB hg3 h0 hd
  set H := fderiv ℝ (fderiv ℝ g) 0 with hHdef
  have hHs : ∀ v w : E2, H v w = H w v := by
    intro v w
    rw [← hB0]
    exact (hBx 0 (mem_ball_self hR)).2 v w
  obtain ⟨v, hv⟩ : ∃ v : E2, H v v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hz : ∀ X Y : E2, H X Y = 0 := by
      intro X Y
      have h := hcon (X + Y)
      simp only [map_add, add_apply, hcon X, hcon Y, hHs Y X] at h
      linarith
    have h1 := hnd (EuclideanSpace.single 0 1) (hz _)
    have h2 := congrArg (fun y : E2 => y 0) h1
    simp at h2
  have hdet : v 0 * v 0 - -v 1 * v 1 ≠ 0 := by
    intro h
    have h0' : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    have h1' : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    apply hv
    have : v = 0 := by
      ext i
      fin_cases i
      · simpa using h0'
      · simpa using h1'
    simp [this]
  set L := morsePlaneEquiv (v 0) (-v 1) (v 1) (v 0) hdet with hLdef
  have hLe0 : L (EuclideanSpace.single 0 1) = v := by
    ext i
    fin_cases i <;> simp [L, morsePlaneEquiv_apply]
  let e0 : E2 := EuclideanSpace.single 0 1
  let e1 : E2 := EuclideanSpace.single 1 1
  let Q : E2 → E2 →L[ℝ] E2 →L[ℝ] ℝ := fun u =>
    (1 / 2 : ℝ) • (morseB g (L u)).bilinearComp (L : E2 →L[ℝ] E2) (L : E2 →L[ℝ] E2)
  have hQ : ∀ u w w' : E2, Q u w w' = 1 / 2 * morseB g (L u) (L w) (L w') := by
    intro u w w'
    simp [Q]
  let A : E2 → ℝ := fun u => Q u e0 e0
  let Bc : E2 → ℝ := fun u => Q u e0 e1
  let D : E2 → ℝ := fun u => Q u e1 e1
  let s : E2 → ℝ := fun u => D u - Bc u ^ 2 / A u
  let W₀ : Set E2 := L ⁻¹' U
  have hW₀ : IsOpen W₀ := hU.preimage L.continuous
  have h0W₀ : (0 : E2) ∈ W₀ := by
    change L 0 ∈ U
    rw [map_zero]; exact h0U
  have hBL : ContDiffOn ℝ (⊤ : ℕ∞) (fun u => morseB g (L u)) W₀ :=
    hBs.comp L.contDiff.contDiffOn (fun u hu => hu)
  have hcoef : ∀ w w' : E2, ContDiffOn ℝ (⊤ : ℕ∞) (fun u => Q u w w') W₀ := by
    intro w w'
    have : (fun u => Q u w w') = fun u => 1 / 2 * morseB g (L u) (L w) (L w') :=
      funext fun u => hQ u w w'
    rw [this]
    exact contDiffOn_const.mul ((hBL.clm_apply contDiffOn_const).clm_apply contDiffOn_const)
  have hcoefc : ∀ w w' : E2, ContinuousAt (fun u => Q u w w') 0 := fun w w' =>
    (hcoef w w').continuousOn.continuousAt (hW₀.mem_nhds h0W₀)
  have hQ0 : ∀ x y : E2, Q 0 x y = 1 / 2 * H (L x) (L y) := by
    intro x y
    rw [hQ, map_zero, hB0]
  have hQ0s : ∀ x y : E2, Q 0 x y = Q 0 y x := by
    intro x y
    rw [hQ0, hQ0, hHs]
  have hexp : ∀ x y : E2, Q 0 x y =
      A 0 * x 0 * y 0 + Bc 0 * (x 0 * y 1 + x 1 * y 0) + D 0 * x 1 * y 1 :=
    morse_bilinear_expansion₂ (Q 0) hQ0s
  have hA0 : A 0 ≠ 0 := by
    have : A 0 = 1 / 2 * H v v := by
      change Q 0 e0 e0 = _
      rw [hQ0, hLe0]
    rw [this]
    exact mul_ne_zero (by norm_num) hv
  have hnd' : IsNondegenerateForm (fun x y : E2 => H (L x) (L y)) :=
    (isNondegenerateForm_comp_linearEquiv L.toLinearEquiv (fun v w : E2 => H v w)).mpr hnd
  have hs0 : s 0 ≠ 0 := by
    intro hs
    let w : E2 := WithLp.toLp 2 ![-(Bc 0) / A 0, 1]
    have hw0 : w 0 = -(Bc 0) / A 0 := rfl
    have hw1 : w 1 = 1 := rfl
    have key : A 0 * (-(Bc 0) / A 0) = -(Bc 0) := by field_simp
    have hw : w = 0 := hnd' w (fun Y => by
      have h : Q 0 w Y = 0 := by
        rw [hexp, hw0, hw1]
        linear_combination Y 1 * hs + Y 0 * key
      rw [hQ0] at h
      linarith)
    have h1 : w 1 = 0 := by rw [hw]; simp
    rw [hw1] at h1
    exact one_ne_zero h1
  obtain ⟨eφ, h0φ, heφ0, -, hφC, hφiC, hφeq⟩ :=
    exists_morseSquareChart_smooth hW₀ h0W₀ (hcoef e0 e0) (hcoef e0 e1) (hcoef e1 e1) hA0 hs0
  have hAc : ContinuousAt A 0 := hcoefc e0 e0
  have hsc : ContinuousAt s 0 :=
    (hcoefc e1 e1).sub (((hcoefc e0 e1).pow 2).div hAc hA0)
  have hev1 : ∀ᶠ u in 𝓝 (0 : E2), L u ∈ ball (0 : E2) R :=
    L.continuous.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact ball_mem_nhds 0 hR)
  have hev : ∀ᶠ u in 𝓝 (0 : E2), (L u ∈ ball (0 : E2) R ∧ L u ∈ U) ∧ A u ≠ 0 ∧
      Real.sign (A u) = Real.sign (A 0) ∧ Real.sign (s u) = Real.sign (s 0) :=
    (hev1.and (hW₀.mem_nhds h0W₀)).and ((hAc.eventually_ne hA0).and
      ((eventually_sign_eq_of_ne hAc hA0).and (eventually_sign_eq_of_ne hsc hs0)))
  obtain ⟨W, hWP, hWo, hW0⟩ := _root_.eventually_nhds_iff.mp hev
  have hWU : ∀ u ∈ W, L u ∈ U := fun u hu => (hWP u hu).1.2
  have hform : ∀ u ∈ W, g (L u) =
      Real.sign (A 0) * (eφ u 0) ^ 2 + Real.sign (s 0) * (eφ u 1) ^ 2 := by
    intro u hu
    obtain ⟨⟨hLu, -⟩, hAu, hsA, hss⟩ := hWP u hu
    obtain ⟨hgx, hsym⟩ := hBx (L u) hLu
    have hQs : ∀ x y : E2, Q u x y = Q u y x := by
      intro x y
      rw [hQ, hQ, hsym]
    have h1 := morse_bilinear_expansion (Q u) hQs u
    have h2 := morseSquareChart_identity A Bc D u hAu
    have h3 : g (L u) = Q u u u := by rw [hgx, hQ]
    rw [h3, h1, hφeq, ← hsA, ← hss]
    exact h2
  have hquad : ∀ w : E2, H (L w) (L w) =
      2 * (A 0 * (w 0 + Bc 0 / A 0 * w 1) ^ 2 + s 0 * w 1 ^ 2) := by
    intro w
    have h := hexp w w
    rw [hQ0] at h
    rw [← morse_complete_square _ _ _ _ _ hA0]
    linear_combination 2 * h
  have hk : formIndex (fun v w : E2 => H v w) = formIndex (fun x y : E2 => H (L x) (L y)) :=
    (formIndex_comp_linearEquiv L.toLinearEquiv (fun v w : E2 => H v w)).symm
  have hsc2 : ∀ (c : ℝ) (x : E2), H (L (c • x)) (L (c • x)) = c ^ 2 * H (L x) (L x) := by
    intro c x
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  let wn : E2 := WithLp.toLp 2 ![-(Bc 0) / A 0, 1]
  let wp : E2 := WithLp.toLp 2 ![1, 0]
  have hwn : H (L wn) (L wn) = 2 * s 0 := by
    rw [hquad]
    have h0' : wn 0 = -(Bc 0) / A 0 := rfl
    have h1' : wn 1 = 1 := rfl
    rw [h0', h1']
    ring
  have hwp : H (L wp) (L wp) = 2 * A 0 := by
    rw [hquad]
    have h0' : wp 0 = 1 := rfl
    have h1' : wp 1 = 0 := rfl
    rw [h0', h1']
    ring
  have hfin : Module.finrank ℝ E2 = 2 := finrank_euclideanSpace_fin
  let swap : E2 ≃L[ℝ] E2 := morsePlaneEquiv 0 1 1 0 (by norm_num)
  have hswap0 : ∀ y : E2, swap y 0 = y 1 := fun y => by
    simp [swap, morsePlaneEquiv_apply]
  have hswap1 : ∀ y : E2, swap y 1 = y 0 := fun y => by
    simp [swap, morsePlaneEquiv_apply]
  rcases hA0.lt_or_gt with ha | ha <;> rcases hs0.lt_or_gt with hs | hs
  · have hi : formIndex (fun v w : E2 => H v w) = 2 := by
      rw [hk, formIndex_eq_finrank_of_neg, hfin]
      intro x hx
      rw [hquad]
      have := morse_quad_pos (Bc 0 / A 0) (neg_pos.mpr ha) (neg_pos.mpr hs) hx
      linarith
    refine morse_chart_assembly_smooth L (ContinuousLinearEquiv.refl ℝ E2) eφ h0φ heφ0
      ⟨hφC, hφiC⟩ hWo hW0 hWU ?_
    intro u hu _
    rw [hi, hform u hu, Real.sign_of_neg ha, Real.sign_of_neg hs]
    simp [morseModel]
    ring
  · have hi : formIndex (fun v w : E2 => H v w) = 1 := by
      rw [hk]
      exact formIndex_eq_one_of_mixed_form _ hfin hsc2 ⟨wp, by rw [hwp]; linarith⟩
        ⟨wn, by rw [hwn]; linarith⟩
    refine morse_chart_assembly_smooth L swap eφ h0φ heφ0 ⟨hφC, hφiC⟩ hWo hW0 hWU ?_
    intro u hu _
    rw [hi, hform u hu, Real.sign_of_neg ha, Real.sign_of_pos hs]
    simp only [morseModel, hswap0, hswap1]
    norm_num
    ring
  · have hi : formIndex (fun v w : E2 => H v w) = 1 := by
      rw [hk]
      exact formIndex_eq_one_of_mixed_form _ hfin hsc2 ⟨wn, by rw [hwn]; linarith⟩
        ⟨wp, by rw [hwp]; linarith⟩
    refine morse_chart_assembly_smooth L (ContinuousLinearEquiv.refl ℝ E2) eφ h0φ heφ0
      ⟨hφC, hφiC⟩ hWo hW0 hWU ?_
    intro u hu _
    rw [hi, hform u hu, Real.sign_of_pos ha, Real.sign_of_neg hs]
    simp [morseModel]
    ring
  · have hi : formIndex (fun v w : E2 => H v w) = 0 := by
      rw [hk]
      apply formIndex_eq_zero_of_pos
      intro x hx
      rw [hquad]
      have := morse_quad_pos (Bc 0 / A 0) ha hs hx
      linarith
    refine morse_chart_assembly_smooth L (ContinuousLinearEquiv.refl ℝ E2) eφ h0φ heφ0
      ⟨hφC, hφiC⟩ hWo hW0 hWU ?_
    intro u hu _
    rw [hi, hform u hu, Real.sign_of_pos ha, Real.sign_of_pos hs]
    simp [morseModel]

/-- `eq:morse-B` in `lem:morse-coords` with smooth data: if `g` is `C^∞` on the ball `B(0,R)`,
then so is the coefficient field `B(x) = 2 ∫₀¹ (1 - t) D²g(t x) dt`. -/
theorem contDiffOn_morseB {g : E2 → ℝ} {R : ℝ} (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (ball 0 R)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (morseB g) (ball 0 R) := by
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ g) (ball 0 R) :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen isOpen_ball).mp hg).2
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (fderiv ℝ g)) (ball 0 R) :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen isOpen_ball).mp h1).2
  have hI := contDiffOn_radial_integral (φ := fun t : ℝ => 1 - t)
    (continuous_const.sub continuous_id) h2
  exact hI.const_smul (2 : ℝ)

/-- `lem:morse-coords` (smooth local coordinates): let `g` be `C^∞` on an open neighbourhood `U`
of `0` in the plane with `g(0) = 0`, `Dg(0) = 0` and `D²g(0)` nondegenerate. Then there is a
chart `e`, `C^∞` with `C^∞` inverse, with `0 ∈ e.source ⊆ U` and `e(0) = 0`, in which `g` is
the model form `eq:morse-normal-form` of the index of `D²g(0)`. -/
theorem exists_morse_coords_smooth {g : E2 → ℝ} {U : Set E2} (hU : IsOpen U)
    (h0U : (0 : E2) ∈ U) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U) (h0 : g 0 = 0)
    (hd : fderiv ℝ g 0 = 0)
    (hnd : IsNondegenerateForm (fun v w : E2 => fderiv ℝ (fderiv ℝ g) 0 v w)) :
    ∃ e : OpenPartialHomeomorph E2 E2, (0 : E2) ∈ e.source ∧ e 0 = 0 ∧ e.source ⊆ U ∧
      ContDiffOn ℝ (⊤ : ℕ∞) e e.source ∧ ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target ∧
      ∀ x ∈ e.source,
        g x = morseModel (formIndex (fun v w : E2 => fderiv ℝ (fderiv ℝ g) 0 v w)) (e x) := by
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU 0 h0U
  have hgR : ContDiffOn ℝ (⊤ : ℕ∞) g (ball 0 R) := hg.mono hRU
  obtain ⟨e, h1, h2, h3, h4, h5, h6⟩ := exists_morse_coords_smooth_of_morseB isOpen_ball
    (mem_ball_self hR) hgR (contDiffOn_morseB hgR) h0 hd hnd
  exact ⟨e, h1, h2, h3.trans hRU, h4, h5, h6⟩

/-- `lem:morse-coords` with the normal form `eq:morse-normal-form` written out case by case:
for `g` smooth near `0` with `g(0) = 0`, `Dg(0) = 0` and `D²g(0)` nondegenerate of index
`λ ≤ 2`, there are smooth local coordinates `(x₁, x₂) = (e x 0, e x 1)` in which
`g = x₁² + x₂²` (`λ = 0`), `g = x₁² - x₂²` (`λ = 1`), `g = -x₁² - x₂²` (`λ = 2`). -/
theorem exists_morse_coords_smooth_normal_form {g : E2 → ℝ} {U : Set E2} (hU : IsOpen U)
    (h0U : (0 : E2) ∈ U) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U) (h0 : g 0 = 0)
    (hd : fderiv ℝ g 0 = 0)
    (hnd : IsNondegenerateForm (fun v w : E2 => fderiv ℝ (fderiv ℝ g) 0 v w)) :
    formIndex (fun v w : E2 => fderiv ℝ (fderiv ℝ g) 0 v w) ≤ 2 ∧
    ∃ e : OpenPartialHomeomorph E2 E2, (0 : E2) ∈ e.source ∧ e 0 = 0 ∧ e.source ⊆ U ∧
      ContDiffOn ℝ (⊤ : ℕ∞) e e.source ∧ ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target ∧
      (formIndex (fun v w : E2 => fderiv ℝ (fderiv ℝ g) 0 v w) = 0 →
        ∀ x ∈ e.source, g x = e x 0 ^ 2 + e x 1 ^ 2) ∧
      (formIndex (fun v w : E2 => fderiv ℝ (fderiv ℝ g) 0 v w) = 1 →
        ∀ x ∈ e.source, g x = e x 0 ^ 2 - e x 1 ^ 2) ∧
      (formIndex (fun v w : E2 => fderiv ℝ (fderiv ℝ g) 0 v w) = 2 →
        ∀ x ∈ e.source, g x = -(e x 0 ^ 2) - e x 1 ^ 2) := by
  have hle : formIndex (fun v w : E2 => fderiv ℝ (fderiv ℝ g) 0 v w) ≤ 2 := by
    have h := formIndex_le_finrank (fun v w : E2 => fderiv ℝ (fderiv ℝ g) 0 v w)
    rwa [finrank_euclideanSpace_fin] at h
  obtain ⟨e, h1, h2, h3, h4, h5, h6⟩ := exists_morse_coords_smooth hU h0U hg h0 hd hnd
  refine ⟨hle, e, h1, h2, h3, h4, h5, ?_, ?_, ?_⟩
  · intro hk x hx
    rw [h6 x hx, hk]
    simp [morseModel]
  · intro hk x hx
    rw [h6 x hx, hk]
    simp [morseModel]
  · intro hk x hx
    rw [h6 x hx, hk]
    simp [morseModel]

end LiquidDrop
