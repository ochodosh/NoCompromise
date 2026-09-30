module

public import NoCompromise.Surface.SurfaceChart
public import NoCompromise.Surface.HeightMorse

@[expose] public section

/-!
# Pulling a surface critical point back to the plane

For a projection chart of an embedded surface (`SurfaceChart.lean`) and a critical point `p`
of a smooth function `h` on the surface, the pulled-back function `g = h ∘ chart⁻¹ - h p`
has `g 0 = 0`, `Dg 0 = 0`, and a Hessian at `0` that is the tangential Hessian of `h` at `p`
transported by a linear isomorphism. In particular nondegeneracy and the index agree. This
is the input needed to apply `lem:morse-coords` on the surface (`lem:local-sectors` on `Σ`).
-/

noncomputable section

open Set Filter Function InnerProductSpace
open scoped Topology Gradient

namespace LiquidDrop

local notation "E2" => EuclideanSpace ℝ (Fin 2)

section FormTransport

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The index of a form is invariant under a linear isomorphism. -/
theorem formIndex_comp_linearEquiv (L : V ≃ₗ[ℝ] W) (B : W → W → ℝ) :
    formIndex (fun x y => B (L x) (L y)) = formIndex B := by
  unfold formIndex
  congr 1
  ext d
  constructor
  · rintro ⟨M, rfl, hM⟩
    refine ⟨M.map (L : V →ₗ[ℝ] W), LinearEquiv.finrank_map_eq L M, ?_⟩
    rintro _ ⟨x, hx, rfl⟩ hne
    exact hM x hx (by rintro rfl; simp at hne)
  · rintro ⟨M, rfl, hM⟩
    refine ⟨M.map (L.symm : W →ₗ[ℝ] V), LinearEquiv.finrank_map_eq L.symm M, ?_⟩
    rintro _ ⟨x, hx, rfl⟩ hne
    have hx0 : x ≠ 0 := by rintro rfl; simp at hne
    simpa using hM x hx hx0

/-- Nondegeneracy of a form is invariant under a linear isomorphism. -/
theorem isNondegenerateForm_comp_linearEquiv (L : V ≃ₗ[ℝ] W) (B : W → W → ℝ) :
    IsNondegenerateForm (fun x y => B (L x) (L y)) ↔ IsNondegenerateForm B := by
  constructor
  · intro h X hX
    have h0 := h (L.symm X) (fun Y => by simpa using hX (L Y))
    simpa using congrArg L h0
  · intro h X hX
    have h0 := h (L X) (fun Y => by simpa using hX (L.symm Y))
    exact L.map_eq_zero_iff.mp h0

end FormTransport

/-- The pull-back of `h - h p` to the plane through the inverse of a surface chart. -/
def chartPullback {S : Set E₃} (e : OpenPartialHomeomorph S E2) (h : E₃ → ℝ) (p : E₃) :
    E2 → ℝ :=
  fun y => h (e.symm y : E₃) - h p

/-- Second derivative along a line through the origin. -/
theorem hasDerivAt_deriv_comp_line {g : E2 → ℝ} (hg : ContDiffAt ℝ 2 g 0) (v : E2) :
    HasDerivAt (deriv (fun t : ℝ => g (t • v))) (fderiv ℝ (fderiv ℝ g) 0 v v) 0 := by
  have hline : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t • v) v t := by
    intro t
    simpa using (hasDerivAt_id t).smul_const v
  have hd : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) 0) 0 :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have h1 : HasDerivAt (fun t : ℝ => fderiv ℝ g (t • v)) (fderiv ℝ (fderiv ℝ g) 0 v) 0 :=
    hd.comp_hasDerivAt_of_eq (0 : ℝ) (hline 0) (by simp)
  have h2 : HasDerivAt (fun t : ℝ => fderiv ℝ g (t • v) v)
      (fderiv ℝ (fderiv ℝ g) 0 v v) 0 := by
    simpa using h1.clm_apply (hasDerivAt_const (0 : ℝ) v)
  have hev : ∀ᶠ y in 𝓝 (0 : E2), DifferentiableAt ℝ g y :=
    (hg.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hcont : Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 (0 : E2)) := by
    simpa using (hline 0).continuousAt.tendsto
  have hev' : ∀ᶠ t in 𝓝 (0 : ℝ), deriv (fun t : ℝ => g (t • v)) t = fderiv ℝ g (t • v) v := by
    filter_upwards [hcont.eventually hev] with t ht
    exact (ht.hasFDerivAt.comp_hasDerivAt t (hline t)).deriv
  exact h2.congr_of_eventuallyEq hev'

variable {S : Set E₃}

/-- Along a chart, the derivative of the inverse is a right inverse of the projection. -/
theorem chart_projection_fderiv {e : OpenPartialHomeomorph S E2} {P : E₃ →L[ℝ] E2} {q : E₃}
    (heP : ∀ x : S, e x = P ((x : E₃) - q)) {k : ℕ} (hk : 1 ≤ k)
    (hC : ContDiffOn ℝ k (fun y => (e.symm y : E₃)) e.target) {y : E2} (hy : y ∈ e.target)
    (v : E2) : P (fderiv ℝ (fun y => (e.symm y : E₃)) y v) = v := by
  set ψ : E2 → E₃ := fun y => (e.symm y : E₃)
  have hψd : DifferentiableAt ℝ ψ y :=
    ((hC.contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by exact_mod_cast
      (Nat.one_le_iff_ne_zero.mp hk)))
  have heq : (fun z => P (ψ z - q)) =ᶠ[𝓝 y] id := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    rw [← heP]
    exact e.right_inv hz
  have hder : HasFDerivAt (fun z => P (ψ z - q)) (P.comp (fderiv ℝ ψ y)) y :=
    P.hasFDerivAt.comp y (hψd.hasFDerivAt.sub_const q)
  have h2 := hder.congr_of_eventuallyEq heq.symm
  have h3 := h2.unique (hasFDerivAt_id y)
  simpa using congrArg (fun L : E2 →L[ℝ] E2 => L v) h3

/-- Along a chart, the derivative of the inverse takes values in the tangent plane. -/
theorem chart_fderiv_mem_tangentPlane {e : OpenPartialHomeomorph S E2} {k : ℕ} (hk : 1 ≤ k)
    (hC : ContDiffOn ℝ k (fun y => (e.symm y : E₃)) e.target) {y : E2} (hy : y ∈ e.target)
    (v : E2) :
    fderiv ℝ (fun y => (e.symm y : E₃)) y v ∈ tangentPlane S (e.symm y : E₃) := by
  set ψ : E2 → E₃ := fun y => (e.symm y : E₃)
  have hψC : ContDiffAt ℝ k ψ y := hC.contDiffAt (e.open_target.mem_nhds hy)
  have hψd : DifferentiableAt ℝ ψ y :=
    hψC.differentiableAt (by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hk))
  rw [mem_tangentPlane_iff]
  intro f hf hf0
  have ht : Tendsto ψ (𝓝 y) (𝓝[S] (ψ y)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hψd.continuousAt.tendsto, Eventually.of_forall fun z => (e.symm z).2⟩
  have he : f ∘ ψ =ᶠ[𝓝 y] fun _ => 0 := ht.eventually hf0
  have hd := hf.hasFDerivAt.comp y hψd.hasFDerivAt
  have hz := (hd.congr_of_eventuallyEq he.symm).unique (hasFDerivAt_const 0 y)
  simpa using congrArg (fun L : E2 →L[ℝ] ℝ => L v) hz

private lemma surfaceHessian_add_add (n : E₃ → E₃) (h : E₃ → ℝ) (p X Y : E₃) :
    surfaceHessian n h p (X + Y) (X + Y) =
      surfaceHessian n h p X X + surfaceHessian n h p X Y + surfaceHessian n h p Y X +
        surfaceHessian n h p Y Y := by
  simp only [surfaceHessian, secondFundamentalForm, map_add, add_apply,
    inner_add_left, inner_add_right]
  ring

/-- Pull-back of a surface critical point through a projection chart (input of
`lem:morse-coords` on `Σ`): the pulled-back function vanishes to second order at `0`, and its
Hessian there is the tangential Hessian transported by a linear isomorphism, so nondegeneracy
and the index agree with those of `h` at `p`. -/
theorem exists_chart_pullback {n : E₃ → E₃} (hS : IsSmoothEmbeddedSurface S)
    (hn : IsUnitNormalField S n) {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {p : E₃}
    (hcrit : IsSurfaceCriticalPoint S h p) :
    ∃ (e : OpenPartialHomeomorph S E2) (P : E₃ →L[ℝ] E2) (U : Set E₃),
      IsOpen U ∧ p ∈ U ∧ e.source = Subtype.val ⁻¹' U ∧
      (⟨p, hcrit.1⟩ : S) ∈ e.source ∧ e ⟨p, hcrit.1⟩ = 0 ∧
      (∀ x : S, e x = P ((x : E₃) - p)) ∧
      ContDiffOn ℝ 3 (fun y => (e.symm y : E₃)) e.target ∧
      ContDiffAt ℝ 3 (chartPullback e h p) 0 ∧ chartPullback e h p 0 = 0 ∧
      fderiv ℝ (chartPullback e h p) 0 = 0 ∧
      (IsNondegenerateForm (fun v w : E2 => fderiv ℝ (fderiv ℝ (chartPullback e h p)) 0 v w) ↔
        IsNondegenerateForm (tangentHessian S n h p)) ∧
      formIndex (fun v w : E2 => fderiv ℝ (fderiv ℝ (chartPullback e h p)) 0 v w) =
        surfaceIndex S n h p := by
  obtain ⟨e, P, U, hU, hpU, hsrc, hps, he0, heP, hC⟩ := hS.exists_projection_chart hcrit.1 3
  refine ⟨e, P, U, hU, hpU, hsrc, hps, he0, heP, hC, ?_⟩
  have h0t : (0 : E2) ∈ e.target := he0 ▸ e.map_source hps
  have hψ0 : (e.symm 0 : E₃) = p := by
    have := e.left_inv hps
    rw [he0] at this
    exact congrArg Subtype.val this
  have hψC : ContDiffAt ℝ 3 (fun y => (e.symm y : E₃)) 0 :=
    hC.contDiffAt (e.open_target.mem_nhds h0t)
  have hψd : DifferentiableAt ℝ (fun y => (e.symm y : E₃)) 0 :=
    hψC.differentiableAt (by norm_num)
  have hh3 : ContDiff ℝ 3 h :=
    hh.of_le (show ((3 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from
      WithTop.coe_le_coe.mpr le_top)
  have hgC : ContDiffAt ℝ 3 (chartPullback e h p) 0 :=
    (hh3.contDiffAt.comp 0 hψC).sub contDiffAt_const
  have hg0 : chartPullback e h p 0 = 0 := by simp [chartPullback, hψ0]
  have htan : ∀ v, fderiv ℝ (fun y => (e.symm y : E₃)) 0 v ∈ tangentPlane S p := by
    intro v
    have := chart_fderiv_mem_tangentPlane (by norm_num) hC h0t v
    rwa [hψ0] at this
  have hinj : Injective (fderiv ℝ (fun y => (e.symm y : E₃)) 0) := by
    intro v w hvw
    have hv := chart_projection_fderiv heP (by norm_num) hC h0t v
    have hw := chart_projection_fderiv heP (by norm_num) hC h0t w
    rw [← hv, ← hw, hvw]
  have hhd : HasFDerivAt h (fderiv ℝ h p) (e.symm 0 : E₃) := by
    rw [hψ0]
    exact (hh3.differentiable (by norm_num) p).hasFDerivAt
  have hgd : fderiv ℝ (chartPullback e h p) 0 = 0 := by
    have hd : HasFDerivAt (chartPullback e h p)
        ((fderiv ℝ h p).comp (fderiv ℝ (fun y => (e.symm y : E₃)) 0)) 0 :=
      (hhd.comp 0 hψd.hasFDerivAt).sub_const (h p)
    rw [hd.fderiv]
    ext v
    simp [hcrit.2 _ (htan v)]
  have hdiag : ∀ v, fderiv ℝ (fderiv ℝ (chartPullback e h p)) 0 v v =
      surfaceHessian n h p (fderiv ℝ (fun y => (e.symm y : E₃)) 0 v)
        (fderiv ℝ (fun y => (e.symm y : E₃)) 0 v) := by
    intro v
    let γ : ℝ → E₃ := fun t => (e.symm (t • v) : E₃)
    have hl : HasDerivAt (fun t : ℝ => t • v) v 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
    have hγC : ContDiffAt ℝ 2 γ 0 := by
      have hl3 : ContDiffAt ℝ 3 (fun t : ℝ => t • v) 0 :=
        (contDiff_id.smul contDiff_const).contDiffAt
      have h' : ContDiffAt ℝ 3 (fun y => (e.symm y : E₃)) ((0 : ℝ) • v) := by
        simpa using hψC
      have h3 : ContDiffAt ℝ 3 ((fun y => (e.symm y : E₃)) ∘ (fun t : ℝ => t • v)) 0 :=
        ContDiffAt.comp 0 h' hl3
      exact h3.of_le (by norm_num)
    have hγ0 : γ 0 = p := by simp [γ, hψ0]
    have hA := hasDerivAt_deriv_comp_eq_surfaceHessian hS hn
      (hh3.of_le (by norm_num)).contDiffAt hcrit hγC hγ0
      (Eventually.of_forall fun t => (e.symm (t • v)).2)
    have hB := hasDerivAt_deriv_comp_line (hgC.of_le (by norm_num)) v
    have hfun : deriv (fun t : ℝ => chartPullback e h p (t • v)) = deriv (h ∘ γ) := by
      funext t
      exact deriv_sub_const (h p)
    have hγd : deriv γ 0 = fderiv ℝ (fun y => (e.symm y : E₃)) 0 v := by
      have h' : HasFDerivAt (fun y => (e.symm y : E₃))
          (fderiv ℝ (fun y => (e.symm y : E₃)) 0) ((0 : ℝ) • v) := by
        simpa using hψd.hasFDerivAt
      exact (h'.comp_hasDerivAt (0 : ℝ) hl).deriv
    rw [hfun] at hB
    rw [hB.unique hA, hγd]
  have hdim : Module.finrank ℝ E2 = Module.finrank ℝ (tangentPlane S p) := by
    rw [finrank_euclideanSpace_fin, hS.finrank_tangentPlane hcrit.1]
  let L₀ : E2 →ₗ[ℝ] tangentPlane S p :=
    ((fderiv ℝ (fun y => (e.symm y : E₃)) 0 : E2 →L[ℝ] E₃) : E2 →ₗ[ℝ] E₃).codRestrict
      (tangentPlane S p) htan
  have hL₀ : Injective L₀ := by
    intro v w hvw
    exact hinj (congrArg Subtype.val hvw)
  let L : E2 ≃ₗ[ℝ] tangentPlane S p := LinearMap.linearEquivOfInjective L₀ hL₀ hdim
  have hLv : ∀ v, ((L v : tangentPlane S p) : E₃) = fderiv ℝ (fun y => (e.symm y : E₃)) 0 v :=
    fun v => rfl
  have hsymg : ∀ v w, fderiv ℝ (fderiv ℝ (chartPullback e h p)) 0 v w =
      fderiv ℝ (fderiv ℝ (chartPullback e h p)) 0 w v :=
    fun v w => (hgC.isSymmSndFDerivAt (by norm_num)) v w
  have hsymH : ∀ X ∈ tangentPlane S p, ∀ Y ∈ tangentPlane S p,
      surfaceHessian n h p X Y = surfaceHessian n h p Y X := by
    intro X hX Y hY
    simp only [surfaceHessian]
    rw [(hh.contDiffAt.isSymmSndFDerivAt (by simp)) X Y,
      secondFundamentalForm_symm hS hn hcrit.1 hX hY]
  have hform : (fun v w : E2 => fderiv ℝ (fderiv ℝ (chartPullback e h p)) 0 v w) =
      fun v w => tangentHessian S n h p (L v) (L w) := by
    funext v w
    simp only [tangentHessian, hLv]
    have h1 := hdiag (v + w)
    simp only [map_add, add_apply] at h1
    rw [surfaceHessian_add_add, hdiag v, hdiag w] at h1
    have h2 := hsymg v w
    have h3 := hsymH _ (htan v) _ (htan w)
    linarith
  refine ⟨hgC, hg0, hgd, ?_, ?_⟩
  · rw [hform]
    exact isNondegenerateForm_comp_linearEquiv L (tangentHessian S n h p)
  · rw [hform]
    exact formIndex_comp_linearEquiv L (tangentHessian S n h p)

end LiquidDrop
