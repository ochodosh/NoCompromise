module

public import NoCompromise.Elliptic.BoundaryNeumannC2
public import NoCompromise.Elliptic.BoundaryNeumannC2HolderAlgebra
public import NoCompromise.Elliptic.BoundaryNeumannInhomC1Lift

@[expose] public section

/-!
# C²,α of the boundary Neumann lift

Transfer lemmas for C¹,α (post-composition with a continuous linear map, pre-composition
with a linear map of norm at most one, agreement on an open neighbourhood), their C²,α
consequences, and the C²,α bounds on the lift `q = x₃ h(x')/b(x')` used in the second
assertion of blueprint `thm:boundary-neumann`.
-/

noncomputable section
open Set Filter Metric
open scoped Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- C⁰,α post-composition with a continuous linear map. -/
lemma boundaryNeumann_holder_postcomp {E F G : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {α : ℝ} {f : E → F} {U : Set E} (hf : HasFiniteHolderNormOn α f U) (L : F →L[ℝ] G) :
    HasFiniteHolderNormOn α (fun x => L (f x)) U ∧
      holderNorm α (fun x => L (f x)) U ≤ ‖L‖ * holderNorm α f U := by
  have hA := mul_nonneg (norm_nonneg L) (holderUniformNorm_nonneg hf.uniform_bounded)
  have hB := mul_nonneg (norm_nonneg L) hf.seminorm_nonneg
  have hv : ∀ x ∈ U, ‖L (f x)‖ ≤ ‖L‖ * holderUniformNorm f U := fun x hx =>
    (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (norm_le_holderUniformNorm hf.uniform_bounded hx) (norm_nonneg L))
  have hh : ∀ x ∈ U, ∀ y ∈ U, ‖L (f x) - L (f y)‖ / ‖x - y‖ ^ α ≤
      ‖L‖ * holderSeminorm α f U := by
    intro x hx y hy
    rw [← map_sub]
    calc
      _ ≤ ‖L‖ * ‖f x - f y‖ / ‖x - y‖ ^ α :=
        div_le_div_of_nonneg_right (L.le_opNorm _) (by positivity)
      _ = ‖L‖ * (‖f x - f y‖ / ‖x - y‖ ^ α) := mul_div_assoc _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (schauder_holder_quotient_le hf hx hy) (norm_nonneg L)
  refine ⟨HasFiniteHolderNormOn.of_bounds hA hB hv hh, (holderNorm_le hA hB hv hh).trans_eq ?_⟩
  dsimp [holderNorm]
  ring

/-- C⁰,α pre-composition with a continuous linear map of norm at most one. -/
lemma boundaryNeumann_holder_precomp {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    {α : ℝ} (hα : 0 ≤ α) {f : F → G} {S : Set E} {T : Set F}
    (hf : HasFiniteHolderNormOn α f T) (P : E →L[ℝ] F) (hP : ‖P‖ ≤ 1)
    (hST : ∀ x ∈ S, P x ∈ T) :
    HasFiniteHolderNormOn α (fun x => f (P x)) S ∧
      holderNorm α (fun x => f (P x)) S ≤ holderNorm α f T := by
  have hA := holderUniformNorm_nonneg hf.uniform_bounded
  have hB := hf.seminorm_nonneg
  have hv : ∀ x ∈ S, ‖f (P x)‖ ≤ holderUniformNorm f T := fun x hx =>
    norm_le_holderUniformNorm hf.uniform_bounded (hST x hx)
  have hh : ∀ x ∈ S, ∀ y ∈ S, ‖f (P x) - f (P y)‖ / ‖x - y‖ ^ α ≤
      holderSeminorm α f T := by
    intro x hx y hy
    by_cases hxy : P x = P y
    · rw [hxy, sub_self, norm_zero, zero_div]
      exact hB
    · have hpos : 0 < ‖P x - P y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
      have hle : ‖P x - P y‖ ≤ ‖x - y‖ := by
        rw [← map_sub]
        exact (P.le_opNorm _).trans (by nlinarith [norm_nonneg (x - y)])
      calc
        _ ≤ ‖f (P x) - f (P y)‖ / ‖P x - P y‖ ^ α :=
          div_le_div_of_nonneg_left (norm_nonneg _) (Real.rpow_pos_of_pos hpos α)
            (Real.rpow_le_rpow hpos.le hle hα)
        _ ≤ _ := schauder_holder_quotient_le hf (hST x hx) (hST y hy)
  exact ⟨HasFiniteHolderNormOn.of_bounds hA hB hv hh, holderNorm_le hA hB hv hh⟩

/-- C¹,α is determined by the values on an open neighbourhood. -/
lemma boundaryNeumann_hasC1HolderOn_congr_open {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ} {f g : E → F} {S O : Set E} (hO : IsOpen O) (hSO : S ⊆ O)
    (he : EqOn f g O) (hf : HasC1HolderOn α f S) :
    HasC1HolderOn α g S ∧ nondivC1HolderNorm α g S ≤ nondivC1HolderNorm α f S := by
  have hd : EqOn (fderiv ℝ f) (fderiv ℝ g) S := fun x hx =>
    (Filter.eventuallyEq_of_mem (hO.mem_nhds (hSO hx)) he).fderiv_eq
  obtain ⟨h0, n0⟩ := boundaryNeumann_holder_congr hf.function_holder (he.mono hSO)
  obtain ⟨h1, n1⟩ := boundaryNeumann_holder_congr hf.derivative_holder hd
  refine ⟨⟨hf.contDiff.congr (fun x hx => (he (hSO hx)).symm), h0, h1⟩, ?_⟩
  unfold nondivC1HolderNorm
  linarith

/-- C¹,α post-composition with a continuous linear map `L`: the norm is at most `‖L‖ N`. -/
theorem boundaryNeumann_hasC1HolderOn_postcomp {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {α : ℝ} {f : E → F} {S O : Set E} (hO : IsOpen O) (hSO : S ⊆ O)
    (hfO : ContDiffOn ℝ 1 f O) (hf : HasC1HolderOn α f S) (L : F →L[ℝ] G) :
    HasC1HolderOn α (fun x => L (f x)) S ∧
      nondivC1HolderNorm α (fun x => L (f x)) S ≤ ‖L‖ * nondivC1HolderNorm α f S := by
  have hdf : ∀ x ∈ S, DifferentiableAt ℝ f x := fun x hx =>
    (hfO.differentiableOn one_ne_zero).differentiableAt (hO.mem_nhds (hSO hx))
  let M : (E →L[ℝ] F) →L[ℝ] (E →L[ℝ] G) := ContinuousLinearMap.compL ℝ E F G L
  have hM : ‖M‖ ≤ ‖L‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L) (fun φ => by
      simpa [M] using L.opNorm_comp_le φ)
  obtain ⟨h0, n0⟩ := boundaryNeumann_holder_postcomp hf.function_holder L
  obtain ⟨h1, n1⟩ := boundaryNeumann_holder_postcomp hf.derivative_holder M
  obtain ⟨h2, n2⟩ := boundaryNeumann_holder_congr h1 (g := fderiv ℝ (fun x => L (f x)))
    (fun x hx => by
      have := (L.hasFDerivAt.comp x (hdf x hx).hasFDerivAt).fderiv
      simp only [M, ContinuousLinearMap.compL_apply]
      exact this.symm)
  refine ⟨⟨L.contDiff.comp_contDiffOn hf.contDiff, h0, h2⟩, ?_⟩
  have := hf.derivative_holder.norm_nonneg
  have h3 : ‖M‖ * holderNorm α (fderiv ℝ f) S ≤ ‖L‖ * holderNorm α (fderiv ℝ f) S :=
    mul_le_mul_of_nonneg_right hM this
  unfold nondivC1HolderNorm
  nlinarith

/-- C¹,α pre-composition with a continuous linear map `P` of norm at most one. -/
theorem boundaryNeumann_hasC1HolderOn_precomp {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {α : ℝ} (hα : 0 ≤ α) {u : F → G} {S : Set E} {T V : Set F} (hV : IsOpen V)
    (hTV : T ⊆ V) (huV : ContDiffOn ℝ 1 u V) (hu : HasC1HolderOn α u T)
    (P : E →L[ℝ] F) (hP : ‖P‖ ≤ 1) (hST : ∀ x ∈ S, P x ∈ T) :
    HasC1HolderOn α (fun x => u (P x)) S ∧
      nondivC1HolderNorm α (fun x => u (P x)) S ≤ nondivC1HolderNorm α u T := by
  have hdu : ∀ x ∈ S, DifferentiableAt ℝ u (P x) := fun x hx =>
    (huV.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds (hTV (hST x hx)))
  let M : (F →L[ℝ] G) →L[ℝ] (E →L[ℝ] G) := (ContinuousLinearMap.compL ℝ E F G).flip P
  have hM : ‖M‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun φ => by
      simp only [M, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply, one_mul]
      exact (φ.opNorm_comp_le P).trans (by nlinarith [norm_nonneg φ]))
  obtain ⟨h0, n0⟩ := boundaryNeumann_holder_precomp hα hu.function_holder P hP hST
  obtain ⟨h1, n1⟩ := boundaryNeumann_holder_precomp hα hu.derivative_holder P hP hST
  obtain ⟨h2, n2⟩ := boundaryNeumann_holder_postcomp h1 M
  obtain ⟨h3, n3⟩ := boundaryNeumann_holder_congr h2 (g := fderiv ℝ (fun x => u (P x)))
    (fun x hx => by
      have := ((hdu x hx).hasFDerivAt.comp x P.hasFDerivAt).fderiv
      simp only [M, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]
      exact this.symm)
  refine ⟨⟨hu.contDiff.comp P.contDiff.contDiffOn hST, h0, h3⟩, ?_⟩
  have := h1.norm_nonneg
  have h4 : ‖M‖ * holderNorm α (fun x => fderiv ℝ u (P x)) S ≤
      holderNorm α (fun x => fderiv ℝ u (P x)) S := by nlinarith
  unfold nondivC1HolderNorm
  linarith

/-- C²,α pre-composition: the derivative of `u ∘ P` is C¹,α with norm at most that of `Du`. -/
theorem boundaryNeumann_hasC2HolderOn_precomp {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {α : ℝ} (hα : 0 ≤ α) {u : F → G} {S : Set E} {T V : Set F} (hV : IsOpen V)
    (hTV : T ⊆ V) (huV : ContDiffOn ℝ 2 u V) (hu' : HasC1HolderOn α (fderiv ℝ u) T)
    (P : E →L[ℝ] F) (hP : ‖P‖ ≤ 1) (hST : ∀ x ∈ S, P x ∈ T) :
    HasC1HolderOn α (fderiv ℝ (fun x => u (P x))) S ∧
      nondivC1HolderNorm α (fderiv ℝ (fun x => u (P x))) S ≤
        nondivC1HolderNorm α (fderiv ℝ u) T := by
  have hO : IsOpen (P ⁻¹' V) := hV.preimage P.continuous
  have hSO : S ⊆ P ⁻¹' V := fun x hx => hTV (hST x hx)
  have hu1 : ContDiffOn ℝ 1 u V := huV.of_le (by norm_num)
  have hDu : ContDiffOn ℝ 1 (fderiv ℝ u) V := huV.fderiv_of_isOpen hV (by norm_num)
  let M : (F →L[ℝ] G) →L[ℝ] (E →L[ℝ] G) := (ContinuousLinearMap.compL ℝ E F G).flip P
  have hM : ‖M‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun φ => by
      simp only [M, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply, one_mul]
      exact (φ.opNorm_comp_le P).trans (by nlinarith [norm_nonneg φ]))
  obtain ⟨h1, n1⟩ := boundaryNeumann_hasC1HolderOn_precomp hα hV hTV hDu hu' P hP hST
  have hc : ContDiffOn ℝ 1 (fun x => fderiv ℝ u (P x)) (P ⁻¹' V) :=
    hDu.comp P.contDiff.contDiffOn (fun _ hx => hx)
  obtain ⟨h2, n2⟩ := boundaryNeumann_hasC1HolderOn_postcomp hO hSO hc h1 M
  obtain ⟨h3, n3⟩ := boundaryNeumann_hasC1HolderOn_congr_open hO hSO
    (g := fderiv ℝ (fun x => u (P x))) (fun x hx => by
      have hd := (hu1.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hx)
      have := (hd.hasFDerivAt.comp x P.hasFDerivAt).fderiv
      simp only [M, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]
      exact this.symm) h2
  refine ⟨h3, n3.trans (n2.trans ?_)⟩
  have := h1.norm_nonneg
  nlinarith

/-- C²,α of a bilinear expression: its derivative is C¹,α with an explicit bound. -/
theorem boundaryNeumann_hasC2HolderOn_bilinear {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {α : ℝ} {f : E → F} {g : E → G} {S O : Set E} (hO : IsOpen O) (hSO : S ⊆ O)
    (hfO : ContDiffOn ℝ 2 f O) (hgO : ContDiffOn ℝ 2 g O)
    (hf : HasC1HolderOn α f S) (hf' : HasC1HolderOn α (fderiv ℝ f) S)
    (hg : HasC1HolderOn α g S) (hg' : HasC1HolderOn α (fderiv ℝ g) S)
    (B : F →L[ℝ] G →L[ℝ] H) :
    HasC1HolderOn α (fderiv ℝ (fun x => B (f x) (g x))) S ∧
      nondivC1HolderNorm α (fderiv ℝ (fun x => B (f x) (g x))) S ≤
        3 * ‖B‖ * nondivC1HolderNorm α f S * nondivC1HolderNorm α (fderiv ℝ g) S +
        3 * ‖B‖ * nondivC1HolderNorm α (fderiv ℝ f) S * nondivC1HolderNorm α g S := by
  have hf1 : ContDiffOn ℝ 1 f O := hfO.of_le (by norm_num)
  have hg1 : ContDiffOn ℝ 1 g O := hgO.of_le (by norm_num)
  have hDf : ContDiffOn ℝ 1 (fderiv ℝ f) O := hfO.fderiv_of_isOpen hO (by norm_num)
  have hDg : ContDiffOn ℝ 1 (fderiv ℝ g) O := hgO.fderiv_of_isOpen hO (by norm_num)
  obtain ⟨hR, nR⟩ := boundaryNeumann_hasC1HolderOn_bilinear hO hSO hf1 hDg hf hg'
    (B.precompR E)
  obtain ⟨hL, nL⟩ := boundaryNeumann_hasC1HolderOn_bilinear hO hSO hDf hg1 hf' hg
    (B.precompL E)
  have hRO : ContDiffOn ℝ 1 (fun x => B.precompR E (f x) (fderiv ℝ g x)) O :=
    ((B.precompR E).contDiff.comp_contDiffOn hf1).clm_apply hDg
  have hLO : ContDiffOn ℝ 1 (fun x => B.precompL E (fderiv ℝ f x) (g x)) O :=
    ((B.precompL E).contDiff.comp_contDiffOn hDf).clm_apply hg1
  obtain ⟨hA, nA⟩ := boundaryNeumann_hasC1HolderOn_add hO hSO hRO hLO hR hL
  obtain ⟨hC, nC⟩ := boundaryNeumann_hasC1HolderOn_congr_open hO hSO
    (g := fderiv ℝ (fun x => B (f x) (g x)))
    (fun x hx => (B.fderiv_of_bilinear
      ((hf1.differentiableOn one_ne_zero).differentiableAt (hO.mem_nhds hx))
      ((hg1.differentiableOn one_ne_zero).differentiableAt (hO.mem_nhds hx))).symm) hA
  refine ⟨hC, nC.trans (nA.trans (add_le_add (nR.trans ?_) (nL.trans ?_)))⟩
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_precompR_le _ B) (by norm_num))
      hf.norm_nonneg) hg'.norm_nonneg
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_precompL_le _ B) (by norm_num))
      hf'.norm_nonneg) hg.norm_nonneg

/-- Constants are C¹,α with norm at most the norm of the constant. -/
lemma boundaryNeumann_hasC1HolderOn_const {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ} (c : F) (S : Set E) :
    HasC1HolderOn α (fun _ : E => c) S ∧ nondivC1HolderNorm α (fun _ : E => c) S ≤ ‖c‖ := by
  have hv0 : ∀ x ∈ S, ‖(fun _ : E => c) x‖ ≤ ‖c‖ := fun _ _ => le_rfl
  have hh0 : ∀ x ∈ S, ∀ y ∈ S, ‖(fun _ : E => c) x - (fun _ : E => c) y‖ / ‖x - y‖ ^ α ≤ 0 :=
    fun _ _ _ _ => by simp
  have hD : fderiv ℝ (fun _ : E => c) = 0 := fderiv_const c
  have hv1 : ∀ x ∈ S, ‖fderiv ℝ (fun _ : E => c) x‖ ≤ 0 := fun _ _ => by simp [hD]
  have hh1 : ∀ x ∈ S, ∀ y ∈ S,
      ‖fderiv ℝ (fun _ : E => c) x - fderiv ℝ (fun _ : E => c) y‖ / ‖x - y‖ ^ α ≤ 0 :=
    fun _ _ _ _ => by simp [hD]
  refine ⟨⟨contDiffOn_const, HasFiniteHolderNormOn.of_bounds (norm_nonneg c) le_rfl hv0 hh0,
    HasFiniteHolderNormOn.of_bounds le_rfl le_rfl hv1 hh1⟩, ?_⟩
  have n0 := holderNorm_le (norm_nonneg c) le_rfl hv0 hh0
  have n1 := holderNorm_le le_rfl le_rfl hv1 hh1
  unfold nondivC1HolderNorm
  linarith

/-- A continuous linear map is C¹,α on a subset of the closed unit ball, norm at most `4 ‖ℓ‖`;
its derivative is constant, with norm at most `‖ℓ‖`. -/
lemma boundaryNeumann_hasC1HolderOn_clm {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (ℓ : E →L[ℝ] F) {S : Set E}
    (hS : S ⊆ closedBall 0 1) :
    (HasC1HolderOn α ℓ S ∧ nondivC1HolderNorm α ℓ S ≤ 4 * ‖ℓ‖) ∧
      (HasC1HolderOn α (fderiv ℝ ℓ) S ∧ nondivC1HolderNorm α (fderiv ℝ ℓ) S ≤ ‖ℓ‖) := by
  have hD : fderiv ℝ ℓ = fun _ => ℓ := funext fun _ => ℓ.fderiv
  obtain ⟨hc, nc⟩ := boundaryNeumann_hasC1HolderOn_const (α := α) ℓ S
  have hn := norm_nonneg ℓ
  have hv : ∀ x ∈ S, ‖ℓ x‖ ≤ ‖ℓ‖ := fun x hx => by
    have : ‖x‖ ≤ 1 := by simpa using hS hx
    exact (ℓ.le_opNorm x).trans (by nlinarith)
  have hh : ∀ x ∈ S, ∀ y ∈ S, ‖ℓ x - ℓ y‖ / ‖x - y‖ ^ α ≤ 2 * ‖ℓ‖ := by
    intro x hx y hy
    have hx' : ‖x‖ ≤ 1 := by simpa using hS hx
    have hy' : ‖y‖ ≤ 1 := by simpa using hS hy
    have hd2 : ‖x - y‖ ≤ 2 := (norm_sub_le x y).trans (by linarith)
    have hd := boundary_neumann_dist_le_two_rpow hα hα1 (norm_nonneg (x - y)) hd2
    have hr := Real.rpow_nonneg (norm_nonneg (x - y)) α
    rcases hr.eq_or_lt with h0 | hpos
    · rw [← h0, div_zero]; positivity
    · rw [div_le_iff₀ hpos, ← map_sub]
      have := ℓ.le_opNorm (x - y)
      nlinarith
  have hA : ContDiffOn ℝ 1 ℓ S := ℓ.contDiff.contDiffOn
  have h0 := HasFiniteHolderNormOn.of_bounds hn (by positivity) hv hh
  have n0 := holderNorm_le hn (by positivity) hv hh
  rw [hD]
  refine ⟨⟨⟨hA, h0, hD ▸ hc.function_holder⟩, ?_⟩, hc, nc⟩
  unfold nondivC1HolderNorm
  rw [hD]
  have := hc.function_norm_le
  linarith

/-- A Hessian entry is an entry of the second Fréchet derivative. -/
lemma boundaryNeumannC2Entry_eq_fderiv_fderiv {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    {x : EuclideanSpace ℝ (Fin 3)} (hw : DifferentiableAt ℝ (fderiv ℝ w) x) (i j : Fin 3) :
    boundaryNeumannC2Entry w x i j = fderiv ℝ (fderiv ℝ w) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) := by
  unfold boundaryNeumannC2Entry
  rw [fderiv_clm_apply hw (differentiableAt_const _)]
  simp

/-- Hölder continuity and boundedness of the Hessian entries from C¹,α of the derivative. -/
lemma boundaryNeumannC2Entry_holder_of_hasC1HolderOn {α : ℝ}
    {w : EuclideanSpace ℝ (Fin 3) → ℝ} {S O : Set (EuclideanSpace ℝ (Fin 3))}
    (hO : IsOpen O) (hSO : S ⊆ O) (hw : ContDiffOn ℝ 2 w O)
    (hD : HasC1HolderOn α (fderiv ℝ w) S) :
    (∀ i j, ∀ x ∈ S, ∀ y ∈ S, |boundaryNeumannC2Entry w x i j - boundaryNeumannC2Entry w y i j| ≤
        nondivC1HolderNorm α (fderiv ℝ w) S * dist x y ^ α) ∧
      (∀ i j, ∀ x ∈ S, |boundaryNeumannC2Entry w x i j| ≤
        nondivC1HolderNorm α (fderiv ℝ w) S) := by
  have hD1 : ContDiffOn ℝ 1 (fderiv ℝ w) O := hw.fderiv_of_isOpen hO (by norm_num)
  have hd : ∀ x ∈ S, DifferentiableAt ℝ (fderiv ℝ w) x := fun x hx =>
    (hD1.differentiableOn one_ne_zero).differentiableAt (hO.mem_nhds (hSO hx))
  have hH := hD.derivative_holder
  have hsemi : holderSeminorm α (fderiv ℝ (fderiv ℝ w)) S ≤
      nondivC1HolderNorm α (fderiv ℝ w) S :=
    (le_add_of_nonneg_left (holderUniformNorm_nonneg hH.uniform_bounded)).trans
      hD.derivative_norm_le
  have hunif : holderUniformNorm (fderiv ℝ (fderiv ℝ w)) S ≤
      nondivC1HolderNorm α (fderiv ℝ w) S :=
    (le_add_of_nonneg_right hH.seminorm_nonneg).trans hD.derivative_norm_le
  have he : ∀ (T : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
      (i j : Fin 3), |T (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ ‖T‖ := by
    intro T i j
    have := T.le_opNorm₂ (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    simpa using this
  refine ⟨fun i j x hx y hy => ?_, fun i j x hx => ?_⟩
  · rw [boundaryNeumannC2Entry_eq_fderiv_fderiv (hd x hx),
      boundaryNeumannC2Entry_eq_fderiv_fderiv (hd y hy), ← sub_apply,
      ← sub_apply]
    refine (he _ i j).trans ?_
    by_cases hxy : x = y
    · subst hxy; simp only [sub_self, norm_zero]
      exact mul_nonneg (hD.norm_nonneg) (Real.rpow_nonneg dist_nonneg α)
    · have hpos : 0 < ‖x - y‖ ^ α :=
        Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
      have hq := schauder_holder_quotient_le hH hx hy
      rw [div_le_iff₀ hpos] at hq
      rw [dist_eq_norm]
      exact hq.trans (mul_le_mul_of_nonneg_right hsemi hpos.le)
  · rw [boundaryNeumannC2Entry_eq_fderiv_fderiv (hd x hx)]
    exact (he _ i j).trans ((norm_le_holderUniformNorm hH.uniform_bounded hx).trans hunif)

lemma boundaryNeumann_lift_triple_le {c a b c' a' b' : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hc' : c ≤ c') (ha' : a ≤ a') (hb' : b ≤ b') :
    3 * c * a * b ≤ 3 * c' * a' * b' := by
  have h1 : c * a ≤ c' * a' := mul_le_mul hc' ha' ha (hc.trans hc')
  have h2 : c * a * b ≤ c' * a' * b' :=
    mul_le_mul h1 hb' hb (mul_nonneg (hc.trans hc') (ha.trans ha'))
  linarith

lemma boundaryNeumann_lift_pair_le {a b a' b' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ha' : a ≤ a') (hb' : b ≤ b') : 3 * a * b ≤ 3 * a' * b' := by
  have h1 : a * b ≤ a' * b' := mul_le_mul ha' hb' hb (ha.trans ha')
  linarith

lemma boundaryNeumann_lift_inv_bound_mono {l N Kp : ℝ} (hl : 0 ≤ l) (hN : 0 ≤ N)
    (hNK : N ≤ Kp) :
    (l + l ^ 2 * N) + 9 * (l + l ^ 2 * N) ^ 2 * N ≤
      (l + l ^ 2 * Kp) + 9 * (l + l ^ 2 * Kp) ^ 2 * Kp := by
  have h0 : 0 ≤ l + l ^ 2 * N := add_nonneg hl (mul_nonneg (sq_nonneg l) hN)
  have h1 : l + l ^ 2 * N ≤ l + l ^ 2 * Kp := by
    have := mul_le_mul_of_nonneg_left hNK (sq_nonneg l); linarith
  have h2 : (l + l ^ 2 * N) ^ 2 ≤ (l + l ^ 2 * Kp) ^ 2 := pow_le_pow_left₀ h0 h1 2
  have h3 : (l + l ^ 2 * N) ^ 2 * N ≤ (l + l ^ 2 * Kp) ^ 2 * Kp :=
    mul_le_mul h2 hNK hN (sq_nonneg _)
  linarith

set_option maxHeartbeats 1000000 in
-- The explicit constant bookkeeping through eleven C¹,α norms is slow to elaborate.
/-- The lift `q = x₃ h(x')/b(x')` is C²,α on the closed quarter half-ball, with a uniform
bound, when `h` and `b ≥ lam > 0` are C²,α on the closed unit disk. This supplies the lift
hypotheses of `boundary_neumann_c2_holder_inhom_of_lift` (blueprint `thm:boundary-neumann`). -/
theorem boundaryNeumannLift_c2_holder {α lam K : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hlam : 0 < lam) :
    ∃ Q : ℝ, 0 ≤ Q ∧
      ∀ (h b : EuclideanSpace ℝ (Fin 2) → ℝ) (U : Set (EuclideanSpace ℝ (Fin 2))),
        IsOpen U → closedBall 0 1 ⊆ U → ContDiffOn ℝ 2 h U → ContDiffOn ℝ 2 b U →
        (∀ y ∈ U, lam ≤ b y) →
        HasC1HolderOn α h (closedBall 0 1) → HasC1HolderOn α (fderiv ℝ h) (closedBall 0 1) →
        HasC1HolderOn α b (closedBall 0 1) → HasC1HolderOn α (fderiv ℝ b) (closedBall 0 1) →
        nondivC1HolderNorm α h (closedBall 0 1) ≤ K →
        nondivC1HolderNorm α (fderiv ℝ h) (closedBall 0 1) ≤ K →
        nondivC1HolderNorm α b (closedBall 0 1) ≤ K →
        nondivC1HolderNorm α (fderiv ℝ b) (closedBall 0 1) ≤ K →
        ContDiffOn ℝ 2 (boundaryNeumannLift h b) (ball 0 1) ∧
        HasC1HolderOn α (boundaryNeumannLift h b) (closure (boundaryHalfBall (1 / 4))) ∧
        nondivC1HolderNorm α (boundaryNeumannLift h b)
          (closure (boundaryHalfBall (1 / 4))) ≤ Q ∧
        HasC1HolderOn α (fderiv ℝ (boundaryNeumannLift h b))
          (closure (boundaryHalfBall (1 / 4))) ∧
        nondivC1HolderNorm α (fderiv ℝ (boundaryNeumannLift h b))
          (closure (boundaryHalfBall (1 / 4))) ≤ Q ∧
        (∀ i j, ∀ x ∈ closure (boundaryHalfBall (1 / 4)),
          ∀ y ∈ closure (boundaryHalfBall (1 / 4)),
            |boundaryNeumannC2Entry (boundaryNeumannLift h b) x i j -
              boundaryNeumannC2Entry (boundaryNeumannLift h b) y i j| ≤ Q * dist x y ^ α) ∧
        (∀ i j, ∀ x ∈ closure (boundaryHalfBall (1 / 4)),
          |boundaryNeumannC2Entry (boundaryNeumannLift h b) x i j| ≤ Q) := by
  set Kp := max K 0
  have hKp : 0 ≤ Kp := le_max_right _ _
  have hKKp : K ≤ Kp := le_max_left _ _
  have hl : 0 ≤ lam⁻¹ := inv_nonneg.mpr hlam.le
  set I := (lam⁻¹ + lam⁻¹ ^ 2 * Kp) + 9 * (lam⁻¹ + lam⁻¹ ^ 2 * Kp) ^ 2 * Kp
  have hI0 : 0 ≤ lam⁻¹ + lam⁻¹ ^ 2 * Kp := add_nonneg hl (mul_nonneg (sq_nonneg _) hKp)
  have hI : 0 ≤ I := add_nonneg hI0 (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hKp)
  set J := 3 * 1 * (3 * 1 * I * I) * Kp
  have hJ : 0 ≤ J := mul_nonneg (mul_nonneg (by norm_num)
    (mul_nonneg (mul_nonneg (by norm_num) hI) hI)) hKp
  set Gb := 3 * Kp * I
  have hGb : 0 ≤ Gb := mul_nonneg (mul_nonneg (by norm_num) hKp) hI
  set DGb := 3 * 1 * Kp * J + 3 * 1 * Kp * I
  have hDGb : 0 ≤ DGb := add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hKp) hJ)
    (mul_nonneg (mul_nonneg (by norm_num) hKp) hI)
  refine ⟨3 * 4 * Gb + (3 * 1 * 4 * DGb + 3 * 1 * 1 * Gb), by positivity, ?_⟩
  intro h b U hU hDU hh2 hb2 hlow hh hh' hb hb' nh nh' nb nb'
  set D : Set (EuclideanSpace ℝ (Fin 2)) := closedBall 0 1 with hDdef
  set S : Set (EuclideanSpace ℝ (Fin 3)) := closure (boundaryHalfBall (1 / 4)) with hSdef
  have hlowD : ∀ y ∈ D, lam ≤ b y := fun y hy => hlow y (hDU hy)
  have hne : ∀ y ∈ U, b y ≠ 0 := fun y hy => (hlam.trans_le (hlow y hy)).ne'
  have hh1 : ContDiffOn ℝ 1 h U := hh2.of_le (by norm_num)
  have hb1 : ContDiffOn ℝ 1 b U := hb2.of_le (by norm_num)
  have hDb1 : ContDiffOn ℝ 1 (fderiv ℝ b) U := hb2.fderiv_of_isOpen hU (by norm_num)
  have hi2 : ContDiffOn ℝ 2 (fun y => (b y)⁻¹) U := hb2.inv hne
  have hi1 : ContDiffOn ℝ 1 (fun y => (b y)⁻¹) U := hi2.of_le (by norm_num)
  have hmul : ‖ContinuousLinearMap.mul ℝ ℝ‖ ≤ 1 := ContinuousLinearMap.opNorm_mul_le ℝ ℝ
  -- the reciprocal
  obtain ⟨hi, ni⟩ := boundaryNeumann_hasC1HolderOn_inv hU hDU hb1 hb hlam hlowD
  have niI : nondivC1HolderNorm α (fun y => (b y)⁻¹) D ≤ I :=
    ni.trans (boundaryNeumann_lift_inv_bound_mono hl hb.norm_nonneg (nb.trans hKKp))
  obtain ⟨hii, nii⟩ := boundaryNeumann_hasC1HolderOn_bilinear hU hDU hi1 hi1 hi hi
    (ContinuousLinearMap.mul ℝ ℝ)
  have hii1 : ContDiffOn ℝ 1
      (fun y => ContinuousLinearMap.mul ℝ ℝ (b y)⁻¹ (b y)⁻¹) U :=
    ((ContinuousLinearMap.mul ℝ ℝ).contDiff.comp_contDiffOn hi1).clm_apply hi1
  have hBi : ‖(-(ContinuousLinearMap.lsmul ℝ ℝ :
      ℝ →L[ℝ] (EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) →L[ℝ]
        (EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)))‖ ≤ 1 := by
    rw [norm_neg]; exact ContinuousLinearMap.opNorm_lsmul_le
  obtain ⟨hdi, ndi⟩ := boundaryNeumann_hasC1HolderOn_bilinear hU hDU hii1 hDb1 hii hb'
    (-(ContinuousLinearMap.lsmul ℝ ℝ :
      ℝ →L[ℝ] (EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) →L[ℝ]
        (EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)))
  obtain ⟨hDi, nDi⟩ := boundaryNeumann_hasC1HolderOn_congr_open hU hDU
    (g := fderiv ℝ (fun y => (b y)⁻¹)) (fun y hy => (boundaryNeumann_fderiv_inv
      ((hb1.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hy))
      (hne y hy)).symm) hdi
  have nDiJ : nondivC1HolderNorm α (fderiv ℝ (fun y => (b y)⁻¹)) D ≤ J := by
    have e1 := boundaryNeumann_lift_triple_le (norm_nonneg _) hi.norm_nonneg hi.norm_nonneg
      hmul niI niI
    refine nDi.trans (ndi.trans ?_)
    exact boundaryNeumann_lift_triple_le (norm_nonneg _) hii.norm_nonneg hb'.norm_nonneg hBi
      (nii.trans e1) (nb'.trans hKKp)
  -- the quotient
  set g : EuclideanSpace ℝ (Fin 2) → ℝ := fun y => h y * (b y)⁻¹ with hgdef
  have hg2 : ContDiffOn ℝ 2 g U := hh2.mul hi2
  have hg1 : ContDiffOn ℝ 1 g U := hg2.of_le (by norm_num)
  obtain ⟨hg, ng⟩ := boundaryNeumann_hasC1HolderOn_mul hU hDU hh1 hi1 hh hi
  have ngG : nondivC1HolderNorm α g D ≤ Gb :=
    ng.trans (boundaryNeumann_lift_pair_le hh.norm_nonneg hi.norm_nonneg (nh.trans hKKp) niI)
  obtain ⟨hDg, nDg⟩ := boundaryNeumann_hasC2HolderOn_bilinear hU hDU hh2 hi2 hh hh' hi hDi
    (ContinuousLinearMap.mul ℝ ℝ)
  have hgfun : (fun y => ContinuousLinearMap.mul ℝ ℝ (h y) (b y)⁻¹) = g :=
    funext fun y => by simp [g]
  rw [hgfun] at hDg nDg
  have nDgG : nondivC1HolderNorm α (fderiv ℝ g) D ≤ DGb :=
    nDg.trans (add_le_add
      (boundaryNeumann_lift_triple_le (norm_nonneg _) hh.norm_nonneg hDi.norm_nonneg hmul
        (nh.trans hKKp) nDiJ)
      (boundaryNeumann_lift_triple_le (norm_nonneg _) hh'.norm_nonneg hi.norm_nonneg hmul
        (nh'.trans hKKp) niI))
  -- the projection and the normal coordinate
  set P := graphProjectionN 2 with hPdef
  have hP : ‖P‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
    rw [one_mul]; exact boundary_neumann_norm_projection_le x)
  let ℓ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ := EuclideanSpace.proj (Fin.last 2)
  have hℓ : ‖ℓ‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
    have := norm_sq_graphProjectionN x
    have h0 : (x (Fin.last 2)) ^ 2 ≤ ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖P x‖]
    rw [one_mul]
    have h1 : |x (Fin.last 2)| ≤ ‖x‖ := by
      nlinarith [sq_abs (x (Fin.last 2)), abs_nonneg (x (Fin.last 2)), norm_nonneg x]
    simpa [ℓ, Real.norm_eq_abs] using h1)
  have hS1 : S ⊆ closedBall 0 1 := fun x hx =>
    closedBall_subset_closedBall (by norm_num : (1 / 4 : ℝ) ≤ 1)
      ((closure_mono inter_subset_left).trans closure_ball_subset_closedBall hx)
  have hST : ∀ x ∈ S, P x ∈ D := fun x hx => boundary_neumann_projection_closedBall (hS1 hx)
  set O : Set (EuclideanSpace ℝ (Fin 3)) := P ⁻¹' U with hOdef
  have hO : IsOpen O := hU.preimage P.continuous
  have hSO : S ⊆ O := fun x hx => hDU (hST x hx)
  set G : EuclideanSpace ℝ (Fin 3) → ℝ := fun x => g (P x) with hGdef
  have hG2 : ContDiffOn ℝ 2 G O := hg2.comp P.contDiff.contDiffOn (fun _ hx => hx)
  have hG1 : ContDiffOn ℝ 1 G O := hG2.of_le (by norm_num)
  obtain ⟨hG, nG⟩ := boundaryNeumann_hasC1HolderOn_precomp hα.le hU hDU hg1 hg P hP hST
  obtain ⟨hDG, nDG⟩ := boundaryNeumann_hasC2HolderOn_precomp hα.le hU hDU hg2 hDg P hP hST
  obtain ⟨⟨hl1, nl1⟩, hl2, nl2⟩ := boundaryNeumann_hasC1HolderOn_clm hα.le hα1 ℓ hS1
  have hℓ2 : ContDiffOn ℝ 2 ℓ O := ℓ.contDiff.contDiffOn
  have hℓ1 : ContDiffOn ℝ 1 ℓ O := ℓ.contDiff.contDiffOn
  -- the lift
  have hq : (fun x => ℓ x * G x) = boundaryNeumannLift h b :=
    funext fun x => by simp [ℓ, G, g, P, boundaryNeumannLift, div_eq_mul_inv]
  have hq' : (fun x => ContinuousLinearMap.mul ℝ ℝ (ℓ x) (G x)) = boundaryNeumannLift h b :=
    funext fun x => by simp [ℓ, G, g, P, boundaryNeumannLift, div_eq_mul_inv]
  obtain ⟨hq1, nq1⟩ := boundaryNeumann_hasC1HolderOn_mul hO hSO hℓ1 hG1 hl1 hG
  obtain ⟨hq2, nq2⟩ := boundaryNeumann_hasC2HolderOn_bilinear hO hSO hℓ2 hG2 hl1 hl2 hG hDG
    (ContinuousLinearMap.mul ℝ ℝ)
  have hqO : ContDiffOn ℝ 2 (fun x => ℓ x * G x) O := hℓ2.mul hG2
  rw [hq] at hq1 nq1 hqO
  rw [hq'] at hq2 nq2
  have nq1' : nondivC1HolderNorm α (boundaryNeumannLift h b) S ≤ 3 * 4 * Gb :=
    nq1.trans (boundaryNeumann_lift_pair_le hl1.norm_nonneg hG.norm_nonneg
      (nl1.trans (by linarith)) (nG.trans ngG))
  have nq2' : nondivC1HolderNorm α (fderiv ℝ (boundaryNeumannLift h b)) S ≤
      3 * 1 * 4 * DGb + 3 * 1 * 1 * Gb :=
    nq2.trans (add_le_add
      (boundaryNeumann_lift_triple_le (norm_nonneg _) hl1.norm_nonneg hDG.norm_nonneg hmul
        (nl1.trans (by linarith)) (nDG.trans nDgG))
      (boundaryNeumann_lift_triple_le (norm_nonneg _) hl2.norm_nonneg hG.norm_nonneg hmul
        (nl2.trans hℓ) (nG.trans ngG)))
  have hball : ball (0 : EuclideanSpace ℝ (Fin 3)) 1 ⊆ O := fun x hx =>
    hDU (boundary_neumann_projection_closedBall (ball_subset_closedBall hx))
  obtain ⟨e1, e2⟩ := boundaryNeumannC2Entry_holder_of_hasC1HolderOn hO hSO hqO hq2
  have hQ1 : nondivC1HolderNorm α (fderiv ℝ (boundaryNeumannLift h b)) S ≤
      3 * 4 * Gb + (3 * 1 * 4 * DGb + 3 * 1 * 1 * Gb) := by linarith
  refine ⟨hqO.mono hball, hq1, by linarith, hq2, hQ1, fun i j x hx y hy => ?_,
    fun i j x hx => (e2 i j x hx).trans hQ1⟩
  exact (e1 i j x hx y hy).trans
    (mul_le_mul_of_nonneg_right hQ1 (Real.rpow_nonneg dist_nonneg α))

end LiquidDrop
