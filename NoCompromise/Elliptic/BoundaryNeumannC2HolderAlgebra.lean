module

public import NoCompromise.Elliptic.NondivSchauderNorm

@[expose] public section

/-!
# Hölder algebra for the boundary Neumann lift

C¹,α is closed under continuous bilinear maps and under inversion of real
functions bounded below by a positive constant, with explicit constants. The
sets may be closed: the functions are C¹ on an open neighbourhood, so the
Fréchet derivative on the set is the actual derivative.
-/

noncomputable section
open Set
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Hölder data depend only on the values on the set. -/
lemma boundaryNeumann_holder_congr {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {α : ℝ} {f g : E → F} {U : Set E} (hf : HasFiniteHolderNormOn α f U)
    (he : EqOn f g U) :
    HasFiniteHolderNormOn α g U ∧ holderNorm α g U ≤ holderNorm α f U := by
  have hA := holderUniformNorm_nonneg hf.uniform_bounded
  have hB := hf.seminorm_nonneg
  have hv : ∀ x ∈ U, ‖g x‖ ≤ holderUniformNorm f U := fun x hx => by
    rw [← he hx]; exact norm_le_holderUniformNorm hf.uniform_bounded hx
  have hh : ∀ x ∈ U, ∀ y ∈ U, ‖g x - g y‖ / ‖x - y‖ ^ α ≤ holderSeminorm α f U :=
    fun x hx y hy => by rw [← he hx, ← he hy]; exact schauder_holder_quotient_le hf hx hy
  exact ⟨HasFiniteHolderNormOn.of_bounds hA hB hv hh, holderNorm_le hA hB hv hh⟩

/-- `nondiv_holder_bilinear` with any bilinear map of operator norm at most `K`. -/
lemma boundaryNeumann_holder_bilinear_le {E F G H : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {α K : ℝ} {f : E → F} {g : E → G} {U : Set E}
    (hf : HasFiniteHolderNormOn α f U) (hg : HasFiniteHolderNormOn α g U)
    (B : F →L[ℝ] G →L[ℝ] H) (hB : ‖B‖ ≤ K) :
    HasFiniteHolderNormOn α (fun x => B (f x) (g x)) U ∧
      holderNorm α (fun x => B (f x) (g x)) U ≤
        3 * K * holderNorm α f U * holderNorm α g U := by
  obtain ⟨h, n⟩ := nondiv_holder_bilinear hf hg B
  refine ⟨h, n.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hB (by norm_num)) hf.norm_nonneg) hg.norm_nonneg

/-- C¹,α on a set `S` is closed under continuous bilinear maps, when both factors are C¹ on an
open neighbourhood `O` of `S`. The C¹,α norm is at most `3 ‖B‖` times the product of the norms. -/
theorem boundaryNeumann_hasC1HolderOn_bilinear {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {α : ℝ} {f : E → F} {g : E → G} {S O : Set E} (hO : IsOpen O) (hSO : S ⊆ O)
    (hfO : ContDiffOn ℝ 1 f O) (hgO : ContDiffOn ℝ 1 g O)
    (hf : HasC1HolderOn α f S) (hg : HasC1HolderOn α g S)
    (B : F →L[ℝ] G →L[ℝ] H) :
    HasC1HolderOn α (fun x => B (f x) (g x)) S ∧
      nondivC1HolderNorm α (fun x => B (f x) (g x)) S ≤
        3 * ‖B‖ * nondivC1HolderNorm α f S * nondivC1HolderNorm α g S := by
  have hdf : ∀ x ∈ S, DifferentiableAt ℝ f x := fun x hx =>
    (hfO.differentiableOn one_ne_zero).differentiableAt (hO.mem_nhds (hSO hx))
  have hdg : ∀ x ∈ S, DifferentiableAt ℝ g x := fun x hx =>
    (hgO.differentiableOn one_ne_zero).differentiableAt (hO.mem_nhds (hSO hx))
  obtain ⟨h0, n0⟩ := nondiv_holder_bilinear hf.function_holder hg.function_holder B
  obtain ⟨h1, n1⟩ := boundaryNeumann_holder_bilinear_le hf.function_holder hg.derivative_holder
    (B.precompR E) (ContinuousLinearMap.norm_precompR_le _ B)
  obtain ⟨h2, n2⟩ := boundaryNeumann_holder_bilinear_le hf.derivative_holder hg.function_holder
    (B.precompL E) (ContinuousLinearMap.norm_precompL_le _ B)
  obtain ⟨h3, n3⟩ := schauder_holder_add h1 h2
  obtain ⟨h4, n4⟩ := boundaryNeumann_holder_congr h3
    (g := fderiv ℝ (fun x => B (f x) (g x)))
    (fun x hx => (B.fderiv_of_bilinear (hdf x hx) (hdg x hx)).symm)
  have hcd : ContDiffOn ℝ 1 (fun x => B (f x) (g x)) S :=
    (B.contDiff.comp_contDiffOn hf.contDiff).clm_apply hg.contDiff
  refine ⟨⟨hcd, h0, h4⟩, ?_⟩
  have ha0 := hf.function_holder.norm_nonneg
  have ha1 := hf.derivative_holder.norm_nonneg
  have hb0 := hg.function_holder.norm_nonneg
  have hb1 := hg.derivative_holder.norm_nonneg
  have h11 : 0 ≤ 3 * ‖B‖ * holderNorm α (fderiv ℝ f) S * holderNorm α (fderiv ℝ g) S := by
    have := norm_nonneg B
    positivity
  unfold nondivC1HolderNorm
  have hexp : 3 * ‖B‖ * (holderNorm α f S + holderNorm α (fderiv ℝ f) S) *
      (holderNorm α g S + holderNorm α (fderiv ℝ g) S) =
      3 * ‖B‖ * holderNorm α f S * holderNorm α g S +
      3 * ‖B‖ * holderNorm α f S * holderNorm α (fderiv ℝ g) S +
      3 * ‖B‖ * holderNorm α (fderiv ℝ f) S * holderNorm α g S +
      3 * ‖B‖ * holderNorm α (fderiv ℝ f) S * holderNorm α (fderiv ℝ g) S := by ring
  rw [hexp]
  linarith

/-- The open-set case of `boundaryNeumann_hasC1HolderOn_bilinear`. -/
theorem boundaryNeumann_hasC1HolderOn_bilinear_of_isOpen {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {α : ℝ} {f : E → F} {g : E → G} {U : Set E} (hU : IsOpen U)
    (hf : HasC1HolderOn α f U) (hg : HasC1HolderOn α g U)
    (B : F →L[ℝ] G →L[ℝ] H) :
    HasC1HolderOn α (fun x => B (f x) (g x)) U ∧
      nondivC1HolderNorm α (fun x => B (f x) (g x)) U ≤
        3 * ‖B‖ * nondivC1HolderNorm α f U * nondivC1HolderNorm α g U :=
  boundaryNeumann_hasC1HolderOn_bilinear hU subset_rfl hf.contDiff hg.contDiff hf hg B

/-- The C⁰,α bound for the reciprocal of a real function bounded below by `lam > 0`. -/
lemma boundaryNeumann_holder_inv {E : Type*} [NormedAddCommGroup E]
    {α lam : ℝ} {b : E → ℝ} {S : Set E} (hb : HasFiniteHolderNormOn α b S) (hlam : 0 < lam)
    (hlow : ∀ x ∈ S, lam ≤ b x) :
    HasFiniteHolderNormOn α (fun x => (b x)⁻¹) S ∧
      holderNorm α (fun x => (b x)⁻¹) S ≤ lam⁻¹ + lam⁻¹ ^ 2 * holderNorm α b S := by
  have hA : 0 ≤ lam⁻¹ := inv_nonneg.mpr hlam.le
  have hB : 0 ≤ lam⁻¹ ^ 2 * holderNorm α b S := mul_nonneg (by positivity) hb.norm_nonneg
  have hv : ∀ x ∈ S, ‖(b x)⁻¹‖ ≤ lam⁻¹ := by
    intro x hx
    have hbx : 0 < b x := hlam.trans_le (hlow x hx)
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hbx)]
    exact inv_anti₀ hlam (hlow x hx)
  have hh : ∀ x ∈ S, ∀ y ∈ S, ‖(b x)⁻¹ - (b y)⁻¹‖ / ‖x - y‖ ^ α ≤
      lam⁻¹ ^ 2 * holderNorm α b S := by
    intro x hx y hy
    have hbx : 0 < b x := hlam.trans_le (hlow x hx)
    have hby : 0 < b y := hlam.trans_le (hlow y hy)
    have hp : 0 ≤ ‖x - y‖ ^ α := by positivity
    have hq : ‖b x - b y‖ / ‖x - y‖ ^ α ≤ holderNorm α b S :=
      (schauder_holder_quotient_le hb hx hy).trans (le_add_of_nonneg_left
        (holderUniformNorm_nonneg hb.uniform_bounded))
    have hd : ‖(b x)⁻¹ - (b y)⁻¹‖ ≤ lam⁻¹ ^ 2 * ‖b x - b y‖ := by
      rw [inv_sub_inv hbx.ne' hby.ne', Real.norm_eq_abs, Real.norm_eq_abs, abs_div,
        abs_of_pos (mul_pos hbx hby), abs_sub_comm, div_le_iff₀ (mul_pos hbx hby)]
      have h1 : 1 ≤ lam⁻¹ ^ 2 * (b x * b y) := by
        rw [inv_pow, ← div_eq_inv_mul, le_div_iff₀ (by positivity), one_mul]
        nlinarith [hlow x hx, hlow y hy]
      nlinarith [abs_nonneg (b x - b y)]
    calc
      _ ≤ lam⁻¹ ^ 2 * ‖b x - b y‖ / ‖x - y‖ ^ α := div_le_div_of_nonneg_right hd hp
      _ = lam⁻¹ ^ 2 * (‖b x - b y‖ / ‖x - y‖ ^ α) := mul_div_assoc _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hq (by positivity)
  exact ⟨HasFiniteHolderNormOn.of_bounds hA hB hv hh, holderNorm_le hA hB hv hh⟩

/-- The derivative of the reciprocal, written as a continuous bilinear expression. -/
lemma boundaryNeumann_fderiv_inv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {b : E → ℝ} {x : E} (hb : DifferentiableAt ℝ b x) (hx : b x ≠ 0) :
    fderiv ℝ (fun y => (b y)⁻¹) x =
      (-(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ)))
        (ContinuousLinearMap.mul ℝ ℝ (b x)⁻¹ (b x)⁻¹) (fderiv ℝ b x) := by
  have hd := (hasFDerivAt_inv (𝕜 := ℝ) hx).comp x hb.hasFDerivAt
  rw [show (fun y => (b y)⁻¹) = (fun y : ℝ => y⁻¹) ∘ b from rfl, hd.fderiv]
  ext v
  simp
  ring

/-- C¹,α is closed under inversion of real functions bounded below by `lam > 0`, when the
function is C¹ on an open neighbourhood `O` of `S`. With `K = lam⁻¹ + lam⁻² N`, `N` the C¹,α norm,
the reciprocal has C¹,α norm at most `K + 9 K² N`. -/
theorem boundaryNeumann_hasC1HolderOn_inv {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α lam : ℝ} {b : E → ℝ} {S O : Set E} (hO : IsOpen O) (hSO : S ⊆ O)
    (hbO : ContDiffOn ℝ 1 b O) (hb : HasC1HolderOn α b S) (hlam : 0 < lam)
    (hlow : ∀ x ∈ S, lam ≤ b x) :
    HasC1HolderOn α (fun x => (b x)⁻¹) S ∧
      nondivC1HolderNorm α (fun x => (b x)⁻¹) S ≤
        (lam⁻¹ + lam⁻¹ ^ 2 * nondivC1HolderNorm α b S) +
          9 * (lam⁻¹ + lam⁻¹ ^ 2 * nondivC1HolderNorm α b S) ^ 2 *
            nondivC1HolderNorm α b S := by
  have hne : ∀ x ∈ S, b x ≠ 0 := fun x hx => (hlam.trans_le (hlow x hx)).ne'
  have hdb : ∀ x ∈ S, DifferentiableAt ℝ b x := fun x hx =>
    (hbO.differentiableOn one_ne_zero).differentiableAt (hO.mem_nhds (hSO hx))
  set N := nondivC1HolderNorm α b S
  set K := lam⁻¹ + lam⁻¹ ^ 2 * N
  have hN := hb.norm_nonneg
  have hK : 0 ≤ K := by positivity
  obtain ⟨hk, nk⟩ := boundaryNeumann_holder_inv hb.function_holder hlam hlow
  have nk' : holderNorm α (fun x => (b x)⁻¹) S ≤ K := by
    have := mul_le_mul_of_nonneg_left hb.function_norm_le (by positivity : (0 : ℝ) ≤ lam⁻¹ ^ 2)
    exact nk.trans (by simp only [K, N]; linarith)
  obtain ⟨hm, nm⟩ := boundaryNeumann_holder_bilinear_le hk hk (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousLinearMap.opNorm_mul_le ℝ ℝ)
  have hL : ‖(-(ContinuousLinearMap.lsmul ℝ ℝ :
      ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ)))‖ ≤ 1 := by
    rw [norm_neg]; exact ContinuousLinearMap.opNorm_lsmul_le
  obtain ⟨hD, nD⟩ := boundaryNeumann_holder_bilinear_le hm hb.derivative_holder _ hL
  obtain ⟨hD', nD'⟩ := boundaryNeumann_holder_congr hD
    (g := fderiv ℝ (fun x => (b x)⁻¹))
    (fun x hx => (boundaryNeumann_fderiv_inv (hdb x hx) (hne x hx)).symm)
  refine ⟨⟨hb.contDiff.inv hne, hk, hD'⟩, ?_⟩
  have hk0 := hk.norm_nonneg
  have hm0 := hm.norm_nonneg
  have hm' : holderNorm α (fun x => ContinuousLinearMap.mul ℝ ℝ (b x)⁻¹ (b x)⁻¹) S ≤
      3 * K ^ 2 := by
    calc
      _ ≤ 3 * 1 * holderNorm α (fun x => (b x)⁻¹) S * holderNorm α (fun x => (b x)⁻¹) S := nm
      _ ≤ 3 * 1 * K * K := by gcongr
      _ = 3 * K ^ 2 := by ring
  have hdN : holderNorm α (fderiv ℝ b) S ≤ N := hb.derivative_norm_le
  have hd0 := hb.derivative_holder.norm_nonneg
  have hD2 : holderNorm α (fderiv ℝ (fun x => (b x)⁻¹)) S ≤ 9 * K ^ 2 * N := by
    calc
      _ ≤ _ := nD'
      _ ≤ 3 * 1 * holderNorm α (fun x => ContinuousLinearMap.mul ℝ ℝ (b x)⁻¹ (b x)⁻¹) S *
          holderNorm α (fderiv ℝ b) S := nD
      _ ≤ 3 * 1 * (3 * K ^ 2) * N := by gcongr
      _ = 9 * K ^ 2 * N := by ring
  unfold nondivC1HolderNorm
  linarith

/-- Products of real C¹,α functions: the C¹,α norm is at most `3 N_f N_g`. -/
theorem boundaryNeumann_hasC1HolderOn_mul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : ℝ} {f g : E → ℝ} {S O : Set E} (hO : IsOpen O) (hSO : S ⊆ O)
    (hfO : ContDiffOn ℝ 1 f O) (hgO : ContDiffOn ℝ 1 g O)
    (hf : HasC1HolderOn α f S) (hg : HasC1HolderOn α g S) :
    HasC1HolderOn α (fun x => f x * g x) S ∧
      nondivC1HolderNorm α (fun x => f x * g x) S ≤
        3 * nondivC1HolderNorm α f S * nondivC1HolderNorm α g S := by
  obtain ⟨h, n⟩ := boundaryNeumann_hasC1HolderOn_bilinear hO hSO hfO hgO hf hg
    (ContinuousLinearMap.mul ℝ ℝ)
  refine ⟨h, n.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    ((mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_mul_le ℝ ℝ)
      (by norm_num)).trans_eq (mul_one 3)) hf.norm_nonneg) hg.norm_nonneg

/-- Scalar multiples of C¹,α fields by real C¹,α functions: the norm is at most `3 N_c N_v`. -/
theorem boundaryNeumann_hasC1HolderOn_smul {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ} {c : E → ℝ} {v : E → F} {S O : Set E} (hO : IsOpen O) (hSO : S ⊆ O)
    (hcO : ContDiffOn ℝ 1 c O) (hvO : ContDiffOn ℝ 1 v O)
    (hc : HasC1HolderOn α c S) (hv : HasC1HolderOn α v S) :
    HasC1HolderOn α (fun x => c x • v x) S ∧
      nondivC1HolderNorm α (fun x => c x • v x) S ≤
        3 * nondivC1HolderNorm α c S * nondivC1HolderNorm α v S := by
  obtain ⟨h, n⟩ := boundaryNeumann_hasC1HolderOn_bilinear hO hSO hcO hvO hc hv
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F)
  refine ⟨h, n.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    ((mul_le_mul_of_nonneg_left ContinuousLinearMap.opNorm_lsmul_le
      (by norm_num)).trans_eq (mul_one 3)) hc.norm_nonneg) hv.norm_nonneg

/-- Quotients by a real C¹,α function bounded below by `lam > 0`. With `K = lam⁻¹ + lam⁻² N_b`,
the C¹,α norm of `f / b` is at most `3 N_f (K + 9 K² N_b)`. -/
theorem boundaryNeumann_hasC1HolderOn_div {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α lam : ℝ} {f b : E → ℝ} {S O : Set E} (hO : IsOpen O) (hSO : S ⊆ O)
    (hfO : ContDiffOn ℝ 1 f O) (hbO : ContDiffOn ℝ 1 b O)
    (hf : HasC1HolderOn α f S) (hb : HasC1HolderOn α b S) (hlam : 0 < lam)
    (hlow : ∀ x ∈ S, lam ≤ b x) :
    HasC1HolderOn α (fun x => f x / b x) S ∧
      nondivC1HolderNorm α (fun x => f x / b x) S ≤
        3 * nondivC1HolderNorm α f S *
          ((lam⁻¹ + lam⁻¹ ^ 2 * nondivC1HolderNorm α b S) +
            9 * (lam⁻¹ + lam⁻¹ ^ 2 * nondivC1HolderNorm α b S) ^ 2 *
              nondivC1HolderNorm α b S) := by
  let O' := O ∩ b ⁻¹' {0}ᶜ
  have hO' : IsOpen O' := hbO.continuousOn.isOpen_inter_preimage hO isOpen_compl_singleton
  have hSO' : S ⊆ O' := fun x hx =>
    ⟨hSO hx, (hlam.trans_le (hlow x hx)).ne'⟩
  have hiO : ContDiffOn ℝ 1 (fun x => (b x)⁻¹) O' :=
    (hbO.mono inter_subset_left).inv (fun x hx => hx.2)
  obtain ⟨hi, ni⟩ := boundaryNeumann_hasC1HolderOn_inv hO hSO hbO hb hlam hlow
  obtain ⟨h, n⟩ := boundaryNeumann_hasC1HolderOn_mul hO' hSO'
    (hfO.mono inter_subset_left) hiO hf hi
  simp only [← div_eq_mul_inv] at h n
  exact ⟨h, n.trans (mul_le_mul_of_nonneg_left ni (mul_nonneg (by norm_num) hf.norm_nonneg))⟩

/-- Sums of C¹,α functions, with the norms adding. -/
theorem boundaryNeumann_hasC1HolderOn_add {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ} {f g : E → F} {S O : Set E} (hO : IsOpen O) (hSO : S ⊆ O)
    (hfO : ContDiffOn ℝ 1 f O) (hgO : ContDiffOn ℝ 1 g O)
    (hf : HasC1HolderOn α f S) (hg : HasC1HolderOn α g S) :
    HasC1HolderOn α (fun x => f x + g x) S ∧
      nondivC1HolderNorm α (fun x => f x + g x) S ≤
        nondivC1HolderNorm α f S + nondivC1HolderNorm α g S := by
  have hdf : ∀ x ∈ S, DifferentiableAt ℝ f x := fun x hx =>
    (hfO.differentiableOn one_ne_zero).differentiableAt (hO.mem_nhds (hSO hx))
  have hdg : ∀ x ∈ S, DifferentiableAt ℝ g x := fun x hx =>
    (hgO.differentiableOn one_ne_zero).differentiableAt (hO.mem_nhds (hSO hx))
  obtain ⟨h0, n0⟩ := schauder_holder_add hf.function_holder hg.function_holder
  obtain ⟨h1, n1⟩ := schauder_holder_add hf.derivative_holder hg.derivative_holder
  obtain ⟨h2, n2⟩ := boundaryNeumann_holder_congr h1
    (g := fderiv ℝ (fun x => f x + g x))
    (fun x hx => (fderiv_add (hdf x hx) (hdg x hx)).symm)
  refine ⟨⟨hf.contDiff.add hg.contDiff, h0, h2⟩, ?_⟩
  unfold nondivC1HolderNorm
  linarith

/-- Differences of C⁰,α functions, with the norms adding. -/
lemma boundaryNeumann_holder_sub {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {α : ℝ} {f g : E → F} {U : Set E}
    (hf : HasFiniteHolderNormOn α f U) (hg : HasFiniteHolderNormOn α g U) :
    HasFiniteHolderNormOn α (fun x => f x - g x) U ∧
      holderNorm α (fun x => f x - g x) U ≤ holderNorm α f U + holderNorm α g U := by
  have hA := add_nonneg (holderUniformNorm_nonneg hf.uniform_bounded)
    (holderUniformNorm_nonneg hg.uniform_bounded)
  have hB := add_nonneg hf.seminorm_nonneg hg.seminorm_nonneg
  have hv : ∀ x ∈ U, ‖f x - g x‖ ≤ holderUniformNorm f U + holderUniformNorm g U :=
    fun x hx => (norm_sub_le _ _).trans (add_le_add
      (norm_le_holderUniformNorm hf.uniform_bounded hx)
      (norm_le_holderUniformNorm hg.uniform_bounded hx))
  have hh : ∀ x ∈ U, ∀ y ∈ U, ‖(f x - g x) - (f y - g y)‖ / ‖x - y‖ ^ α ≤
      holderSeminorm α f U + holderSeminorm α g U := by
    intro x hx y hy
    have he : (f x - g x) - (f y - g y) = (f x - f y) - (g x - g y) := by abel
    rw [he]
    calc
      _ ≤ (‖f x - f y‖ + ‖g x - g y‖) / ‖x - y‖ ^ α :=
        div_le_div_of_nonneg_right (norm_sub_le _ _) (by positivity)
      _ = ‖f x - f y‖ / ‖x - y‖ ^ α + ‖g x - g y‖ / ‖x - y‖ ^ α := add_div _ _ _
      _ ≤ _ := add_le_add (schauder_holder_quotient_le hf hx hy)
        (schauder_holder_quotient_le hg hx hy)
  refine ⟨HasFiniteHolderNormOn.of_bounds hA hB hv hh, (holderNorm_le hA hB hv hh).trans_eq ?_⟩
  dsimp [holderNorm]
  ring

/-- Differences of C¹,α functions, with the norms adding. -/
theorem boundaryNeumann_hasC1HolderOn_sub {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ} {f g : E → F} {S O : Set E} (hO : IsOpen O) (hSO : S ⊆ O)
    (hfO : ContDiffOn ℝ 1 f O) (hgO : ContDiffOn ℝ 1 g O)
    (hf : HasC1HolderOn α f S) (hg : HasC1HolderOn α g S) :
    HasC1HolderOn α (fun x => f x - g x) S ∧
      nondivC1HolderNorm α (fun x => f x - g x) S ≤
        nondivC1HolderNorm α f S + nondivC1HolderNorm α g S := by
  have hdf : ∀ x ∈ S, DifferentiableAt ℝ f x := fun x hx =>
    (hfO.differentiableOn one_ne_zero).differentiableAt (hO.mem_nhds (hSO hx))
  have hdg : ∀ x ∈ S, DifferentiableAt ℝ g x := fun x hx =>
    (hgO.differentiableOn one_ne_zero).differentiableAt (hO.mem_nhds (hSO hx))
  obtain ⟨h0, n0⟩ := boundaryNeumann_holder_sub hf.function_holder hg.function_holder
  obtain ⟨h1, n1⟩ := boundaryNeumann_holder_sub hf.derivative_holder hg.derivative_holder
  obtain ⟨h2, n2⟩ := boundaryNeumann_holder_congr h1
    (g := fderiv ℝ (fun x => f x - g x))
    (fun x hx => (fderiv_sub (hdf x hx) (hdg x hx)).symm)
  refine ⟨⟨hf.contDiff.sub hg.contDiff, h0, h2⟩, ?_⟩
  unfold nondivC1HolderNorm
  linarith

end LiquidDrop
