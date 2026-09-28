import NoCompromise.Elliptic.NondivSchauderNorm

/-!
# `C^{k,α}` bookkeeping for the boundary Schauder iteration

`HasCkHolderOn k α f U K` says that `f` is `C^k` on an open set `U ⊇ K`, that all
iterated derivatives of order `≤ k` are bounded on `K`, and that the `k`-th one is
`α`-Hölder on `K`. We prove the order-reduction identity
`C^{k+1,α} ↔ (differentiable, bounded, fderiv ∈ C^{k,α})`, the inclusion
`C^{k+1,α} ⊆ C^{k,α}` on convex bounded sets, that `C^{k+1}` functions are `C^{k,α}`
on convex compact sets, and the algebra rules (sums, post-composition with continuous
linear maps, continuous bilinear maps, products, quotients) used in the all-orders
Schauder iteration, together with the characterisation through coordinate partials on
`ℝ³` and the comparison with `HasC1HolderOn`.
-/

noncomputable section
open Set Metric Filter
open scoped Topology
namespace LiquidDrop

/-- `f` is `C^{k,α}` on `K` relative to an open set `U ⊇ K`: `C^k` on `U`, all iterated
derivatives of order `≤ k` bounded on `K`, the `k`-th one `α`-Hölder on `K`. -/
structure HasCkHolderOn {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k : ℕ) (α : ℝ) (f : E → F) (U K : Set E) : Prop where
  contDiffOn : ContDiffOn ℝ k f U
  bounded : ∀ m ≤ k, ∃ B, ∀ x ∈ K, ‖iteratedFDeriv ℝ m f x‖ ≤ B
  holder : ∃ C, ∀ x ∈ K, ∀ y ∈ K,
    ‖iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k f y‖ ≤ C * dist x y ^ α

section General

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- A Lipschitz map on a bounded set is `α`-Hölder there, `α ≤ 1`. -/
lemma ckHolder_holder_of_lipschitz {α : ℝ} (hα1 : α ≤ 1) {K : Set E}
    (hK : Bornology.IsBounded K) {g : E → F} {L : ℝ} (hL : 0 ≤ L)
    (hg : ∀ x ∈ K, ∀ y ∈ K, ‖g x - g y‖ ≤ L * dist x y) :
    ∃ C, ∀ x ∈ K, ∀ y ∈ K, ‖g x - g y‖ ≤ C * dist x y ^ α := by
  refine ⟨L * diam K ^ (1 - α), fun x hx y hy => (hg x hx y hy).trans ?_⟩
  have hd : 0 ≤ dist x y := dist_nonneg
  calc L * dist x y = L * (dist x y ^ (1 - α) * dist x y ^ α) := by
        rw [← Real.rpow_add' hd (by norm_num), sub_add_cancel, Real.rpow_one]
    _ ≤ L * (diam K ^ (1 - α) * dist x y ^ α) := by
        apply mul_le_mul_of_nonneg_left _ hL
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hd _)
        exact Real.rpow_le_rpow hd (dist_le_diam_of_mem hK hx hy) (sub_nonneg.2 hα1)
    _ = L * diam K ^ (1 - α) * dist x y ^ α := by ring

/-- Differences of `(k+1)`-st derivatives of `f` and of `k`-th derivatives of
`fderiv ℝ f` have equal norms. -/
lemma ckHolder_norm_iteratedFDeriv_succ_sub (f : E → F) (k : ℕ) (x y : E) :
    ‖iteratedFDeriv ℝ (k + 1) f x - iteratedFDeriv ℝ (k + 1) f y‖ =
      ‖iteratedFDeriv ℝ k (fderiv ℝ f) x - iteratedFDeriv ℝ k (fderiv ℝ f) y‖ := by
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
  simp only [Function.comp_apply]
  rw [← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map]

lemma ckHolder_norm_iteratedFDeriv_zero_sub (f : E → F) (x y : E) :
    ‖iteratedFDeriv ℝ 0 f x - iteratedFDeriv ℝ 0 f y‖ = ‖f x - f y‖ := by
  rw [iteratedFDeriv_zero_eq_comp]
  simp only [Function.comp_apply]
  rw [← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map]

/-- `C^{0,α}`: continuous on `U`, bounded and `α`-Hölder on `K`. -/
theorem hasCkHolderOn_zero_iff {α : ℝ} {f : E → F} {U K : Set E} :
    HasCkHolderOn 0 α f U K ↔ ContinuousOn f U ∧ (∃ B, ∀ x ∈ K, ‖f x‖ ≤ B) ∧
      ∃ C, ∀ x ∈ K, ∀ y ∈ K, ‖f x - f y‖ ≤ C * dist x y ^ α := by
  constructor
  · rintro ⟨h1, h2, ⟨C, hC⟩⟩
    refine ⟨h1.continuousOn, ?_, C, fun x hx y hy => ?_⟩
    · obtain ⟨B, hB⟩ := h2 0 le_rfl
      exact ⟨B, fun x hx => by simpa [norm_iteratedFDeriv_zero] using hB x hx⟩
    · rw [← ckHolder_norm_iteratedFDeriv_zero_sub]; exact hC x hx y hy
  · rintro ⟨h1, ⟨B, hB⟩, ⟨C, hC⟩⟩
    refine ⟨by exact_mod_cast contDiffOn_zero.2 h1, fun m hm => ?_, C, fun x hx y hy => ?_⟩
    · obtain rfl : m = 0 := Nat.le_zero.1 hm
      exact ⟨B, fun x hx => by rw [norm_iteratedFDeriv_zero]; exact hB x hx⟩
    · rw [ckHolder_norm_iteratedFDeriv_zero_sub]; exact hC x hx y hy

/-- `HasCkHolderOn` only depends on the values on the open set `U`. -/
theorem HasCkHolderOn.congr {k : ℕ} {α : ℝ} {f g : E → F} {U K : Set E} (hU : IsOpen U)
    (hKU : K ⊆ U) (hf : HasCkHolderOn k α f U K) (hfg : EqOn g f U) :
    HasCkHolderOn k α g U K := by
  have key : ∀ m, ∀ x ∈ U, iteratedFDeriv ℝ m g x = iteratedFDeriv ℝ m f x := fun m x hx =>
    ((Filter.eventuallyEq_of_mem (hU.mem_nhds hx) hfg).iteratedFDeriv ℝ m).eq_of_nhds
  refine ⟨hf.contDiffOn.congr hfg, fun m hm => ?_, ?_⟩
  · obtain ⟨B, hB⟩ := hf.bounded m hm
    exact ⟨B, fun x hx => by rw [key m x (hKU hx)]; exact hB x hx⟩
  · obtain ⟨C, hC⟩ := hf.holder
    exact ⟨C, fun x hx y hy => by rw [key k x (hKU hx), key k y (hKU hy)]; exact hC x hx y hy⟩

/-- Order reduction: `f` is `C^{k+1,α}` iff it is differentiable on `U`, bounded on `K`,
and `fderiv ℝ f` is `C^{k,α}`. -/
theorem HasCkHolderOn.succ_iff {k : ℕ} {α : ℝ} {f : E → F} {U K : Set E} (hU : IsOpen U) :
    HasCkHolderOn (k + 1) α f U K ↔ DifferentiableOn ℝ f U ∧ (∃ B, ∀ x ∈ K, ‖f x‖ ≤ B) ∧
      HasCkHolderOn k α (fderiv ℝ f) U K := by
  have hcd : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) f U ↔
      DifferentiableOn ℝ f U ∧ ContDiffOn ℝ k (fderiv ℝ f) U := by
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    simp
  constructor
  · rintro ⟨h1, h2, ⟨C, hC⟩⟩
    obtain ⟨hd, hc⟩ := hcd.1 h1
    refine ⟨hd, ?_, hc, fun m hm => ?_, C, fun x hx y hy => ?_⟩
    · obtain ⟨B, hB⟩ := h2 0 (Nat.zero_le _)
      exact ⟨B, fun x hx => by simpa [norm_iteratedFDeriv_zero] using hB x hx⟩
    · obtain ⟨B, hB⟩ := h2 (m + 1) (by omega)
      exact ⟨B, fun x hx => by rw [norm_iteratedFDeriv_fderiv]; exact hB x hx⟩
    · rw [← ckHolder_norm_iteratedFDeriv_succ_sub]; exact hC x hx y hy
  · rintro ⟨hd, ⟨B, hB⟩, h1, h2, ⟨C, hC⟩⟩
    refine ⟨hcd.2 ⟨hd, h1⟩, fun m hm => ?_, C, fun x hx y hy => ?_⟩
    · rcases m with _ | m
      · exact ⟨B, fun x hx => by rw [norm_iteratedFDeriv_zero]; exact hB x hx⟩
      · obtain ⟨B', hB'⟩ := h2 m (by omega)
        exact ⟨B', fun x hx => by rw [← norm_iteratedFDeriv_fderiv]; exact hB' x hx⟩
    · rw [ckHolder_norm_iteratedFDeriv_succ_sub]; exact hC x hx y hy

/-- If `f` is `C^{k+1}` on the open set `U` and its `(k+1)`-st derivative is bounded on
the convex bounded set `K ⊆ U`, the `k`-th derivative is `α`-Hölder on `K`. -/
lemma ckHolder_holder_of_contDiffOn_succ {k : ℕ} {α : ℝ} (hα1 : α ≤ 1)
    {f : E → F} {U K : Set E} (hU : IsOpen U) (hKU : K ⊆ U) (hK : Convex ℝ K)
    (hKb : Bornology.IsBounded K) (hf : ContDiffOn ℝ (k + 1 : ℕ) f U) {B : ℝ}
    (hB : ∀ x ∈ K, ‖iteratedFDeriv ℝ (k + 1) f x‖ ≤ B) :
    ∃ C, ∀ x ∈ K, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k f y‖ ≤ C * dist x y ^ α := by
  have hdiff : ∀ x ∈ K, DifferentiableAt ℝ (iteratedFDeriv ℝ k f) x := fun x hx =>
    (hf.contDiffAt (hU.mem_nhds (hKU hx))).differentiableAt_iteratedFDeriv
      (by exact_mod_cast Nat.lt_succ_self k)
  have hbd : ∀ x ∈ K, ‖fderiv ℝ (iteratedFDeriv ℝ k f) x‖ ≤ max B 0 := fun x hx => by
    rw [norm_fderiv_iteratedFDeriv]; exact (hB x hx).trans (le_max_left _ _)
  refine ckHolder_holder_of_lipschitz hα1 hKb (le_max_right B 0) fun x hx y hy => ?_
  rw [dist_eq_norm]
  exact hK.norm_image_sub_le_of_norm_fderiv_le hdiff hbd hy hx

/-- `C^{k+1,α} ⊆ C^{k,α}` on a convex bounded set. -/
theorem HasCkHolderOn.of_succ {k : ℕ} {α : ℝ} (hα1 : α ≤ 1) {f : E → F}
    {U K : Set E} (hU : IsOpen U) (hKU : K ⊆ U) (hK : Convex ℝ K)
    (hKb : Bornology.IsBounded K) (hf : HasCkHolderOn (k + 1) α f U K) :
    HasCkHolderOn k α f U K := by
  obtain ⟨B, hB⟩ := hf.bounded (k + 1) le_rfl
  exact ⟨hf.contDiffOn.of_le (by exact_mod_cast Nat.le_succ k),
    fun m hm => hf.bounded m (hm.trans (Nat.le_succ k)),
    ckHolder_holder_of_contDiffOn_succ hα1 hU hKU hK hKb hf.contDiffOn hB⟩

/-- `C^{k,α} ⊆ C^{m,α}` for `m ≤ k` on a convex bounded set. -/
theorem HasCkHolderOn.mono_order {k m : ℕ} (hmk : m ≤ k) {α : ℝ} (hα1 : α ≤ 1) {f : E → F}
    {U K : Set E} (hU : IsOpen U) (hKU : K ⊆ U)
    (hK : Convex ℝ K) (hKb : Bornology.IsBounded K) (hf : HasCkHolderOn k α f U K) :
    HasCkHolderOn m α f U K := by
  revert hf
  induction k, hmk using Nat.le_induction with
  | base => exact id
  | succ n _ ih => exact fun hf => ih (hf.of_succ hα1 hU hKU hK hKb)

/-- A `C^{k+1}` function on an open set `U` is `C^{k,α}` on every convex compact
`K ⊆ U`. -/
theorem HasCkHolderOn.of_contDiffOn {k : ℕ} {α : ℝ} (hα1 : α ≤ 1)
    {f : E → F} {U K : Set E} (hU : IsOpen U) (hKU : K ⊆ U) (hK : Convex ℝ K)
    (hKc : IsCompact K) (hf : ContDiffOn ℝ (k + 1 : ℕ) f U) : HasCkHolderOn k α f U K := by
  have hbd : ∀ m ≤ k + 1, ∃ B, ∀ x ∈ K, ‖iteratedFDeriv ℝ m f x‖ ≤ B := by
    intro m hm
    have hcont : ContinuousOn (iteratedFDeriv ℝ m f) K := fun x hx =>
      ((hf.contDiffAt (hU.mem_nhds (hKU hx))).continuousAt_iteratedFDeriv
        (by exact_mod_cast hm)).continuousWithinAt
    exact hKc.exists_bound_of_continuousOn hcont
  obtain ⟨B, hB⟩ := hbd (k + 1) le_rfl
  exact ⟨hf.of_le (by exact_mod_cast Nat.le_succ k), fun m hm => hbd m (by omega),
    ckHolder_holder_of_contDiffOn_succ hα1 hU hKU hK hKc.isBounded hf hB⟩

/-- A smooth function on an open set `U` is `C^{k,α}` on every convex compact `K ⊆ U`,
for every `k`. -/
theorem HasCkHolderOn.of_contDiffOn_smooth {α : ℝ} (hα1 : α ≤ 1)
    {f : E → F} {U K : Set E} (hU : IsOpen U) (hKU : K ⊆ U) (hK : Convex ℝ K)
    (hKc : IsCompact K) (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f U) (k : ℕ) :
    HasCkHolderOn k α f U K :=
  HasCkHolderOn.of_contDiffOn hα1 hU hKU hK hKc (hf.of_le (by exact_mod_cast le_top))

/-- Sums of `C^{k,α}` functions. -/
theorem HasCkHolderOn.add {k : ℕ} {α : ℝ} {f g : E → F} {U K : Set E} (hU : IsOpen U)
    (hKU : K ⊆ U) (hf : HasCkHolderOn k α f U K) (hg : HasCkHolderOn k α g U K) :
    HasCkHolderOn k α (fun x => f x + g x) U K := by
  have key : ∀ m ≤ k, ∀ x ∈ K, iteratedFDeriv ℝ m (fun x => f x + g x) x =
      iteratedFDeriv ℝ m f x + iteratedFDeriv ℝ m g x := fun m hm x hx => by
    have hx' := hU.mem_nhds (hKU hx)
    exact iteratedFDeriv_add_apply ((hf.contDiffOn.contDiffAt hx').of_le (by exact_mod_cast hm))
      ((hg.contDiffOn.contDiffAt hx').of_le (by exact_mod_cast hm))
  obtain ⟨C₁, hC₁⟩ := hf.holder
  obtain ⟨C₂, hC₂⟩ := hg.holder
  refine ⟨hf.contDiffOn.add hg.contDiffOn, fun m hm => ?_, C₁ + C₂, fun x hx y hy => ?_⟩
  · obtain ⟨B₁, hB₁⟩ := hf.bounded m hm
    obtain ⟨B₂, hB₂⟩ := hg.bounded m hm
    exact ⟨B₁ + B₂, fun x hx => by
      rw [key m hm x hx]; exact (norm_add_le _ _).trans (add_le_add (hB₁ x hx) (hB₂ x hx))⟩
  · rw [key k le_rfl x hx, key k le_rfl y hy, add_sub_add_comm, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hC₁ x hx y hy) (hC₂ x hx y hy))

/-- Post-composition with a fixed continuous linear map. -/
theorem HasCkHolderOn.clm_comp {k : ℕ} {α : ℝ} {f : E → F} {U K : Set E} (hU : IsOpen U)
    (hKU : K ⊆ U) (hf : HasCkHolderOn k α f U K) (L : F →L[ℝ] G) :
    HasCkHolderOn k α (fun x => L (f x)) U K := by
  have key : ∀ m ≤ k, ∀ x ∈ K, iteratedFDeriv ℝ m (fun x => L (f x)) x =
      L.compContinuousMultilinearMap (iteratedFDeriv ℝ m f x) := fun m hm x hx =>
    L.iteratedFDeriv_comp_left (hf.contDiffOn.contDiffAt (hU.mem_nhds (hKU hx)))
      (by exact_mod_cast hm)
  obtain ⟨C, hC⟩ := hf.holder
  refine ⟨L.contDiff.comp_contDiffOn hf.contDiffOn, fun m hm => ?_, ‖L‖ * C,
    fun x hx y hy => ?_⟩
  · obtain ⟨B, hB⟩ := hf.bounded m hm
    exact ⟨‖L‖ * B, fun x hx => by
      rw [key m hm x hx]
      exact (L.norm_compContinuousMultilinearMap_le _).trans
        (mul_le_mul_of_nonneg_left (hB x hx) (norm_nonneg _))⟩
  · rw [key k le_rfl x hx, key k le_rfl y hy]
    have e : L.compContinuousMultilinearMap (iteratedFDeriv ℝ k f x) -
        L.compContinuousMultilinearMap (iteratedFDeriv ℝ k f y) =
        L.compContinuousMultilinearMap (iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k f y) := by
      ext v; simp
    rw [e, mul_assoc]
    exact (L.norm_compContinuousMultilinearMap_le _).trans
      (mul_le_mul_of_nonneg_left (hC x hx y hy) (norm_nonneg _))

theorem HasCkHolderOn.neg {k : ℕ} {α : ℝ} {f : E → F} {U K : Set E} (hU : IsOpen U)
    (hKU : K ⊆ U) (hf : HasCkHolderOn k α f U K) :
    HasCkHolderOn k α (fun x => -f x) U K :=
  (hf.clm_comp hU hKU (-ContinuousLinearMap.id ℝ F)).congr hU hKU fun x _ => by simp

theorem HasCkHolderOn.const_smul {k : ℕ} {α : ℝ} {f : E → F} {U K : Set E} (hU : IsOpen U)
    (hKU : K ⊆ U) (hf : HasCkHolderOn k α f U K) (c : ℝ) :
    HasCkHolderOn k α (fun x => c • f x) U K :=
  (hf.clm_comp hU hKU (c • ContinuousLinearMap.id ℝ F)).congr hU hKU fun x _ => by simp

theorem HasCkHolderOn.sub {k : ℕ} {α : ℝ} {f g : E → F} {U K : Set E} (hU : IsOpen U)
    (hKU : K ⊆ U) (hf : HasCkHolderOn k α f U K) (hg : HasCkHolderOn k α g U K) :
    HasCkHolderOn k α (fun x => f x - g x) U K :=
  (hf.add hU hKU (hg.neg hU hKU)).congr hU hKU fun x _ => by simp [sub_eq_add_neg]

/-- Order zero of the bilinear rule. -/
lemma ckHolder_bilinear_zero {α : ℝ} {U K : Set E} (B : F →L[ℝ] G →L[ℝ] H) {f : E → F}
    {g : E → G} (hf : HasCkHolderOn 0 α f U K) (hg : HasCkHolderOn 0 α g U K) :
    HasCkHolderOn 0 α (fun x => B (f x) (g x)) U K := by
  rw [hasCkHolderOn_zero_iff] at hf hg ⊢
  obtain ⟨hfc, ⟨Bf, hBf⟩, ⟨Cf, hCf⟩⟩ := hf
  obtain ⟨hgc, ⟨Bg, hBg⟩, ⟨Cg, hCg⟩⟩ := hg
  have hBf' : ∀ x ∈ K, ‖f x‖ ≤ max Bf 0 := fun x hx => (hBf x hx).trans (le_max_left _ _)
  have hBg' : ∀ x ∈ K, ‖g x‖ ≤ max Bg 0 := fun x hx => (hBg x hx).trans (le_max_left _ _)
  refine ⟨(B.continuous.comp_continuousOn hfc).clm_apply hgc,
    ⟨‖B‖ * max Bf 0 * max Bg 0, fun x hx => ?_⟩,
    ⟨‖B‖ * max Cf 0 * max Bg 0 + ‖B‖ * max Bf 0 * max Cg 0, fun x hx y hy => ?_⟩⟩
  · calc ‖B (f x) (g x)‖ ≤ ‖B‖ * ‖f x‖ * ‖g x‖ := B.le_opNorm₂ _ _
      _ ≤ ‖B‖ * max Bf 0 * max Bg 0 := by
        gcongr
        exacts [hBf' x hx, hBg' x hx]
  · have hd : 0 ≤ dist x y ^ α := Real.rpow_nonneg dist_nonneg _
    have h1 : ‖f x - f y‖ ≤ max Cf 0 * dist x y ^ α :=
      (hCf x hx y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hd)
    have h2 : ‖g x - g y‖ ≤ max Cg 0 * dist x y ^ α :=
      (hCg x hx y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hd)
    have e : B (f x) (g x) - B (f y) (g y) = B (f x - f y) (g x) + B (f y) (g x - g y) := by
      simp only [map_sub, sub_apply]; abel
    rw [e]
    calc ‖B (f x - f y) (g x) + B (f y) (g x - g y)‖
        ≤ ‖B (f x - f y) (g x)‖ + ‖B (f y) (g x - g y)‖ := norm_add_le _ _
      _ ≤ ‖B‖ * ‖f x - f y‖ * ‖g x‖ + ‖B‖ * ‖f y‖ * ‖g x - g y‖ :=
        add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _)
      _ ≤ ‖B‖ * (max Cf 0 * dist x y ^ α) * max Bg 0 +
          ‖B‖ * max Bf 0 * (max Cg 0 * dist x y ^ α) := by
        gcongr <;> first | exact h1 | exact h2 | exact hBg' x hx | exact hBf' y hy
      _ = _ := by ring

/-- A fixed directional derivative of a `C^{k+1,α}` function is `C^{k,α}`. -/
theorem HasCkHolderOn.partial {k : ℕ} {α : ℝ} {f : E → F} {U K : Set E} (hU : IsOpen U)
    (hKU : K ⊆ U) (hf : HasCkHolderOn (k + 1) α f U K) (v : E) :
    HasCkHolderOn k α (fun x => fderiv ℝ f x v) U K :=
  (((HasCkHolderOn.succ_iff hU).1 hf).2.2.clm_comp hU hKU
    (ContinuousLinearMap.apply ℝ F v)).congr hU hKU fun x _ => by simp

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Bounds and a Hölder estimate on `K` give a finite Hölder norm on `K`. -/
lemma ckHolder_hasFiniteHolderNormOn {α : ℝ} {g : E → F} {K : Set E} {A C : ℝ}
    (hA : ∀ x ∈ K, ‖g x‖ ≤ A) (hC : ∀ x ∈ K, ∀ y ∈ K, ‖g x - g y‖ ≤ C * dist x y ^ α) :
    HasFiniteHolderNormOn α g K := by
  refine HasFiniteHolderNormOn.of_bounds (A := max A 0) (B := max C 0) (le_max_right _ _)
    (le_max_right _ _) (fun x hx => (hA x hx).trans (le_max_left _ _)) fun x hx y hy => ?_
  rcases eq_or_ne x y with rfl | hxy
  · simp
  · have hpos : 0 < ‖x - y‖ ^ α :=
      Real.rpow_pos_of_pos (norm_pos_iff.2 (sub_ne_zero.2 hxy)) _
    rw [div_le_iff₀ hpos]
    have := hC x hx y hy
    rw [dist_eq_norm] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpos.le)

/-- `C^{1,α}` in the sense of `HasCkHolderOn` on a convex bounded `K ⊆ U` gives
`HasC1HolderOn α f K`. -/
theorem HasCkHolderOn.hasC1HolderOn {α : ℝ} (hα1 : α ≤ 1) {f : E → F} {U K : Set E}
    (hU : IsOpen U) (hKU : K ⊆ U) (hK : Convex ℝ K) (hKb : Bornology.IsBounded K)
    (hf : HasCkHolderOn 1 α f U K) : HasC1HolderOn α f K := by
  obtain ⟨-, ⟨A, hA⟩, ⟨C, hC⟩⟩ := hasCkHolderOn_zero_iff.1 (hf.of_succ hα1 hU hKU hK hKb)
  obtain ⟨-, ⟨A', hA'⟩, ⟨C', hC'⟩⟩ :=
    hasCkHolderOn_zero_iff.1 ((HasCkHolderOn.succ_iff hU).1 hf).2.2
  exact ⟨by exact_mod_cast hf.contDiffOn.mono hKU, ckHolder_hasFiniteHolderNormOn hA hC,
    ckHolder_hasFiniteHolderNormOn hA' hC'⟩

end General

section Bilinear

universe u v uE uF uG uH

/-- Bilinear rule with the value spaces in a universe above that of `E`; the induction on
`k` uses `precompR`/`precompL`, which change the value spaces to spaces of continuous
linear maps on `E`. -/
lemma ckHolder_bilinear_aux {E : Type u} {F G H : Type (max u v)} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    {k : ℕ} {α : ℝ} (hα1 : α ≤ 1) {U K : Set E} (hU : IsOpen U) (hKU : K ⊆ U)
    (hK : Convex ℝ K) (hKb : Bornology.IsBounded K)
    (B : F →L[ℝ] G →L[ℝ] H) {f : E → F} {g : E → G}
    (hf : HasCkHolderOn k α f U K) (hg : HasCkHolderOn k α g U K) :
    HasCkHolderOn k α (fun x => B (f x) (g x)) U K := by
  induction k generalizing F G H with
  | zero => exact ckHolder_bilinear_zero B hf hg
  | succ k ih =>
    obtain ⟨hfd, ⟨Bf, hBf⟩, hf'⟩ := (HasCkHolderOn.succ_iff hU).1 hf
    obtain ⟨hgd, ⟨Bg, hBg⟩, hg'⟩ := (HasCkHolderOn.succ_iff hU).1 hg
    have hfk := hf.of_succ hα1 hU hKU hK hKb
    have hgk := hg.of_succ hα1 hU hKU hK hKb
    refine (HasCkHolderOn.succ_iff hU).2 ⟨?_, ?_, ?_⟩
    · exact (B.differentiable.comp_differentiableOn hfd).clm_apply hgd
    · refine ⟨‖B‖ * max Bf 0 * max Bg 0, fun x hx => ?_⟩
      calc ‖B (f x) (g x)‖ ≤ ‖B‖ * ‖f x‖ * ‖g x‖ := B.le_opNorm₂ _ _
        _ ≤ ‖B‖ * max Bf 0 * max Bg 0 := by
          gcongr
          exacts [(hBf x hx).trans (le_max_left _ _), (hBg x hx).trans (le_max_left _ _)]
    · have hsum : HasCkHolderOn k α (fun x => B.precompR E (f x) (fderiv ℝ g x) +
          B.precompL E (fderiv ℝ f x) (g x)) U K :=
        (ih (B.precompR E) hfk hg').add hU hKU (ih (B.precompL E) hf' hgk)
      refine hsum.congr hU hKU fun x hx => ?_
      exact B.fderiv_of_bilinear (hfd.differentiableAt (hU.mem_nhds hx))
        (hgd.differentiableAt (hU.mem_nhds hx))

/-- Bilinear rule: `x ↦ B (f x) (g x)` is `C^{k,α}` for a fixed continuous bilinear map
`B` and `C^{k,α}` functions `f`, `g` on a convex bounded `K ⊆ U`, `U` open. (Reduced to
`ckHolder_bilinear_aux` by lifting the value spaces to a common universe.) -/
theorem HasCkHolderOn.bilinear {E : Type uE} {F : Type uF} {G : Type uG} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    {k : ℕ} {α : ℝ} (hα1 : α ≤ 1) {U K : Set E} (hU : IsOpen U) (hKU : K ⊆ U)
    (hK : Convex ℝ K) (hKb : Bornology.IsBounded K)
    (B : F →L[ℝ] G →L[ℝ] H) {f : E → F} {g : E → G}
    (hf : HasCkHolderOn k α f U K) (hg : HasCkHolderOn k α g U K) :
    HasCkHolderOn k α (fun x => B (f x) (g x)) U K := by
  let eF : ULift.{max uE uF uG uH} F ≃L[ℝ] F := ContinuousLinearEquiv.ulift
  let eG : ULift.{max uE uF uG uH} G ≃L[ℝ] G := ContinuousLinearEquiv.ulift
  let eH : ULift.{max uE uF uG uH} H ≃L[ℝ] H := ContinuousLinearEquiv.ulift
  let B' : ULift.{max uE uF uG uH} F →L[ℝ] ULift.{max uE uF uG uH} G →L[ℝ]
      ULift.{max uE uF uG uH} H :=
    (ContinuousLinearMap.compL ℝ (ULift.{max uE uF uG uH} G) H (ULift.{max uE uF uG uH} H)
      (eH.symm : H →L[ℝ] ULift.{max uE uF uG uH} H)).comp
      (B.bilinearComp (eF : ULift.{max uE uF uG uH} F →L[ℝ] F)
        (eG : ULift.{max uE uF uG uH} G →L[ℝ] G))
  have h := ckHolder_bilinear_aux.{uE, max uF uG uH} hα1 hU hKU hK hKb B'
    (hf.clm_comp hU hKU (eF.symm : F →L[ℝ] ULift.{max uE uF uG uH} F))
    (hg.clm_comp hU hKU (eG.symm : G →L[ℝ] ULift.{max uE uF uG uH} G))
  refine (h.clm_comp hU hKU (eH : ULift.{max uE uF uG uH} H →L[ℝ] H)).congr hU hKU
    fun x _ => ?_
  simp [B']

end Bilinear

section Real

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Products of real `C^{k,α}` functions. -/
theorem HasCkHolderOn.mul {k : ℕ} {α : ℝ} (hα1 : α ≤ 1) {U K : Set E} (hU : IsOpen U)
    (hKU : K ⊆ U) (hK : Convex ℝ K) (hKb : Bornology.IsBounded K) {f g : E → ℝ}
    (hf : HasCkHolderOn k α f U K) (hg : HasCkHolderOn k α g U K) :
    HasCkHolderOn k α (fun x => f x * g x) U K :=
  (hf.bilinear hα1 hU hKU hK hKb (ContinuousLinearMap.mul ℝ ℝ) hg).congr hU hKU
    fun x _ => by simp

/-- A real `C^{k,α}` function times a vector-valued `C^{k,α}` function. -/
theorem HasCkHolderOn.smul {k : ℕ} {α : ℝ} (hα1 : α ≤ 1) {U K : Set E} (hU : IsOpen U)
    (hKU : K ⊆ U) (hK : Convex ℝ K) (hKb : Bornology.IsBounded K) {f : E → ℝ} {g : E → F}
    (hf : HasCkHolderOn k α f U K) (hg : HasCkHolderOn k α g U K) :
    HasCkHolderOn k α (fun x => f x • g x) U K :=
  (hf.bilinear hα1 hU hKU hK hKb (ContinuousLinearMap.lsmul ℝ ℝ) hg).congr hU hKU
    fun x _ => by simp

/-- Order zero of the quotient rule. -/
lemma ckHolder_inv_zero {α : ℝ} {U K : Set E} {f : E → ℝ} (hf : HasCkHolderOn 0 α f U K)
    (hne : ∀ x ∈ U, f x ≠ 0) (hKU : K ⊆ U) {lam : ℝ} (hlam : 0 < lam)
    (hlow : ∀ x ∈ K, lam ≤ |f x|) :
    HasCkHolderOn 0 α (fun x => (f x)⁻¹) U K := by
  rw [hasCkHolderOn_zero_iff] at hf ⊢
  obtain ⟨hfc, -, ⟨C, hC⟩⟩ := hf
  refine ⟨hfc.inv₀ hne, ⟨lam⁻¹, fun x hx => ?_⟩, ⟨max C 0 / lam ^ 2, fun x hx y hy => ?_⟩⟩
  · rw [Real.norm_eq_abs, abs_inv]
    exact inv_anti₀ hlam (hlow x hx)
  · have hx0 : f x ≠ 0 := hne x (hKU hx)
    have hy0 : f y ≠ 0 := hne y (hKU hy)
    have hd : 0 ≤ dist x y ^ α := Real.rpow_nonneg dist_nonneg _
    have e : (f x)⁻¹ - (f y)⁻¹ = (f y - f x) / (f x * f y) := by field_simp
    rw [Real.norm_eq_abs, e, abs_div, abs_mul,
      div_le_iff₀ (mul_pos (abs_pos.2 hx0) (abs_pos.2 hy0))]
    have h1 : |f y - f x| ≤ max C 0 * dist x y ^ α := by
      rw [abs_sub_comm, ← Real.norm_eq_abs]
      exact (hC x hx y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hd)
    have h2 : lam ^ 2 ≤ |f x| * |f y| := by
      rw [sq]; exact mul_le_mul (hlow x hx) (hlow y hy) hlam.le (abs_nonneg _)
    calc |f y - f x| ≤ max C 0 * dist x y ^ α := h1
      _ = max C 0 / lam ^ 2 * dist x y ^ α * lam ^ 2 := by field_simp
      _ ≤ max C 0 / lam ^ 2 * dist x y ^ α * (|f x| * |f y|) := by gcongr

/-- Quotient rule: the reciprocal of a real `C^{k,α}` function which does not vanish on
`U` and is bounded away from zero on `K` is `C^{k,α}`. -/
theorem HasCkHolderOn.inv {k : ℕ} {α : ℝ} (hα1 : α ≤ 1) {U K : Set E} (hU : IsOpen U)
    (hKU : K ⊆ U) (hK : Convex ℝ K) (hKb : Bornology.IsBounded K) {f : E → ℝ}
    (hf : HasCkHolderOn k α f U K) (hne : ∀ x ∈ U, f x ≠ 0)
    (hlow : ∃ lam > 0, ∀ x ∈ K, lam ≤ |f x|) :
    HasCkHolderOn k α (fun x => (f x)⁻¹) U K := by
  obtain ⟨lam, hlam, hlow⟩ := hlow
  induction k generalizing f with
  | zero => exact ckHolder_inv_zero hf hne hKU hlam hlow
  | succ k ih =>
    obtain ⟨hfd, -, hf'⟩ := (HasCkHolderOn.succ_iff hU).1 hf
    have hik := ih (hf.of_succ hα1 hU hKU hK hKb) hne hlow
    refine (HasCkHolderOn.succ_iff hU).2 ⟨hfd.inv hne, ⟨lam⁻¹, fun x hx => ?_⟩, ?_⟩
    · rw [Real.norm_eq_abs, abs_inv]; exact inv_anti₀ hlam (hlow x hx)
    · have hsq : HasCkHolderOn k α (fun x => -((f x)⁻¹ * (f x)⁻¹)) U K :=
        (hik.mul hα1 hU hKU hK hKb hik).neg hU hKU
      refine (hsq.smul hα1 hU hKU hK hKb hf').congr hU hKU fun x hx => ?_
      have hx0 := hne x hx
      have hD := ((hasFDerivAt_inv hx0).comp x
        (hfd.differentiableAt (hU.mem_nhds hx)).hasFDerivAt).fderiv
      rw [show (fun x => (f x)⁻¹) = (fun y : ℝ => y⁻¹) ∘ f from rfl, hD]
      ext v
      simp
      ring

end Real

section Euclidean

/-- A real linear functional on `ℝ³` is the sum of its coordinate entries times the
coordinate projections. -/
lemma ckHolder_functional_eq_sum (ℓ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) :
    ℓ = ∑ k, ℓ (EuclideanSpace.single k 1) •
      (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) := by
  apply ContinuousLinearMap.coe_injective
  refine (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext fun i => ?_
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    ContinuousLinearMap.coe_coe]
  simp

/-- A differentiable real function on `ℝ³`, bounded on `K`, whose coordinate partials are
`C^{k,α}` is `C^{k+1,α}`. -/
theorem hasCkHolderOn_succ_of_partials {k : ℕ} {α : ℝ} {U K : Set (EuclideanSpace ℝ (Fin 3))}
    (hU : IsOpen U) (hKU : K ⊆ U) {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hfd : DifferentiableOn ℝ f U) (hfb : ∃ B, ∀ x ∈ K, ‖f x‖ ≤ B)
    (hpart : ∀ i, HasCkHolderOn k α (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) U K) :
    HasCkHolderOn (k + 1) α f U K := by
  refine (HasCkHolderOn.succ_iff hU).2 ⟨hfd, hfb, ?_⟩
  have hs := (((hpart 0).clm_comp hU hKU (ContinuousLinearMap.toSpanSingleton ℝ
      (EuclideanSpace.proj 0 : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ))).add hU hKU
    ((hpart 1).clm_comp hU hKU (ContinuousLinearMap.toSpanSingleton ℝ
      (EuclideanSpace.proj 1 : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)))).add hU hKU
    ((hpart 2).clm_comp hU hKU (ContinuousLinearMap.toSpanSingleton ℝ
      (EuclideanSpace.proj 2 : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)))
  refine hs.congr hU hKU fun x _ => ?_
  conv_lhs => rw [ckHolder_functional_eq_sum (fderiv ℝ f x)]
  simp [Fin.sum_univ_three, ContinuousLinearMap.toSpanSingleton_apply]

end Euclidean

end LiquidDrop
