module

public import NoCompromise.Elliptic.BoundaryNeumannCkLevel
public import NoCompromise.Elliptic.BoundaryNeumannIterateStep

@[expose] public section

/-!
# All levels of the smooth boundary Neumann iteration (`thm:boundary-neumann`)

We prove `BoundaryNeumannCkLevel k` for every `k`, by induction on `k`.

* Level `0` is the C²,α theorem at scale `R` (`boundary_neumann_c2_holder_scaled`): its
  second derivatives, continuous, bounded and α-Hölder on the half ball of radius `(3/8) R`,
  are the coordinate partials of the first partials of `w`.
* Level `k + 1` from level `k`: for a tangential direction `i`, `∂ᵢw` solves the
  differentiated problem on the half ball of radius `R/2`
  (`boundary_neumann_smooth_tangential_equation`) with the datum `∂ᵢH - (∂ᵢA)∇w`, which is
  `C^{k+1,α}`; level `k` at radius `R/2` makes `∂ᵢw` of class `C^{k+2,α}` on the half ball of
  radius `(3/8)(1/2)^{k+1} R`. The normal derivative `∂₃w` has partials `∂ₗ∂₃w = ∂₃∂ₗw`
  (`l` tangential) and `∂₃∂₃w`, which equals the `C^{k+1,α}` expression obtained by solving
  the classical equation for it (using `A₃₃ ≥ lam > 0`). Hence all coordinate partials of `w`
  are `C^{k+2,α}` and `w` is `C^{k+3,α}`.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Restriction of `HasCkHolderOn` to a smaller open set and a smaller set. -/
theorem boundaryNeumannCkIterate_mono {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ} {α : ℝ} {f : E → F}
    {U K U' K' : Set E} (hf : HasCkHolderOn k α f U K) (hU' : U' ⊆ U) (hK' : K' ⊆ K) :
    HasCkHolderOn k α f U' K' := by
  obtain ⟨C, hC⟩ := hf.holder
  refine ⟨hf.contDiffOn.mono hU', fun m hm => ?_, C, fun x hx y hy => hC x (hK' hx) y (hK' hy)⟩
  obtain ⟨B, hB⟩ := hf.bounded m hm
  exact ⟨B, fun x hx => hB x (hK' hx)⟩

lemma boundaryNeumannCkIterate_isCompact_closure (R : ℝ) :
    IsCompact (closure (boundaryHalfBall R)) :=
  (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) R).of_isClosed_subset isClosed_closure
    ((closure_mono (fun _ hx => hx.1 : boundaryHalfBall R ⊆ ball 0 R)).trans
      closure_ball_subset_closedBall)

lemma boundaryNeumannCkIterate_isBounded (R : ℝ) :
    Bornology.IsBounded (boundaryHalfBall R) :=
  isBounded_ball.subset (fun _ hx => hx.1 : boundaryHalfBall R ⊆ ball 0 R)

/-- Symmetry of the Hessian entries of a C² function on an open set. -/
lemma boundaryNeumannCkIterate_entry_comm {U : Set (EuclideanSpace ℝ (Fin 3))}
    (hU : IsOpen U) {w : EuclideanSpace ℝ (Fin 3) → ℝ} (hw : ContDiffOn ℝ 2 w U)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ U) (i j : Fin 3) :
    boundaryNeumannC2Entry w x i j = boundaryNeumannC2Entry w x j i := by
  unfold boundaryNeumannC2Entry
  rw [nondiv_fderiv_coordinate_eq hU hw j hx, nondiv_fderiv_coordinate_eq hU hw i hx]
  exact ((hw.contDiffAt (hU.mem_nhds hx)).isSymmSndFDerivAt (by norm_num)).eq _ _

/-- The expanded classical equation in the open half ball of radius `R`, for a solution that
is C² on an open neighbourhood of the closed half ball, with the convention
`Aᵢⱼ = (A eⱼ)ᵢ`. -/
theorem boundaryNeumannCkIterate_pointwise_equation {R : ℝ}
    {U : Set (EuclideanSpace ℝ (Fin 3))}
    (hUc : closure (boundaryHalfBall R) ⊆ U)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hA : ContDiffOn ℝ 1 A U) (hH : ContDiffOn ℝ 1 H U) (hw : ContDiffOn ℝ 2 w U)
    (he : IsBoundaryNeumannEquationOn A (gradient w) H R) :
    ∀ x ∈ boundaryHalfBall R,
      (∑ i, ∑ j, A x (EuclideanSpace.single j 1) i * boundaryNeumannC2Entry w x i j) +
      (∑ i, ∑ j, fderiv ℝ A x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) i * fderiv ℝ w x (EuclideanSpace.single j 1)) =
      divergenceN H x := by
  intro x hx
  have hU := isOpen_boundaryHalfBall R
  have hsub : boundaryHalfBall R ⊆ U := subset_closure.trans hUc
  have hw1 : ContDiffOn ℝ 2 w (boundaryHalfBall R) := hw.mono hsub
  have hDw : ContDiffOn ℝ 1 (fderiv ℝ w) (boundaryHalfBall R) :=
    hw1.fderiv_of_isOpen hU (by norm_num)
  have hGw : ContDiffOn ℝ 1 (gradient w) (boundaryHalfBall R) :=
    (toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm.toContinuousLinearEquiv.contDiff
      |>.comp_contDiffOn hDw
  have hF : ContDiffOn ℝ 1 (fun y => A y (gradient w y) - H y) (boundaryHalfBall R) :=
    ((hA.mono hsub).clm_apply hGw).sub (hH.mono hsub)
  have hflux : divergenceN (fun y => A y (gradient w y) - H y) x = 0 := by
    refine boundary_neumann_c2_divergence_eq_zero hU hF ?_ hx
    intro φ hφ hcφ hsφ
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := boundaryHalfBall R)
      (fun x hx => by
        rw [gradient_eq_zero_of_notMem_tsupport (fun ht => hx (hsφ ht)), inner_zero_right])]
    exact he φ hφ hcφ (hsφ.trans inter_subset_left)
  have hdG := (hGw.contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero
  have hpartial (i j : Fin 3) :
      fderiv ℝ (gradient w) x (EuclideanSpace.single i 1) j =
        boundaryNeumannC2Entry w x i j := by
    have he : (fun y => fderiv ℝ w y (EuclideanSpace.single j 1)) =
        fun y => gradient w y j := funext fun y => (gradient_apply_eq_fderiv_single w y j).symm
    unfold boundaryNeumannC2Entry
    rw [he]
    change _ = fderiv ℝ ((EuclideanSpace.proj j) ∘ gradient w) x _
    rw [((EuclideanSpace.proj j).hasFDerivAt.comp x hdG.hasFDerivAt).fderiv]
    rfl
  have hdA := ((hA.mono hsub).contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero
  have hdH := ((hH.mono hsub).contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero
  have hp := boundary_neumann_c2_divergence_product hdA hdG hdH
  rw [hflux] at hp
  simp only [hpartial, gradient_apply_eq_fderiv_single] at hp
  linarith

/-- Level `0` of the smooth boundary Neumann iteration: the C²,α theorem at scale `R`. -/
theorem boundaryNeumannCkLevel_zero : BoundaryNeumannCkLevel 0 := by
  intro α lam cap R hα hα1 hlam hR hR1 U hU hUc A H w hA hH hw hcap' hell hcross hH0 hw0 he
  have hKc := boundaryNeumannCkIterate_isCompact_closure R
  have hKv : Convex ℝ (closure (boundaryHalfBall R)) := (convex_boundaryHalfBall R).closure
  have hKb := hKc.isBounded
  have hAK : HasC1HolderOn α A (closure (boundaryHalfBall R)) :=
    hasC1HolderOn_of_contDiffOn_two hα.le hα1.le hKc hKv hU hUc
      (hA.of_le (by simp : (2 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)))
  have hHK : HasC1HolderOn α H (closure (boundaryHalfBall R)) :=
    hH.hasC1HolderOn hα1.le hU hUc hKv hKb
  have hwK : HasC1HolderOn α w (closure (boundaryHalfBall R)) :=
    hw.hasC1HolderOn hα1.le hU hUc hKv hKb
  obtain ⟨C, hC, hsc⟩ := boundary_neumann_c2_holder_scaled hα hα1 hlam (le_max_right cap 0)
    hAK.norm_nonneg (add_nonneg hwK.norm_nonneg hHK.norm_nonneg)
  obtain ⟨hc2, hent⟩ := hsc hR hR1 A H w hAK hHK hwK le_rfl le_rfl
    (fun x hx => (hcap' x hx).trans (le_max_left _ _)) hell hcross hH0 hw0 he
  have hρ : (3 / 8 * (1 / 2 : ℝ) ^ 0 * R) = R * (3 / 8) := by ring
  rw [hρ]
  have hS : IsOpen (boundaryHalfBall (R * (3 / 8))) := isOpen_boundaryHalfBall _
  have hSR : boundaryHalfBall (R * (3 / 8)) ⊆ closure (boundaryHalfBall R) :=
    (boundaryHalfBall_mono (by linarith)).trans subset_closure
  have hwb : ∃ B, ∀ x ∈ boundaryHalfBall (R * (3 / 8)), ‖w x‖ ≤ B := by
    obtain ⟨B, hB⟩ := hw.bounded 0 (Nat.zero_le _)
    refine ⟨B, fun x hx => ?_⟩
    have h := hB x (hSR hx)
    rwa [norm_iteratedFDeriv_zero] at h
  have hdwb : ∀ i : Fin 3, ∃ B, ∀ x ∈ boundaryHalfBall (R * (3 / 8)),
      ‖fderiv ℝ w x (EuclideanSpace.single i 1)‖ ≤ B := by
    intro i
    obtain ⟨-, ⟨B, hB⟩, -⟩ :=
      hasCkHolderOn_zero_iff.1 (hw.partial hU hUc (EuclideanSpace.single i 1))
    exact ⟨B, fun x hx => hB x (hSR hx)⟩
  refine hasCkHolderOn_succ_of_partials (k := 1) hS subset_rfl
    (hc2.differentiableOn (by norm_num)) hwb fun i => ?_
  have hd1 : ContDiffOn ℝ 1 (fun x => fderiv ℝ w x (EuclideanSpace.single i 1))
      (boundaryHalfBall (R * (3 / 8))) :=
    (hc2.fderiv_of_isOpen hS (by norm_num)).clm_apply contDiffOn_const
  refine hasCkHolderOn_succ_of_partials (k := 0) hS subset_rfl
    (hd1.differentiableOn one_ne_zero) (hdwb i) fun j => ?_
  obtain ⟨D, hDeq, hDc, hDb, hDh⟩ := hent j i
  have e1 : ∀ x ∈ boundaryHalfBall (R * (3 / 8)),
      fderiv ℝ (fun y => fderiv ℝ w y (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single j 1) = D x := fun x hx => (hDeq hx).symm
  refine hasCkHolderOn_zero_iff.2 ⟨(hDc.mono subset_closure).congr e1,
    ⟨(R ^ 2)⁻¹ * C, fun x hx => ?_⟩, ⟨(R ^ 2)⁻¹ * (C * R⁻¹ ^ α), fun x hx y hy => ?_⟩⟩
  · rw [e1 x hx, Real.norm_eq_abs]
    exact hDb x (subset_closure hx)
  · rw [e1 x hx, e1 y hy, Real.norm_eq_abs]
    have h := hDh x (subset_closure hx) y (subset_closure hy)
    rw [Real.mul_rpow (inv_nonneg.2 hR.le) dist_nonneg] at h
    exact h.trans (le_of_eq (by ring))

/-- The step of the smooth boundary Neumann iteration: level `k` gives level `k + 1`. -/
theorem boundaryNeumannCkLevel_succ (k : ℕ) (ih : BoundaryNeumannCkLevel k) :
    BoundaryNeumannCkLevel (k + 1) := by
  intro α lam cap R hα hα1 hlam hR hR1 U hU hUc A H w hA hH hw hcap' hell hcross hH0 hw0 he
  have hKc := boundaryNeumannCkIterate_isCompact_closure R
  have hKv : Convex ℝ (closure (boundaryHalfBall R)) := (convex_boundaryHalfBall R).closure
  have hKb := hKc.isBounded
  have hA2 : ContDiffOn ℝ 2 A U := hA.of_le (by simp : (2 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞))
  have hH2 : ContDiffOn ℝ 2 H U := hH.contDiffOn.of_le (by norm_cast; omega)
  have hw2 : ContDiffOn ℝ 2 w U := hw.contDiffOn.of_le (by norm_cast; omega)
  have hAk : ∀ m : ℕ, HasCkHolderOn m α A U (closure (boundaryHalfBall R)) :=
    HasCkHolderOn.of_contDiffOn_smooth hα1.le hU hUc hKv hKc hA
  have hG : HasCkHolderOn (k + 1) α (gradient w) U (closure (boundaryHalfBall R)) :=
    ((((HasCkHolderOn.succ_iff hU).1 hw).2.2).clm_comp hU hUc
      (toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm.toContinuousLinearEquiv.toContinuousLinearMap
      ).congr hU hUc fun x _ => rfl
  have hK2 : closure (boundaryHalfBall (R / 2)) ⊆ closure (boundaryHalfBall R) :=
    closure_mono (boundaryHalfBall_mono (by linarith))
  have hK2U := hK2.trans hUc
  have hfin : ∀ t : Fin 3, t = 0 ∨ t = 1 ∨ t = 2 := by decide
  have h0 : (0 : Fin 3) ≠ Fin.last 2 := by decide
  have h1 : (1 : Fin 3) ≠ Fin.last 2 := by decide
  -- the tangential derivatives are `C^{k+2,α}`
  have htan : ∀ i : Fin 3, i ≠ Fin.last 2 →
      HasCkHolderOn (k + 2) α (fun x => fderiv ℝ w x (EuclideanSpace.single i 1))
        (boundaryHalfBall (3 / 8 * (1 / 2) ^ (k + 1) * R))
        (boundaryHalfBall (3 / 8 * (1 / 2) ^ (k + 1) * R)) := by
    intro i hi
    obtain ⟨heq, hdat0, hgrad0⟩ := boundary_neumann_smooth_tangential_equation
      (R := R) (r := R / 2) (by linarith) hU hUc hA2 hH2 hw2 he hcross hH0 hw0 hi
    have hHi : HasCkHolderOn (k + 1) α (boundaryNeumannSmoothDatum A (gradient w) H i) U
        (closure (boundaryHalfBall R)) := by
      have h1 := hH.partial hU hUc (EuclideanSpace.single i 1)
      have h2 := (hAk (k + 2)).partial hU hUc (EuclideanSpace.single i 1)
      have h3 := h2.bilinear hα1.le hU hUc hKv hKb
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))) hG
      exact (h1.sub hU hUc h3).congr hU hUc fun x _ => rfl
    have hvi : HasCkHolderOn (k + 1) α (fun x => fderiv ℝ w x (EuclideanSpace.single i 1)) U
        (closure (boundaryHalfBall R)) := hw.partial hU hUc _
    have h := ih hα hα1 hlam (half_pos hR) (by linarith) hU hK2U hA
      (boundaryNeumannCkIterate_mono hHi subset_rfl hK2)
      (boundaryNeumannCkIterate_mono hvi subset_rfl hK2)
      (fun x hx => hcap' x (hK2 hx)) (fun x hx => hell x (hK2 hx))
      (fun x hx => hcross x (hK2 hx)) hdat0 hgrad0 heq
    have hρ : 3 / 8 * (1 / 2 : ℝ) ^ k * (R / 2) = 3 / 8 * (1 / 2) ^ (k + 1) * R := by ring
    rwa [hρ] at h
  -- the half ball `S` of the conclusion
  have hρR : 3 / 8 * (1 / 2 : ℝ) ^ (k + 1) * R ≤ R := by
    have : (1 / 2 : ℝ) ^ (k + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  set S := boundaryHalfBall (3 / 8 * (1 / 2 : ℝ) ^ (k + 1) * R) with hSdef
  have hS : IsOpen S := isOpen_boundaryHalfBall _
  have hSv : Convex ℝ S := convex_boundaryHalfBall _
  have hSb : Bornology.IsBounded S := boundaryNeumannCkIterate_isBounded _
  have hSR : S ⊆ boundaryHalfBall R := boundaryHalfBall_mono hρR
  have hSK : S ⊆ closure (boundaryHalfBall R) := hSR.trans subset_closure
  have hSU : S ⊆ U := hSK.trans hUc
  have hsymm : ∀ x ∈ S, ∀ i j : Fin 3,
      boundaryNeumannC2Entry w x i j = boundaryNeumannC2Entry w x j i :=
    fun x hx i j => boundaryNeumannCkIterate_entry_comm hU hw2 (hSU hx) i j
  -- the pieces of the classical equation are `C^{k+1,α}` on `S`
  have ha : ∀ i j : Fin 3,
      HasCkHolderOn (k + 1) α (fun x => A x (EuclideanSpace.single j 1) i) S S := fun i j =>
    boundaryNeumannCkIterate_mono
      (((hAk (k + 1)).clm_comp hU hUc (ContinuousLinearMap.apply ℝ
        (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace.single j 1))).clm_comp hU hUc
        (EuclideanSpace.proj i)) hSU hSK
  have hdA : ∀ i j : Fin 3, HasCkHolderOn (k + 1) α
      (fun x => fderiv ℝ A x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) i)
      S S := fun i j =>
    boundaryNeumannCkIterate_mono
      ((((hAk (k + 2)).partial hU hUc (EuclideanSpace.single i 1)).clm_comp hU hUc
        (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin 3))
          (EuclideanSpace.single j 1))).clm_comp hU hUc (EuclideanSpace.proj i)) hSU hSK
  have hdw : ∀ j : Fin 3,
      HasCkHolderOn (k + 1) α (fun x => fderiv ℝ w x (EuclideanSpace.single j 1)) S S :=
    fun j => boundaryNeumannCkIterate_mono (hw.partial hU hUc _) hSU hSK
  have hdH : ∀ i : Fin 3,
      HasCkHolderOn (k + 1) α (fun x => fderiv ℝ H x (EuclideanSpace.single i 1) i) S S :=
    fun i => boundaryNeumannCkIterate_mono
      ((hH.partial hU hUc (EuclideanSpace.single i 1)).clm_comp hU hUc
        (EuclideanSpace.proj i)) hSU hSK
  have hdivH : HasCkHolderOn (k + 1) α (divergenceN H) S S :=
    (((hdH 0).add hS subset_rfl (hdH 1)).add hS subset_rfl (hdH 2)).congr hS subset_rfl
      fun x _ => by simp only [divergenceN, Fin.sum_univ_three]
  have hE : ∀ i j : Fin 3, j ≠ Fin.last 2 →
      HasCkHolderOn (k + 1) α (fun x => boundaryNeumannC2Entry w x i j) S S :=
    fun i j hj => (htan j hj).partial hS subset_rfl (EuclideanSpace.single i 1)
  have hlow : ∀ x ∈ S, lam ≤ A x (EuclideanSpace.single 2 1) 2 := by
    intro x hx
    have h := hell x (hSK hx) (EuclideanSpace.single 2 1)
    simpa [EuclideanSpace.inner_single_right, PiLp.norm_single] using h
  -- the normal second derivative solved from the classical equation
  let T : EuclideanSpace ℝ (Fin 3) → ℝ := fun x => ∑ i, ∑ j,
    fderiv ℝ A x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) i *
      fderiv ℝ w x (EuclideanSpace.single j 1)
  let R' : EuclideanSpace ℝ (Fin 3) → ℝ := fun x =>
    A x (EuclideanSpace.single 0 1) 0 * boundaryNeumannC2Entry w x 0 0 +
    A x (EuclideanSpace.single 1 1) 0 * boundaryNeumannC2Entry w x 0 1 +
    A x (EuclideanSpace.single 2 1) 0 * boundaryNeumannC2Entry w x 2 0 +
    A x (EuclideanSpace.single 0 1) 1 * boundaryNeumannC2Entry w x 1 0 +
    A x (EuclideanSpace.single 1 1) 1 * boundaryNeumannC2Entry w x 1 1 +
    A x (EuclideanSpace.single 2 1) 1 * boundaryNeumannC2Entry w x 2 1 +
    A x (EuclideanSpace.single 0 1) 2 * boundaryNeumannC2Entry w x 2 0 +
    A x (EuclideanSpace.single 1 1) 2 * boundaryNeumannC2Entry w x 2 1
  let Q : EuclideanSpace ℝ (Fin 3) → ℝ := fun x =>
    (divergenceN H x - T x - R' x) / A x (EuclideanSpace.single 2 1) 2
  have hTij : ∀ i j : Fin 3, HasCkHolderOn (k + 1) α
      (fun x => fderiv ℝ A x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) i *
        fderiv ℝ w x (EuclideanSpace.single j 1)) S S :=
    fun i j => (hdA i j).mul hα1.le hS subset_rfl hSv hSb (hdw j)
  have hTi : ∀ i : Fin 3, HasCkHolderOn (k + 1) α (fun x => ∑ j,
      fderiv ℝ A x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) i *
        fderiv ℝ w x (EuclideanSpace.single j 1)) S S := fun i =>
    (((hTij i 0).add hS subset_rfl (hTij i 1)).add hS subset_rfl (hTij i 2)).congr hS
      subset_rfl fun x _ => by simp only [Fin.sum_univ_three]
  have hT : HasCkHolderOn (k + 1) α T S S :=
    (((hTi 0).add hS subset_rfl (hTi 1)).add hS subset_rfl (hTi 2)).congr hS
      subset_rfl fun x _ => by simp only [T, Fin.sum_univ_three]
  have hm : ∀ i j l m : Fin 3, m ≠ Fin.last 2 → HasCkHolderOn (k + 1) α
      (fun x => A x (EuclideanSpace.single j 1) i * boundaryNeumannC2Entry w x l m) S S :=
    fun i j l m hm => (ha i j).mul hα1.le hS subset_rfl hSv hSb (hE l m hm)
  have hR' : HasCkHolderOn (k + 1) α R' S S := by
    have := ((((((((hm 0 0 0 0 h0).add hS subset_rfl (hm 0 1 0 1 h1)).add hS subset_rfl
      (hm 0 2 2 0 h0)).add hS subset_rfl (hm 1 0 1 0 h0)).add hS subset_rfl
      (hm 1 1 1 1 h1)).add hS subset_rfl (hm 1 2 2 1 h1)).add hS subset_rfl
      (hm 2 0 2 0 h0)).add hS subset_rfl (hm 2 1 2 1 h1))
    exact this
  have hinv : HasCkHolderOn (k + 1) α (fun x => (A x (EuclideanSpace.single 2 1) 2)⁻¹) S S :=
    (ha 2 2).inv hα1.le hS subset_rfl hSv hSb
      (fun x hx => (hlam.trans_le (hlow x hx)).ne')
      ⟨lam, hlam, fun x hx => (hlow x hx).trans (le_abs_self _)⟩
  have hQ : HasCkHolderOn (k + 1) α Q S S :=
    (((hdivH.sub hS subset_rfl hT).sub hS subset_rfl hR').mul hα1.le hS subset_rfl hSv hSb
      hinv).congr hS subset_rfl fun x _ => by simp only [Q, div_eq_mul_inv]
  have hQeq : ∀ x ∈ S, boundaryNeumannC2Entry w x 2 2 = Q x := by
    intro x hx
    have hx1 := hSR hx
    have heqn := boundaryNeumannCkIterate_pointwise_equation hUc
      (hA.of_le (by simp : (1 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞))) (hH2.of_le (by norm_num)) hw2 he x hx1
    have hpos : 0 < A x (EuclideanSpace.single 2 1) 2 := hlam.trans_le (hlow x hx)
    simp only [Fin.sum_univ_three] at heqn
    rw [hsymm x hx 0 2, hsymm x hx 1 2] at heqn
    simp only [Q, T, R']
    rw [eq_div_iff hpos.ne']
    simp only [Fin.sum_univ_three]
    linear_combination heqn
  -- the normal derivative is `C^{k+2,α}`
  have hN : HasCkHolderOn (k + 2) α (fun x => fderiv ℝ w x (EuclideanSpace.single 2 1)) S S := by
    refine hasCkHolderOn_succ_of_partials (k := k + 1) hS subset_rfl
      ((hdw 2).contDiffOn.differentiableOn (by exact_mod_cast Nat.succ_ne_zero k)) ?_
      fun l => ?_
    · obtain ⟨B, hB⟩ := (hdw 2).bounded 0 (Nat.zero_le _)
      refine ⟨B, fun x hx => ?_⟩
      have h := hB x hx
      rwa [norm_iteratedFDeriv_zero] at h
    · obtain rfl | rfl | rfl := hfin l
      · exact (hE 2 0 h0).congr hS subset_rfl fun y hy => hsymm y hy 0 2
      · exact (hE 2 1 h1).congr hS subset_rfl fun y hy => hsymm y hy 1 2
      · exact hQ.congr hS subset_rfl fun y hy => hQeq y hy
  -- all coordinate partials of `w` are `C^{k+2,α}`, so `w` is `C^{k+3,α}`
  have hwb : ∃ B, ∀ x ∈ S, ‖w x‖ ≤ B := by
    obtain ⟨B, hB⟩ := hw.bounded 0 (Nat.zero_le _)
    refine ⟨B, fun x hx => ?_⟩
    have h := hB x (hSK hx)
    rwa [norm_iteratedFDeriv_zero] at h
  refine hasCkHolderOn_succ_of_partials (k := k + 2) hS subset_rfl
    ((hw2.mono hSU).differentiableOn two_ne_zero) hwb fun i => ?_
  obtain rfl | rfl | rfl := hfin i
  · exact htan 0 h0
  · exact htan 1 h1
  · exact hN

/-- All levels of the smooth boundary Neumann iteration (blueprint `thm:boundary-neumann`):
for every `k`, a smooth coefficient and `C^{k+1,α}` datum and solution of the homogeneous
flat conormal problem near the closed half ball of radius `R ≤ 1` give a `C^{k+2,α}`
solution on the half ball of radius `(3/8)(1/2)ᵏ R`. -/
theorem boundaryNeumannCkLevel_holds (k : ℕ) : BoundaryNeumannCkLevel k := by
  induction k with
  | zero => exact boundaryNeumannCkLevel_zero
  | succ k ih => exact boundaryNeumannCkLevel_succ k ih

end LiquidDrop
