module

public import NoCompromise.Elliptic.BoundaryNeumannC2InhomData
public import NoCompromise.Elliptic.BoundaryNeumannC2InhomPrimitive
public import NoCompromise.Elliptic.BoundaryNeumannC2Scaled
public import NoCompromise.Elliptic.QuasilinearNorm

@[expose] public section

/-! The smooth lift and the local homogeneous equation for inhomogeneous data. -/

noncomputable section
open Set Filter Metric InnerProductSpace MeasureTheory
open scoped Topology Gradient RealInnerProductSpace
namespace LiquidDrop

theorem boundary_neumann_c2_inhom_smooth_lift_datum
    {lam : ℝ} (hlam : 0 < lam)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)} {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : EuclideanSpace ℝ (Fin 2) → ℝ} {O : Set (EuclideanSpace ℝ (Fin 3))}
    (hO : IsOpen O) (hsub : closedBall 0 1 ⊆ O)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) A O) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f O)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hpos : ∃ U : Set (EuclideanSpace ℝ (Fin 2)), IsOpen U ∧ closedBall 0 1 ⊆ U ∧
      ∀ x ∈ U, lam ≤ boundaryNeumannNormalCoefficient A x) :
    ContDiffOn ℝ (⊤ : ℕ∞) (boundaryNeumannLift h (boundaryNeumannNormalCoefficient A))
      (ball 0 1) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (boundaryNeumannInhomDatum A f h) (ball 0 1) := by
  obtain ⟨U, -, hUs, hUp⟩ := hpos
  let V := U ∩ graphBaseEmbedding ⁻¹' O
  have hb : ContDiffOn ℝ (⊤ : ℕ∞) (boundaryNeumannNormalCoefficient A) V :=
    (boundaryNeumannNormalCoefficient_contDiffOn hA).mono inter_subset_right
  have hVs : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ⊆ V := by
    intro x hx
    refine ⟨hUs hx, hsub ?_⟩
    simpa only [mem_closedBall, dist_zero_right, norm_graphBaseEmbedding] using hx
  have hq : ContDiffOn ℝ (⊤ : ℕ∞)
      (boundaryNeumannLift h (boundaryNeumannNormalCoefficient A)) (ball 0 1) :=
    (boundaryNeumannLift_smoothOn hh.contDiffOn hb
      (fun x hx => (hlam.trans_le (hUp x hx.1)).ne')).mono
        (fun x hx => hVs (boundary_neumann_projection_closedBall (ball_subset_closedBall hx)))
  refine ⟨hq, ?_⟩
  have hg : ContDiffOn ℝ (⊤ : ℕ∞)
      (gradient (boundaryNeumannLift h (boundaryNeumannNormalCoefficient A))) (ball 0 1) :=
    (toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm.contDiff.comp_contDiffOn
      (hq.fderiv_of_isOpen isOpen_ball (by simp))
  exact ((boundaryNeumannPrimitive_smoothOn hO hsub hf).add
    ((hh.comp (graphProjectionN 2).contDiff).contDiffOn.smul contDiffOn_const)).sub
      ((hA.mono (ball_subset_closedBall.trans hsub)).clm_apply hg)

lemma boundary_neumann_c2_inhom_holder_of_gradient
    {n : ℕ} {α C : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (hC : 0 ≤ C)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {K O : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (hcK : Convex ℝ K) (hO : IsOpen O) (hKO : K ⊆ O)
    (hu : ContDiffOn ℝ 1 u O)
    (hb : ∀ x ∈ K, ‖gradient u x‖ ≤ C)
    (hh : ∀ x ∈ K, ∀ y ∈ K, ‖gradient u x - gradient u y‖ ≤ C * dist x y ^ α) :
    HasC1HolderOn α u K := by
  refine ⟨hu.mono hKO,
    boundary_neumann_c2_inhom_finiteHolder_of_contDiffOn hα hα1 hK hcK hO hKO hu, ?_⟩
  apply (quasilinear_holder_of_modulus hC hC ?_ ?_).1
  · intro x hx
    simpa only [gradient, LinearIsometryEquiv.norm_map] using hb x hx
  · intro x hx y hy
    simpa only [gradient, ← map_sub, LinearIsometryEquiv.norm_map] using hh x hx y hy

lemma boundary_neumann_c2_inhom_holder_sub
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ} {u q : E → F} {K : Set E}
    (hu : HasC1HolderOn α u K) (hq : HasC1HolderOn α q K)
    (hdu : ∀ x ∈ K, DifferentiableAt ℝ u x)
    (hdq : ∀ x ∈ K, DifferentiableAt ℝ q x) :
    HasC1HolderOn α (fun x => u x - q x) K := by
  refine ⟨hu.contDiff.sub hq.contDiff,
    (nondiv_holder_sub hu.function_holder hq.function_holder).1, ?_⟩
  have he : EqOn (fderiv ℝ (fun x => u x - q x))
      (fun x => fderiv ℝ u x - fderiv ℝ q x) K :=
    fun x hx => fderiv_fun_sub (hdu x hx) (hdq x hx)
  exact (nondiv_holder_congr he).1.mpr
    (nondiv_holder_sub hu.derivative_holder hq.derivative_holder).1

lemma boundary_neumann_c2_inhom_equation_mono
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {F H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {r R : ℝ} (hr : r ≤ R) (he : IsBoundaryNeumannEquationOn A F H R) :
    IsBoundaryNeumannEquationOn A F H r := by
  intro φ hφ hcφ hsφ
  have hsR := hsφ.trans (ball_subset_ball hr)
  have hz (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∉ ball 0 r) :
      inner ℝ (A x (F x) - H x) (gradient φ x) = 0 := by
    rw [gradient_eq_zero_of_notMem_tsupport (fun hx' => hx (hsφ hx')), inner_zero_right]
  rw [← boundary_neumann_integral_upper_eq _ hz,
    boundary_neumann_integral_upper_eq _
      (fun x hx => hz x (fun hx' => hx (ball_subset_ball hr hx')))]
  exact he φ hφ hcφ hsR

lemma boundary_neumann_c2_inhom_equation_congr
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {F G H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)} {r : ℝ}
    (he : IsBoundaryNeumannEquationOn A F H r)
    (hFG : F =ᵐ[volume.restrict (boundaryHalfBall r)] G) :
    IsBoundaryNeumannEquationOn A G H r := by
  intro φ hφ hcφ hsφ
  calc
    _ = ∫ x in boundaryHalfBall r, inner ℝ (A x (F x) - H x) (gradient φ x) := by
      apply integral_congr_ae
      filter_upwards [hFG] with x hx
      rw [hx]
    _ = 0 := he φ hφ hcφ hsφ

lemma boundary_neumann_c2_inhom_gradient_sub
    {u q : EuclideanSpace ℝ (Fin 3) → ℝ} {x : EuclideanSpace ℝ (Fin 3)}
    (hu : DifferentiableAt ℝ u x) (hq : DifferentiableAt ℝ q x) :
    gradient (fun y => u y - q y) x = gradient u x - gradient q x := by
  simp only [gradient, fderiv_fun_sub hu hq, map_sub]

lemma boundary_neumann_c2_inhom_normal_zero
    {A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    {v : EuclideanSpace ℝ (Fin 3)}
    (hcross : ∀ i : Fin 3, i ≠ Fin.last 2 → A (EuclideanSpace.single i 1) (Fin.last 2) = 0)
    (hpos : A (EuclideanSpace.single (Fin.last 2) 1) (Fin.last 2) ≠ 0)
    (hv : A v (Fin.last 2) = 0) : v (Fin.last 2) = 0 := by
  have he : v = v 0 • EuclideanSpace.single (0 : Fin 3) 1 +
      v 1 • EuclideanSpace.single (1 : Fin 3) 1 +
      v (Fin.last 2) • EuclideanSpace.single (Fin.last 2) 1 := by
    ext i
    fin_cases i <;> simp
  rw [he, map_add, map_add, map_smul, map_smul, map_smul,
    PiLp.add_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, PiLp.smul_apply,
    hcross 0 (by decide), hcross 1 (by decide), smul_zero, smul_zero,
    zero_add, zero_add, smul_eq_mul] at hv
  exact (mul_eq_zero.mp hv).resolve_right hpos

lemma boundary_neumann_c2_inhom_entry_add
    {u q : EuclideanSpace ℝ (Fin 3) → ℝ} {O : Set (EuclideanSpace ℝ (Fin 3))}
    (hO : IsOpen O) (hu : ContDiffOn ℝ 2 u O) (hq : ContDiffOn ℝ 2 q O)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ O) (i j : Fin 3) :
    boundaryNeumannC2Entry (fun y => u y + q y) x i j =
      boundaryNeumannC2Entry u x i j + boundaryNeumannC2Entry q x i j := by
  have he : (fun y => fderiv ℝ (fun z => u z + q z) y (EuclideanSpace.single j 1))
      =ᶠ[𝓝 x] (fun y => fderiv ℝ u y (EuclideanSpace.single j 1) +
        fderiv ℝ q y (EuclideanSpace.single j 1)) := by
    filter_upwards [hO.mem_nhds hx] with y hy
    rw [fderiv_fun_add
      ((hu.contDiffAt (hO.mem_nhds hy)).differentiableAt (by norm_num))
      ((hq.contDiffAt (hO.mem_nhds hy)).differentiableAt (by norm_num)),
      add_apply]
  have hdu : DifferentiableAt ℝ
      (fun y => fderiv ℝ u y (EuclideanSpace.single j 1)) x :=
    (((hu.fderiv_of_isOpen hO (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply
      contDiffOn_const).contDiffAt (hO.mem_nhds hx)).differentiableAt one_ne_zero
  have hdq : DifferentiableAt ℝ
      (fun y => fderiv ℝ q y (EuclideanSpace.single j 1)) x :=
    (((hq.fderiv_of_isOpen hO (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply
      contDiffOn_const).contDiffAt (hO.mem_nhds hx)).differentiableAt one_ne_zero
  unfold boundaryNeumannC2Entry
  rw [he.fderiv_eq, fderiv_fun_add hdu hdq, add_apply]

lemma boundary_neumann_c2_inhom_entry_continuous
    {q : EuclideanSpace ℝ (Fin 3) → ℝ} {O : Set (EuclideanSpace ℝ (Fin 3))}
    (hO : IsOpen O) (hq : ContDiffOn ℝ 2 q O) (i j : Fin 3) :
    ContinuousOn (fun x => boundaryNeumannC2Entry q x i j) O := by
  have hd := ((hq.fderiv_of_isOpen hO
    (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).fderiv_of_isOpen hO
      (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 1)).continuousOn
  have hc : ContinuousOn (fun x =>
      fderiv ℝ (fderiv ℝ q) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) O :=
    (hd.clm_apply continuousOn_const).clm_apply continuousOn_const
  apply hc.congr
  intro x hx
  dsimp only [boundaryNeumannC2Entry]
  rw [nondiv_fderiv_coordinate_eq hO hq j hx]
  rfl

end LiquidDrop
