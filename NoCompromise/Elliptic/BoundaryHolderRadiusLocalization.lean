import NoCompromise.Elliptic.BoundaryHolderZeroSpace
import NoCompromise.Elliptic.BoundaryHolderLocalization
import NoCompromise.Elliptic.QuasilinearCampanatoPullback

/-!
# Actual zero extension and similarity pullback at positive radii

Compact H¹ functions supported in the closed upper halfspace have actual zero
flat trace. This applies after similarity pullback of the localized extension,
without assuming any trace commutation theorem.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma HasH1GradientOn.boundary_zeroTrace_of_upper_support {k : ℕ}
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : HasH1GradientOn f G univ) (hcf : HasCompactSupport f)
    (hs : ∀ x ∈ tsupport f, 0 ≤ x (Fin.last k)) :
    HasZeroFlatTraceOn f G univ := by
  have haux (D : Set (EuclideanSpace ℝ (Fin (k + 1)))) (hD : IsOpen D)
      (he : D = univ ∩ {x | 0 < x (Fin.last k)})
      (hF : HasH1GradientOn f G D)
      (hz : H1Space.ofFunction f G hF ∈ h1ZeroSubmodule hD) :
      HasZeroFlatTraceOn f G univ := by
    subst D
    exact hF.hasZeroFlatTraceOn_of_mem_h1Zero isOpen_univ hz
  exact haux _ boundary_holder_open_upper (univ_inter _).symm
    (hf.mono (subset_univ _))
    (hf.mem_h1Zero_upperHalfspace_of_support (Fin.last k) hcf hs)

lemma HasH1GradientOn.boundary_comp_similarity_global {k : ℕ}
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : HasH1GradientOn f G univ) (hcf : HasCompactSupport f)
    (hs : ∀ x ∈ tsupport f, 0 ≤ x (Fin.last k))
    (c : EuclideanSpace ℝ (Fin (k + 1))) (hc : c (Fin.last k) = 0)
    {r : ℝ} (hr : 0 < r) :
    HasH1GradientOn (f ∘ frozenBallScaling c hr)
      (fun x => r • G (frozenBallScaling c hr x)) univ ∧
      HasZeroFlatTraceOn (f ∘ frozenBallScaling c hr)
        (fun x => r • G (frozenBallScaling c hr x)) univ := by
  let e := frozenBallScaling c hr
  have hchain := (hf.comp_homeomorph_on isOpen_univ isOpen_univ e
    (quasilinear_ballScaling_lipschitz c hr) (quasilinear_ballScaling_symm_lipschitz c hr)
    (fun _ _ => mem_univ _)).1
  have hd (x) : (fderiv ℝ e x).adjoint = r • ContinuousLinearMap.id ℝ _ := by
    rw [frozenBallScaling_fderiv]
    simp only [map_smul, ContinuousLinearMap.adjoint_id]
  have hH : HasH1GradientOn (f ∘ e) (fun x => r • G (e x)) univ := by
    simpa only [hd, smul_apply, ContinuousLinearMap.id_apply] using hchain
  refine ⟨hH, hH.boundary_zeroTrace_of_upper_support (hcf.comp_homeomorph e) ?_⟩
  intro x hx
  have he := hs (e x) (tsupport_comp_subset_preimage f e.continuous hx)
  change 0 ≤ (c + r • x) (Fin.last k) at he
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hc, zero_add] at he
  exact nonneg_of_mul_nonneg_right he hr

/-- A cutoff adapted to the original positive radius. -/
def boundaryHolderRadiusBump {r : ℝ} (hr : 0 < r) :
    ContDiffBump (0 : EuclideanSpace ℝ (Fin 3)) :=
  ⟨r / 64, r / 32, by positivity, by linarith⟩

lemma boundaryHolderRadiusBump_one {r : ℝ} (hr : 0 < r)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ ball 0 (r / 64)) :
    boundaryHolderRadiusBump hr x = 1 ∧ gradient (boundaryHolderRadiusBump hr) x = 0 := by
  refine ⟨(boundaryHolderRadiusBump hr).one_of_mem_closedBall (ball_subset_closedBall hx), ?_⟩
  have he := (boundaryHolderRadiusBump hr).eventuallyEq_one_of_mem_ball hx
  ext i
  rw [gradient_apply_eq_fderiv_single, he.fderiv_eq]
  simp

lemma boundaryHolderRadiusBump_support {r : ℝ} (hr : 0 < r) :
    tsupport (boundaryHolderRadiusBump hr) ⊆ coordinateCube 3 (r / 16) := by
  intro x hx i
  have hx' : ‖x‖ ≤ r / 32 := by
    rw [(boundaryHolderRadiusBump hr).tsupport_eq] at hx
    change dist x 0 ≤ r / 32 at hx
    simpa only [dist_zero_right] using hx
  have hi : |x i| ≤ ‖x‖ := PiLp.norm_apply_le x i
  linarith

lemma boundary_holder_radius_cube_subset {r : ℝ} (hr : 0 < r) :
    coordinateCube 3 (r / 8) ⊆ ball (0 : EuclideanSpace ℝ (Fin 3)) r := by
  intro x hx
  have hh := norm_le_succ_card_mul_of_mem_coordinateCube (by positivity : 0 ≤ r / 8) hx
  change dist x 0 < r
  rw [dist_zero_right]
  norm_num at hh
  linarith

/-- Genuine zero extension of a compact cutoff inside an arbitrary half-ball. -/
theorem HasH1GradientOn.boundary_radius_zero_extension {r : ℝ} (hr : 0 < r)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hf : HasH1GradientOn f G (ball 0 r ∩ {x | 0 < x (Fin.last 2)}))
    (hT : HasZeroFlatTraceOn f G (ball 0 r)) :
    HasH1GradientOn
      ({x | 0 < x (Fin.last 2)}.indicator (fun x => boundaryHolderRadiusBump hr x * f x))
      ({x | 0 < x (Fin.last 2)}.indicator (fun x =>
        boundaryHolderRadiusBump hr x • G x + f x • gradient (boundaryHolderRadiusBump hr) x))
      univ :=
  (hf.mono (inter_subset_inter_left _ (boundary_holder_radius_cube_subset hr)))
    |>.boundary_zero_extension_halfCube (by linarith)
      (hT.mono (boundary_holder_radius_cube_subset hr)) (boundaryHolderRadiusBump hr).contDiff
      (boundaryHolderRadiusBump hr).hasCompactSupport (boundaryHolderRadiusBump_support hr)

/-- A compact global zero extension agrees exactly with both original components
on the smaller half-ball. The lower-halfspace support condition is pointwise. -/
theorem HasH1GradientOn.exists_boundary_radius_zero_extension {r : ℝ} (hr : 0 < r)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hf : HasH1GradientOn f G (ball 0 r ∩ {x | 0 < x (Fin.last 2)}))
    (hT : HasZeroFlatTraceOn f G (ball 0 r)) :
    ∃ (u : EuclideanSpace ℝ (Fin 3) → ℝ)
      (H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)),
      HasH1GradientOn u H univ ∧ HasCompactSupport u ∧
      (∀ x ∈ tsupport u, 0 ≤ x (Fin.last 2)) ∧
      EqOn u f (ball 0 (r / 64) ∩ {x | 0 < x (Fin.last 2)}) ∧
      EqOn H G (ball 0 (r / 64) ∩ {x | 0 < x (Fin.last 2)}) := by
  let U := {x : EuclideanSpace ℝ (Fin 3) | 0 < x (Fin.last 2)}
  let b := boundaryHolderRadiusBump hr
  let u := U.indicator (fun x => b x * f x)
  let H := U.indicator (fun x => b x • G x + f x • gradient b x)
  have hsu : tsupport u ⊆ tsupport b := by
    apply closure_minimal ?_ (isClosed_tsupport b)
    intro x hx
    by_contra hb
    have hb0 := image_eq_zero_of_notMem_tsupport hb
    have hu0 : u x = 0 := by simp [u, hb0]
    exact hx hu0
  have hsU : tsupport u ⊆ {x | 0 ≤ x (Fin.last 2)} := by
    apply closure_minimal ?_ (isClosed_le continuous_const (EuclideanSpace.proj _).continuous)
    intro x hx
    by_contra hxu
    change ¬0 ≤ x (Fin.last 2) at hxu
    have hxU : x ∉ U := fun hh => hxu hh.le
    have hu0 : u x = 0 := indicator_of_notMem hxU _
    exact hx hu0
  refine ⟨u, H, hf.boundary_radius_zero_extension hr hT,
    b.hasCompactSupport.of_isClosed_subset (isClosed_tsupport u) hsu,
    fun x hx => hsU hx, ?_, ?_⟩
  · intro x hx
    have hb := (boundaryHolderRadiusBump_one hr hx.1).1
    simp only [u, indicator_of_mem (show x ∈ U from hx.2), b, hb, one_mul]
  · intro x hx
    obtain ⟨hb, hg⟩ := boundaryHolderRadiusBump_one hr hx.1
    simp only [H, indicator_of_mem (show x ∈ U from hx.2), b, hb, hg, one_smul, smul_zero, add_zero]

end LiquidDrop
