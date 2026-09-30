module

public import NoCompromise.Sobolev.Hilbert

@[expose] public section

/-!
# H¹ algebra and lifting bounded operators

Algebra of weak-gradient representatives follows from the linear Hilbert-space
graph. A bounded linear operator on raw functions descends to H¹ classes when
it preserves H¹ and respects almost-everywhere equality. Target openness makes
the chosen output gradient independent of its construction.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace LiquidDrop

set_option maxSynthPendingDepth 8

namespace H1Space

variable {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}

@[simp]
lemma toLp_zero : (0 : H1Space U).toLp = 0 := rfl

@[simp]
lemma toLp_add (u v : H1Space U) : (u + v).toLp = u.toLp + v.toLp := rfl

@[simp]
lemma toLp_smul (c : ℝ) (u : H1Space U) : (c • u).toLp = c • u.toLp := rfl

@[simp]
lemma gradientLp_zero : (0 : H1Space U).gradientLp = 0 := rfl

@[simp]
lemma gradientLp_add (u v : H1Space U) :
    (u + v).gradientLp = u.gradientLp + v.gradientLp := rfl

@[simp]
lemma gradientLp_smul (c : ℝ) (u : H1Space U) : (c • u).gradientLp = c • u.gradientLp := rfl

lemma coeFn_zero : ⇑(0 : H1Space U) =ᵐ[volume.restrict U] 0 :=
  Lp.coeFn_zero ℝ 2 (volume.restrict U)

lemma coeFn_add (u v : H1Space U) :
    ⇑(u + v) =ᵐ[volume.restrict U] fun x => u x + v x :=
  Lp.coeFn_add u.toLp v.toLp

lemma coeFn_smul (c : ℝ) (u : H1Space U) :
    ⇑(c • u) =ᵐ[volume.restrict U] fun x => c * u x :=
  Lp.coeFn_smul c u.toLp

lemma coeFn_gradientLp_zero :
    ⇑(0 : H1Space U).gradientLp =ᵐ[volume.restrict U] 0 :=
  Lp.coeFn_zero (EuclideanSpace ℝ (Fin n)) 2 (volume.restrict U)

lemma coeFn_gradientLp_add (u v : H1Space U) :
    ⇑(u + v).gradientLp =ᵐ[volume.restrict U] fun x => u.gradientLp x + v.gradientLp x :=
  Lp.coeFn_add u.gradientLp v.gradientLp

lemma coeFn_gradientLp_smul (c : ℝ) (u : H1Space U) :
    ⇑(c • u).gradientLp =ᵐ[volume.restrict U] fun x => c • u.gradientLp x :=
  Lp.coeFn_smul c u.gradientLp

/-- On an open domain, a represented H¹ class depends only on the scalar AE class. -/
lemma ofFunction_congr (hU : IsOpen U)
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {G H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G U) (hg : HasH1GradientOn g H U)
    (heq : f =ᵐ[volume.restrict U] g) : ofFunction f G hf = ofFunction g H hg :=
  ext_ae hU ((coeFn_ofFunction f G hf).trans (heq.trans (coeFn_ofFunction g H hg).symm))

@[simp]
lemma ofFunction_coeFn (hU : IsOpen U) (u : H1Space U) :
    ofFunction u u.gradientLp u.hasH1GradientOn = u :=
  ext_ae hU (coeFn_ofFunction u u.gradientLp u.hasH1GradientOn)

end H1Space

/-- Zero has zero weak gradient on any region. -/
theorem HasH1GradientOn.zero {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n))) :
    HasH1GradientOn (fun _ => 0) (fun _ => 0) U :=
  (0 : H1Space U).hasH1GradientOn.congr_ae H1Space.coeFn_zero H1Space.coeFn_gradientLp_zero

/-- Sums of H¹ representatives have the sum of their specified weak gradients. -/
theorem HasH1GradientOn.add {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {G H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G U) (hg : HasH1GradientOn g H U) :
    HasH1GradientOn (fun x => f x + g x) (fun x => G x + H x) U := by
  let u := H1Space.ofFunction f G hf
  let v := H1Space.ofFunction g H hg
  apply (u + v).hasH1GradientOn.congr_ae
  · filter_upwards [H1Space.coeFn_add u v, H1Space.coeFn_ofFunction f G hf,
      H1Space.coeFn_ofFunction g H hg] with x hx hfx hgx
    exact hx.trans (congrArg₂ (· + ·) hfx hgx)
  · filter_upwards [H1Space.coeFn_gradientLp_add u v, H1Space.gradientLp_ofFunction f G hf,
      H1Space.gradientLp_ofFunction g H hg] with x hx hGx hHx
    exact hx.trans (congrArg₂ (· + ·) hGx hHx)

/-- Scalar multiplication multiplies the specified weak gradient by the same scalar. -/
theorem HasH1GradientOn.const_mul {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G U) (c : ℝ) :
    HasH1GradientOn (fun x => c * f x) (fun x => c • G x) U := by
  let u := H1Space.ofFunction f G hf
  apply (c • u).hasH1GradientOn.congr_ae
  · filter_upwards [H1Space.coeFn_smul c u, H1Space.coeFn_ofFunction f G hf] with x hx hfx
    exact hx.trans (congrArg (c * ·) hfx)
  · filter_upwards [H1Space.coeFn_gradientLp_smul c u, H1Space.gradientLp_ofFunction f G hf]
      with x hx hGx
    exact hx.trans (congrArg (c • ·) hGx)

/-- Negating a representative negates its weak gradient. -/
theorem HasH1GradientOn.neg {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G U) :
    HasH1GradientOn (fun x => -f x) (fun x => -G x) U := by
  simpa only [neg_one_mul, neg_one_smul] using hf.const_mul (-1)

/-- Differences have the difference of their specified weak gradients. -/
theorem HasH1GradientOn.sub {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {G H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G U) (hg : HasH1GradientOn g H U) :
    HasH1GradientOn (fun x => f x - g x) (fun x => G x - H x) U := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- Finite sums retain the sum of the specified weak gradients. -/
theorem HasH1GradientOn.finsetSum {n : ℕ} {ι : Type*}
    {U : Set (EuclideanSpace ℝ (Fin n))} (s : Finset ι)
    {f : ι → EuclideanSpace ℝ (Fin n) → ℝ}
    {G : ι → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : ∀ i ∈ s, HasH1GradientOn (f i) (G i) U) :
    HasH1GradientOn (fun x => ∑ i ∈ s, f i x) (fun x => ∑ i ∈ s, G i x) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasH1GradientOn.zero U
  | @insert i s hi hs =>
    simpa only [Finset.sum_insert hi] using
      (hf i (Finset.mem_insert_self i s)).add (hs fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- Zero belongs to H¹ on any region. -/
theorem IsH1On.zero {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n))) :
    IsH1On (fun _ => 0) U := ⟨_, HasH1GradientOn.zero U⟩

/-- H¹ is closed under addition of representatives. -/
theorem IsH1On.add {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsH1On f U) (hg : IsH1On g U) :
    IsH1On (fun x => f x + g x) U := by
  obtain ⟨G, hG⟩ := hf
  obtain ⟨H, hH⟩ := hg
  exact ⟨_, hG.add hH⟩

/-- H¹ is closed under real scalar multiplication. -/
theorem IsH1On.const_mul {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsH1On f U) (c : ℝ) :
    IsH1On (fun x => c * f x) U := by
  obtain ⟨G, hG⟩ := hf
  exact ⟨_, hG.const_mul c⟩

/-- H¹ is closed under negation. -/
theorem IsH1On.neg {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsH1On f U) : IsH1On (fun x => -f x) U := by
  obtain ⟨G, hG⟩ := hf
  exact ⟨_, hG.neg⟩

/-- H¹ is closed under subtraction. -/
theorem IsH1On.sub {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsH1On f U) (hg : IsH1On g U) :
    IsH1On (fun x => f x - g x) U := by
  obtain ⟨G, hG⟩ := hf
  obtain ⟨H, hH⟩ := hg
  exact ⟨_, hG.sub hH⟩

/-- Null changes of representatives preserve H¹ membership. -/
theorem IsH1On.congr_ae {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsH1On f U)
    (heq : f =ᵐ[volume.restrict U] g) : IsH1On g U := by
  obtain ⟨G, hG⟩ := hf
  exact ⟨G, hG.congr_ae heq EventuallyEq.rfl⟩

/-- Finite sums of H¹ representatives remain H¹. -/
theorem IsH1On.finsetSum {n : ℕ} {ι : Type*}
    {U : Set (EuclideanSpace ℝ (Fin n))} (s : Finset ι)
    {f : ι → EuclideanSpace ℝ (Fin n) → ℝ} (hf : ∀ i ∈ s, IsH1On (f i) U) :
    IsH1On (fun x => ∑ i ∈ s, f i x) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsH1On.zero U
  | @insert i s hi hs =>
    simpa only [Finset.sum_insert hi] using
      (hf i (Finset.mem_insert_self i s)).add (hs fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- Restrict a weak-gradient identity to any smaller region. Compact test support
allows each restricted integral to be identified with its global integral. -/
theorem HasWeakGradientOn.mono {n : ℕ} {U V : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasWeakGradientOn f G U) (hVU : V ⊆ U) : HasWeakGradientOn f G V := by
  refine ⟨hf.locallyIntegrable_function.mono_set hVU,
    hf.locallyIntegrable_gradient.mono_set hVU, ?_⟩
  intro i φ hφ hcφ hsφ
  have hleft (W : Set (EuclideanSpace ℝ (Fin n))) (hs : tsupport φ ⊆ W) :
      (∫ x in W, f x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x, f x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [fderiv_of_notMem_tsupport ℝ (fun ht => hx (hs ht))]
    simp
  have hright (W : Set (EuclideanSpace ℝ (Fin n))) (hs : tsupport φ ⊆ W) :
      (∫ x in W, φ x * G x i) = ∫ x, φ x * G x i := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht)), zero_mul]
  rw [hleft V hsφ, hright V hsφ, ← hleft U (hsφ.trans hVU), ← hright U (hsφ.trans hVU)]
  exact hf.test_eq i φ hφ hcφ (hsφ.trans hVU)

/-- H¹ representatives and their specified weak gradients restrict to smaller regions. -/
theorem HasH1GradientOn.mono {n : ℕ} {U V : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G U) (hVU : V ⊆ U) : HasH1GradientOn f G V :=
  ⟨hf.toHasWeakGradientOn.mono hVU,
    hf.memLp_function.mono_measure (Measure.restrict_mono hVU le_rfl),
    hf.memLp_gradient.mono_measure (Measure.restrict_mono hVU le_rfl)⟩

/-- Membership in H¹ restricts to every smaller region. -/
theorem IsH1On.mono {n : ℕ} {U V : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsH1On f U) (hVU : V ⊆ U) : IsH1On f V := by
  obtain ⟨G, hG⟩ := hf
  exact ⟨G, hG.mono hVU⟩

/-- The sum of the scalar and gradient L² norms satisfies the finite triangle inequality. -/
theorem h1_lpNorm_finsetSum_le {n : ℕ} {ι : Type*}
    {U : Set (EuclideanSpace ℝ (Fin n))} (s : Finset ι)
    {f : ι → EuclideanSpace ℝ (Fin n) → ℝ}
    {G : ι → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : ∀ i ∈ s, HasH1GradientOn (f i) (G i) U) :
    lpNorm (fun x => ∑ i ∈ s, f i x) 2 (volume.restrict U) +
      lpNorm (fun x => ∑ i ∈ s, G i x) 2 (volume.restrict U) ≤
        ∑ i ∈ s, (lpNorm (f i) 2 (volume.restrict U) +
          lpNorm (G i) 2 (volume.restrict U)) := by
  simpa only [← Finset.sum_apply, Finset.sum_add_distrib] using
    add_le_add (lpNorm_sum_le (fun i hi => (hf i hi).memLp_function) (by norm_num))
      (lpNorm_sum_le (fun i hi => (hf i hi).memLp_gradient) (by norm_num))

/-- An H¹ function that vanishes almost everywhere on an open set has zero weak gradient. -/
theorem HasH1GradientOn.gradient_eq_zero_ae {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G U) (hz : f =ᵐ[volume.restrict U] 0) :
    G =ᵐ[volume.restrict U] 0 :=
  HasWeakGradientOn.unique hU
    (hf.toHasWeakGradientOn.congr_ae hz EventuallyEq.rfl)
    (HasH1GradientOn.zero U).toHasWeakGradientOn

/-- A linear map with a genuine H¹ output and component-norm bound respects scalar AE
classes on an open source domain. No target openness or sign condition on `C` is needed. -/
theorem h1_bounded_linearMap_congr_ae {n m : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {V : Set (EuclideanSpace ℝ (Fin m))}
    (hU : IsOpen U)
    (T : (EuclideanSpace ℝ (Fin n) → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin m) → ℝ))
    (C : ℝ)
    (hbound : ∀ f G, HasH1GradientOn f G U → ∃ H, HasH1GradientOn (T f) H V ∧
      lpNorm (T f) 2 (volume.restrict V) + lpNorm H 2 (volume.restrict V) ≤
        C * (lpNorm f 2 (volume.restrict U) + lpNorm G 2 (volume.restrict U)))
    (f g : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsH1On f U) (hg : IsH1On g U)
    (heq : f =ᵐ[volume.restrict U] g) : T f =ᵐ[volume.restrict V] T g := by
  obtain ⟨G, hG⟩ := hf
  obtain ⟨H, hH⟩ := hg
  have hd := hG.sub hH
  have hz : (fun x => f x - g x) =ᵐ[volume.restrict U] 0 := by
    filter_upwards [heq] with x hx
    exact sub_eq_zero.mpr hx
  have hdz := hd.gradient_eq_zero_ae hU hz
  have hf0 : lpNorm (fun x => f x - g x) 2 (volume.restrict U) = 0 :=
    (lpNorm_eq_zero hd.memLp_function (by norm_num)).mpr hz
  have hG0 : lpNorm (fun x => G x - H x) 2 (volume.restrict U) = 0 :=
    (lpNorm_eq_zero hd.memLp_gradient (by norm_num)).mpr hdz
  obtain ⟨K, hK, hb⟩ := hbound _ _ hd
  rw [hf0, hG0, add_zero, mul_zero] at hb
  have hT0 : lpNorm (T (fun x => f x - g x)) 2 (volume.restrict V) = 0 := by
    have hk0 : 0 ≤ lpNorm K 2 (volume.restrict V) := lpNorm_nonneg
    exact le_antisymm (by linarith) lpNorm_nonneg
  have hzT := (lpNorm_eq_zero hK.memLp_function (by norm_num)).mp hT0
  change T (f - g) =ᵐ[volume.restrict V] 0 at hzT
  rw [map_sub] at hzT
  filter_upwards [hzT] with x hx
  exact sub_eq_zero.mp hx

namespace H1Space

variable {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}

/-- The chosen representative of an H¹ class has an H¹ weak gradient. -/
lemma isH1On (u : H1Space U) : IsH1On u U := ⟨u.gradientLp, u.hasH1GradientOn⟩

/-- Form the H¹ class of a representative by choosing a weak gradient. On an open domain,
weak-gradient uniqueness makes this choice immaterial. -/
def ofH1Function (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsH1On f U) : H1Space U :=
  ofFunction f hf.choose hf.choose_spec

lemma coeFn_ofH1Function (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsH1On f U) :
    ⇑(ofH1Function f hf) =ᵐ[volume.restrict U] f :=
  coeFn_ofFunction f hf.choose hf.choose_spec

/-- Choosing a gradient gives the same class as any specified genuine weak gradient. -/
lemma ofH1Function_eq_ofFunction (hU : IsOpen U)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsH1On f U)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hG : HasH1GradientOn f G U) : ofH1Function f hf = ofFunction f G hG :=
  ext_ae hU ((coeFn_ofH1Function f hf).trans (coeFn_ofFunction f G hG).symm)

/-- A raw linear operator preserving H¹ and scalar AE equality descends to the H¹ graph
space on an open target domain. Source and target dimensions may differ. -/
def liftLinearMap {m : ℕ} {V : Set (EuclideanSpace ℝ (Fin m))} (hV : IsOpen V)
    (T : (EuclideanSpace ℝ (Fin n) → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin m) → ℝ))
    (hH1 : ∀ f, IsH1On f U → IsH1On (T f) V)
    (hAE : ∀ f g, IsH1On f U → IsH1On g U → f =ᵐ[volume.restrict U] g →
      T f =ᵐ[volume.restrict V] T g) : H1Space U →ₗ[ℝ] H1Space V where
  toFun f := ofH1Function (T f) (hH1 f f.isH1On)
  map_add' f g := by
    apply ext_ae hV
    have hsum : T (⇑(f + g)) =ᵐ[volume.restrict V] fun x => T f x + T g x := by
      have h := hAE (⇑(f + g)) (fun x => f x + g x) (f + g).isH1On
        (f.isH1On.add g.isH1On) (coeFn_add f g)
      change T (⇑(f + g)) =ᵐ[volume.restrict V] T (⇑f + ⇑g) at h
      rw [map_add] at h
      exact h
    filter_upwards [coeFn_ofH1Function (T (⇑(f + g))) (hH1 (⇑(f + g)) (f + g).isH1On),
      coeFn_add (ofH1Function (T f) (hH1 f f.isH1On))
        (ofH1Function (T g) (hH1 g g.isH1On)),
      coeFn_ofH1Function (T f) (hH1 f f.isH1On),
      coeFn_ofH1Function (T g) (hH1 g g.isH1On), hsum] with x hx hsum' hf hg hT
    simp only [hx, hsum', hf, hg, hT]
  map_smul' c f := by
    apply ext_ae hV
    have hsmul : T (⇑(c • f)) =ᵐ[volume.restrict V] fun x => c * T f x := by
      have h := hAE (⇑(c • f)) (fun x => c * f x) (c • f).isH1On
        (f.isH1On.const_mul c) (coeFn_smul c f)
      change T (⇑(c • f)) =ᵐ[volume.restrict V] T (c • ⇑f) at h
      rw [map_smul] at h
      exact h
    filter_upwards [coeFn_ofH1Function (T (⇑(c • f))) (hH1 (⇑(c • f)) (c • f).isH1On),
      coeFn_smul c (ofH1Function (T f) (hH1 f f.isH1On)),
      coeFn_ofH1Function (T f) (hH1 f f.isH1On), hsmul] with x hx hsmul' hf hT
    simp only [RingHom.id_apply, hx, hsmul', hf, hT]

lemma coeFn_liftLinearMap {m : ℕ} {V : Set (EuclideanSpace ℝ (Fin m))} (hV : IsOpen V)
    (T : (EuclideanSpace ℝ (Fin n) → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin m) → ℝ))
    (hH1 : ∀ f, IsH1On f U → IsH1On (T f) V)
    (hAE : ∀ f g, IsH1On f U → IsH1On g U → f =ᵐ[volume.restrict U] g →
      T f =ᵐ[volume.restrict V] T g) (f : H1Space U) :
    ⇑(liftLinearMap hV T hH1 hAE f) =ᵐ[volume.restrict V] T f :=
  coeFn_ofH1Function (T f) (hH1 f f.isH1On)

/-- On represented input functions, the lift gives the class of the original operator. -/
lemma liftLinearMap_ofFunction {m : ℕ} {V : Set (EuclideanSpace ℝ (Fin m))} (hV : IsOpen V)
    (T : (EuclideanSpace ℝ (Fin n) → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin m) → ℝ))
    (hH1 : ∀ f, IsH1On f U → IsH1On (T f) V)
    (hAE : ∀ f g, IsH1On f U → IsH1On g U → f =ᵐ[volume.restrict U] g →
      T f =ᵐ[volume.restrict V] T g)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : HasH1GradientOn f G U) :
    liftLinearMap hV T hH1 hAE (ofFunction f G hf) =
      ofH1Function (T f) (hH1 f ⟨G, hf⟩) := by
  apply ext_ae hV
  exact (coeFn_liftLinearMap hV T hH1 hAE _).trans
    ((hAE (ofFunction f G hf) f (ofFunction f G hf).isH1On ⟨G, hf⟩
      (coeFn_ofFunction f G hf)).trans (coeFn_ofH1Function (T f) (hH1 f ⟨G, hf⟩)).symm)

section ContinuousLift

variable {m : ℕ} {V : Set (EuclideanSpace ℝ (Fin m))}
  (hV : IsOpen V)
  (T : (EuclideanSpace ℝ (Fin n) → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin m) → ℝ))
  (C : ℝ) (hC : 0 ≤ C)
  (hbound : ∀ f G, HasH1GradientOn f G U → ∃ H, HasH1GradientOn (T f) H V ∧
    lpNorm (T f) 2 (volume.restrict V) + lpNorm H 2 (volume.restrict V) ≤
      C * (lpNorm f 2 (volume.restrict U) + lpNorm G 2 (volume.restrict U)))
  (hAE : ∀ f g, IsH1On f U → IsH1On g U → f =ᵐ[volume.restrict U] g →
    T f =ᵐ[volume.restrict V] T g)

include hbound

/-- The output-existence part of a quantitative H¹ operator bound gives H¹ preservation. -/
lemma isH1On_map_of_bound (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsH1On f U) :
    IsH1On (T f) V := by
  obtain ⟨G, hG⟩ := hf
  obtain ⟨H, hH, _⟩ := hbound f G hG
  exact ⟨H, hH⟩

include hC

/-- Sum-of-component L² bounds give a Hilbert norm bound with explicit factor two. -/
lemma norm_liftLinearMap_le (hH1 : ∀ f, IsH1On f U → IsH1On (T f) V) (f : H1Space U) :
    ‖liftLinearMap hV T hH1 hAE f‖ ≤ (2 * C) * ‖f‖ := by
  obtain ⟨H, hH, hb⟩ := hbound f f.gradientLp f.hasH1GradientOn
  have heq : liftLinearMap hV T hH1 hAE f = ofFunction (T f) H hH := by
    apply ext_ae hV
    exact (coeFn_liftLinearMap hV T hH1 hAE f).trans (coeFn_ofFunction (T f) H hH).symm
  calc
    _ ≤ lpNorm (T f) 2 (volume.restrict V) + lpNorm H 2 (volume.restrict V) := by
      rw [heq]
      exact norm_ofFunction_le (T f) H hH
    _ ≤ C * (lpNorm f 2 (volume.restrict U) +
        lpNorm f.gradientLp 2 (volume.restrict U)) := hb
    _ = C * (‖f.toLp‖ + ‖f.gradientLp‖) := by
      rw [norm_toLp_eq_lpNorm, norm_gradientLp_eq_lpNorm]
    _ ≤ C * (2 * ‖f‖) := mul_le_mul_of_nonneg_left f.sum_norm_le hC
    _ = (2 * C) * ‖f‖ := by ring

/-- Lift a quantitatively bounded raw function operator to a continuous H¹ operator.
The bound supplies an actual output weak gradient; AE compatibility handles representatives. -/
def liftContinuousLinearMap : H1Space U →L[ℝ] H1Space V :=
  (liftLinearMap hV T (isH1On_map_of_bound T C hbound) hAE).mkContinuous (2 * C)
    (norm_liftLinearMap_le hV T C hC hbound hAE (isH1On_map_of_bound T C hbound))

lemma coeFn_liftContinuousLinearMap (f : H1Space U) :
    ⇑(liftContinuousLinearMap hV T C hC hbound hAE f) =ᵐ[volume.restrict V] T f :=
  coeFn_liftLinearMap hV T (isH1On_map_of_bound T C hbound) hAE f

/-- The continuous lift acts on every specified H¹ representative as the raw operator. -/
lemma liftContinuousLinearMap_ofFunction (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : HasH1GradientOn f G U) :
    liftContinuousLinearMap hV T C hC hbound hAE (ofFunction f G hf) =
      ofH1Function (T f) (isH1On_map_of_bound T C hbound f ⟨G, hf⟩) :=
  liftLinearMap_ofFunction hV T (isH1On_map_of_bound T C hbound) hAE f G hf

/-- The lifted operator has norm at most twice the component-norm bound. -/
lemma norm_liftContinuousLinearMap_le : ‖liftContinuousLinearMap hV T C hC hbound hAE‖ ≤ 2 * C :=
  LinearMap.mkContinuous_norm_le _ (mul_nonneg (by norm_num) hC)
    (norm_liftLinearMap_le hV T C hC hbound hAE (isH1On_map_of_bound T C hbound))

/-- On open source and target domains, the quantitative H¹ bound itself supplies all
AE compatibility needed to descend a raw linear operator. -/
def liftBoundedLinearMap (hU : IsOpen U) : H1Space U →L[ℝ] H1Space V :=
  liftContinuousLinearMap hV T C hC hbound (h1_bounded_linearMap_congr_ae hU T C hbound)

lemma coeFn_liftBoundedLinearMap (hU : IsOpen U) (f : H1Space U) :
    ⇑(liftBoundedLinearMap hV T C hC hbound hU f) =ᵐ[volume.restrict V] T f :=
  coeFn_liftContinuousLinearMap hV T C hC hbound
    (h1_bounded_linearMap_congr_ae hU T C hbound) f

lemma liftBoundedLinearMap_ofFunction (hU : IsOpen U)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : HasH1GradientOn f G U) :
    liftBoundedLinearMap hV T C hC hbound hU (ofFunction f G hf) =
      ofH1Function (T f) (isH1On_map_of_bound T C hbound f ⟨G, hf⟩) :=
  liftContinuousLinearMap_ofFunction hV T C hC hbound
    (h1_bounded_linearMap_congr_ae hU T C hbound) f G hf

lemma norm_liftBoundedLinearMap_le (hU : IsOpen U) :
    ‖liftBoundedLinearMap hV T C hC hbound hU‖ ≤ 2 * C :=
  norm_liftContinuousLinearMap_le hV T C hC hbound
    (h1_bounded_linearMap_congr_ae hU T C hbound)

end ContinuousLift

end H1Space

end LiquidDrop
