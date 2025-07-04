import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Towards a formalization of the Second Partial Derivatives Test
Project members: Asaf, Erin, Janani, Martin
 -/

lemma update₀ {α : Type*} (a b c : α)  :
  Function.update ![a,b] 0 c = ![c,b] := by
  ext i
  fin_cases i <;> simp

lemma update₁ {α : Type*} (a b c : α) :
  Function.update ![a,b] 1 c = ![a,c] := by
  ext i
  fin_cases i <;> simp

noncomputable def hessianLinearCompanion {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ := fun a => {
    toFun := fun b => iteratedFDeriv ℝ 2 f x₀ ![a,b]
                    + iteratedFDeriv ℝ 2 f x₀ ![b,a]
    map_add' := fun b c => by
      have h_add := (iteratedFDeriv ℝ 2 f x₀).map_update_add'
      have h₀ := h_add ![b, a] 0 b c
      have h₁ := h_add ![a, b] 1 b c
      repeat simp [update₁] at h₁; simp [update₀] at h₀
      linarith
    map_smul' := by
      intro m x
      have h_smul := (iteratedFDeriv ℝ 2 f x₀).map_update_smul'
      have h₀ := h_smul ![x,a] 0 m x
      have h₁ := h_smul ![a,x] 1 m x
      repeat rw [update₀] at h₀; rw [update₁] at h₁
      simp at h₀ h₁ ⊢
      linarith
  }

noncomputable def hessianLinearCompanion₀ {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin 1))
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ := fun a => {
    toFun := fun b => iteratedFDeriv ℝ 2 f x₀ ![a,b] 0
                    + iteratedFDeriv ℝ 2 f x₀ ![b,a] 0
    map_add' := fun b c => by
      have h_add := (iteratedFDeriv ℝ 2 f x₀).map_update_add'
      have h₀ := h_add ![b, a] 0 b c
      have h₁ := h_add ![a, b] 1 b c
      repeat simp [update₁] at h₁; simp [update₀] at h₀
      repeat rw [h₀, h₁]
      ring_nf
      field_simp
      linarith
    map_smul' := by
      intro m x
      have h_smul := (iteratedFDeriv ℝ 2 f x₀).map_update_smul'
      have h₀ := h_smul ![x,a] 0 m x
      have h₁ := h_smul ![a,x] 1 m x
      repeat rw [update₀] at h₀; rw [update₁] at h₁
      simp at h₀ h₁ ⊢
      repeat rw [h₀, h₁]
      ring_nf
      field_simp
  }

noncomputable def hessianBilinearCompanion {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)): LinearMap.BilinMap ℝ (EuclideanSpace ℝ (Fin n)) ℝ := {
    toFun := hessianLinearCompanion f x₀
    map_add' := fun x y => by
        have had := (iteratedFDeriv ℝ 2 f x₀).map_update_add'
        ext i
        have had₀ := had ![x,i] 0 x y
        have had₁ := had ![i,i] 1 x y
        repeat rw [update₀] at had₀
        repeat rw [update₁] at had₁
        simp [hessianLinearCompanion] at had₀ had₁ ⊢
        exact
          (Mathlib.Tactic.Ring.add_pf_add_overlap had₀.symm had₁.symm).symm

    map_smul' := fun m x => LinearMap.ext_iff.mpr <| fun x₁ => by
        have hsm := (iteratedFDeriv ℝ 2 f x₀).map_update_smul'
        have hsm₀ := hsm ![x,x₁] 0 m x
        have hsm₁ := hsm ![x₁,x] 1 m x
        have h := CancelDenoms.add_subst hsm₀.symm hsm₁.symm
        repeat rw [update₀, update₁] at h
        exact h.symm
}

noncomputable def hessianBilinearCompanion₀ {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin 1))
    (x₀ : EuclideanSpace ℝ (Fin n)): LinearMap.BilinMap ℝ (EuclideanSpace ℝ (Fin n)) ℝ := {
    toFun := hessianLinearCompanion₀ f x₀
    map_add' := fun x y => by
        have had := (iteratedFDeriv ℝ 2 f x₀).map_update_add'
        ext i
        have had₀ := had ![x,i] 0 x y
        have had₁ := had ![i,i] 1 x y
        repeat rw [update₀] at had₀
        repeat rw [update₁] at had₁
        simp [hessianLinearCompanion₀] at had₀ had₁ ⊢
        repeat rw [had₀, had₁]
        ring_nf
        field_simp
        linarith
    map_smul' := fun m x => LinearMap.ext_iff.mpr <| fun x₁ => by
        have hsm := (iteratedFDeriv ℝ 2 f x₀).map_update_smul'
        have hsm₀ := hsm ![x,x₁] 0 m x
        have hsm₁ := hsm ![x₁,x] 1 m x
        simp
        repeat rw [update₀] at hsm₀
        repeat rw [update₁] at hsm₁
        simp [hessianLinearCompanion₀] at hsm₀ hsm₁ ⊢
        repeat rw [hsm₀, hsm₁]
        ring_nf
        field_simp
}




/-- Unnecessarily complicated.
 For a more familiar constructor when R is a ring, see QuadraticMap.ofPolar -/
noncomputable def hessianQuadraticMap {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
  QuadraticMap ℝ (EuclideanSpace ℝ (Fin n)) ℝ :=
  {
    toFun := fun y => iteratedFDeriv ℝ 2 f x₀ ![y,y]
    exists_companion' := by
      have hsm := (iteratedFDeriv ℝ 2 f x₀).map_update_smul'
      have had := (iteratedFDeriv ℝ 2 f x₀).map_update_add'
      use hessianBilinearCompanion f x₀
      intro x y
      have had₀ := had ![x, x + y] 0 x y
      have had₁ := had ![x,x] 1 x y
      have had₂ := had ![y,x] 1 x y
      repeat rw [update₀] at had₀; rw [update₁] at had₁ had₂
      simp [hessianLinearCompanion, hessianBilinearCompanion] at had₀ had₁ had₂ ⊢
      linarith
    toFun_smul := by
      have hsm := (iteratedFDeriv ℝ 2 f x₀).map_update_smul'
      have had := (iteratedFDeriv ℝ 2 f x₀).map_update_add'
      intro u v
      have hsm₀ := hsm ![v, v] 0 u v
      have hsm₁ := hsm ![u • v,v] 1 u v
      repeat simp [update₀] at hsm₀; simp [update₁] at hsm₁
      rw [smul_eq_mul, mul_assoc, ← hsm₀, hsm₁]
  }

/-- This is the main of showing PosDef implies IsCoercive. -/
lemma maybe_not_lp_sphere {n : ℕ} (f : EuclideanSpace ℝ (Fin n.succ) → ℝ)
    (hf : Continuous f) (hf' : ∀ x ≠ 0, f x > 0) :
    ∃ x : Metric.sphere 0 1, ∀ y : Metric.sphere 0 1, f x.1 ≤ f y.1 := by
  have h₀ : HasCompactSupport
    fun (x : ↑(Metric.sphere (0:EuclideanSpace ℝ (Fin n.succ)) 1)) ↦ f ↑x := by
    rw [hasCompactSupport_def]
    rw [Function.support]
    have : @setOf ↑(Metric.sphere (0:EuclideanSpace ℝ (Fin n.succ)) (1:ℝ)) (fun x ↦ f x.1 ≠ 0)
      = Set.univ := by
      apply subset_antisymm
      simp
      intro a ha
      suffices f a > 0 by
        aesop
      apply hf'
      intro hc
      have : ‖a.1‖ = 1 := norm_eq_of_mem_sphere a
      rw [hc] at this
      simp at this
    rw [this]
    simp
    exact CompactSpace.isCompact_univ
  have ⟨m,hm⟩ := @Continuous.exists_forall_le_of_hasCompactSupport ℝ
    (Metric.sphere (0:EuclideanSpace ℝ (Fin n.succ)) 1) _
    _ _ _ (by
      have := (@NormedSpace.sphere_nonempty (EuclideanSpace ℝ (Fin n.succ))
        _ _ _ 0 1).mpr (by simp)
      exact Set.Nonempty.to_subtype this) _
        (fun x => f x) (by
          refine Continuous.comp' hf ?_
          exact continuous_subtype_val) h₀
  use m

theorem conthess {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x₀ : EuclideanSpace ℝ (Fin n)} :
    Continuous (hessianQuadraticMap f x₀) := by
  simp [hessianQuadraticMap]
  show Continuous fun y ↦ (iteratedFDeriv ℝ 2 f x₀) ![y, y]
  refine Continuous.comp' ?_ ?_
  · exact ContinuousMultilinearMap.coe_continuous (iteratedFDeriv ℝ 2 f x₀)
  · refine Continuous.matrixVecCons ?_ ?_
    · exact continuous_id'
    · refine Continuous.matrixVecCons ?_ ?_
      · exact continuous_id'
      · exact continuous_const


lemma maybe_not_lp_sphere'
 {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n.succ) → ℝ} {x₀ : EuclideanSpace ℝ (Fin n.succ)}
  (hf : (hessianQuadraticMap f x₀).PosDef) :
    ∃ x : Metric.sphere 0 1, ∀ y : Metric.sphere 0 1,
    (hessianQuadraticMap f x₀) x.1 ≤ (hessianQuadraticMap f x₀) y.1 := by
  exact @maybe_not_lp_sphere n (hessianQuadraticMap f x₀) conthess hf



/-- A continuous multilinear map is, in particular, bilinear
in the sense needed to consider the `IsCoercive` proposition. -/
noncomputable def continuousBilinearMap_of_continuousMultilinearMap {n : ℕ}
    (g : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => EuclideanSpace ℝ (Fin n)) ℝ) :
    (EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ := {
    toFun := fun x => {
        toFun := fun y => g.toFun ![x,y]
        map_add' := by
            intro a b
            have := g.map_update_add ![x,b] 1 a b
            repeat rw [update₁] at this
            exact this
        map_smul' := by
            intro m a
            have := g.map_update_smul ![x,a] 1 m a
            repeat rw [update₁] at this
            exact this
        cont := Continuous.comp' g.cont <| Continuous.matrixVecCons continuous_const
                <| Continuous.matrixVecCons continuous_id' continuous_const
    }
    map_add' := by
        intro a b
        ext c
        have := g.map_update_add ![a,c] 0 a b
        repeat rw [update₀] at this
        exact this
    map_smul' := by
        intro c x
        ext y
        have := g.map_update_smul ![x,y] 0 c x
        repeat rw [update₀] at this
        exact this
    cont := continuous_clm_apply.mpr fun x => Continuous.comp' g.cont
        <| Continuous.matrixVecCons continuous_id' continuous_const
}


lemma getCoercive₀ {f : EuclideanSpace ℝ (Fin 0) → ℝ}
    {x₀ : EuclideanSpace ℝ (Fin 0)} :
    IsCoercive (continuousBilinearMap_of_continuousMultilinearMap
        (iteratedFDeriv ℝ 2 f x₀)) := by
  simp [IsCoercive, continuousBilinearMap_of_continuousMultilinearMap]
  use 1
  constructor
  · simp
  · intro u
    have : u = ![] := by refine PiLp.ext ?_; intro z;have := z.2;simp at this
    subst this
    simp
    have : @norm (EuclideanSpace ℝ (Fin 0)) (PiLp.normedAddCommGroup 2 fun x ↦ ℝ).toNorm
      (@Matrix.vecEmpty ℝ : Fin 0 → ℝ) = 0 := by simp;exact Subsingleton.eq_zero ![]
    rw [this]
    simp
    have : f = fun z => f ![] := by
      ext z
      congr
      ext i
      have := i.2
      simp at this
    rw [this]
    simp
    rw [iteratedFDeriv_succ_apply_left]
    simp
    rw [iteratedFDeriv]
    simp

lemma getCoercive {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hf : (hessianQuadraticMap f x₀).PosDef) :
    IsCoercive (continuousBilinearMap_of_continuousMultilinearMap
        (iteratedFDeriv ℝ 2 f x₀)) := by
  by_cases H : n = 0
  · subst H
    exact @getCoercive₀ f x₀
  obtain ⟨m,hm⟩ : ∃ m : ℕ, n = m.succ := by exact Nat.exists_eq_succ_of_ne_zero H
  subst hm
  have := @maybe_not_lp_sphere' m f x₀ hf
  simp [IsCoercive, continuousBilinearMap_of_continuousMultilinearMap]
  simp [hessianQuadraticMap] at this
  obtain ⟨m,hm⟩ := this
  have := hm.2
  use (iteratedFDeriv ℝ 2 f x₀) ![m, m]
  have := hf m (by intro hc;subst hc;simp at hm)
  simp [hessianQuadraticMap] at this
  constructor
  · exact this
  · intro u
    by_cases hu : u = 0
    · subst hu
      simp
      rw [iteratedFDeriv_succ_apply_left]
      simp
    · have h₁ : ‖u‖ ≠ 0 := by exact norm_ne_zero_iff.mpr hu
      have h₂ : 0 < ‖u‖⁻¹ := Right.inv_pos.mpr <| norm_pos_iff.mpr hu
      have h₃ : ‖u‖ * ‖u‖⁻¹ = 1 := CommGroupWithZero.mul_inv_cancel ‖u‖ h₁
      repeat (
        refine le_of_mul_le_mul_right ?_ h₂
        rw [mul_assoc, h₃]
        simp)
      have : (iteratedFDeriv ℝ 2 f x₀) ![u, u] * ‖u‖⁻¹
        = (iteratedFDeriv ℝ 2 f x₀) ![‖u‖⁻¹ • u, u] := by
        rw [mul_comm]
        rw [iteratedFDeriv_succ_apply_left]
        rw [iteratedFDeriv_succ_apply_left]
        simp
        left
        congr
      rw [this]
      have h₄ : (iteratedFDeriv ℝ 2 f x₀) ![‖u‖⁻¹ • u, u] * ‖u‖⁻¹
        = (iteratedFDeriv ℝ 2 f x₀) ![‖u‖⁻¹ • u, ‖u‖⁻¹ • u] := by
        let G := iteratedFDeriv ℝ 2 f x₀
        show G ![‖u‖⁻¹ • u, u] * ‖u‖⁻¹ = G ![‖u‖⁻¹ • u, ‖u‖⁻¹ • u]
        rw [mul_comm]
        let v := ‖u‖⁻¹ • u
        show  ‖u‖⁻¹ * G ![v, u] = G ![v, ‖u‖⁻¹ • u]
        show  ‖u‖⁻¹ * G.toFun ![v, u] = G.toFun ![v, ‖u‖⁻¹ • u]
        simp
        have := G.map_update_smul' ![v,u] 1 ‖u‖⁻¹ u
        repeat rw [update₁] at this
        symm
        simp at this ⊢
        rw [this]
      rw [h₄]
      have := hm.2 (‖u‖⁻¹ • u) (by simp [norm_smul];field_simp)
      simp at this ⊢
      exact this



-- theorem second_partial_deriv_test_for_deg_two {n : ℕ}
--     {f : EuclideanSpace ℝ (Fin n) → ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
--     (h : ∀ x, f x = f x₀
--                      + inner ℝ (gradient f x₀) (x - x₀)
--                   + (1 / 2) * hessianQuadraticMap f x₀ (x - x₀))
--     (h₀ : gradient f x₀ = 0) (hQQ : (hessianQuadraticMap f x₀).PosDef) :
--     IsLocalMin f x₀ := Filter.eventually_iff_exists_mem.mpr <| by
--   use Set.univ
--   constructor
--   · simp
--   · intro y _
--     rw [h y, h₀]
--     simp
--     exact QuadraticMap.PosDef.nonneg hQQ (y - x₀)

noncomputable def higher_taylor_coeff {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) (k : ℕ) :=
    fun x =>
    (1 / Nat.factorial k) * (iteratedFDeriv ℝ k f x₀ fun _ => x - x₀)

noncomputable def higher_taylor {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    EuclideanSpace ℝ (Fin n) → ℝ := by
    intro x
    let h (i) := higher_taylor_coeff f x₀ i x
    exact ∑ i ∈ Finset.range (k+1), h i

-- theorem second_partial_deriv_test_for_deg_two' {n : ℕ}
--     {f : EuclideanSpace ℝ (Fin n) → ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
--     (h : ∀ x, f x
--       = (1 / Nat.factorial 0) * (iteratedFDeriv ℝ 0 f x₀ fun _ => x - x₀)
--       + (1 / Nat.factorial 1) * (iteratedFDeriv ℝ 1 f x₀ fun _ => x - x₀)
--       + (1 / Nat.factorial 2) * (iteratedFDeriv ℝ 2 f x₀ fun _ => x - x₀))
--     (h₀ : gradient f x₀ = 0) (hQQ : (hessianQuadraticMap f x₀).PosDef) :
--     IsLocalMin f x₀ := Filter.eventually_iff_exists_mem.mpr <| by
--   use Set.univ
--   constructor
--   · simp
--   · intro y _
--     have h : ∀ x, f x
--       = (1 / Nat.factorial 0) * iteratedFDeriv ℝ 0 f x₀ ![]
--       + (1 / Nat.factorial 1) * (iteratedFDeriv ℝ 1 f x₀ (fun _ => x - x₀))
--       + (1 / Nat.factorial 2) * (fun y => iteratedFDeriv ℝ 2 f x₀ ![y, y]) (x - x₀)
--                   := by
--                   intro x
--                   convert h x using 2
--                   congr
--                   simp
--                   congr
--                   ext i j
--                   fin_cases i <;> simp
--     have h : ∀ x, f x = (1 / Nat.factorial 0) * iteratedFDeriv ℝ 0 f x₀ ![]
--                   + (1 / Nat.factorial 1) * iteratedFDeriv ℝ 1 f x₀ ![x - x₀]
--                   + (1 / Nat.factorial 2) * (fun y => iteratedFDeriv ℝ 2 f x₀ ![y, y]) (x - x₀)
--                   := by
--                   intro x
--                   convert h x using 2
--                   congr
--                   ext;simp
--     have h₁ : inner ℝ (gradient f x₀) (y - x₀) = (fderiv ℝ f x₀) (y - x₀) := by
--         unfold gradient
--         simp

--     have h₂ : (iteratedFDeriv ℝ 1 f x₀) ![y - x₀] = (fderiv ℝ f x₀) (y - x₀) := by
--         simp
--     have h₃ := Eq.trans h₁ h₂.symm
--     have := h y
--     rw [← h₃] at this
--     simp only [iteratedFDeriv_zero_apply] at this

--     rw [h₀] at this
--     simp at this
--     rw [this]
--     simp
--     exact QuadraticMap.PosDef.nonneg hQQ (y - x₀)

/- If a multivariate function equals its second Taylor polynomial
then the second derivative test holds for it.
This includes basic examples in multivariable calculus such as
z = y² - x², z = x² + y² and z = 1 - x² - y² + 7x - 9xy.
-/
-- theorem second_partial_deriv_test_for_deg_two'' {n : ℕ}
--     {f : EuclideanSpace ℝ (Fin n) → ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
--     (h : f = higher_taylor f x₀ 2)
--     (h₀ : gradient f x₀ = 0) (hQQ : (hessianQuadraticMap f x₀).PosDef) :
--     IsLocalMin f x₀ := by
--     exact @second_partial_deriv_test_for_deg_two' n f x₀ (by
--         intro x
--         nth_rewrite 1 [h]

--         simp [higher_taylor, higher_taylor_coeff]
--         rw [Finset.range_succ]
--         simp
--         rw [Finset.range_succ]
--         simp
--         suffices (2⁻¹ * (iteratedFDeriv ℝ 2 f x₀) fun i => x - x₀) =
--         2⁻¹ * (iteratedFDeriv ℝ 2 f x₀) (Fin.repeat 2 ![x - x₀]) by linarith
--         congr
--         ext i j
--         fin_cases i <;> simp) h₀ hQQ

/-- This version generalizes the 1-variable 2nd derivative test. -/
theorem isLocalMin_of_PosDef_of_Littleo {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
    (h : (fun x => |f x - higher_taylor f x₀ 2 x|) =o[nhds x₀] fun x => ‖x - x₀‖ ^ 2)
    (h₀ : gradient f x₀ = 0)
    (hf : (hessianQuadraticMap f x₀).PosDef)
     :
    IsLocalMin f x₀ := by
  have hQQ : IsCoercive (continuousBilinearMap_of_continuousMultilinearMap
        (iteratedFDeriv ℝ 2 f x₀)) :=  @getCoercive n f x₀ hf
  obtain ⟨C,hC⟩ := hQQ
  simp [Asymptotics.IsLittleO, Asymptotics.IsBigOWith] at h
  apply Filter.Eventually.mono <| h (half_pos hC.1)
  intro x
  have h₄ := hC.2 (x - x₀)
  simp [continuousBilinearMap_of_continuousMultilinearMap] at h₄
  have h₃ : ∑ x_1 ∈ Finset.range 3, higher_taylor_coeff f x₀ x_1 x
   = higher_taylor_coeff f x₀ 0 x + higher_taylor_coeff f x₀ 1 x +
     higher_taylor_coeff f x₀ 2 x := by
    repeat rw [Finset.range_succ]; simp
    linarith
  simp [higher_taylor]
  rw [h₃]
  simp [higher_taylor_coeff]
  intro h₁
  have h₂ : inner ℝ (gradient f x₀) (x - x₀) = (fderiv ℝ f x₀) (x - x₀) := by
    unfold gradient; simp
  rw [h₀] at h₂
  simp at h₂
  rw [← h₂] at h₁
  simp at h₁
  rw [mul_assoc,show ![x - x₀, x - x₀] = fun _ => x - x₀ by
    ext i j; fin_cases i <;> simp] at h₄
  rw [(Lean.Grind.Semiring.pow_two ‖x - x₀‖).symm] at h₄
  have h₅ : - (f x - (f x₀ + 2⁻¹ * (iteratedFDeriv ℝ 2 f x₀) fun x_1 => x - x₀))
    ≤ (C / 2) * ‖x - x₀‖ ^ 2 := le_of_max_le_right h₁
  ring_nf at h₅
  linarith

-- instance : NontriviallyNormedField (EuclideanSpace ℝ (Fin 1)) := by
--     refine {
--             toNormedField := {

--             }
--             non_trivial := by use ![2];sorry
--     }

-- theorem getone {n : ℕ}
--     {f : EuclideanSpace ℝ (Fin 1) → ℝ} {x₀ : EuclideanSpace ℝ (Fin 1)}
--     (h : (fun x => |f x - higher_taylor f x₀ 2 x|) =o[nhds x₀] fun x => ‖x - x₀‖ ^ 2)
--     (h₀ : deriv (deriv f) x₀ > 0) :
--     IsCoercive (continuousBilinearMap_of_continuousMultilinearMap
--         (iteratedFDeriv ℝ 2 f x₀)) := by
--   simp [continuousBilinearMap_of_continuousMultilinearMap, IsCoercive]
--   sorry

lemma better_types (f : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) (hf : f = fun x => x)
    (x₀ : EuclideanSpace ℝ (Fin 1)) (x : Fin 2 → EuclideanSpace ℝ (Fin 1)):
    iteratedFDeriv ℝ 2 f x₀ x = 0 := by
  rw [hf]
  rw [iteratedFDeriv_two_apply]
  have : fderiv ℝ (fun x : EuclideanSpace ℝ (Fin 1) => x) = by
    intro y
    exact {
        toFun := id
        map_add' := by simp
        map_smul' := by simp
        cont := by continuity
    } := by
    ext i j
    simp
  rw [this]
  simp


noncomputable def g {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x₀ h : EuclideanSpace ℝ (Fin n)) : ℝ → ℝ := fun t => f <| x₀ + t • h

lemma Then  {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x₀ h : EuclideanSpace ℝ (Fin n)) (t : ℝ)
    (h₁ : DifferentiableAt ℝ f ((fun t => x₀ + t • h) t))
    (h₂ : DifferentiableAt ℝ (fun t => x₀ + t • h) t)
    :
    deriv (g f x₀ h) t =
    fderiv ℝ f (x₀ + t • h) (h) := by
  unfold g
  rw [show (fun t => f (x₀ + t • h)) = f ∘ fun t => x₀ + t • h by ext;simp]
  rw [← fderiv_deriv]
  rw [fderiv_comp t h₁ h₂]
  simp
  have : deriv (fun y => y • h) t = h := by
    rw [deriv_fun_smul differentiableAt_fun_id <| differentiableAt_const h]
    simp
  rw [this]

-- instance {n : ℕ} : Norm (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin 1)) := by
--     exact ContinuousLinearMap.hasOpNorm
example {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin 1))
    (x₀ x h : EuclideanSpace ℝ (Fin n)) (t : ℝ) (ε : ℝ) : Prop := by
    let d := ‖iteratedFDeriv ℝ 2 f x₀‖
    have a := iteratedFDeriv ℝ 1 f (x+h)
    have b := fun y => iteratedFDeriv ℝ 2 f x ![h,y]
    have G : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin 1) := {
        toFun := fun y =>
            iteratedFDeriv ℝ 1 f (x+h) ![y]
        map_add' := fun u v => by simp
        map_smul' := fun m u => by simp
        cont := by sorry
    }
    have H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin 1) := {
        toFun := fun y =>
            iteratedFDeriv ℝ 2 f x ![h,y]
        map_add' := fun u v => by
            --have := (hessianQuadraticMap f) --.map_add'
            -- need a Fin 1 version of that.
            sorry
        map_smul' := fun m u => by simp;sorry
        cont := by sorry
    }
    have F : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin 1) := {
        toFun := fun y =>
            iteratedFDeriv ℝ 1 f (x+h) ![y] - iteratedFDeriv ℝ 1 f (x) ![y]
                                      + iteratedFDeriv ℝ 2 f x ![h,y]
        map_add' := fun u v => by simp;sorry
        map_smul' := fun m u => by simp;sorry
        cont := by sorry
    }
    exact (‖F‖ < ε * ‖h‖)

    -- ∃ δ > 0, ∀ h : EuclideanSpace ℝ (Fin n), ‖h‖ < δ →
    --     fderiv ℝ f (x + h) - fderiv ℝ f (x) - iteratedFDeriv ℝ 2 f x ![h,h]
    --     -- ‖ fderiv f (x + h) - fderiv f (x) - iteratedFDeriv ℝ 2 f x (h) ‖
    --     = 0
    --     --< ε • ‖ h ‖
    --     := sorry

/-!

# WORK NOT DIRECTLY USED

-/

noncomputable def part_deriv_x
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) : ℝ → ℝ → ℝ :=
    fun y => deriv fun x => f ![x, y]

noncomputable def partDeriv_x
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) : EuclideanSpace ℝ (Fin 2) → ℝ :=
    fun x => part_deriv_x f (x 0) (x 1)

theorem grad_zero_of_extr (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (a : Fin 2 → ℝ) (h₀ : DifferentiableAt ℝ f a)
    (h : IsLocalExtr f a) : gradient f a =0 := by
    apply HasGradientAt.gradient
    have h₁ := (hasFDerivAt_iff_hasGradientAt).mp
        (DifferentiableAt.hasFDerivAt h₀)
    rw [IsLocalExtr.fderiv_eq_zero h] at h₁
    simp at h₁
    exact h₁

example : fderiv ℝ (fun x : ℝ => x) =
  fun _ => {
    toFun := id
    map_add' := by simp
    map_smul' := by simp
  } := by ext x;simp

noncomputable def hessian {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => iteratedFDeriv ℝ 2 f x ![Pi.single i 1, Pi.single j 1]

-- Correct, but hard to prove things about?
noncomputable def hessianDet (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n)) := (hessian f x).det


/-!

# WORK CONTAINING SORRIES

-/

example (a b c d : ℝ) (f : EuclideanSpace ℝ (Fin 2) → ℝ) (x₀ : EuclideanSpace ℝ (Fin 2))
    (h : ∀ x y, f ![x, y] = 0) :
    ∀ x, f x = f x₀ + inner ℝ (gradient f x₀) (x - x₀) + (1 / 2) * hessianQuadraticMap f x₀ (x - x₀)
    := by

    sorry


example (a b c d j k : ℝ) (f : EuclideanSpace ℝ (Fin 2) → ℝ) (x' : EuclideanSpace ℝ (Fin 2))
(h : ∀ x y, f ![x, y] = a * x ^ 2 + b * x * y + c * y ^ 2 + d + j * x + k * y) :
∀ x, f x = f x' + inner ℝ (gradient f x') (x - x') + (1 / 2) * hessianQuadraticMap f x' (x - x')
:= by
    intro x

    let x₁ := x 0
    let x₂ := x 1
    let x'₁ := x' 0
    let x'₂ := x' 1

    have fx : f x = f ![x₁, x₂] := by
      congr
      ext i
      fin_cases i <;> simp [x₁, x₂]
    have fx' : f x' = f ![x'₁, x'₂] := by
      congr
      ext i
      fin_cases i <;> simp [x'₁, x'₂]
    rw [fx, fx']

    have fx_eq := h x₁ x₂
    rw [fx_eq]

    have fx'_eq := h x'₁ x'₂
    rw [fx'_eq]

-- not sure how to get lean to calculate this or the hessian
    let grad_fx' : EuclideanSpace ℝ (Fin 2) :=
      ![2 * a * x'₁ + b * x'₂ + j, b * x'₁ + 2 * c * x'₂ + k]

    let hess : Matrix (Fin 2) (Fin 2) ℝ := !![2 * a, b; b, 2 * c]
    let lin_hess := Matrix.toEuclideanLin hess
    let dx := x - x'

    have grad_eq : gradient f x' = grad_fx' := by
      sorry
    rw [grad_eq]


    have hess_eq : hessianQuadraticMap f x' dx = inner ℝ (lin_hess dx) dx := by
      sorry
    rw [hess_eq]

--everyone, say thank you chat for these

    have inner_grad :
      inner ℝ grad_fx' dx =  (2 * a * x'₁ + b * x'₂ + j) * (x₁ - x'₁) +
      (b * x'₁ + 2 * c * x'₂ + k) * (x₂ - x'₂) := by
        simp [inner, grad_fx', dx]
        ring
    rw [inner_grad]

    have inner_hess :
      inner ℝ (lin_hess dx) dx = 2 * a * (x₁ - x'₁)^2 + 2 * c *
      (x₂ - x'₂)^2 + 2 * b * (x₁ - x'₁) * (x₂ - x'₂) := by
        simp
        sorry
    rw [inner_hess]

    linarith

noncomputable def hessianQuadraticMap₀ {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin 1))
    (x₀ : EuclideanSpace ℝ (Fin n)) :
  QuadraticMap ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin 1)) := by
  exact @QuadraticMap.ofPolar ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin 1))
    _ _ _ _ _ (fun y => iteratedFDeriv ℝ 2 f x₀ ![y,y])
    (by
        intro a x
        simp
        have hsm := (iteratedFDeriv ℝ 2 f x₀).map_update_smul'
        have had := (iteratedFDeriv ℝ 2 f x₀).map_update_add'
        have := hsm 0
        sorry)
    (by
        intro x x' y
        simp [QuadraticMap.polar]
        sorry)
    (by
        intro a x y
        simp [QuadraticMap.polar]
        sorry)
