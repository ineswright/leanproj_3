import tactic
import analysis.calculus.fderiv
import analysis.calculus.cont_diff
import analysis.inner_product_space.pi_L2
import cont_differentiability
import differentiability

-- HELP: f is a parametrised curve so usually defined with
-- f : [a, b] → ℝⁿ
example (n : ℕ) : euclidean_space ℝ (fin n) = (fin n → ℝ) := rfl

structure regular_curve (n : ℕ) (f : ℝ → euclidean_space ℝ (fin n)) (a b : ℝ) :=
( cont_diff := cont_diff_on ℝ ⊤ f (set.Icc a b) )
( nonneg_deriv := ∀ t : ℝ, t ∈ set.Icc a b → norm (fderiv ℝ f t) ≠ 0 )

-- Otherwise it considers it a Type! Then you can't write ¬ regular_curve2 ...
structure regular_curve2 (f : ℝ → ℝ × ℝ) (a b : ℝ) : Prop :=
( cont_diff : cont_diff_on ℝ ⊤ f (set.Icc a b) )
( nonneg_deriv : ∀ t : ℝ, t ∈ set.Icc a b → norm (fderiv ℝ f t) ≠ 0 ) 

structure regular_curve3 (f : ℝ → ℝ × ℝ × ℝ) (a b : ℝ) :=
( cont_diff : cont_diff_on ℝ ⊤ f (set.Icc a b) )
( nonneg_deriv : ∀ t : ℝ, t ∈ set.Icc a b → norm (fderiv ℝ f t) ≠ 0 ) 

-- TODO: coercion from regular_curve2 to regular_curve3
-- TODO: if a proposition is true for regular_curve, then it's true for regular_curve2 and 3.

-- The below line segment, circle and helix are all regular curves on 
-- [0, 1], [0, 2π] and [0, 6π] respectively.
-- The reducible just means I don't have to unfold it myself before applying my tactics
@[reducible] def φ₁ : ℝ → ℝ × ℝ := λ t, (2 * t - 1, 3 * t + 2)

@[reducible] noncomputable def φ₂ (r : ℝ) : ℝ → ℝ × ℝ := λ θ, (r * real.cos θ, r * real.sin θ)

@[reducible] noncomputable def φ₃ : ℝ → ℝ × ℝ × ℝ := λ θ, (real.cos θ, real.sin θ, θ)  

-- I've used this several times in the proofs below. Thanks Ÿael for the concise version
lemma id_ne_zero : continuous_linear_map.id ℝ ℝ ≠ 0 :=
  λ h, one_ne_zero (fun_like.congr_fun h 1)

example : regular_curve2 φ₁ 0 1 :=
begin
  refine ⟨_, _⟩,
  { cont_differentiability, },
  { intros t ht,
    have hd1 : differentiable ℝ (λ x : ℝ, 2 * x - 1), { differentiability, },
    have hd2 : differentiable ℝ (λ x : ℝ, 3 * x + 2), { differentiability, },
    specialize hd1 t, specialize hd2 t,
    -- simp only [ne.def, norm_eq_zero],
    rw [differentiable_at.fderiv_prod hd1 hd2],
    rw [fderiv_sub (differentiable_at.const_mul (differentiable_at_id') (2 : ℝ)) (differentiable_at_const (1 : ℝ))],
    rw [fderiv_add ((differentiable_at.const_mul (differentiable_at_id') (3 : ℝ))) (differentiable_at_const (2 : ℝ))],
    rw [fderiv_const_mul differentiable_at_id', fderiv_const_mul differentiable_at_id'],
    rw [fderiv_const, fderiv_const],
    rw [fderiv_id'],
    simp only [pi.zero_apply, sub_zero, add_zero, continuous_linear_map.op_norm_prod, ne.def, norm_eq_zero, 
      prod.mk_eq_zero, smul_eq_zero, bit0_eq_zero, one_ne_zero, false_or, not_and],
    intro h,
    push_neg,
    exact ⟨three_ne_zero, id_ne_zero⟩,
    },  
end

example : regular_curve2 (φ₂ 1) 0 (2*real.pi) :=
begin
  refine ⟨_, _⟩,
  { cont_differentiability,
    { exact cont_diff.cont_diff_on real.cont_diff_cos, },
    { exact cont_diff.cont_diff_on real.cont_diff_sin, },   
  },
  { intros t ht,
    have hd1 : differentiable ℝ (λ θ : ℝ, 1 * real.cos θ), { differentiability, },
    have hd2 : differentiable ℝ (λ θ : ℝ, 1 * real.sin θ), { differentiability, },
    specialize hd1 t, specialize hd2 t,
    rw [differentiable_at.fderiv_prod hd1 hd2],
    rw [fderiv_const_mul (differentiable.cos (differentiable_id') t)],
    rw [fderiv_const_mul (differentiable.sin (differentiable_id') t)],
    rw [one_smul, one_smul],
    rw [fderiv_cos (differentiable_id' t)],
    rw [fderiv_sin (differentiable_id' t)],
    simp only [fderiv_id', continuous_linear_map.op_norm_prod, ne.def, norm_eq_zero, prod.mk_eq_zero, neg_eq_zero, smul_eq_zero,
      not_and],
    rintro (h1 | h2),
    { 
      rintro (h2 | h3),
      { 
        rw real.sin_eq_zero_iff_cos_eq at h1,
        rw h2 at h1,
        apply or.elim h1 zero_ne_one,
        -- ⊢ (0 : ℝ) = -1 → false
        sorry,
      },
      { exact id_ne_zero h3, },
    }, 
    { exact false.elim (id_ne_zero h2), },
  },  
end

example : regular_curve3 φ₃ 0 (6*real.pi) :=
begin
  refine ⟨_, _⟩,
  { cont_differentiability,
    { exact cont_diff.cont_diff_on real.cont_diff_cos, },
    { exact cont_diff.cont_diff_on real.cont_diff_sin, },   
  },
  { intros t ht,
    have : differentiable ℝ (λ x, (real.sin x, x)), { differentiability, },
    rw [differentiable_at.fderiv_prod (differentiable.cos differentiable_id' t) (this t)],
    simp only [fderiv_cos, differentiable_at_id', fderiv_id', continuous_linear_map.op_norm_prod, ne.def, norm_eq_zero,
      prod.mk_eq_zero, neg_eq_zero, smul_eq_zero, not_and],
    rintro (h1 | h2),
    { intro h,
      rw [differentiable_at.fderiv_prod (differentiable.sin differentiable_id' t) (differentiable_id' t)] at h,
      rw [fderiv_sin (differentiable_id' t)] at h,
      rw [fderiv_id'] at h,
      rw fun_like.ext_iff at h,
      specialize h real.pi,
      simp only [continuous_linear_map.prod_apply, continuous_linear_map.coe_smul', continuous_linear_map.coe_id', pi.smul_apply,
        id.def, algebra.id.smul_eq_mul, continuous_linear_map.zero_apply, prod.mk_eq_zero, mul_eq_zero] at h,
      exact real.pi_ne_zero h.2, },
    { exact false.elim (id_ne_zero h2), },
  },  
end

-- And some curves which are not regular
@[reducible] def φ₄ : ℝ → ℝ × ℝ := λ x, (x, |x|)

@[reducible] def φ₅ : ℝ → ℝ × ℝ := λ x, (0, x^2)

-- I can't write ¬ (regular_curve2) for some reason
example : (regular_curve2 φ₄ (-8) 8) → false := 
begin
  rintro ⟨h1, h2⟩, 
  sorry,
end