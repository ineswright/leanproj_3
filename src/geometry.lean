import tactic
import analysis.calculus.fderiv
import analysis.calculus.cont_diff
import analysis.inner_product_space.pi_L2
import cont_differentiability
import differentiability
import unordered_interval

example (n : ℕ) : euclidean_space ℝ (fin n) = (fin n → ℝ) := rfl
example (n : ℕ) : (ℝ → euclidean_space ℝ (fin n)) = (ℝ → (fin n → ℝ)) := rfl

/-- A regular curve is a smooth map : [a, b] → ℝ^n such that the norm of it's
derivative is nonzero everywhere -/
structure regular_curve (n : ℕ) (f : ℝ → euclidean_space ℝ (fin n)) (a b : ℝ) :=
( cont_diff : cont_diff_on ℝ ⊤ f (set.uIcc a b) )
( nezero_deriv : ∀ t : ℝ, t ∈ set.uIcc a b → norm (fderiv ℝ f t) ≠ 0 )

/-- A regular curve in ℝ × ℝ follows the same requirements as on a euclidean space -/
structure regular_curve2 (f : ℝ → ℝ × ℝ) (a b : ℝ) : Prop :=
( cont_diff : cont_diff_on ℝ ⊤ f (set.uIcc a b) )
( nezero_deriv : ∀ t : ℝ, t ∈ set.uIcc a b → norm (fderiv ℝ f t) ≠ 0 ) 

/-- A regular curve in ℝ × ℝ × ℝ follows the same requirements as on a euclidean space -/
structure regular_curve3 (f : ℝ → ℝ × ℝ × ℝ) (a b : ℝ) : Prop :=
( cont_diff : cont_diff_on ℝ ⊤ f (set.uIcc a b) )
( nezero_deriv : ∀ t : ℝ, t ∈ set.uIcc a b → norm (fderiv ℝ f t) ≠ 0 ) 

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
    -- These rewrites 'calculate' what we expect fderiv to be
    rw [differentiable_at.fderiv_prod hd1 hd2, fderiv_sub (differentiable_at.const_mul 
      (differentiable_at_id') (2 : ℝ)) (differentiable_at_const (1 : ℝ)),
      fderiv_add ((differentiable_at.const_mul (differentiable_at_id') (3 : ℝ))) 
      (differentiable_at_const (2 : ℝ)), fderiv_const_mul differentiable_at_id', 
      fderiv_const_mul differentiable_at_id', fderiv_const, fderiv_const, fderiv_id'],
    simp only [pi.zero_apply, sub_zero, add_zero, continuous_linear_map.op_norm_prod, ne.def, 
      norm_eq_zero, prod.mk_eq_zero, smul_eq_zero, bit0_eq_zero, one_ne_zero, false_or, not_and],
    intro h,
    push_neg,
    exact ⟨three_ne_zero, id_ne_zero⟩, },  
end

example : regular_curve2 (φ₂ 1) 0 (2*real.pi) :=
begin
  refine ⟨_, _⟩,
  { cont_differentiability,
    { exact cont_diff.cont_diff_on real.cont_diff_cos, },
    { exact cont_diff.cont_diff_on real.cont_diff_sin, }, },
  { intros t ht,
    have hd1 : differentiable ℝ (λ θ : ℝ, 1 * real.cos θ), { differentiability, },
    have hd2 : differentiable ℝ (λ θ : ℝ, 1 * real.sin θ), { differentiability, },
    specialize hd1 t, specialize hd2 t,
    rw [differentiable_at.fderiv_prod hd1 hd2, fderiv_const_mul (differentiable.cos 
      (differentiable_id') t), fderiv_const_mul (differentiable.sin (differentiable_id') t), 
      one_smul, one_smul, fderiv_cos (differentiable_id' t), fderiv_sin (differentiable_id' t)],
    simp only [fderiv_id', continuous_linear_map.op_norm_prod, ne.def, norm_eq_zero, 
      prod.mk_eq_zero, neg_eq_zero, smul_eq_zero, not_and],
    rintro (h1 | h2),
    { -- Goal: ¬(real.cos t = 0 ∨ continuous_linear_map.id ℝ ℝ = 0)
      -- h1 : real.sin t = 0
      rintro (h2 | h3),
      { rw [real.sin_eq_zero_iff_cos_eq, h2] at h1,
        apply or.elim h1 zero_ne_one,
        -- Thanks Deepro, this tactic handles all the coercions I couldn't figure out!
        norm_num, },
      { exact id_ne_zero h3, },
    }, 
    { -- Goal: ¬(real.cos t = 0 ∨ continuous_linear_map.id ℝ ℝ = 0)
      -- h2 : continuous_linear_map.id ℝ ℝ = 0 
      exact false.elim (id_ne_zero h2), },
  },  
end

example : regular_curve3 φ₃ 0 (6*real.pi) :=
begin
  refine ⟨_, _⟩,
  { cont_differentiability,
    { exact cont_diff.cont_diff_on real.cont_diff_cos, },
    { exact cont_diff.cont_diff_on real.cont_diff_sin, }, },
  { intros t ht,
    have : differentiable ℝ (λ x, (real.sin x, x)), { differentiability, },
    rw [differentiable_at.fderiv_prod (differentiable.cos differentiable_id' t) (this t)],
    simp only [fderiv_cos, differentiable_at_id', fderiv_id', continuous_linear_map.op_norm_prod, 
      ne.def, norm_eq_zero, prod.mk_eq_zero, neg_eq_zero, smul_eq_zero, not_and],
    rintro (h1 | h2),
    { -- Goal: ¬fderiv ℝ (λ (x : ℝ), (real.sin x, x)) t = 0
      -- h1 : real.sin t = 0
      intro h,
      rw [differentiable_at.fderiv_prod (differentiable.sin differentiable_id' t) 
        (differentiable_id' t)] at h,
      rw [fderiv_sin (differentiable_id' t)] at h,
      rw [fderiv_id'] at h,
      rw fun_like.ext_iff at h,
      specialize h real.pi,
      simp only [continuous_linear_map.prod_apply, continuous_linear_map.coe_smul', 
        continuous_linear_map.coe_id', pi.smul_apply, id.def, algebra.id.smul_eq_mul, 
        continuous_linear_map.zero_apply, prod.mk_eq_zero, mul_eq_zero] at h,
      exact real.pi_ne_zero h.2, },
    { -- Goal: ¬fderiv ℝ (λ (x : ℝ), (real.sin x, x)) t = 0
      -- h2 : continuous_linear_map.id ℝ ℝ = 0
      exact false.elim (id_ne_zero h2), },
  },  
end

-- And some curves which are not regular
@[reducible] def φ₄ : ℝ → ℝ × ℝ := λ x, (x, |x|)

@[reducible] def φ₅ : ℝ → ℝ × ℝ := λ x, (0, x^2)

lemma abs_not_differentiable_at_zero : ¬ differentiable_at ℝ (λ x : ℝ, |x|) 0 :=
begin
  sorry,
  -- Goal: prove false from a proof that abs is differentiable at 0
  -- There's zero machinery in mathlib that I can find to say that the absolute 
  -- value function ℝ → ℝ is differentiable on (-∞, 0) or (0, ∞) or what it's derivative is 
  -- or that it's not differentiable at 0.
  -- I suspect the easiest way to do this without dealing with limits and filters
  -- Would be some kind of congruence (deriv_within_congr) along the lines of
  -- abs(x) = id(x) on [0, ∞) → deriv abs(x) = 1 on [0, ∞)
  -- abs(x) = -x) on [0, ∞) → deriv abs(x) = -1 on (-∞, 0]
  -- deriv = 1 and -1 at 0 therefore contradiction
  -- false.elim 1 ≠ -1 
end

example : ¬ (regular_curve2 φ₄ (-8) 8) := 
begin
  rintro ⟨h, -⟩,
  -- h : cont_diff_on ℝ ⊤ φ₄ (set.uIcc (-8) 8)
  -- from which can be deduced that the absolute value function is differentiable
  -- within set.uIoo (-8) 8. This contracts lemma abs_not_differentiable_at_zero
  apply abs_not_differentiable_at_zero (differentiable_within_at.differentiable_at 
    (cont_diff_on.differentiable_on h le_top 0 (by norm_num)).snd 
    (mem_nhds_iff_exists_Ioo_subset.mpr ⟨(-8 : ℝ), 8, _, _⟩)),
  { -- Goal: 0 ∈ set.Ioo (-8) 8
    split; linarith, },
  { -- Goal: set.Ioo (-8) 8 ⊆ set.uIcc (-8) 8
    exact λ x hx, set.uIoo_subset_uIcc _ _ (set.Ioo_subset_uIoo _ _ hx), },
end

-- With help from Kevin Buzzard
lemma squared (t : ℝ) (x : ℝ) : (fderiv ℝ (λ x, x ^ 2) t x) = 2 * t * x := 
begin
  rw [←mul_one x, ←smul_eq_mul, map_smul, fderiv_deriv],
  simp only [deriv_pow'', differentiable_at_id', nat.cast_bit0, algebra_map.coe_one, pow_one, 
    deriv_id'', mul_one, algebra.id.smul_eq_mul],
  ring,
end

example : (regular_curve2 φ₅ (-1) 1) → false :=
begin
  rintro ⟨-, h⟩, 
  specialize h 0 (by norm_num),
  simp only [ne.def, norm_eq_zero] at h,
  rw [differentiable_at.fderiv_prod (differentiable_const (0 : ℝ) (0 : ℝ)) 
    (differentiable.pow differentiable_id' 2 0), fun_like.ext_iff] at h,
  push_neg at h,
  obtain ⟨n, hn⟩ := h,
  simp only [fderiv_const, pi.zero_apply, continuous_linear_map.prod_apply, 
    continuous_linear_map.zero_apply, ne.def, prod.mk_eq_zero, eq_self_iff_true, true_and] at hn,
  apply hn,
  rw [squared, mul_zero, zero_mul],
end
