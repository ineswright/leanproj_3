
import analysis.special_functions.trigonometric.deriv
import analysis.calculus.fderiv
import cont_differentiability
import differentiability

open real

noncomputable def φ₁ : ℝ → ℝ × ℝ × ℝ := 
λ x, (real.sin x, x^4+37*x^2+1, abs x)

-- When I didn't have a version of cont_diff_on_id', couldn't unwrap definitions to solve
-- cont_diff_on ℝ n (λ x, x) as it didn't realise this was id, so needed this
-- example : cont_diff_on ℝ ⊤ φ₁ (set.Icc 0 1) :=
-- begin
--   apply cont_diff_on.prod,
--   cont_differentiability, 
--     { exact cont_diff.cont_diff_on cont_diff_sin, },
--     { exact cont_diff_on_id, },
--     { exact cont_diff_on_id, },
--     { apply cont_diff_on.congr cont_diff_on_id,
--       intros x hx, exact abs_of_nonneg hx.1, },  
-- end

example (f g h : ℝ → ℝ) (hf : differentiable ℝ f) (hg : differentiable ℝ g) 
  (hh : differentiable ℝ h) : differentiable ℝ (λ x, - (h x) + ((f ∘ g) x) ^ 3) 
  := 
begin
  differentiability,
  -- issue with having written the algorithm this way
  -- Goal: differentiable ℝ (λ (x : ℝ), (f ∘ g) x)
  -- decomposes into
  apply differentiable.comp,
  -- Goals: differentiable ℝ (f ∘ g) and differentiable ℝ (λ (x : ℝ), x)
  -- which fails given the algorithm
  -- should I raise this with Zulip ?
  exact differentiable.comp hf hg,
  exact differentiable_id,
end

example : cont_diff_on ℝ ⊤ φ₁ (set.Icc 0 1) :=
begin
  -- tactic can't figure out how to apply cont_diff_on.prod itself the first time
  -- but can do it fine on its own the second
  apply cont_diff_on.prod,
  cont_differentiability, 
  -- adding cont_diff_on.congr to the tactic makes the first goal fail,
  -- because it transforms into ⊢ sin x = id x,
  -- although it successfully works on the second
    { exact cont_diff.cont_diff_on cont_diff_sin, },
    { apply cont_diff_on.congr cont_diff_on_id,
      intros x hx, exact abs_of_nonneg hx.1, },  
end