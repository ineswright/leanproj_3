import analysis.special_functions.trigonometric.deriv
import analysis.calculus.fderiv
import cont_differentiability

open real

noncomputable def φ₁ : ℝ → ℝ × ℝ × ℝ := 
λ x, (real.sin x, x^4+37*x^2+1, abs x)

example : cont_diff_on ℝ ⊤ φ₁ (set.Icc 0 1) :=
begin
  apply cont_diff_on.prod,
  { apply cont_diff.cont_diff_on,
    exact cont_diff_sin, },
  { apply cont_diff_on.prod,
    { apply cont_diff.cont_diff_on,
      apply cont_diff.add,
      { apply cont_diff.add,
        { apply cont_diff.pow,
          exact cont_diff_id, },
        { apply cont_diff.mul,
          { exact cont_diff_const, },
          { apply cont_diff.pow, 
            exact cont_diff_id, }, }, },
      { exact cont_diff_const, }, }, 
    { apply cont_diff_on.congr,
      { exact cont_diff_on_id, },
      { intros x hx, exact abs_of_nonneg hx.1, }, }, },
end

example : cont_diff_on ℝ ⊤ φ₁ (set.Icc 0 1) :=
begin
  -- tactic can't figure out to apply this first ? Perhaps because
  -- it's a product of many ?
  apply cont_diff_on.prod,
  cont_differentiability, 
  -- adding cont_diff_on.congr to the tactic makes the first goal fail,
  -- because it transforms into ⊢ sin x = id x,
  -- although it successfully works on the second
    { exact cont_diff.cont_diff_on cont_diff_sin, },
    { apply cont_diff_on.congr cont_diff_on_id,
      intros x hx, exact abs_of_nonneg hx.1, },  
end