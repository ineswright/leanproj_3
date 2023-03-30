import analysis.special_functions.trigonometric.deriv
import analysis.calculus.fderiv
import cont_differentiability

open real

noncomputable def φ₁ : ℝ → ℝ × ℝ × ℝ := 
λ x, (real.sin x, x^4+37*x^2+1, abs x)

-- Manual proof found by Kevin Buzzard or Heather from Zulip - I don't remember
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
  -- Not sure why this first cont_diff_on.prod can't be done by the tactic
  apply cont_diff_on.prod,
  cont_differentiability,
    { exact cont_diff.cont_diff_on cont_diff_sin, },
    { apply cont_diff_on.congr cont_diff_on_id,
      intros x hx, exact abs_of_nonneg hx.1, },  
end