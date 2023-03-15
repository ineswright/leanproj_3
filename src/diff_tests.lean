import analysis.special_functions.trigonometric.basic
import differentiability

example (f g h : ℝ → ℝ) (hf : differentiable ℝ f) (hg : differentiable ℝ g) 
  : differentiable ℝ (f ∘ g) := by differentiability

example (f g h : ℝ → ℝ) (hf : differentiable ℝ f) (hg : differentiable ℝ g) 
  : differentiable ℝ (λ x, f (g x)) := by differentiability

example (f g h : ℝ → ℝ) (hf : differentiable ℝ f) (hg : differentiable ℝ g) 
  : differentiable ℝ (λ x, f x + g x) := by differentiability
  
example (f g h : ℝ → ℝ) (hf : differentiable ℝ f) (hg : differentiable ℝ g) 
  : differentiable ℝ (λ x, f x + 3) := by differentiability

example (f g h : ℝ → ℝ) (hf : differentiable ℝ f) (hg : differentiable ℝ g) 
  : differentiable ℝ (λ x, 32 * (f x) ) := by differentiability

example (f g h : ℝ → ℝ) (hf : differentiable ℝ f) (hg : differentiable ℝ g) 
  : differentiable ℝ (λ x, (f x) * (g x) ) := by differentiability

example (f g h : ℝ → ℝ) (hf : differentiable ℝ f) (hg : differentiable ℝ g) 
  (hh : differentiable ℝ h) : differentiable ℝ (λ x, - (h x) + ((f ∘ g) x) ^ 3) 
  := by differentiability

-- HELP : (deterministic) timeout
-- example (f : ℝ → ℝ) (hf : differentiable ℝ f) : differentiable ℝ (λ x, real.sin (f x)) := 
-- begin
--   differentiability,
-- end

