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
  := 
begin
  differentiability,
  -- Goal: differentiable ℝ (λ (x : ℝ), (f ∘ g) x)
  -- Cannot be decomposed by the tactic as one of the sub functions is the identity
  -- therefore we have to proceed manually
  apply differentiable.comp,
  -- Goals: differentiable ℝ (f ∘ g) and differentiable ℝ (λ (x : ℝ), x)
  exact differentiable.comp hf hg,
  exact differentiable_id,
end

example (f g h : ℝ → ℝ) (hf : differentiable ℝ f) (hg : differentiable ℝ g) 
  (hh : differentiable ℝ h) : differentiable ℝ (λ x, - (h x) + (f (g x)) ^ 3) 
  := by differentiability

example (f g h : ℝ → ℝ) (hf : differentiable ℝ f) (hg : differentiable ℝ g) 
  : differentiable ℝ (λ x, (f x, g x) ) := by differentiability

example (f : ℝ → (ℝ × ℝ)) (hf : differentiable ℝ f) : differentiable ℝ (λ x, (f x).1 ) := 
  by differentiability

example (f : ℝ → ℝ) (hf : differentiable ℝ f) 
  : differentiable ℝ (λ x, real.sin (f x)) := by differentiability

example (f : ℝ → ℝ) (hf : differentiable ℝ f) 
  : differentiable ℝ (λ x, real.cosh (f x)) := by differentiability

example (f : ℝ → ℝ) (hf : differentiable ℝ f) 
  : differentiable ℝ (λ x, real.exp (f x)) := by differentiability

-- The tactic can even apply other necessary hypothesis
example (f : ℝ → ℝ) (hf : differentiable ℝ f) (hfn0 : ∀ x, f x ≠ 0)
  : differentiable ℝ (λ x, real.log (f x)) := by differentiability

example (f g : ℝ → ℝ) (hf : differentiable ℝ f) (hg : differentiable ℝ g) (h : ∀ x, g x ≠ 0)
  : differentiable ℝ (λ x, f x / (g x)) := by differentiability