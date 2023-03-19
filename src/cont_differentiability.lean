/-
This tactic is mostly a copy of the continuity tactic by Reid Barton,
with some modifications from the measurability tactic by Rémy Degenne
-/
import tactic.auto_cases
import tactic.tidy
import tactic.with_local_reducibility
import tactic.show_term
import analysis.calculus.cont_diff
import analysis.special_functions.trigonometric.deriv
/-!
# Tactics for continuous differentiability

### `cont_differentiability` tactic

Automatically solve goals of the form `cont_diff_on _ n f s`.

Mark lemmas with `@[cont_differentiability]` to add them to the set of lemmas
used by `cont_differentiability`.
-/

/-- User attribute used to mark tactics used by `cont_differentiability`.
-/
@[user_attribute]
meta def cont_differentiability : user_attribute :=
{ name := `cont_differentiability,
  descr := "lemmas usable to prove differentiable" }

-- Mark some differentiability lemmas already defined in `algebra.calculus.fderiv`
-- and `analysis.special_functions. ...`
attribute [cont_differentiability]
  cont_diff_on_id
  cont_diff_on_const
  cont_diff_on.prod
  cont_diff_on.add
  cont_diff_on.sub
  cont_diff_on.pow
  cont_diff_on.neg
  cont_diff_on.mul
  cont_diff_on.fst
  cont_diff_on.snd
  cont_diff_on.smul
  -- It can't even find this for some reason ?
  -- cont_diff_sin
  -- -- Need some division something. ?
  -- differentiable.prod
  -- differentiable.sum
  -- differentiable_pi
  -- differentiable.exp
  -- differentiable.cexp
  -- differentiable.log
  -- differentiable.sin
  -- differentiable.cos

@[cont_differentiability] lemma cont_diff_on_id' {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E] {s : set E} 
  {n : ℕ∞} : cont_diff_on 𝕜 n (λ (y : E), y) s :=
  cont_diff_id.cont_diff_on

  
namespace tactic
/--
Tactic to apply `cont_diff_on.comp` when appropriate.

Applying `cont_diff_on.comp` is not always a good idea, so we have some
extra logic here to try to avoid bad cases.

* If the function we're trying to prove continuous is actually
  constant, and that constant is a function application `f z`, then
  continuous.comp would produce new goals `cont_diff_on _ _ f _`, `continuous
  (λ _, z)`, which is silly. We avoid this by failing if we could
  apply continuous_const.

* continuous.comp will always succeed on `cont_diff_on _ _ (λ x, f x) _` and
  produce new goals `cont_diff_on _ _ (λ x, x) _`, `cont_diff_on _ _ f _`. We detect
  this by failing if a new goal can be closed by applying
  continuous_id.
-/
meta def apply_cont_diff_on.comp : tactic unit :=
`[fail_if_success { exact cont_diff_const };
  refine cont_diff_on.comp _ _;
  fail_if_success { exact cont_diff_id }]

-- https://github.com/leanprover-community/mathlib/blob/master/src/measure_theory/tactic.lean
-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/differentiability.20tactic
/--
We don't want the intros1 tactic to apply to a goal of the form `differentiable f`. 
This tactic tests the target to see if it matches that form.
 -/
meta def goal_is_not_cont_differentiable : tactic unit :=
do t ← tactic.target,
  match t with
  | `(cont_diff_on _ _ %%f _) := failed
  | _ := skip
  end

/-- List of tactics used by `cont_differentiability` internally. -/
meta def cont_differentiability_tactics (md : transparency := reducible) : list (tactic string) :=
[
  -- This first part is from the measurability tactic
  propositional_goal >> tactic.interactive.apply_assumption none {use_exfalso := ff}
                        >> pure "apply_assumption {use_exfalso := ff}",
  goal_is_not_cont_differentiable >> 
    intros1               >>= λ ns, pure ("intros " ++ (" ".intercalate (ns.map (λ e, e.to_string)))),
  apply_rules [] [``cont_differentiability] 50 { md := md }
                        >> pure "apply_rules with cont_differentiability",
  apply_cont_diff_on.comp >> pure "refine differentiable.comp _ _"
]

namespace interactive
setup_tactic_parser

/--
Solve goals of the form `cont_diff_on _ _ f _`. `cont_differentiability?` reports back the proof term it found.
-/
meta def cont_differentiability
  (bang : parse $ optional (tk "!")) (trace : parse $ optional (tk "?")) (cfg : tidy.cfg := {}) :
  tactic unit :=
let md              := if bang.is_some then semireducible else reducible,
    cont_differentiable_core := tactic.tidy { tactics := cont_differentiability_tactics md, ..cfg },
    trace_fn        := if trace.is_some then show_term else id in
trace_fn cont_differentiable_core

/-- Version of `cont_differentiability` for use with auto_param. -/
meta def cont_differentiability' : tactic unit := cont_differentiability none none {}

/--
`cont_differentiability` solves goals of the form `cont_diff_on _ _ f _` by applying lemmas tagged with the
`cont_differentiability` user attribute.

You can also use `cont_differentiability!`, which applies lemmas with `{ md := semireducible }`.
The default behaviour is more conservative, and only unfolds `reducible` definitions
when attempting to match lemmas with the goal.

`cont_differentiability?` reports back the proof term it found.
-/
add_tactic_doc
{ name := "cont_differentiability / cont_differentiability'",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.cont_differentiability, `tactic.interactive.cont_differentiability'],
  tags := ["lemma application"] }

end interactive
end tactic