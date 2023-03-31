/-
This tactic is mostly derived from the continuity tactic by Reid Barton,
with some modifications from the measurability tactic by Rémy Degenne
See writeup for details
-/
import tactic.auto_cases
import tactic.tidy
import tactic.with_local_reducibility
import tactic.show_term
import analysis.calculus.fderiv
import analysis.special_functions.exp_deriv
import analysis.special_functions.trigonometric.deriv
import analysis.special_functions.log.deriv
/-!
# Tactics for differentiability

### `differentiability` tactic

Automatically solve goals of the form `differentiable f`.

Mark lemmas with `@[differentiability]` to add them to the set of lemmas
used by `differentiability`.
-/

/-- User attribute used to mark tactics used by `differentiability`. -/

@[user_attribute]
meta def differentiability : user_attribute :=
{ name := `differentiability,
  descr := "lemmas usable to prove differentiable" }

-- Mark some differentiability lemmas already defined in `algebra.calculus.fderiv`
-- and `analysis.special_functions. ...`
attribute [differentiability]
  differentiable_id
  differentiable_id'
  differentiable_const
  differentiable.mul
  differentiable.div
  differentiable.smul
  differentiable.pow
  differentiable.add
  differentiable.sub
  differentiable.neg
  differentiable.prod
  differentiable.fst
  differentiable.snd
  differentiable.sum
  differentiable_pi
  differentiable.exp
  differentiable.cexp
  differentiable.log
  differentiable.sin
  differentiable.cos
  differentiable.sinh
  differentiable.cosh
  differentiable.csin
  differentiable.ccos
  differentiable.csinh
  differentiable.ccosh
  
namespace tactic
/--
Tactic to apply `differentiable.comp` when appropriate.

Applying `differentiable.comp` is not always a good idea, so we have some
extra logic here to try to avoid bad cases.

* If the function we're trying to prove differentiable is actually
  constant, and that constant is a function application `f z`, then
  differentiable.comp would produce new goals `differentiable f`, `differentiable
  (λ _, z)`, which is silly. We avoid this by failing if we could
  apply differentiable_const.

* differentiable.comp will always succeed on `differentiable (λ x, f x)` and
  produce new goals `differentiable (λ x, x)`, `differentiable f`. We detect
  this by failing if a new goal can be closed by applying
  differentiable_id.
-/
meta def apply_differentiable.comp : tactic unit :=
`[fail_if_success { exact differentiable_const };
  refine differentiable.comp _ _;
  fail_if_success { exact differentiable_id }]

-- https://github.com/leanprover-community/mathlib/blob/master/src/measure_theory/tactic.lean
-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/differentiability.20tactic
/--
We don't want the intros1 tactic to apply to a goal of the form `differentiable f`. 
This tactic tests the target to see if it matches that form.
 -/
meta def goal_is_not_differentiable : tactic unit :=
do t ← tactic.target,
  match t with
  | `(differentiable _ %%f) := failed
  | _ := skip
  end

/-- List of tactics used by `differentiability` internally. -/
meta def differentiability_tactics (md : transparency := reducible) : list (tactic string) :=
[
  -- This first part is from the measurability tactic
  propositional_goal >> tactic.interactive.apply_assumption none {use_exfalso := ff}
                        >> pure "apply_assumption {use_exfalso := ff}",
  goal_is_not_differentiable >> 
    intros1               >>= λ ns, pure ("intros " ++ (" ".intercalate (ns.map (λ e, e.to_string)))),
  apply_rules [] [``differentiability] 50 { md := md }
                        >> pure "apply_rules with differentiability",
  apply_differentiable.comp >> pure "refine differentiable.comp _ _"
]

namespace interactive
setup_tactic_parser

/--
Solve goals of the form `differentiability f`. `differentiability?` reports back the proof term it found.
-/
meta def differentiability
  (bang : parse $ optional (tk "!")) (trace : parse $ optional (tk "?")) (cfg : tidy.cfg := {}) :
  tactic unit :=
let md              := if bang.is_some then semireducible else reducible,
    differentiable_core := tactic.tidy { tactics := differentiability_tactics md, ..cfg },
    trace_fn        := if trace.is_some then show_term else id in
trace_fn differentiable_core

/-- Version of `differentiability` for use with auto_param. -/
meta def differentiability' : tactic unit := differentiability none none {}

/--
`differentiable` solves goals of the form `differentiable f` by applying lemmas tagged with the
`differentiable` user attribute.

You can also use `differentiability!`, which applies lemmas with `{ md := semireducible }`.
The default behaviour is more conservative, and only unfolds `reducible` definitions
when attempting to match lemmas with the goal.

`differentiability?` reports back the proof term it found.
-/
add_tactic_doc
{ name := "differentiability / differentiability'",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.differentiability, `tactic.interactive.differentiability'],
  tags := ["lemma application"] }

end interactive
end tactic