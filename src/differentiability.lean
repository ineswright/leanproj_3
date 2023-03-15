/-
Copyright (c) 2020 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton

Modified by Ines Wright from continuity to differentiability
-/
import tactic.auto_cases
import tactic.tidy
import tactic.with_local_reducibility
import tactic.show_term
import analysis.calculus.fderiv
/-!
# Tactics for topology



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

-- Mark some continuity lemmas already defined in `topology.basic`
attribute [differentiability]
  differentiable.comp
  differentiable_id
  differentiable_id'
  differentiable_const
  differentiable.mul
  -- Need some division something. ?
  differentiable.smul
  differentiable.pow -- for natural powers
  differentiable.add
  differentiable.neg
  differentiable.prod
  differentiable.fst
  differentiable.snd
  -- differentiable.sum
  -- differentiable_pi


namespace tactic
/--
Tactic to apply `differentiable.comp` when appropriate.

Applying `differentiable.comp` is not always a good idea, so we have some
extra logic here to try to avoid bad cases.

* If the function we're trying to prove continuous is actually
  constant, and that constant is a function application `f z`, then
  continuous.comp would produce new goals `differentiable f`, `continuous
  (λ _, z)`, which is silly. We avoid this by failing if we could
  apply continuous_const.

* continuous.comp will always succeed on `differentiable (λ x, f x)` and
  produce new goals `differentiable (λ x, x)`, `differentiable f`. We detect
  this by failing if a new goal can be closed by applying
  continuous_id.
-/
meta def apply_differentiable.comp : tactic unit :=
`[fail_if_success { exact differentiable_const };
  refine differentiable.comp _ _;
  fail_if_success { exact differentiable_id }]

/-- List of tactics used by `continuity` internally. -/
meta def differentiability_tactics (md : transparency := reducible) : list (tactic string) :=
[
  intros1               >>= λ ns, pure ("intros " ++ (" ".intercalate (ns.map (λ e, e.to_string)))),
  apply_rules [] [``differentiable] 50 { md := md }
                        >> pure "apply_rules with differentiability",
  apply_differentiable.comp >> pure "refine differentiable.comp _ _"
]

namespace interactive
setup_tactic_parser

/--
Solve goals of the form `continuous f`. `continuity?` reports back the proof term it found.
-/
meta def differentiability
  (bang : parse $ optional (tk "!")) (trace : parse $ optional (tk "?")) (cfg : tidy.cfg := {}) :
  tactic unit :=
let md              := if bang.is_some then semireducible else reducible,
    differentiable_core := tactic.tidy { tactics := differentiability_tactics md, ..cfg },
    trace_fn        := if trace.is_some then show_term else id in
trace_fn differentiable_core

/-- Version of `differentiable` for use with auto_param. -/
meta def differentiable' : tactic unit := differentiability none none {}

/--
`differentiable` solves goals of the form `differentiable f` by applying lemmas tagged with the
`differentiable` user attribute.

```
example {X Y : Type*} [topological_space X] [topological_space Y]
  (f₁ f₂ : X → Y) (hf₁ : continuous f₁) (hf₂ : continuous f₂)
  (g : Y → ℝ) (hg : continuous g) : continuous (λ x, (max (g (f₁ x)) (g (f₂ x))) + 1) :=
by continuity
```
will discharge the goal, generating a proof term like
`((continuous.comp hg hf₁).max (continuous.comp hg hf₂)).add continuous_const`

You can also use `continuity!`, which applies lemmas with `{ md := semireducible }`.
The default behaviour is more conservative, and only unfolds `reducible` definitions
when attempting to match lemmas with the goal.

`continuity?` reports back the proof term it found.
-/
add_tactic_doc
{ name := "differentiability / differentiability'",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.differentiability, `tactic.interactive.differentiability'],
  tags := ["lemma application"] }

end interactive

end tactic
