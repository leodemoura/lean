/-
Copyright (c) 2017 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
prelude
import init.meta.tactic
import init.meta.interactive

/-
This module has been temporarily disabled.
Reason: we are refactoring the tactic framework using two states: a nonbacktrackable one and one that is backtrackable.
The nonbacktrackable state is hidden inside a new opaque monad: tactic_core.
We considered two ways of supporting run_async.

1- We provide the APIs
```
mk_child_state : tactic_core child_state
run_child : tactic_core α → child_state → α
```
The `mk_child_state` primitive would create a copy of a subset of the nonbacktrackable state.
For example, it would contain a new child name generator.
Then `run_child` would execute the given tactic using the new child name generator and a fresh cache object.
The main disadvantage of this approach is that we cannot easily add more state to the nonbacktrackable state object.

2- Implement `run_async` in C++. We would not need to add the primitives `mk_child_state` and `run_child`,
but we could still have problems when adding more state to the nonbacktrackable state object.

The `async` tactic is not being used. So, we just disable it for now.
-/

#exit

namespace tactic

private meta def report {α} (s : tactic_state) : option (unit → format) → α
| (some fmt) := undefined_core $ format.to_string $ fmt () ++ format.line ++ to_fmt s
| none       := undefined_core "silent failure"


private meta def run_or_fail {α} (s : tactic_state) (tac : tactic α) : α :=
match tac s with
| (result.success a s) := a
| (result.exception fmt _ s') := report s' fmt
end

meta def run_async {α : Type} (tac : tactic α) : tactic (task α) := do
s ← read, return $ task.delay $ λ _,
  match tac s with
  | (result.success a s) := a
  | (result.exception fmt _ s') := report s' fmt
  end

meta def prove_goal_async (tac : tactic unit) : tactic unit := do
ctx ← local_context, revert_lst ctx,
tgt ← target, tgt ← instantiate_mvars tgt,
env ← get_env, tgt ← return $ env.unfold_untrusted_macros tgt,
when tgt.has_meta_var (fail "goal contains metavariables"),
params ← return tgt.collect_univ_params,
lemma_name ← new_aux_decl_name,
proof ← run_async (do
  goal_meta ← mk_meta_var tgt,
  set_goals [goal_meta],
  ctx.mmap' (λc, intro c.local_pp_name),
  tac,
  proof ← instantiate_mvars goal_meta,
  proof ← return $ env.unfold_untrusted_macros proof,
  when proof.has_meta_var $ fail "async proof failed: contains metavariables",
  return proof),
add_decl $ declaration.thm lemma_name params tgt proof,
exact (expr.const lemma_name (params.map level.param))

namespace interactive
open interactive.types

/-- Proves the first goal asynchronously as a separate lemma. -/
meta def async (tac : itactic) : tactic unit :=
prove_goal_async tac

end interactive
end tactic
