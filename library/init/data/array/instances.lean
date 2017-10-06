/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.array.lemmas
import init.data.list

namespace array
universes u w
variables {α : Type u} {β : Type w} {n : nat}

instance [has_repr α] : has_repr (array α n) :=
⟨repr ∘ to_list⟩

meta instance [has_to_format α] : has_to_format (array α n) :=
⟨to_fmt ∘ to_list⟩

meta instance [has_to_tactic_format α] : has_to_tactic_format (array α n) :=
⟨tactic.pp ∘ to_list⟩

end array
