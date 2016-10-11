open nat
-- set_option trace.type_context.eqn_lemmas true

def add2 : nat → nat → nat
| a 0            := a
| a (nat.succ b) := nat.succ (add2 a b)

instance inst2 : has_add nat :=
⟨add2⟩

definition fib : nat → nat
| 0     := 1
| 1     := 1
| (x+2) := fib x + fib (x+1)

theorem fib0 : fib 0 = 1 :=
rfl

theorem fib1 : fib 1 = 1 :=
rfl

theorem fib_succ_succ (a : nat) : fib (a+2) = fib a + fib (a+1) :=
rfl

example : fib 8 = 34 :=
rfl
