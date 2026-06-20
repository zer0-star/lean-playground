import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.FinCases
import Mathlib.Data.ZMod.Defs

example : ∀ n : Fin 9, n^9 - n^3 ≡ 0 [MOD 9] := by
  intro n
  fin_cases n
  all_goals
    simp
    decide

#check (inferInstance : Monoid (Fin 100))
#check (inferInstance : Pow (Fin 100) Nat)

#eval (3 : Fin 997) ^ 1000000000000
