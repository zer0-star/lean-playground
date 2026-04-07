import Mathlib.Tactic.Common

inductive Term : Nat → Type
  | var : Fin n → Term n
  | app : Term n → Term n → Term n
  | lam : Term (n+1) → Term n
  | unit : Term n
