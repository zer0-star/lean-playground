import LeanPlayground.AVLTree

structure KV (α β : Type) where
  key : α
  value : β

instance [Ord α] : Ord (KV α β) where
  compare a b := compare a.key b.key

def main : IO Unit := do
  let stdin ← IO.getStdin
  let xs := (← stdin.getLine).trim.splitOn.map String.toNat!
  let N := xs[0]!
  let Q := xs[1]!
  let line := (← stdin.getLine).trim
  let as := if N == 0 then [] else line.splitOn.map String.toNat!
  let mut t : AVLTree Nat := as.foldl (.insert) {}
  for _ in [:Q] do
    let line := (← stdin.getLine).trim
    let xs := line.splitOn.map String.toNat!
    match xs with
    | [0, x] => do
      t := t.insert x
    | [1, x] =>
      t := t.delete x
    | [2, x] =>
      match t.kth (x-1) with
      | some y => IO.println y
      | none => IO.println "-1"
    | [3, x] =>
      IO.println (t.indexOf (x+1))
    | [4, x] =>
      let n := t.indexOf (x+1)
      match n with
      | 0 => IO.println "-1"
      | m+1 => match t.kth m with
        | some y => IO.println y
        | none => IO.println "-1"
    | [5, x] =>
      match t.kth (t.indexOf x) with
      | some y => IO.println y
      | none => IO.println "-1"
    | _ => unreachable!

#eval ({ 0, 1, 2, 3, 5, 9 } : AVLTree Nat) |>.indexOf 1
