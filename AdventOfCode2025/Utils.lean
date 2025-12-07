namespace AdventOfCode2025.Utils

def sequence [Monad m] : List (m α) → m (List α) :=
  List.mapM id

private def foldlGatherResultsAccum (f : α → β → α) : (init : List α) → init ≠ [] → List β → List α
  | init, h, [] => init.reverse
  | init, h, x :: xs => foldlGatherResultsAccum f (f (init.head h) x :: init) (by simp) xs

-- This is the same as scanl, I just wanted to define this as an exercise
def foldlGatherResults (f : α → β → α) (init : α) : List β → List α :=
  foldlGatherResultsAccum f [init] (by simp)

-- TODO (in the future): Prove theorem - foldlGatherResults is equivalent to scanl.

-- TODO (in the future): Prove theorem - the result of calling foldl is equivalent to
-- calling foldlGatherResults and then doing .getLast on the result.

private def foldlGatherAndSideResultsAccum
  (f : α → β → α)
  (g : α → β → γ)
  : (acc : List α)
  → (side : List γ)
  → acc ≠ []
  → List β
  → List α × List γ
  | acc, side, h, [] => (acc.reverse, side.reverse)
  | acc, side, h, x :: xs =>
    foldlGatherAndSideResultsAccum f g (f (acc.head h) x :: acc) (g (acc.head h) x :: side) (by simp) xs

def foldlGatherAndSideResults
  (f : α → β → α)
  (g : α → β → γ)
  (init : α)
  : List β → List α × List γ :=
  foldlGatherAndSideResultsAccum f g [init] [] (by simp)
