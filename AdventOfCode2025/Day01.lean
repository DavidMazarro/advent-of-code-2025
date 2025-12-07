import AdventOfCode2025.Utils

namespace AdventOfCode2025.Day01

open AdventOfCode2025.Utils

---------- Exercise 1 ----------

inductive DialRotation : Type
  | left : Nat -> DialRotation
  | right : Nat -> DialRotation
deriving Repr

def initialDialValue : Fin 100 := 50

def parseNat (str : String) : Except String Nat :=
  match str.toNat? with
    | some n => .ok n
    | none => .error s!"Tried to parse '{str}' as a Nat but it's not a valid natural number."

def parseDialRotation (str : String) : Except String DialRotation :=
  match str.take 1 with
    | "L" => DialRotation.left <$> parseNat (str.drop 1)
    | "R" => DialRotation.right <$> parseNat (str.drop 1)
    | _ => .error s!"Tried to parse {str} as a dial rotation, but it's not encoded in the right format."

def parseDialRotations (strDialRotations : List String) : Except String (List DialRotation) :=
  sequence ∘ List.map parseDialRotation <| strDialRotations

def rotateDial (dial : Fin 100) (dialRotation : DialRotation) : Fin 100 :=
  match dialRotation with
    | .left rot => Fin.ofNat 100 ∘ Int.toNat <| (dial - Int.ofNat rot) % 100
    | .right rot => Fin.ofNat 100 ∘ Int.toNat <| (dial + Int.ofNat rot) % 100

def foldDialValues (dialRotations : List DialRotation) : Nat :=
  let dialPositions := foldlGatherResults rotateDial initialDialValue dialRotations
  let howManyDialTo0 := List.foldl (λ (acc dial) => if dial = 0 then acc + 1 else acc) 0 dialPositions
  howManyDialTo0

def solveExercise1 (inputFile : System.FilePath) : EIO String Nat := do
  let input ← IO.toEIO (s!"IO exception: {·}") (Array.toList <$> IO.FS.lines inputFile)
  let mSolution := foldDialValues <$> parseDialRotations input
  match mSolution with
    | .ok solution => return solution
    | .error error => throw s!"Program error: {error}"

#eval EIO.toIO IO.userError (solveExercise1 "AdventOfCode2025/inputs/day01.txt")

---------- Exercise 2 ----------

def rotateTimesItCrosses0 (dial : Fin 100) (dialRotation : DialRotation) : Nat :=
  match dialRotation with
    | .left rot =>
      let rotatedDial := dial - Int.ofNat rot
      -- If after a left rotation the dial is still a positive number,
      -- it means we didn't reach 0.
      if rotatedDial > 0 then 0
      else
        -- Int.tdiv rounds towards 0, so:
        -- 0 / 100 = 0
        -- -50 / 100 = 0
        -- -100 / 100 = 1
        -- So we need to increase the result by 1, *unless* our dial started at 0.
        (Int.tdiv rotatedDial 100).natAbs
        + (if dial = 0 then 0 else 1)
    -- Right rotations are easy, integer division by 100 suffices.
    | .right rot => ((dial + Int.ofNat rot) / 100).natAbs

def foldDialValuesCross0 (dialRotations : List DialRotation) : Nat :=
  let dialPositions := foldlGatherAndSideResults rotateDial rotateTimesItCrosses0 initialDialValue dialRotations
  let howManyDialCrosses0 := List.foldl (· + ·) 0 dialPositions.snd
  howManyDialCrosses0

def solveExercise2 (inputFile : System.FilePath) : EIO String Nat := do
  let input ← IO.toEIO (s!"IO exception: {·}") (Array.toList <$> IO.FS.lines inputFile)
  let mSolution := foldDialValuesCross0 <$> parseDialRotations input
  match mSolution with
    | .ok solution => return solution
    | .error error => throw s!"Program error: {error}"

#eval EIO.toIO IO.userError (solveExercise2 "AdventOfCode2025/inputs/day01.txt")
