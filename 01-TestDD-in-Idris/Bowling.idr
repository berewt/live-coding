module Bowling

 %default total

data OngoingFrame = NoOngoing
                   | Incomplete Nat
                   | ExtraRoll1 Nat
                   | ExtraRoll2 Nat Nat

data Frame = Normal Nat Nat
           | Spare Nat Nat
           | Strike
           | LastStrike Nat Nat
           | LastSpare Nat Nat Nat

data Game : Type where
  MkGame : (ongoingFrame : OngoingFrame) -> (completed: List Frame) -> Game

newGame : Game
newGame = MkGame NoOngoing []

isLastFrame : (completed : List Frame) -> Dec (length completed = 9)
isLastFrame completed = decEq (length completed) 9

isSpare : (first : Nat) -> (second : Nat) -> Dec (first + second = 10)
isSpare first second = decEq (first + second) 10

isStrike : (first : Nat) -> Dec (first = 10)
isStrike first = decEq first 10

addFrame : (completed : List Frame) -> (newFrame : Frame) -> List Frame
addFrame completed newFrame = completed ++ [newFrame]

rolls : Game -> Nat -> Game
rolls (MkGame NoOngoing completed) first with (isStrike first)
  rolls (MkGame NoOngoing completed) first | (Yes prf) with (isLastFrame completed)
    rolls (MkGame NoOngoing completed) first | (Yes prf) | (Yes x) = MkGame (ExtraRoll1 10) completed
    rolls (MkGame NoOngoing completed) first | (Yes prf) | (No contra) = MkGame NoOngoing (addFrame completed Strike)
  rolls (MkGame NoOngoing completed) first | (No contra) = MkGame (Incomplete first) completed

rolls (MkGame (Incomplete first) completed) second with (isSpare first second)
  rolls (MkGame (Incomplete first) completed) second | (No contra) = MkGame NoOngoing (addFrame completed (Normal first second))
  rolls (MkGame (Incomplete first) completed) second | (Yes prf) with (isLastFrame completed)
    rolls (MkGame (Incomplete first) completed) second | (Yes prf) | (Yes x) = MkGame (ExtraRoll2 first second) completed
    rolls (MkGame (Incomplete first) completed) second | (Yes prf) | (No contra) = MkGame NoOngoing (addFrame completed (Spare first second))

rolls (MkGame (ExtraRoll1 first) completed) second = MkGame (ExtraRoll2 first second) completed
rolls (MkGame (ExtraRoll2 first second) completed) third with (isStrike first)
  rolls (MkGame (ExtraRoll2 first second) completed) third | (Yes prf) = MkGame NoOngoing (addFrame completed (LastStrike second third))
  rolls (MkGame (ExtraRoll2 first second) completed) third | (No contra) = MkGame NoOngoing (addFrame completed (LastSpare first second third))

listRolls : List Frame -> List Nat
listRolls [] = []
listRolls ((Normal k j) :: xs) = k::j::listRolls xs
listRolls ((Spare k j) :: xs) = k::j::listRolls xs
listRolls (Strike :: xs) = 10::listRolls xs
listRolls (LastStrike k j :: xs) = 10::k::j::listRolls xs
listRolls (LastSpare k j i :: xs) = k::j::i::listRolls xs

bonus : (numberOfRolls : Nat) -> (xs : List Frame) -> Nat
bonus n = sum . take n . listRolls

scoreFrames : (xs : List Frame) -> Nat
scoreFrames [] = 0
scoreFrames ((Normal k j) :: xs) = k + j + scoreFrames xs
scoreFrames ((Spare _ _) :: xs)  = 10 + bonus 1 xs + scoreFrames xs
scoreFrames (Strike :: xs)       = 10 + bonus 2 xs + scoreFrames xs
scoreFrames (LastStrike k j :: xs) = 10 + k + j + scoreFrames xs
scoreFrames (LastSpare _ _ j :: xs) = 10 + j + scoreFrames xs

score : Game -> Nat
score (MkGame _ xs) = scoreFrames xs

-- Test

replay : List Nat -> Game
replay = foldl rolls newGame

allInTheGuttersScoresZero : score (replay (replicate 20 0)) = 0
allInTheGuttersScoresZero = Refl

allOneDownsScores20 : score (replay (replicate 20 1)) = 20
allOneDownsScores20 = Refl

spareScoringIsOK : score (replay (5::5::3::replicate 17 0)) = 16
spareScoringIsOK = Refl

strikeScoringIsOK : score (replay (10::3::6::replicate 16 0)) = 28
strikeScoringIsOK = Refl

perfectScoreIs300 : score (replay (replicate 12 10)) = 300
perfectScoreIs300 = Refl

lastFrameSpareScoresIsOk : score (replay (replicate 18 0 ++ [5,5,3])) = 13
lastFrameSpareScoresIsOk = Refl
