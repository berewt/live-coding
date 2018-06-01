module Bowling

 %default total

namespace cst

  pinsNumber : Nat
  pinsNumber = 10

  totalFrames : Nat
  totalFrames = 10

data FrameStatus = Incomplete Nat
                 | ExtraRoll1 Nat
                 | ExtraRoll2 Nat Nat

data Frame = Normal Nat Nat
           | Spare Nat
           | Strike
           | LastSpecial Nat Nat Nat

data Game : (toBeCompleted : Nat) -> Type where
  NewGame : Game 10
  CompletedFrame : (frame : Frame) -> (game : Game (S tbc)) -> Game tbc
  OngoingFrame : FrameStatus -> Game (S tbc) -> Game (S tbc)



isLastFrame : (completed : Nat) -> Dec (completed = 0)
isLastFrame completed = decEq completed 0

isSpare : (first : Nat) -> (second : Nat) -> Dec (first + second = cst.pinsNumber)
isSpare first second = decEq (first + second) pinsNumber

isStrike : (first : Nat) -> Dec (first = cst.pinsNumber)
isStrike first = decEq first pinsNumber

addFrame : (completed : List Frame) -> (newFrame : Frame) -> List Frame
addFrame completed newFrame = completed ++ [newFrame]

rolls : Game (S n) -> Nat -> Either (Game (S n)) (Game n)

rolls NewGame k with (isStrike k)
  | (Yes _) = Right (CompletedFrame Strike NewGame)
  | (No _) = Left (OngoingFrame (Incomplete k) NewGame)

rolls (CompletedFrame frame game) k {n} with (isStrike k)
  | (No _) = Left (OngoingFrame (Incomplete k) (CompletedFrame frame game))
  | (Yes _) with (isLastFrame n)
     | (Yes _) = Left (OngoingFrame (ExtraRoll1 k) (CompletedFrame frame game))
     | (No _) = Right (CompletedFrame Strike (CompletedFrame frame game))

rolls (OngoingFrame (Incomplete j) y) k {n} with (isSpare j k)
  | (Yes _) with (isLastFrame n)
    | (Yes _) = Left (OngoingFrame (ExtraRoll2 j k) (OngoingFrame (Incomplete j) y))
    | (No _) = Right (CompletedFrame (Spare j) (OngoingFrame (Incomplete j) y))
  | (No _) = Right (CompletedFrame (Normal j k) (OngoingFrame (Incomplete j) y))

rolls (OngoingFrame (ExtraRoll1 j) y) k = Left (OngoingFrame (ExtraRoll2 j k) (OngoingFrame (ExtraRoll1 j) y))

rolls (OngoingFrame (ExtraRoll2 j i) y) k = Right (CompletedFrame (LastSpecial j i k) (OngoingFrame (ExtraRoll2 j i) y))

listRolls : List Frame -> List Nat
listRolls [] = []
listRolls ((Normal k j) :: xs) = k::j::listRolls xs
listRolls ((Spare k) :: xs) = k :: minus 10 k :: listRolls xs
listRolls (Strike :: xs) = pinsNumber::listRolls xs
listRolls (LastSpecial k j i :: xs) = k::j::i::listRolls xs

bonus : (numberOfRolls : Nat) -> (xs : List Frame) -> Nat
bonus n = sum . take n . listRolls

scoreFrames : (xs : List Frame) -> Nat
scoreFrames [] = 0
scoreFrames ((Normal k j) :: xs) = k + j + scoreFrames xs
scoreFrames ((Spare _) :: xs)  = pinsNumber + bonus 1 xs + scoreFrames xs
scoreFrames (Strike :: xs)       = pinsNumber + bonus 2 xs + scoreFrames xs
scoreFrames (LastSpecial k j i :: xs) = k + j + i + scoreFrames xs

listFrames : Game n -> List Frame
listFrames NewGame = []
listFrames (CompletedFrame frame game) = listFrames game ++ [frame]
listFrames (OngoingFrame x game) = listFrames game

score : Game Z -> Nat
score = scoreFrames . listFrames

-- Test

replay : List Nat -> Maybe (n ** Game n)
replay = foldlM go (_ ** NewGame)
  where

    go : (n : Nat ** Game n) -> Nat -> Maybe (n' : Nat ** Game n')
    go (Z     ** game) k = Nothing
    go ((S n) ** game) k = either (\g => (Just (_ ** g))) (\g => (Just (_ ** g))) $ rolls game k

score' : Maybe (n ** Game n) -> Maybe Nat
score' Nothing = Nothing
score' (Just ((S _) ** _)) = Nothing
score' (Just (Z ** game)) = Just (score game)

--

allInTheGuttersScoresZero : score' (replay (replicate 20 0)) = Just 0
allInTheGuttersScoresZero = Refl

allOneDownsScores20 : score' (replay (replicate 20 1)) = Just 20
allOneDownsScores20 = Refl

spareScoringIsOK : score' (replay (5::5::3::replicate 17 0)) = Just 16
spareScoringIsOK = Refl

strikeScoringIsOK : score' (replay (10::3::6::replicate 16 0)) = Just 28
strikeScoringIsOK = Refl

perfectScoreIs300 : score' (replay (replicate 12 10)) = Just 300
perfectScoreIs300 = Refl

lastFrameSpareScoresIsOk : score' (replay (replicate 18 0 ++ [5,5,3])) = Just 13
lastFrameSpareScoresIsOk = Refl
