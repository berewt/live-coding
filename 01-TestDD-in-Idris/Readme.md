# TestDD in Idris, the bowling kata


## The Bowling Kata

Inspiration came from [the Bowling Kata] by Uncle Bob.

### Bowling Scoring

The game consists of 10 frames.
In each frame the player has two opportunities to knock down 10 pins.
The score for the frame is the total number of pins knocked down,
plus bonuses for strikes and spares.

A spare is when the player knocks down all 10 pins in two tries.
The bonus for that frame is the number of pins knocked down by the next roll.

A strike is when the player knocks down all 10 pins on his first try.
The bonus for that frame is the value of the next two balls rolled.

In the tenth frame a player who rolls a spare or strike is allowed to roll the extra
balls to complete the frame.
However no more than three balls can be rolled in tenth frame.


### Objectives

Write a class named `Game` that has two methods:

- `roll(pins : int)` is called each time the player rolls a ball.
  The argument is the number of pins knocked down.
- `score() : int` is called only at the very end of the game.
  It returns the total score for that game.

## TDD Rules

### Development cycles

1. Write a test
2. Watch it fails
3. Code corresponding logic
4. Make it pass
5. Refactor
6. Make it pass again

### Refactor rules

1. No duplication
2. No magic value
3. Use meaningful names for domain elements
4. Avoid booleans
5. Prefer meaningful types to meaningful variables

# Configuration

- MacOs
- NeoVim (with Idris plugin)
- Idris 0.12

[the Bowling Kata]: http://butunclebob.com/ArticleS.UncleBob.TheBowlingGameKata
