import lib

module Impl<inStr/0 input> {
  module H = Helpers<input/0>;

  int p1Start() {
    result = H::lines(0).regexpCapture("Player 1 starting position: (\\d+)", 1).toInt()
  }

  int p2Start() {
    result = H::lines(1).regexpCapture("Player 2 starting position: (\\d+)", 1).toInt()
  }

  bindingset[roll]
  int diceValue(int roll) { result = roll % 100 + 1 }

  boolean winningRound(int round) {
    round = -1 and result = false
    or
    result = p1Win(round).booleanOr(p2Win(round))
  }

  boolean p1Win(int round) {
    p1ScoreAfterRound(round) >= 1000 and result = true
    or
    p1ScoreAfterRound(round) < 1000 and result = false
  }

  boolean p2Win(int round) {
    p2ScoreAfterRound(round) >= 1000 and result = true
    or
    p2ScoreAfterRound(round) < 1000 and result = false
  }

  int diceRollsBeforeRound(int round) {
    round = 0 and result = 0
    or
    result = diceRollsBeforeRound(round - 1) + 6 and
    p1Win(round - 1) = false
    or
    result = diceRollsBeforeRound(round - 1) + 3 and
    p1Win(round - 1) = true
  }

  int p1PosAfterRound(int round) {
    round = -1 and result = p1Start()
    or
    winningRound(round - 1) = false and
    result =
      (
          (
              p1PosAfterRound(round - 1) + diceValue(diceRollsBeforeRound(round)) +
                diceValue(diceRollsBeforeRound(round) + 1) +
                diceValue(diceRollsBeforeRound(round) + 2) + 9
            ) % 10
        ) + 1
  }

  int p1ScoreAfterRound(int round) {
    round = -1 and result = 0
    or
    result = p1ScoreAfterRound(round - 1) + p1PosAfterRound(round)
  }

  int p2PosAfterRound(int round) {
    round = -1 and result = p2Start()
    or
    winningRound(round - 1) = false and
    result =
      (
          (
              p2PosAfterRound(round - 1) + diceValue(diceRollsBeforeRound(round) + 3) +
                diceValue(diceRollsBeforeRound(round) + 4) +
                diceValue(diceRollsBeforeRound(round) + 5) + 9
            ) % 10
        ) + 1
  }

  int p2ScoreAfterRound(int round) {
    round = -1 and result = 0
    or
    result = p2ScoreAfterRound(round - 1) + p2PosAfterRound(round) and p1Win(round) = false
    or
    result = p2ScoreAfterRound(round - 1) and p1Win(round) = true
  }

  int winningRound() { winningRound(result) = true }

  int totalRolls() { result = diceRollsBeforeRound(winningRound() + 1) }

  int losingScore() {
    result = p1ScoreAfterRound(winningRound()).minimum(p2ScoreAfterRound(winningRound()))
  }

  int p1Result() { result = totalRolls() * losingScore() }

  newtype TGameState =
    MkGameState(int p1Score, int p1Pos, int p2Score, int p2Pos, boolean p1Turn) {
      p1Score in [0 .. 30] and
      p2Score in [0 .. 30] and
      p1Pos in [1 .. 10] and
      p2Pos in [1 .. 10] and
      p1Turn in [true, false]
    }

  class GameState extends TGameState {
    string toString() {
      exists(int p1Score, int p1Pos, int p2Score, int p2Pos, boolean p1Turn |
        this = MkGameState(p1Score, p1Pos, p2Score, p2Pos, p1Turn) and
        result =
          "P1:" + p1Score + "@" + p1Pos + " P2:" + p2Score + "@" + p2Pos + " Turn:" +
            any(string s |
              p1Turn = true and s = "p1"
              or
              p1Turn = false and s = "p2"
            )
      )
    }
  }

  predicate isWinning(GameState state) {
    exists(int p1Score, int p1Pos, int p2Score, int p2Pos, boolean p1Turn |
      state = MkGameState(p1Score, p1Pos, p2Score, p2Pos, p1Turn) and
      (p1Score >= 21 or p2Score >= 21)
    )
  }

  predicate isWinningP1(GameState state) {
    exists(int p1Score, int p1Pos, int p2Score, int p2Pos, boolean p1Turn |
      state = MkGameState(p1Score, p1Pos, p2Score, p2Pos, p1Turn) and
      p1Score >= 21
    )
  }

  predicate isWinningP2(GameState state) {
    exists(int p1Score, int p1Pos, int p2Score, int p2Pos, boolean p1Turn |
      state = MkGameState(p1Score, p1Pos, p2Score, p2Pos, p1Turn) and
      p2Score >= 21
    )
  }

  int diceMove(int k) {
    k in [0 .. 26] and
    result = k % 3 + (k / 3) % 3 + (k / 9) % 3 + 3
  }

  GameState stateMove(GameState prev, int k) {
    not isWinning(prev) and
    exists(int p1Score, int p1Pos, int p2Score, int p2Pos, boolean p1Turn |
      prev = MkGameState(p1Score, p1Pos, p2Score, p2Pos, p1Turn)
    |
      p1Turn = true and
      exists(int newP1Pos, int newP1Score |
        newP1Pos = (p1Pos + diceMove(k) - 1) % 10 + 1 and
        newP1Score = p1Score + newP1Pos and
        result = MkGameState(newP1Score, newP1Pos, p2Score, p2Pos, false)
      )
      or
      p1Turn = false and
      exists(int newP2Pos, int newP2Score |
        newP2Pos = (p2Pos + diceMove(k) - 1) % 10 + 1 and
        newP2Score = p2Score + newP2Pos and
        result = MkGameState(p1Score, p1Pos, newP2Score, newP2Pos, true)
      )
    )
  }

  GameState hasStateMove(GameState prev) {
    result = stateMove(prev, _)
  }

  GameState startState() { result = MkGameState(0, p1Start(), 0, p2Start(), true) }

  GameState isReachable() { result = hasStateMove*(startState()) }

  GameState reachableStateMove(GameState prev, int k) { prev = isReachable() and result = stateMove(prev, k) }

  language[monotonicAggregates]
  float reachableCount(GameState state) {
    state = startState() and result = 1
    or
    state = isReachable() and
    state != startState() and
    result = sum(GameState pred, int k | reachableStateMove(pred, k) = state | reachableCount(pred))
  }

  float p1WinCount() { result = sum(GameState state | isWinningP1(state) | reachableCount(state)) }

  float p2WinCount() { result = sum(GameState state | isWinningP2(state) | reachableCount(state)) }

  float p2Result() { result = p1WinCount().maximum(p2WinCount()) }

}

string testInput() { result = "Player 1 starting position: 4\nPlayer 2 starting position: 8" }

string realInput() { result = "Player 1 starting position: 7\nPlayer 2 starting position: 8" }

module TestImpl = Impl<testInput/0>;

module RealImpl = Impl<realInput/0>;

select 1
