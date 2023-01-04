import lib

module TestImpl = Impl<testInput/0>;

module RealImpl = Impl<realInput/0>;

module MiniTestImpl = Impl<miniTestInput/0>;

module Impl<inStr/0 input> {
  int maxRounds() { result = 10000 }

  boolean initialElf(int x, int y) {
    exists(string type | type = Helpers<input/0>::lines(x).charAt(y) |
      type = "#" and result = true
      or
      type = "." and result = false
    )
  }

  int padding() { result = 100 }

  int minX() { result = min(int x | exists(int y | exists(initialElf(x, y)))) - padding() }

  int maxX() { result = max(int x | exists(int y | exists(initialElf(x, y)))) + padding() }

  int minY() { result = min(int y | exists(int x | exists(initialElf(x, y)))) - padding() }

  int maxY() { result = max(int y | exists(int x | exists(initialElf(x, y)))) + padding() }

  boolean initialWithPadding(int x, int y) {
    x in [minX() .. maxX()] and
    y in [minY() .. maxY()] and
    (
      result = initialElf(x, y)
      or
      not exists(initialElf(x, y)) and result = false
    )
  }

  pragma[assume_small_delta]
  cached
  boolean elfAt(int round, int x, int y) {
    round = 0 and result = initialWithPadding(x, y)
    or
    result = newElf(round - 1, x, y) and
    round <= maxRounds() and
    notDone(round - 1)
  }

  pragma[nomagic]
  boolean hasNeighbour(int round, int x, int y) {
    elfAt(round, x, y) = true and
    result =
      elfAt(round, x - 1, y - 1)
          .booleanOr(elfAt(round, x, y - 1))
          .booleanOr(elfAt(round, x + 1, y - 1))
          .booleanOr(elfAt(round, x - 1, y))
          .booleanOr(elfAt(round, x + 1, y))
          .booleanOr(elfAt(round, x - 1, y + 1))
          .booleanOr(elfAt(round, x, y + 1))
          .booleanOr(elfAt(round, x + 1, y + 1))
  }

  predicate roundDone(int i) {
    exists(elfAt(i, _, _)) and
    forall(int x, int y |
      x in [minX() .. maxX()] and
      y in [minY() .. maxY()]
    |
      elfAt(i, x, y) = false or
      hasNeighbour(i, x, y) = false
    )
  }

  predicate notDone(int i) {
    exists(int x, int y |
      x in [minX() .. maxX()] and
      y in [minY() .. maxY()]
    |
      elfAt(i, x, y) = true and
      hasNeighbour(i, x, y) = true
    )
  }

  int firstRoundDone() { result = min(int i | roundDone(i)) + 1 }

  boolean neighbourNorth(int round, int x, int y) {
    elfAt(round, x, y) = true and
    result =
      elfAt(round, x - 1, y - 1)
          .booleanOr(elfAt(round, x - 1, y))
          .booleanOr(elfAt(round, x - 1, y + 1))
  }

  boolean neighbourEast(int round, int x, int y) {
    elfAt(round, x, y) = true and
    result =
      elfAt(round, x - 1, y + 1)
          .booleanOr(elfAt(round, x, y + 1))
          .booleanOr(elfAt(round, x + 1, y + 1))
  }

  boolean neighbourSouth(int round, int x, int y) {
    elfAt(round, x, y) = true and
    result =
      elfAt(round, x + 1, y - 1)
          .booleanOr(elfAt(round, x + 1, y))
          .booleanOr(elfAt(round, x + 1, y + 1))
  }

  boolean neighbourWest(int round, int x, int y) {
    elfAt(round, x, y) = true and
    result =
      elfAt(round, x - 1, y - 1)
          .booleanOr(elfAt(round, x, y - 1))
          .booleanOr(elfAt(round, x + 1, y - 1))
  }

  boolean canMoveKind(int round, int kind, int prevX, int prevY, int nextX, int nextY) {
    kind = 0 and
    result = neighbourNorth(round, prevX, prevY).booleanNot() and
    nextX = prevX - 1 and
    nextY = prevY
    or
    kind = 1 and
    result = neighbourSouth(round, prevX, prevY).booleanNot() and
    nextX = prevX + 1 and
    nextY = prevY
    or
    kind = 2 and
    result = neighbourWest(round, prevX, prevY).booleanNot() and
    nextX = prevX and
    nextY = prevY - 1
    or
    kind = 3 and
    result = neighbourEast(round, prevX, prevY).booleanNot() and
    nextX = prevX and
    nextY = prevY + 1
  }

  int proposedMove(int round, int prevX, int prevY, int nextX, int nextY) {
    elfAt(round, prevX, prevY) = true and
    (
      hasNeighbour(round, prevX, prevY) = false and
      nextX = prevX and
      nextY = prevY and
      result = -1
      or
      hasNeighbour(round, prevX, prevY) = true and
      canMoveKind(round, round % 4, prevX, prevY, nextX, nextY) = true and
      result = round % 4
      or
      hasNeighbour(round, prevX, prevY) = true and
      canMoveKind(round, round % 4, prevX, prevY, _, _) = false and
      canMoveKind(round, (round + 1) % 4, prevX, prevY, nextX, nextY) = true and
      result = (round + 1) % 4
      or
      hasNeighbour(round, prevX, prevY) = true and
      canMoveKind(round, round % 4, prevX, prevY, _, _) = false and
      canMoveKind(round, (round + 1) % 4, prevX, prevY, _, _) = false and
      canMoveKind(round, (round + 2) % 4, prevX, prevY, nextX, nextY) = true and
      result = (round + 2) % 4
      or
      hasNeighbour(round, prevX, prevY) = true and
      canMoveKind(round, round % 4, prevX, prevY, _, _) = false and
      canMoveKind(round, (round + 1) % 4, prevX, prevY, _, _) = false and
      canMoveKind(round, (round + 2) % 4, prevX, prevY, _, _) = false and
      canMoveKind(round, (round + 3) % 4, prevX, prevY, nextX, nextY) = true and
      result = (round + 3) % 4
      or
      hasNeighbour(round, prevX, prevY) = true and
      canMoveKind(round, round % 4, prevX, prevY, _, _) = false and
      canMoveKind(round, (round + 1) % 4, prevX, prevY, _, _) = false and
      canMoveKind(round, (round + 2) % 4, prevX, prevY, _, _) = false and
      canMoveKind(round, (round + 3) % 4, prevX, prevY, _, _) = false and
      nextX = prevX and
      nextY = prevY and
      result = -1
    )
  }

  int broken(int round, int x, int y) {
    notDone(round) and
    x in [minX() .. maxX()] and
    y in [minY() .. maxY()] and
    count(elfAt(round, x, y)) = result and
    result != 1
  }

  pragma[assume_small_delta]
  boolean newElf(int round, int x, int y) {
    0 = countTargets(round, x, y) and
    elfAt(round, x, y) = false and
    result = false
    or
    1 = countTargets(round, x, y) and
    result = true
    or
    1 < countTargets(round, x, y) and
    result = false
    or
    exists(proposedMove(round, x, y, x, y)) and
    result = true
    or
    exists(int proposedX, int proposedY |
      0 = countTargets(round, x, y) and
      exists(proposedMove(round, x, y, proposedX, proposedY)) and
      countTargets(round, proposedX, proposedY) = 1 and
      (
        proposedX != x
        or
        proposedX = x and proposedY != y
      ) and
      result = false
    )
    or
    exists(int proposedX, int proposedY |
      0 = countTargets(round, x, y) and
      exists(proposedMove(round, x, y, proposedX, proposedY)) and
      countTargets(round, proposedX, proposedY) != 1 and
      result = true
    )
  }

  string debugPrint(int round) {
    result =
      strictconcat(int x |
        x in [minX() .. maxX()]
      |
        strictconcat(int y |
              y in [minY() .. maxY()]
            |
              any(string s, boolean b |
                  elfAt(round, x, y) = b and
                  if b = true then s = "#" else s = "."
                |
                  s
                )
              order by
                y
            ) + "\n"
        order by
          x
      )
  }

  int northTargetCount(int round, int x, int y) {
    (
      x + 1 > maxX() and exists(elfAt(round, x, y)) and result = 0
      or
      elfAt(round, x + 1, y) = false and result = 0
      or
      proposedMove(round, x + 1, y, _, _) != 0 and result = 0
      or
      proposedMove(round, x + 1, y, _, _) = 0 and result = 1
    )
  }

  int southTargetCount(int round, int x, int y) {
    (
      x - 1 < minX() and exists(elfAt(round, x, y)) and result = 0
      or
      elfAt(round, x - 1, y) = false and result = 0
      or
      proposedMove(round, x - 1, y, _, _) != 1 and result = 0
      or
      proposedMove(round, x - 1, y, _, _) = 1 and result = 1
    )
  }

  int westTargetCount(int round, int x, int y) {
    (
      y - 1 < minY() and exists(elfAt(round, x, y)) and result = 0
      or
      elfAt(round, x, y - 1) = false and result = 0
      or
      proposedMove(round, x, y - 1, _, _) != 3 and result = 0
      or
      proposedMove(round, x, y - 1, _, _) = 3 and result = 1
    )
  }

  int eastTargetCount(int round, int targetX, int targetY) {
    (
      targetY + 1 > maxY() and result = 0 and exists(elfAt(round, targetX, targetY))
      or
      elfAt(round, targetX, targetY + 1) = false and result = 0
      or
      proposedMove(round, targetX, targetY + 1, _, _) != 2 and result = 0
      or
      proposedMove(round, targetX, targetY + 1, _, _) = 2 and result = 1
    )
  }

  int stayCount(int round, int targetX, int targetY) {
    elfAt(round, targetX, targetY) = false and result = 0
    or
    proposedMove(round, targetX, targetY, _, _) = -1 and result = 1
    or
    proposedMove(round, targetX, targetY, _, _) != -1 and result = 0
  }

  int countTargets(int round, int x, int y) {
    result =
      northTargetCount(round, x, y) + southTargetCount(round, x, y) + westTargetCount(round, x, y) +
        eastTargetCount(round, x, y) + stayCount(round, x, y)
  }

  int minElfX() { result = min(int x | true = elfAt(maxRounds(), x, _)) }

  int maxElfX() { result = max(int x | true = elfAt(maxRounds(), x, _)) }

  int minElfY() { result = min(int y | true = elfAt(maxRounds(), _, y)) }

  int maxElfY() { result = max(int y | true = elfAt(maxRounds(), _, y)) }
}

select 1

string miniTestInput() { result = ".....\n..##.\n..#..\n.....\n..##.\n....." }

string testInput() { result = "....#..\n..###.#\n#...#.#\n.#...##\n#.###..\n##.#.##\n.#..#.." }

string realInput() {
  result =
    "#.#####..#..##......##.#..####....#.#.####..##.#######..##..##.###...#..\n..#..##.#.#.#.##.#......######.#...###....#....#.#..#####.....#..#.####.\n....#..#.###.####.......#.#.###..#.######...##..#.#.#..#.######.####..##\n...#.#..####...#..##.#.####..#..##.#####..##.#...#..##..#..#.#.#.####...\n.##..###..###.#.##...#..#.#.##.##.###.##....#.####.#.##.#..##.#####.#..#\n#.#.###.#######..#...#####.##..##..##.#...#.#...#####.##....###.#...###.\n...#...##.#..#.###....#.#.##..#.#..##.#.#.#..#...#.....#.####.##.#..##..\n####.#...##.##.#..#.#####.#.##.###..#...#.#.##.##......##..#.#..##..##..\n..#.##.##.####....##.....#.#.......##.#..#.###.####.###.#.....#.#.#...##\n##...###..###.#.####.#..#...###...####..#####.#.#..##....#.#.####...#..#\n####..#.#.##.##....#..##.###.#..#..###.##.#.....#######..##.##....#.#.##\n.##...#.#####...#......##.#.##..#.####......#..###.##.##..#.#...##....##\n.#.##.#.##.#..#..###.#.###....#.#.#.#.#.###....##..####.#######.##.##.#.\n#######.##.#...###.#..#######.#..##.#..#.#...#.#.#.#..##.##.#.#.#....#..\n#.#.#.#.##..##..#.##...##.#.###.####...####.##..#.##.##.###.###.#....##.\n#...######.#....####.#.#.##....#..#...##.........#####.###..##.#.#..#.#.\n#.#.#.#.#...#.###...#.....#.#....######......#..#..#.###.#..#.#.##.#....\n#.##.#...#####.#....#.#.#..##...##.##.##.#####.####.#.##.#.###...#.##.##\n#...#.#.###........##..#...#.###...###.##......##.####..#.##....##.#..##\n#####.#..#.....#######..........#..####..##.#.#####..###...#...##.#.####\n...###..##.##.##.##.#..###...###.#.##.#.###.##.#.#........###...#....##.\n###.##...##.###..#..#.#.#...##.#.#.....##.#.##....####.####..#######..##\n##.#.#..#..###.#.#######..#..#.#.#..#####...####...#.####....##.###..##.\n..#.#.#....####.#.......#..#..###.##.#...##.####..###.#.#..####..#.####.\n.#.#..##.##..#...##...###.##.#.#.#..#####...#...#####..##.#...###..#.##.\n..###.#...#.#...#.###...###.##.#.#....#.#...##...##.....#.##.#.###.#....\n##....#..#........###..#.##.#..##...#.#.#..##.####.#...#.########.###...\n..#####.##.#...#..##...###.#####...#....#.##.######.#..#.##....###..##..\n.####.##..###...#.##...#.#.##..###.......#.###.#.##...#.#....#.#.##..##.\n#..#..###....#..#.#.....#.#.#####..##...####....####.#.#.##....#####.##.\n##########.####.#...##.##...#....##..##...###....#..###.##..##.###...###\n##.###..##.####.....#.#.....#.##...#...###..#.#...#....###..###.......#.\n##..###.#....##..#.#....###...#.####.#.###.#.#.#..##.##..##.######.##...\n#...####...#.##..##.##.#..####.#..#..#.##.##....#..#.##..##.#.###..#.###\n#.#..##.###.....#....###.##.##.#.###.#####.#.....##.##.##..#.##.###..###\n#...#..##..#..###....#..#...#..###...#.##.#.#.###...###..#.##..#..##.##.\n#.#..#.##.#...#..............#.###...##.##.#.....########.###....#.....#\n#..#.#...##..#.#.###.##.#.#....####.#.##.#.###.###.#..#..##.....#..####.\n.....###....##.##..##..#....######......##.###..#.#......#.#..#..#...#.#\n.##...###.#.#.###...##...##.#.####..#.###.#.#.#.###...##.#...#....###..#\n#..####.#...#.##..#..#.###.###...#.#.#..##....####..#...##........####..\n....##.##....#.....#..##..###..####..##.#.#.######..#....#..####.###.#..\n.#.##..#..#.#.....#........#..###.##.###.##.#..#..##.....#.#.###.###..#.\n#.#.#.#..#.###.#..#.##.##..######.##.######.#...#.###..#...#...##....#.#\n##..#...##.#.#.#.######.####.###...####..#....####...#.#..###...##.##..#\n.##.#....#...##...#...##.##.####..#.##..#.##.####..#.##..#..###..######.\n.##.#.#.##.#.####..#..#..##.#....#...####.###.##.####.....###..#..#.#..#\n#.##..#....##....##...#.##..####.#..####....###.##...###....##.###.##...\n..##..##.#...#.#..###...#.#.#.###.#.#######..#..###.#.###..#.###....#..#\n#..##.##.####..##.#....##..#.#......###....######..#.....###.....#.#.#..\n.#...###.##...#.##.##...##...##..####...#..########.###..########.#..#.#\n###.##.###.#.##.#..#.###....##...###.#.###.##..#.#...#..#####.##.##...#.\n.###.####..###.#.....####.#...###.##.#.##..#..#....##....#.#..#....###..\n##.#.#..##.#####..########..##...####....#.##.#.#.###.###.####.....####.\n#....###.....####.###.###.##..#...#.##.##...##.#..#.........#####......#\n##.####.#.#..#..#.##...#.##......#...#.#.#.####.##..##...####.....#.#.#.\n...#.###.#..###.....#.#####.#.....####.###...#.###....#...#..#.#...##.#.\n.#.......#...#......##..#.###....#.######..###.##...###...##.#.#.##..#.#\n.##.###.#..#.#####..###...#.###...##.#.####.#.#.#..#....#####...#..##.##\n.###..#...##..#.....##.#...#.#...##..##.#.###..###.#....##.###.###..#...\n#######.##..#..#.#...#..#.#..#.#..###..#########.#.....#.....####.##.#.#\n#.##..####...##.#..###.###...#....####...####..#...#####...##.#...#####.\n#..##.#..#.######.#.#.#.##...##..#...##...#.......#.#####.#...#.##..#.#.\n.##..#..###..#####.#.##..######.##...#.###.##.##.#..#....#..#.###..####.\n...#...##.#...##.#.###.#.#..##..####.....#..........#..#.........##..##.\n#####..##......##.##...#.##.###...####....##.##..#.###.#..##..#.##.#....\n.###....##.#####.#.###.#.##...##.####....###..#......#.#..#....##.#.#.##\n..###.#....#######.#.#..#.###.##.##..#..###...##.###.##.####.##.##.####.\n.#.#...##.#..##.....###.#..#.#...##..#..#.#.#.###.##.##.#.....#.##..#...\n.#####.#....#..#.####..####..#....#....##.#...#.##...###.#.#...#########\n###.####....#.####..#..###....#.###.##...#####.###...#.#..#.#........###\n#.#.######...#.#..#####.#.####.....##...#.###.#.##..##.#.#.##..#.####.#."
}
