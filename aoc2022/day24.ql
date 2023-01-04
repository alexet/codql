import lib

select 1

module TestImpl = Impl<testInput/0>;

//module RealImpl = Impl<realInput/0>;
module Impl<inStr/0 input> {
  string blizzardAt(int x, int y) {
    result = Helpers<input/0>::lines(x).charAt(y) and
    result in ["<", ">", "^", "v"]
  }

  int blizzardId(int x, int y) {
    exists(int longId |
      x = longId % 1000 and
      y = longId / 1000 and
      longId = rank[result + 1](int x2, int y2 | exists(blizzardAt(x2, y2)) | x2 + y2 * 1000)
    )
  }

  int height() { result = max(int i | exists(Helpers<input/0>::lines(i))) - 1 }

  int width() { result = max(int i | exists(Helpers<input/0>::lines(_).charAt(i))) - 1 }

  int maxRounds() { result = (width() + height()) * 10 }

  predicate reachableInRound(int round, int x, int y, int step) {
    round = 0 and x = -1 and y = 0 and step = 0
    or
    exists(int prevX, int prevY, int prevStep |
      round in [0 .. maxRounds()] and
      reachableInRound(round - 1, prevX, prevY, prevStep) and
      not exists(Blizzard blizzard | blizzard.posAtRound(round, x, y)) and
      (
        x = prevX - 1 and y = prevY
        or
        x = prevX + 1 and y = prevY
        or
        x = prevX and y = prevY - 1
        or
        x = prevX and y = prevY + 1
        or
        x = prevX and y = prevY
      ) and
      handleStep(x, y, prevStep, step)
    )
  }

  predicate handleStep(int x, int y, int prevStep, int step) {
    step in [0 .. 2] and
    (
      x in [0 .. height() - 1] and y in [0 .. width() - 1] and step = prevStep
      or
      x = height() and
      y = width() - 1 and
      (
        prevStep = 0 and step = 1
        or
        prevStep != 0 and step = prevStep
      )
      or
      x = -1 and
      y = 0 and
      (
        prevStep = 1 and step = 2
        or
        prevStep != 1 and step = prevStep
      )
    )
  }

  predicate reachesGoal(int round, int x, int y, int step) {
    reachableInRound(round, x, y, step) and
    round = minRounds() and
    x = width() and
    y = height() - 1
    or
    exists(int nextX, int nextY, int nextStep |
      reachableInRound(round, x, y, step) and
      reachesGoal(round + 1, nextX, nextY, nextStep) and
      (
        x = nextX - 1 and y = nextY
        or
        x = nextX + 1 and y = nextY
        or
        x = nextX and y = nextY - 1
        or
        x = nextX and y = nextY + 1
        or
        x = nextX and y = nextY
      ) and
      handleStep(nextX, nextY, step, nextStep)
    )
  }

  string posChar(int round, int i, int j) {
    round in [0 .. maxRounds()] and
    (
      reachesGoal(round, i, j, _) and result = "E"
      or
      i = -1 and j in [-1 .. width()] and result = "#" and j != 0
      or
      i = height() and j in [-1 .. width()] and result = "#" and j != width()
      or
      j = -1 and i in [-1 .. height()] and result = "#"
      or
      j = width() and i in [-1 .. height()] and result = "#"
      or
      i = -1 and j = 0 and not reachesGoal(round, i, j, _) and result = "."
      or
      i = height() and j = width() - 1 and not reachesGoal(round, i, j, _) and result = "."
      or
      reachesGoal(round, i, j, _) and result = "E"
      or
      i in [0 .. height() - 1] and
      j in [0 .. width() - 1] and
      not reachesGoal(round, i, j, _) and
      exists(int blizzardCount |
        blizzardCount = count(Blizzard blizzard | blizzard.posAtRound(round, i, j)) and
        (
          blizzardCount = 0 and not reachesGoal(round, i, j, _) and result = "."
          or
          blizzardCount = 1 and
          result = any(Blizzard blizzard | blizzard.posAtRound(round, i, j)).blizzardType()
          or
          blizzardCount > 1 and result = blizzardCount.toString()
        )
      )
    )
  }

  string blizzardImage(int round) {
    round in [0 .. maxRounds()] and
    result =
      strictconcat(int i |
        |
        strictconcat(int j | | posChar(round, i, j) order by j) + "\n" order by i
      )
  }

  int minRounds() { result = min(int round | reachableInRound(round, height(), width() - 1, 2)) }

  class Blizzard instanceof int {
    int x;
    int y;
    string type;

    Blizzard() { this = blizzardId(x + 1, y + 1) and type = blizzardAt(x + 1, y + 1) }

    bindingset[round]
    predicate posAtRound(int round, int x2, int y2) {
      type = "^" and x2 = (((x - round) % height()) + height()) % height() and y2 = y
      or
      type = "v" and x2 = (x + round) % height() and y2 = y
      or
      type = "<" and x2 = x and y2 = (((y - round) % width()) + width()) % width()
      or
      type = ">" and x2 = x and y2 = (y + round) % width()
    }

    string blizzardType() { result = type }

    string toString() {
      result = "Blizzard " + this.(int) + " at " + x + ", " + y + " of type " + type
    }
  }
}

string testInput() { result = "#.######\n#>>.<^<#\n#.<..<<#\n#>v.><>#\n#<^v^^>#\n######.#" }

string realInput() {
  result =
    "#.########################################################################################################################\n#>v<^^><<>^>^>v<>>^^.v>^vv<^v<v><vv.^^^^v<v<v><<^v.<>^^^>>>>><^<.vvvvv.^v>vv<>v<v<^>^v<^v.<>>v<><v^v>.v>^vv^>><v>v>.^>><>#\n#<.v<v>>>.>>>>^<vv><^^v>>v>^><v^>^<.<v^<>>><v<vv<<^^<^^v^<.>v.v>>.v<^><v<v<>^><^>^>><.<<<<^>^^^v.v.>v><^<^v^>.>^>>vv.v^<<#\n#<<>v>^<<^v^<<<vv.>^^>^^v^>>v<>v>v<><^^v<^>><^<>^^v^vv<v<<<>^v^v<.<^>^<>>>.<><<<v<v<<<vv<>>v.^^<v.vv<^<^><^<vv^v<v<v>v.^<#\n#.v^v<v<>>>.v^vv<<v^<vv<<vvv^>^^v.v^v^^v<>^^^^^><.v^v>>v>>^>vvv^^<<^>^v^.v<^<<^v^v>>vv.<<^<<v<v>>^v>^>v.v^><><vvv^>v<>^<<#\n#<v<^<v<^<>v>>v^>>^<<>>v.^^<>vv^<><.v^>><<^<v><<^>>^^^<vv>^<v>.>><<.v^v^<v>^<v>>>>vvv<><^><<<v>v>v.^<<.<v^<>vv<v<<>v>^>v>#\n#.^.<>v>v^v<v>>v<>v>vv<.^><^v<<><>^.^>>v<^v.v^^^^<vv>^<vv^>vv^>^.<>.<^^v<>><^^^.><^v>v^^<>v>>v><>>v.^^<>>v<<^<^<v<vv.>^<<#\n#>^v^>^v>...^<>^.<v>.v<v<>^^v<<<^.v>v>^.><<.v<v<>.>v>>v>>><<v<><^.v>.>>>^>^>.v<>>>v<^^>^v<<^v>^v^<v.v>><>><vvv^v>v^v<v<<<#\n#<^.vv><<><>v^^<^.<^<><..v.^vv<v.vvv><v<^v>v<^v>v^v^^^^<>^^^.^^^v^v>>v^>><>v>^<>v^^.^<^^<v>>v^vvvv>>v^><^<<>>>^<<^v^^<<><#\n#<>><^<^<<^v^>>>v<.>..v>.^>>^v^<<v^<<vv<^v^><<.><^^><.vvv^>>.>>^<^vv><.v>^^>>>.>^vv<^<<>vv<>vv^^^v.>>>><..v>.^<^v<>v.<vv<#\n#<<.<><>.<^<<<<^>^<>^vv^>^>^>vv>>v>>v^>.^.>vv<><.v><<>>vvv.v^^vv>>>v<v<><^<^<>^.v<^^>^><.>>^^^^^vv<<^>^<<v<^v^<.v<<v<<.<<#\n#>>v>.^.<><>^.vvv<vv>^>.^^.v>^v.v>^<vv^v>v>^v^vv<<>><v.<><<v><>^<^<v<>.<^<^^<>^<>>v^v.^<v^^<v^>v<<^.^>>^v>^^^>vv.v.>^v>^>#\n#>^<>v^^^v<v^vv>>v.^>>>^v>><>^v^><v^.v><<>>><^<<.<>v<><><^v^>^^<^^>>^v^>^>^vv^<>>>^v^<.v^^^v<v<v...>^>^<^^v<v^^v>^^>.<^^>#\n#<v<v^^v<>><<<^vvv<vv>>.^.<>>.^v^^<>>v^^>v><>v><v<^^.v^>>.vv^v><>^^v<>>^>^<<^.>v<v^vvv^.><<<v.^^<vvv^<.>>^.<<vv^<<<>.^>><#\n#>.>^.v.>>^<v><><^<.>^v<><>v^^<.>vvv<><>.<v<>.><<.^v^^v^.>vvvv^>.<>><<^v<<>^<<<><<>>^<^>^v<^v<>v^>v<v<.>^<^vv<>^<^>>^>^<<#\n#<.^.>^vv<><>^^<^<.<>vv.>^<<<>v><.<<v<>^<>>v<^^<v^v^^>v<v<^<vv<.v^<>v<^>>.<>^<^.vv><.><v<^<<^<<>^<>v<vvv^v^^>><v>v>..v<<>#\n#<^v>><<v.^^.<^>^<^vvv.^v^v<>vv^v<^vvvvvv^v><>>.^<<^v>v.v.>.^<<^^>>>v^><v^>>>.v^^>.>><^.^^.>.>v^<v^>^<<v<<^><>v<^^>^<v<v<#\n#.v><v>>>v^>^^v<>^<<>>^<v>^><<v^><^.<<v<vv<<^v^^><>><^^><><^^^vv>.^>.<v.^v<v<^<<.v.>>>><<<^v<<.<^<>v.^<^<vvv<.v<.v><^>v<>#\n#<v<v^<^v><<^<>^>>>>^^v<>^^>v<v.^^^^^.^<^<<^><<v^><^.><^><v^>.^>v^v>v.><^<^>v<>^>.<>^..<<>^^>^<><^<^..vv>v^^^v>^^<..^.v<>#\n#>v<<v<<<^.^vvv>>v.>v^v>v<><v.^><^v<>^v<v^v<v<.^^.>v>.v>vvvv^>vv^>^^v><v^>>>.<v^>><.<v><<.>>^^v^vvv<vv^^^<^>v^>vv>^>^vv>>#\n#><<v>^>>>>vv<<><>^>^v>^vv^<^v><>v^.<.^.v>^<<^v>v<.^v.>^v<^^^>v^^.^>vv.<v^>>^.><<>>^<<>.>v.v>>^..>><<..v^>><>v<>.<^v.>>^<#\n#.<<^^<.^v>>>>.>^vv<^<<>>>>^v>v<^.v^<^>>v^<^>^^>>v<>^<v^^^^>><^<^^>>v<.<<v.^v<>>.vv^^^<v^^.^v.<>^>^>><><^.vv<v>v>v<^^>.<>#\n#<<<v>.^v>v>v<^^>vv^<vv<vv><v>v<vv<.>vv<^^^<.v<>..^<<<<<^^^>><v^^>>^<<^v^>><.^<^.<^.<v<vv<..^.><<>vv<^<v<v.<>.<<^v<<^>vv<#\n#.>^^.<<>.>>>.<^<>.<<v<^>v>v>v^v^<v>v^<^>^<<>v^^v^v^^^<>^vvv^vv<.^^>.v^<.>>^>vvv^>.v^>v^v^>.^^<v<<vv^^>v>^vvvvv<vvv^<<>>>#\n#<^v^.<<<><^<<v^^^v^^^<^^<<>.^<^v<.>.^^..^v<<^>^.<<>>.<^>v.^<v>.v^^.<vv^^>v^><v^><^.>>>>>^v<v<^vv^^>^v^.^.^^^>v^<.><>^^>>#\n#.v^vv.^v>vv>>v<vv^^v<v>><.<>><^^>^v.vvvv>><^^>v^v>.v^<.<^.<^<^v.><v>^v<<^^<>vv>>>^v^v^<^<^^^>..<><^<^.vv<<<v>v^.^>^<>^><#\n########################################################################################################################.#"
}
