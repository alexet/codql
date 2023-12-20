import lib

module Impl<inStr/0 input> {
  import Helpers<input/0>

  string baseKind(int x, int y) { result = lines(y).charAt(x) }

  int width() { result = max(int x | exists(baseKind(x, _))) + 1 }

  int height() { result = max(int y | exists(baseKind(_, y))) + 1 }

  pragma[noinline]
  int iters() { result in [0 .. 800] }

  int northGroupStart(int x, int y) {
    baseKind(x, y) != "#" and
    (
      y = 0 and result = y and x in [0 .. width() - 1]
      or
      baseKind(x, y - 1) = "#" and result = y
      or
      not baseKind(x, y - 1) = "#" and result = northGroupStart(x, y - 1)
    )
  }

  int southGroupStart(int x, int y) {
    baseKind(x, y) != "#" and
    (
      y = height() - 1 and result = y and x in [0 .. width() - 1]
      or
      baseKind(x, y + 1) = "#" and result = y
      or
      not baseKind(x, y + 1) = "#" and result = southGroupStart(x, y + 1)
    )
  }

  int eastGroupStart(int x, int y) {
    baseKind(x, y) != "#" and
    (
      x = width() - 1 and result = x and y in [0 .. height() - 1]
      or
      baseKind(x + 1, y) = "#" and result = x
      or
      not baseKind(x + 1, y) = "#" and result = eastGroupStart(x + 1, y)
    )
  }

  int westGroupStart(int x, int y) {
    baseKind(x, y) != "#" and
    (
      x = 0 and result = x and y in [0 .. height() - 1]
      or
      baseKind(x - 1, y) = "#" and result = x
      or
      not baseKind(x - 1, y) = "#" and result = westGroupStart(x - 1, y)
    )
  }

  int rockWeight(int n, int x, int y) {
    kind(n, x, y) = "O" and result = 1
    or
    kind(n, x, y) = "." and result = 0
  }

  pragma[noinline]
  predicate northContext(int x, int y, int y2) {
    exists(int end |
    end = southGroupStart(x, y) and
    y = northGroupStart(x, y)
    and 
    y2 in [y .. end]
    )
  }

  language[monotonicAggregates]
  int rocksInNorthGroup(int n, int x, int y) {
    n = iters() and

      result =
        strictsum(int y2 |
          northContext(x, y, y2) and
          |
          rockWeight(pragma[only_bind_into](n), pragma[only_bind_into](x), y2)
        )
    
  }

  pragma[noinline]
  predicate southContext(int n, int x, int y, int start) {
    n = iters() and
    start = northGroupStart(x, y) and
    y = southGroupStart(x, y)
  }

  language[monotonicAggregates]
  int rocksInSouthGroup(int n, int x, int y) {
    exists(int start |
      southContext(n, x, y, start) and
      result =
        sum(int y2 |
          y2 in [start .. y]
        |
          rockWeight(pragma[only_bind_into](n), pragma[only_bind_into](x), y2)
        )
    )
  }

  pragma[noinline]
  predicate eastContext(int n, int x, int y, int start) {
    n = iters() and
    start = westGroupStart(x, y) and
    x = eastGroupStart(x, y)
  }

  language[monotonicAggregates]
  int rocksInEastGroup(int n, int x, int y) {
    exists(int start |
      eastContext(n, x, y, start) and
      result =
        sum(int x2 |
          x2 in [start .. x]
        |
          rockWeight(pragma[only_bind_into](n), x2, pragma[only_bind_into](y))
        )
    )
  }
  pragma[noinline]
  predicate westContext(int n, int x, int y, int end) {
    n = iters() and
    end = eastGroupStart(x, y) and
    x = westGroupStart(x, y)
  }

  language[monotonicAggregates]
  int rocksInWestGroup(int n, int x, int y) {
    exists(int end |
      westContext(n, x, y, end) and
      result =
        sum(int x2 |
          x2 in [x .. end]
        |
          rockWeight(pragma[only_bind_into](n), x2, pragma[only_bind_into](y))
        )
    )
  }

  string afterKind(int n, int x, int y) {
    baseKind(x, y) = "#" and result = "#" and n = iters()
    or
    baseKind(pragma[only_bind_out](x), pragma[only_bind_out](y)) in [".", "O"] and
    n = iters() and
    exists(int fallPoint, int rocks, int case | case = n % 4 |
      case = 0 and
      fallPoint = northGroupStart(x, y) and
      rocks = rocksInNorthGroup(n, x, fallPoint) and
      if fallPoint + rocks > y then result = "O" else result = "."
      or
      case = 1 and
      fallPoint = westGroupStart(x, y) and
      rocks = rocksInWestGroup(n, fallPoint, y) and
      if fallPoint + rocks > x then result = "O" else result = "."
      or
      case = 2 and
      fallPoint = southGroupStart(x, y) and
      rocks = rocksInSouthGroup(n, x, fallPoint) and
      if fallPoint - rocks < y then result = "O" else result = "."
      or
      case = 3 and
      fallPoint = eastGroupStart(x, y) and
      rocks = rocksInEastGroup(n, fallPoint, y) and
      if fallPoint - rocks < x then result = "O" else result = "."
    )
  }

  pragma[noinline]
  cached
  string kind(int n, int x, int y) {
    n = 0 and result = baseKind(x, y)
    or
    result = afterKind(n - 1, x, y) and n = iters()
  }

  int weight(int n, int x, int y) {
    kind(n, x, y) = "#" and result = 0
    or
    kind(n, x, y) = "." and result = 0
    or
    kind(n, x, y) = "O" and result = height() - y
  }

  string value(int n) {
    result =
      strictconcat(int y | | strictconcat(int x | | kind(n, x, y) order by x), "\n" order by y)
  }

  int iterGap(int n) { result = min(int y | value(y) = value(n) and y > n) - n }

  int iterKind() { result = (1000000000 % (iterGap(_) / 4)) * 4 }

  int baseIter() { result = ((min(int n | exists(iterGap(n))) / iterGap(_)) + 1) * iterGap(_) }

  float total(int n) { result = strictsum(int x, int y | | weight(n, x, y).(float)) }

  float p1() { result = total(1) }

  float p2() { result = total(iterKind() + baseIter()) }
}

string testInput() {
  result =
    "O....#....\nO.OO#....#\n.....##...\nOO.#O....O\n.O.....O#.\nO.#..O.#.#\n..O..#O..O\n.......O..\n#....###..\n#OO..#...."
}

module TestImpl = Impl<testInput/0>;

string realInput() {
  result =
    "......#.O#O.##...O.....#...#..##...OO#.OO.......O.##....O.......O..#.#..O.O...O#O.O....#.O..OO..O.O.\n.##.##OO..#.#O..##..OOO#..O.....O.O...#.........#.......#.O#.O..O...O..OO#O..O....#..O..#OO.O..O....\nO.....#..#..O.#OOO.OO..O..#..#O.....O...#.O..#..#O#.........#.#.....###.#.#.O...#.#.O......O..OO..#.\nO..#.#..#........O......O.OO#.OO..O.O...O.O.......O...O......#....O##.#.OO.#..#.O#O.O.#.#.O...#...O.\n...O........#.O.....#O.....OO#.#.##O...#..OO...#.O.#.##.OO...#.O.#O..O......#..#.....#..#..O#..#....\n..O....O.....O.#..O...O..#O..O.O.#....#.#OO.O#.#..#....#..#....#.OOO..O.O#O##O......#.O.O...#O.....O\n.OO.#....#.O..O..OO.....#.O.OO........OO...#.#..O....#.O.....O.#.#..#...O#.#.O##O..#O#.OO..#O.#.O#..\n.O..O.##O...O.O..O.O.....O....O...#O.........O.....O.#.O........O.OO.#O....OO..O..O.........#O......\n....#....O...O...#OO#....#O......O#..O.#OO.#.##.#.....O.#O.O##....#.O.......O.#O##........#......O.O\n.#OO#.OO.O.##O.#..#.##OO.O....O#.....#...##..#.....#O#O.O....O.O..#....O...#.O.O.....O..#OOO#O...#O.\n#....#......#..O.........#..#..O.###..#...#.O.O...OOO#......#..#O...O#..#OO#.#..#....#OO.OOO.....OO.\n.OO#....###....OO..#O..O..O.O..O.O..O...#..#O...#O.OOOO..#..##...#.O.OO..#O...#.O#....O...O...#....#\n.....O...O###O.#....#.O.....O..OOO.....O.#.O.O#.#.O.#.O..O...#OO...#O.#O....O.#.#....#O#..O......OO#\n.O#.#.O.OO......#.....#....O.....O.O...OOO..........##......O......O....OO...O..O#....O....OO.......\n#.......#...O.OOO...##O.OO.O.O...O..OO#O#O###.....#.OOO.O#O#.....#..#.O###O.......#OO.O...O.O....O.O\nO....#.O.............O..#.......O.#.....O....#..O.#O#OO.O.#O.O....O..#O#.O....#O#OO..#..O.O......OO.\nO...#.O.OO.O.#O#O.#.....###.O..#.#.#.O.O..#..#........#.O...#....#.O.....O.....#O.O..O..#...##....O.\n....#............O#.....O...OOO..#O....##..#..O#...O..##.O...O....#.......##.O.#.#O..O..O.#O#...###O\n...#O...O.OO#.....O..#......O.O#O..##O.O.O..#.#O.......O..O...#....O...#.#O...#.O.#O#.#.#O..O.###O.O\n#..#O..O.#...#...#..O..#..#......O.....O.#...O..#.OO........#..#....#...##..O..O..O.......O...OO...O\n.OOO...O.........#.O....O..O##....##.......#....#O..#.OO.O......O#O....#.......O......O.O......##..O\n......#...#O#...#...#OO.O#...O.O.O....O.O.....#.#..O.........O#.#.#..O#.#..#.......O.O....O...OO.O..\n...........#.OO....OOOO.....O...O#...O...#OO..O.O.#..#.O##O........#......#...#.#...##OO....#O#O###.\n.#.##O....O#.O........O........OOO.OO..#..OO.....O.O.####...OO..O...#.O...O.OOO.#.....#..#.OO#.#O#O.\n..O..#.#..OO....OO..O............OO.....O#..OOO.O.O..#.O...O..O.OO#.O.#O.OO......#.##......O.#OO....\n#.O...#O#O...O.O....O...#.###O...#...#...O..OO...O.......O.#....#..O.#O.#O..O..#O#...O....#.O.##O#..\n.O#.....OO....O#.#.......#.#..###OO.......O....#...#O..#..#.O.O....O.O..#O........##O..#...O#.#O..O#\n.O..##..#.....#.......#.....O....#..#O...#O#.O..O.O............O...#.#.#..OO#...O..#..O.O..#.....O.#\n..O..O#..#.###O..........#..O.OO.....O#.O..O...#.......###.......O..O#...#O##..O...O...#O....O#...O.\n..#O.#...OOOO.O...OO.OO...#....#.#.##...#.O.#O..#..O........O#.O...O.O#.....O#.#O..O...O.....#..#...\nOO.....O.O#.O#.#.#...O#.#...#.........OO.#.#...#....O.OO...O...#O.##.O........O.O...O..O#..O..#.#.O.\n.#.#..O..O..OO##...#.O.###O...#.O.....O...O...OO#.O...#O.#....#..OO#.O.O...#O#.#....O...#OO#..OO.#O.\nO..O....O......#..O.#.#.#.#.....O.....#.#.O...O....OO....O.....O.....O...O.#O.....#OO...#..#.##..#..\n..O#....#..##......O..O..#....OO....OOO...#O...#...O..##..#...OO...OO......O#.OO....O....O.#O..O.O#O\n.....O.....#OOO.O.O.OO..O.O....#....O..O#O#..#.#......#.O.O##.O..O......OOO...O.........O..O#.O.##.#\n.O.#.....O#...O#.....OOO....O.O#....#.OO#......O........#.OO#O...O.##O.O....O..O#O.#.......O.....O#.\n..O..#.O.....#.OOO.#.....#O.#...O.OO..O.....#O.###...O.#..##...O...#.##......O....O...O#....O....O..\n.O.O#O.O#.O......#.#.O..O#.......O.OO...OO...O.#OO#.....OO.O.O..#..OOO.....O#....O.#.....#....#.O...\n..O.........#.O..##...#..#OO#O#.#..#......O.#...#..#O.........#.#...OO....#......OO#O.##O.O..OO#....\n...O#.O.#.#........#.#..O.O#...O.#......O....##..##.#.O..OO.#.#....O..O....O..#O.#...#O#.O...#....O#\n...O..#...O...#O...#...OO.#O..#.O....O.#.O..O..O#.O....O.##O..#O.##....#.OO..#.#..#...OOO.O..O.#....\n.......O#.O.#O##O..O..O.....O...O..O#O..O#O..#....O..O........O.....OO#...#...O.O#O....#.OO#....##..\n#.##O#.......#...O#...#...#...#O.O.O...O..#.OO......#.O.#...##.O.#.O..O..#O#O...........OOOOOOO....#\n.....O..O.#..O......#....O.....OO..O..#.....#.O..#..OO..#.OO.O.#....#...##...O.......#OO.O...#O.....\nO.......##..OO...#..O.#.#.#.....O#.....O..O#.O#....##....O.#..OO.#..#OOO.O.O###O#.#OO......O...O...O\n.......O..##O....O...#..#....O..OO#..O##O...O.OO....#....O...#.##O...O...##..#.#.O..O#O....#O...#O..\nO.O.....O.O#.O#.O....O.#..##O.#.O..#.#.O.O###.#.O...#..O.O#...#.O.....#O..OO.O#O#..#O#.#...........O\n.#...O.O#...#..OOO.O....O..#....O#...#........O#O.##.#...OO.....#....#O..#O.....O#...O...........#..\n.#.#...O#O.....O#OO.#O....O##..##..O...#..O.O.O.....O..#O..O#O......#.O...O........O...#.........O.O\nO.#O.##.....O#...OOO.......O.O.#.#.#.....#.OO.......#O.....#.O.O#...O##..#.#.............#.O#O....#.\n...O##.O#....OO.........#OO........O.O.OOO.#.#..O..#...OO....OO..........O...OO#OO..#O...O.O..O...O.\n.OO.O#..#.#.O...#O...O..#...O.O..#..##.........#..##O.OO..#..O#.........#O.OOO......O.##...O#O....#.\n.OOO....O...#..#O.......#.O......OO.O#O.....O...O..#....O.O#......O.O....O....OOO###..OO...#OO......\n.O..O....#...OO.O...#....#O.O...#...OO##.....O..O...O........O...O#O...O...O.O....OO.OO......O.....#\n...#...#.OOO...O.......#......O.O.#.##.#.O.O...##.OO.#.O.O..OO#......OO..O.O#.#.......#..#.OO.O.OOO.\nO#..#..##..O..OOO..O....#..O.......O...##O#..#..#.O.OO..#.O....#...OOO..O.O...OOO#.........#.#O...O.\n.#...O..#.##.O........O..#..#O..##...#..OO...#.....O#..O.....#.##......#..OO........O..O#....#O#....\nO.O#..O..#OOO..#.......#...#.O....##...#.O#...O......##........O.O####O.OO#..O....#...##O#..O..#....\n....#..O..#.O..O#O.#.......O.##....O#O#.OO.OO#.......O.O#..O...#O.OO.O.#..##OO#.O..OO.O.#OO#....O#O.\n....O..O...O...O#.#O.O...#.#O...O...O...O....#O##.#......##......O.....OO###OO....OO##.#...#.....OO#\n.O.O.#...O...O......#.O..OOO#..O.O...O.#O......O......O...O.##..O.....#..#..O.#....O...##...........\n#.O..##O.OO.O.....###O##OOO#O.#.#OO.O.O.O...#.#O#OOOO#.#O..O....O......OO....O........##.O..#O..O...\nO#O..#OOO.O..O......#...O.......O.#..O#........#..##..#..O..O...#.#..#....O..O..OO.......O..#..O#..#\n..#....#.O..#.O#OO...........#...#.#OO#...#...#.##..O.#O.O.##...O#.#...O.##....O.O.O....O..O#.O.##.O\nO..#.O...O....#....##.....#.#.O#..O..O.....#O.OO#.O..#...#.#.#.O.#..O#..OO.##O..O......O#O#..#..O.O.\n.O....O.....O.#.......O.......O...#O..#...O..#OO##..O...##.#.O.O#.O..OO.......#OO.O....OO....##O.OO#\n..OO.#..O.......#O.O....O..#.O.O.OO....O..#....O.O.O....OO.#O##.....OOO#..O.#O.#...##OO.#...O.O.O..#\n..OO..OO.O#O...O..........O........O.O..#.#.O.O.......#O...O.O...##.#....#.O..#.....#...O.#...OO#O.#\n.O.O.O.O..O#...O.....#.....O..O#....O..#..O###.O#.O.O...O.....O...##.#...O#..O#..O......O#...O.O....\n.#...OO...OO.O#O.#....#....#O#..#...O.O...#OO.#O..#...#.O.......O#O..O#..#.#.OO...##.OO..O.#...O....\n....##...OOO..OO..O.O..#..#..##O..#O...........#..#..O#.OO.#....#..##OO#O.O#..#O#.##O##O##OO.O.#O.#O\n.....#..O.....#....O#..#.O#.#..#OO.#..O.....O...#..#.O.O....#.#O.O.#..#.O.OO..O..#..O..#..#OOO....#O\nOO#.#O..........O.......O#O..#O.#.##OO.#....O..O..#.O....#OO..#.##...#.....##O#.O.O...O#..O#..#....#\n.O..O.OO..O.#...........OOO##..O..O...O.O#.O#OO...O.#...O.#.O.##.#..O.OO##.O.##O.O...O....OO#.......\n.OOO.......#..O......OO.#...O...O#O.#......#.......O.#..#O..#O#...O.........OOO...O...##O.....#...OO\nO..O.......#.O.O..#O##.##O.......#...O..OO.OO.#.OO.#.O.#.O...O....OO..O.##.......O....#.#.O..#....##\n#..O.OO....#O......O..O.O...#.O....OO.O.OO..#..OO......#.....#.##.OO.##O.#O......#...O.OOO.....O..O.\n.O....##..OO.##O####..........O##.##.O..O#O##.#O.#..O#......#O.OO........O#......##O...#OOO.....#.#.\n.....#O..#..#....OO#....O.##....O.O.O.O#..#O.O..O....OO..OOOO.O.O.O..O....#.#..O..O..#...OO....#.O#O\n#.#.#OO.....##.O...........#.##...#.#.O#O......#.......O.OOO..#.O...O....#.O.....#....O..#..O...##O.\n......OO...#....#...O#.OO...OO...O...O..#.#....##......O..................O.O..#.##......#.........#\n..O..#.O..##O.#.OO##O.OO.O..O..#....O.#.#.O.O..OO........O......O..O..#........###.#....O.#.#.......\n..##.......OO#..#.O.O#O.##.#..#.#...#O......O.O..O#...#O.O...OO...#..O#..#..O.#..O##..#...#..##..#O#\n#O.OO..#....O...OO.#...O#.....O#..#..O...OO..#.....OO#.#.O...O..O.O.O.O.......O..O#..O..#OO.O#..#O#O\n......#........O.......#.O.O#.O...#...O.#........O..#O.#.O...O..O.##..O.O.........#OO.##............\n#OO.O.O#O.#O..O.O.#.O..#.#O.O#......##..#O.........#O.....O..O#.##OOO.#......##...O.#..O##...O.#O.#.\n#...O.#O.O..OO...O.##...#.O...O#O.#.#.O....O......O....O...#...O..#.....O#....O.O.#O.......#.O.###.O\n....##..O......O.........#.O..#..#O...OOO....#O###......#.#...#..OO....#...OO..O#.O..##.O.#........#\n......#.O#O#...OOO....OO..#.#...O...OO......#.###........O.OOO......##..O#...OO..O.#OO#....O.OO.##..\n.#O#O#...##O...##O#...#.............#.#.O..O#OOO.##O#.O..#....O#....O......O..........#.#..O#.#...O.\nO#O#.....OOO.....#............#.OO.#.O...O...O..#...#...##...O...O...O..#..O....O.....O.........#...\n...#O......O.##..#O...O#.O#O...O...#...O...O..#..O.O..........#....##..O.......#........#OO.........\n........#.O....O#.#.#O......##..#.#.....O.#..#...O..OO.O.#OO..O....O#...O.#..O.O...#.O.#O..O.O..#OO.\n..#.#.......#...#.O#...OOOOO..#...O...OOOO#..#...O.#OO..#..O............O....O..#.O.#.O.#...#..O.#.#\n.#O....#.O..#O.O.#..#OO....O.O..O##O...O.##.....#..OO.##...#....OO...#.OO...O.#.O#.....##.#OO.#.##..\n.O..O.O...##......#OOO..OO....O....O#..#.......O....O...#O.#.O.O#O#O#.......O.#.....O.....##.#..#.O.\n#.#O..O##....OOO..O##....#O.O.O##...O.#OO..##..O.#...O..O#...O.....#.##....O..OO.#.O...O.OO..#..O...\n..#.#...O..OOO#...#..........#.O...###.......O..O....O..#..#....##.....OO#O......O.OO....#..#...#OOO\n.O...O...#.##.#OO.#.O...O...O#O.#O....#..#....O#...OO.O....#O.O........O....#.....O...O#.OO..#......\n.OO.O.#....O.O#......O#...#.##O#...O.#....#..O#O..#...#....O..OOO#.#.....O#.#O.##.#O#O.#.O....#.##O.\n"
}

module RealImpl = Impl<realInput/0>;

select 1
