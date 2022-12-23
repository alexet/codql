import lib

signature module CubeMap {
  int cubeFromPos(int x, int y, int cx, int cy);

  int cubeMove(int cube, int dir, int newDir);

  int faceSize();
}

module TestImpl = Impl<testInput/0, TestCubeMap>;

module RealImpl = Impl<realInput/0, RealCubeMap>;

module Impl<inStr/0 input, CubeMap Cube> {
  string mapTile(int x, int y) {
    result = Helpers<input/0>::groupedLines(0, x).charAt(y) and
    result != " "
  }

  string instrs() { result = Helpers<input/0>::groups(1) }

  string instrDir(int i) { result = instrs().regexpFind("(L|R)", i, _) }

  int instrLen(int i) { result = instrs().regexpFind("[0-9]+", i, _).toInt() }

  int maxLen() { result = max(instrLen(_)) }

  int instrFacing(int i) {
    i = 0 and result = 0
    or
    instrDir(i - 1) = "L" and result = (instrFacing(i - 1) + 3) % 4
    or
    instrDir(i - 1) = "R" and result = (instrFacing(i - 1) + 1) % 4
  }

  int leftTile(int x) { result = min(int y | exists(mapTile(x, y))) }

  int rightTile(int x) { result = max(int y | exists(mapTile(x, y))) }

  int topTile(int y) { result = min(int x | exists(mapTile(x, y))) }

  int bottomTile(int y) { result = max(int x | exists(mapTile(x, y))) }

  int width(int x) { result = rightTile(x) - leftTile(x) + 1 }

  int height(int y) { result = bottomTile(y) - topTile(y) + 1 }

  bindingset[prevY, offset]
  int yOffPos(int x, int prevY, int offset) {
    result = (prevY + offset - leftTile(x)) % width(x) + leftTile(x)
  }

  bindingset[prevY, offset]
  int yOffNeg(int x, int prevY, int offset) {
    result = (prevY - offset - leftTile(x) + width(x)) % width(x) + leftTile(x)
  }

  bindingset[prevX, offset]
  int xOffPos(int y, int prevX, int offset) {
    result = (prevX + offset - topTile(y)) % height(y) + topTile(y)
  }

  bindingset[prevX, offset]
  int xOffNeg(int y, int prevX, int offset) {
    result = (prevX - offset - topTile(y) + height(y)) % height(y) + topTile(y)
  }

  predicate start(int x, int y) { x = 0 and y = min(int y2 | mapTile(0, y2) = ".") }

  predicate stopPointRight(int x, int y) {
    exists(int yLeft |
      mapTile(x, y) = "." and
      yLeft = yOffPos(x, y, 1) and
      mapTile(x, yLeft) = "#"
    )
  }

  predicate stopPointLeft(int x, int y) {
    exists(int yRight |
      mapTile(x, y) = "." and
      yRight = yOffNeg(x, y, 1) and
      mapTile(x, yRight) = "#"
    )
  }

  predicate stopPointUp(int x, int y) {
    exists(int xDown |
      mapTile(x, y) = "." and
      xDown = xOffNeg(y, x, 1) and
      mapTile(xDown, y) = "#"
    )
  }

  predicate stopPointDown(int x, int y) {
    exists(int xUp |
      mapTile(x, y) = "." and
      xUp = xOffPos(y, x, 1) and
      mapTile(xUp, y) = "#"
    )
  }

  bindingset[x, prevY, maxMove]
  int tryMoveRight(int x, int prevY, int maxMove) {
    result =
      min(int y, int offSet |
        y = yOffPos(x, prevY, offSet) and
        offSet in [0 .. maxMove] and
        stopPointRight(x, y)
      |
        y order by offSet
      )
    or
    not exists(int y, int offSet |
      y = yOffPos(x, prevY, offSet) and
      stopPointRight(x, y) and
      offSet in [0 .. maxMove]
    ) and
    result = yOffPos(x, prevY, maxMove)
  }

  bindingset[x, prevY, maxMove]
  int tryMoveLeft(int x, int prevY, int maxMove) {
    result =
      min(int y, int offSet |
        y = yOffNeg(x, prevY, offSet) and
        offSet in [0 .. maxMove] and
        stopPointLeft(x, y)
      |
        y order by offSet
      )
    or
    not exists(int y, int offSet |
      y = yOffNeg(x, prevY, offSet) and
      stopPointLeft(x, y) and
      offSet in [0 .. maxMove]
    ) and
    result = yOffNeg(x, prevY, maxMove)
  }

  bindingset[y, prevX, maxMove]
  int tryMoveUp(int y, int prevX, int maxMove) {
    result =
      min(int x, int offSet |
        x = xOffNeg(y, prevX, offSet) and
        offSet in [0 .. maxMove] and
        stopPointUp(x, y)
      |
        x order by offSet
      )
    or
    not exists(int x, int offSet |
      x = xOffNeg(y, prevX, offSet) and
      stopPointUp(x, y) and
      offSet in [0 .. maxMove]
    ) and
    result = xOffNeg(y, prevX, maxMove)
  }

  bindingset[y, prevX, maxMove]
  int tryMoveDown(int y, int prevX, int maxMove) {
    result =
      min(int x, int offSet |
        x = xOffPos(y, prevX, offSet) and
        offSet in [0 .. maxMove] and
        stopPointDown(x, y)
      |
        x order by offSet
      )
    or
    not exists(int x, int offSet |
      x = xOffPos(y, prevX, offSet) and
      stopPointDown(x, y) and
      offSet in [0 .. maxMove]
    ) and
    result = xOffPos(y, prevX, maxMove)
  }

  predicate pos(int i, int x, int y) {
    i = 0 and start(x, y)
    or
    exists(int facing, int prevX, int prevY |
      facing = instrFacing(i - 1) and
      pos(i - 1, prevX, prevY) and
      (
        facing = 0 and
        x = prevX and
        y = tryMoveRight(prevX, prevY, instrLen(i - 1))
        or
        facing = 1 and
        x = tryMoveDown(prevY, prevX, instrLen(i - 1)) and
        y = prevY
        or
        facing = 2 and
        x = prevX and
        y = tryMoveLeft(prevX, prevY, instrLen(i - 1))
        or
        facing = 3 and
        x = tryMoveUp(prevY, prevX, instrLen(i - 1)) and
        y = prevY
      )
    )
  }

  int instrLen() { result = count(int i | exists(instrLen(i))) }

  predicate finalPos(int x, int y) { pos(instrLen(), x, y) }

  int code() {
    exists(int x, int y, int facing |
      finalPos(x, y) and
      facing = instrFacing(instrLen() - 1) and
      result = (x + 1) * 1000 + 4 * (y + 1) + facing
    )
  }

  // Note folding rules directly copied from the input :(
  /**
   * .12
   * .3.
   * 45.
   * 6..
   */
  int flipFacing(int facing) { facing in [0 .. 4] and result = (facing + 2) % 4 }

  predicate fipCorrect(int origCube, int origFacing, int newCube, int newFacing) {
    newCube = Cube::cubeMove(origCube, origFacing, newFacing) and
    origCube = Cube::cubeMove(newCube, flipFacing(newFacing), flipFacing(origFacing))
  }

  predicate move2(int x, int y, int facing, int offSet, int newX, int newY, int newFacing) {
    exists(int origCube, int origCX, int origCY, int newCube, int newCX, int newCY |
      origCube = Cube::cubeFromPos(x, y, origCX, origCY) and
      cubeMove(origCube, origCX, origCY, facing, offSet, newCube, newCX, newCY, newFacing) and
      newCube = Cube::cubeFromPos(newX, newY, newCX, newCY)
    )
  }

  predicate stopper(int x, int y, int facing) {
    exists(int newX, int newY |
      move2(x, y, facing, 1, newX, newY, _) and
      mapTile(newX, newY) = "#" and
      mapTile(x, y) = "."
    )
  }

  predicate hasStopper(int x, int y, int facing, int offset) {
    exists(int newX, int newY, int newFacing |
      move2(x, y, facing, offset, newX, newY, newFacing) and
      stopper(newX, newY, newFacing)
    )
  }

  cached
  predicate moveBlocked(int x, int y, int facing, int maxOffSet, int newX, int newY, int newFacing) {
    maxOffSet in [0 .. maxLen()] and
    (
      not exists(int offSet |
        hasStopper(x, y, facing, offSet) and
        offSet in [0 .. maxOffSet]
      ) and
      move2(x, y, facing, maxOffSet, newX, newY, newFacing)
      or
      exists(int offSet |
        offSet =
          min(int offSet2 |
            offSet2 in [0 .. maxOffSet] and
            hasStopper(x, y, facing, offSet2)
          |
            offSet2
          ) and
        move2(x, y, facing, offSet, newX, newY, newFacing)
      )
    )
  }

  predicate cubeMove(
    int origCube, int origX, int origY, int origFacing, int offSet, int newCube, int newX, int newY,
    int newFacing
  ) {
    origX in [0 .. Cube::faceSize() - 1] and
    origY in [0 .. Cube::faceSize() - 1] and
    offSet in [0 .. maxLen()] and
    origFacing in [0 .. 3] and
    origCube in [1 .. 6] and
    (
      newCube = origCube and
      origFacing = newFacing and
      (
        origFacing = 0 and
        newX = origX and
        newY = origY + offSet and
        newY < Cube::faceSize()
        or
        origFacing = 1 and
        newX = origX + offSet and
        newY = origY and
        newX < Cube::faceSize()
        or
        origFacing = 2 and
        newX = origX and
        newY = origY - offSet and
        newY >= 0
        or
        origFacing = 3 and
        newX = origX - offSet and
        newY = origY and
        newX >= 0
      )
      or
      exists(int edgePos, int remaining |
        remaining >= 0 and
        (
          origFacing = 0 and
          edgePos = origX and
          remaining = offSet - (Cube::faceSize() - origY)
          or
          origFacing = 1 and
          edgePos = Cube::faceSize() - 1 - origY and
          remaining = offSet - (Cube::faceSize() - origX)
          or
          origFacing = 2 and
          edgePos = Cube::faceSize() - 1 - origX and
          remaining = offSet - origY - 1
          or
          origFacing = 3 and
          edgePos = origY and
          remaining = offSet - origX - 1
        ) and
        newCube = Cube::cubeMove(origCube, origFacing, newFacing) and
        (
          newFacing = 0 and
          newX = edgePos and
          newY = remaining
          or
          newFacing = 1 and
          newX = remaining and
          newY = Cube::faceSize() - edgePos - 1
          or
          newFacing = 2 and
          newX = Cube::faceSize() - edgePos - 1 and
          newY = Cube::faceSize() - remaining - 1
          or
          newFacing = 3 and
          newX = Cube::faceSize() - remaining - 1 and
          newY = edgePos
        )
      )
    )
  }

  int addFacing(int prevFacing, int step) {
    prevFacing in [0 .. 3] and
    (
      instrDir(step) = "L" and result = (prevFacing + 3) % 4
      or
      instrDir(step) = "R" and result = (prevFacing + 1) % 4
    )
  }

  cached
  predicate pos2(int i, int x, int y, int newFacing) {
    i = 0 and start(x, y) and newFacing = 0
    or
    exists(int prevFacing, int midFacing, int prevX, int prevY |
      (
        i = 1 and midFacing = prevFacing
        or
        midFacing = addFacing(prevFacing, i - 2)
      ) and
      pos2(i - 1, prevX, prevY, prevFacing) and
      moveBlocked(prevX, prevY, midFacing, instrLen(i - 1), x, y, newFacing)
    )
  }

  predicate finalPos2(int x, int y, int facing) { pos2(instrLen(), x, y, facing) }

  int code2() {
    exists(int x, int y, int facing |
      finalPos2(x, y, facing) and
      result = (x + 1) * 1000 + 4 * (y + 1) + facing
    )
  }
}

select 1

module TestCubeMap implements CubeMap {
  int faceSize() { result = 4 }

  /**
   * ..1
   * 234
   * ..56
   */
  int cubeFromPos(int x, int y, int cx, int cy) {
    result = 1 and x in [0 .. 3] and y in [8 .. 11] and cx = x - 0 and cy = y - 8
    or
    result = 2 and x in [4 .. 7] and y in [0 .. 3] and cx = x - 4 and cy = y - 0
    or
    result = 3 and x in [4 .. 7] and y in [4 .. 7] and cx = x - 4 and cy = y - 4
    or
    result = 4 and x in [4 .. 7] and y in [8 .. 11] and cx = x - 4 and cy = y - 8
    or
    result = 5 and x in [8 .. 11] and y in [8 .. 11] and cx = x - 8 and cy = y - 8
    or
    result = 6 and x in [8 .. 11] and y in [12 .. 15] and cx = x - 8 and cy = y - 12
  }

  int cubeMove(int cube, int oldFacing, int newFacing) {
    cube = 1 and oldFacing = 0 and newFacing = 2 and result = 6
    or
    cube = 1 and oldFacing = 1 and newFacing = 1 and result = 4
    or
    cube = 1 and oldFacing = 2 and newFacing = 1 and result = 3
    or
    cube = 1 and oldFacing = 3 and newFacing = 1 and result = 2
    or
    cube = 2 and oldFacing = 0 and newFacing = 0 and result = 3
    or
    cube = 2 and oldFacing = 1 and newFacing = 3 and result = 5
    or
    cube = 2 and oldFacing = 2 and newFacing = 3 and result = 6
    or
    cube = 2 and oldFacing = 3 and newFacing = 1 and result = 1
    or
    cube = 3 and oldFacing = 0 and newFacing = 0 and result = 4
    or
    cube = 3 and oldFacing = 1 and newFacing = 0 and result = 5
    or
    cube = 3 and oldFacing = 2 and newFacing = 2 and result = 2
    or
    cube = 3 and oldFacing = 3 and newFacing = 0 and result = 1
    or
    cube = 4 and oldFacing = 0 and newFacing = 1 and result = 6
    or
    cube = 4 and oldFacing = 1 and newFacing = 1 and result = 5
    or
    cube = 4 and oldFacing = 2 and newFacing = 2 and result = 3
    or
    cube = 4 and oldFacing = 3 and newFacing = 3 and result = 1
    or
    cube = 5 and oldFacing = 0 and newFacing = 0 and result = 6
    or
    cube = 5 and oldFacing = 1 and newFacing = 3 and result = 2
    or
    cube = 5 and oldFacing = 2 and newFacing = 3 and result = 3
    or
    cube = 5 and oldFacing = 3 and newFacing = 3 and result = 4
    or
    cube = 6 and oldFacing = 0 and newFacing = 2 and result = 1
    or
    cube = 6 and oldFacing = 1 and newFacing = 0 and result = 2
    or
    cube = 6 and oldFacing = 2 and newFacing = 2 and result = 5
    or
    cube = 6 and oldFacing = 3 and newFacing = 2 and result = 4
  }
}

string testInput() {
  result =
    "        ...#\n        .#..\n        #...\n        ....\n...#.......#\n........#...\n..#....#....\n..........#.\n        ...#....\n        .....#..\n        .#......\n        ......#.\n\n10R5L5R10L4R5L5"
}

module RealCubeMap implements CubeMap {
  int faceSize() { result = 50 }

  int cubeFromPos(int x, int y, int cx, int cy) {
    x in [0 .. 49] and y in [50 .. 99] and result = 1 and cx = x - 0 and cy = y - 50
    or
    x in [0 .. 49] and y in [100 .. 149] and result = 2 and cx = x - 0 and cy = y - 100
    or
    x in [50 .. 99] and y in [50 .. 99] and result = 3 and cx = x - 50 and cy = y - 50
    or
    x in [100 .. 149] and y in [0 .. 49] and result = 4 and cx = x - 100 and cy = y - 0
    or
    x in [100 .. 149] and y in [50 .. 99] and result = 5 and cx = x - 100 and cy = y - 50
    or
    x in [150 .. 199] and y in [0 .. 49] and result = 6 and cx = x - 150 and cy = y - 0
  }

  /**
   * .12
   * .3.
   * 45.
   * 6..
   */
  int cubeMove(int cube, int oldFacing, int newFacing) {
    cube = 1 and oldFacing = 0 and result = 2 and newFacing = 0
    or
    cube = 1 and oldFacing = 1 and result = 3 and newFacing = 1
    or
    cube = 1 and oldFacing = 2 and result = 4 and newFacing = 0
    or
    cube = 1 and oldFacing = 3 and result = 6 and newFacing = 0
    or
    cube = 2 and oldFacing = 0 and result = 5 and newFacing = 2
    or
    cube = 2 and oldFacing = 1 and result = 3 and newFacing = 2
    or
    cube = 2 and oldFacing = 2 and result = 1 and newFacing = 2
    or
    cube = 2 and oldFacing = 3 and result = 6 and newFacing = 3
    or
    cube = 3 and oldFacing = 0 and result = 2 and newFacing = 3
    or
    cube = 3 and oldFacing = 1 and result = 5 and newFacing = 1
    or
    cube = 3 and oldFacing = 2 and result = 4 and newFacing = 1
    or
    cube = 3 and oldFacing = 3 and result = 1 and newFacing = 3
    or
    cube = 4 and oldFacing = 0 and result = 5 and newFacing = 0
    or
    cube = 4 and oldFacing = 1 and result = 6 and newFacing = 1
    or
    cube = 4 and oldFacing = 2 and result = 1 and newFacing = 0
    or
    cube = 4 and oldFacing = 3 and result = 3 and newFacing = 0
    or
    cube = 5 and oldFacing = 0 and result = 2 and newFacing = 2
    or
    cube = 5 and oldFacing = 1 and result = 6 and newFacing = 2
    or
    cube = 5 and oldFacing = 2 and result = 4 and newFacing = 2
    or
    cube = 5 and oldFacing = 3 and result = 3 and newFacing = 3
    or
    cube = 6 and oldFacing = 0 and result = 5 and newFacing = 3
    or
    cube = 6 and oldFacing = 1 and result = 2 and newFacing = 1
    or
    cube = 6 and oldFacing = 2 and result = 1 and newFacing = 1
    or
    cube = 6 and oldFacing = 3 and result = 4 and newFacing = 3
  }
}

string realInput() {
  result =
    "                                                  ........................................#............##.......##......#...........#..........#......\n                                                  ...................#..#.......#..................#......#...................#.....#.......#.....#...\n                                                  #......#................#......................#.......#...............#.......##.#.................\n                                                  .#......#.................#........#..#.................#.....#............##.......................\n                                                  ............#.........#.#......#..............................#..........#......#.........#....#..#.\n                                                  ....#.........#....#..#.............#..........#....#.................#............#................\n                                                  #...#........#....#..#.....#..........................................#......#........#.............\n                                                  ....................#...#.##........#.#.....###........##.......#..#....................#...........\n                                                  #.........................................................#..............#.....#..............#...#.\n                                                  .........##.#...#.................#..............#..........................##.....#................\n                                                  .#.................#.#...............#.#..#...........#.......................#...........#.........\n                                                  ....#.............#...#................#....#.#...........#.........#.......#...................#...\n                                                  ..............#........#............................#.....#...#....#................................\n                                                  ..............#..............#...........##..#............................................#.........\n                                                  ........##..................#........................#.....#........................................\n                                                  ............................#.##....#..........#.....#......#.................#....#..............#.\n                                                  ................#........................#..##.....#..............................#.................\n                                                  ..#.....#......................#...#............#............................#.....#...............#\n                                                  .#.#..#.#...............................#..........#.#......#......#............................#...\n                                                  .............#.......#.#...##.................#..#.#............#.........#.....................#...\n                                                  ..........................#.#.#....#...#....#....#........#.........................................\n                                                  ......#...#....#...........#....#..#.#.#...#.....##...........#...............#.......#.##..........\n                                                  ......#....#...#..#......................#.......................#...................#.....#...#....\n                                                  ....................#..................#..............#..##..#.......#........#.............#.......\n                                                  ...............#........#................#...#.........#..#...............#................#.....#..\n                                                  ....#...................#........#....##.....#..........#...#.##..................#..#.............#\n                                                  ......#..............#.....#..#.......##.....#..#.....#.............................................\n                                                  ................#..........#.....#..............#......#.....................#..............#.......\n                                                  .....#...........................#....##............#.....................#..#.#.....#..#...........\n                                                  ............................#.#.#.......#...##..................#..................#..............#.\n                                                  .............#..#.#...........#.#...........#........#...#.....#...........#.............#..........\n                                                  ..............................#......#........#.#.....##..........................#....#.....#.#....\n                                                  ...#.............#.............#...........#....#.#......#...#......................#......#........\n                                                  ........#....#...#..............#....#.........#.........#.........#....#...............##.........#\n                                                  #...#.....#...#....................#...#.....#............#.#................#.........#...#........\n                                                  ..........#.#...........#......#........#........#..#.##.#.........#........#.........#.............\n                                                  .....#....#..........................................................##.#...#.............#........#\n                                                  ..............#......#................#.#..............#...#......#.........##.................##...\n                                                  ........#....#.##....#...........................#.................#...#.......#.....#.#............\n                                                  .........................#.......#....#......#...#..#.........#.........#.....................#.....\n                                                  ..................#........#........#.#.............#.........#...........................#.....#.#.\n                                                  .....#..........................#.....#....#....#.........#....................#....................\n                                                  ..#..#............#.#....#.......#..............#.....#........................#..........#......#..\n                                                  ..............#...#......#................#...........................................#........#....\n                                                  ..#....#..................#....#..................#........#....##......#..............#.##.........\n                                                  .......................#....#.............#.........#....#.......#............#.............#.......\n                                                  ......................#..#.............#....#..............#.............#.#.#.............#........\n                                                  .#...........#..............................................#.................#..........#.#.#......\n                                                  ........#......#..#..#.#........#.#....##.........#...............#.....#.......#.#..........#....#.\n                                                  .............................#....##............#.#.##.............................#................\n                                                  ........#....................#........##..........\n                                                  ..#.........#....#.....#..#......#........##......\n                                                  .....##...........................#...............\n                                                  ...................#..#.................#.........\n                                                  .#...........................#...#.....#..........\n                                                  .................#......#.......#.................\n                                                  .#......#....#...###..........##.................#\n                                                  ....#.#........................##...............#.\n                                                  ............#...............#.......#.#.....#.#.##\n                                                  ...............#....#...........#........#........\n                                                  ..#.........#.....#............#...#.......#..#...\n                                                  #..#..............#......#........................\n                                                  .....#........#.........................##....#...\n                                                  .#....#...#...#............#.....#...............#\n                                                  .#..#.......##.............#..#......###......##..\n                                                  .#.....#..#.................#..#...#....#.......#.\n                                                  ..#.........#.................#.........#.........\n                                                  .....#...........##........#......................\n                                                  .............#............................#..#....\n                                                  ...........#.....#............#...................\n                                                  ...#..............#....#..........................\n                                                  ...#....................#...................#..#..\n                                                  .............#...#..........#.#...................\n                                                  ........#..........#...#..........................\n                                                  .#................##...........#......#..#.#......\n                                                  ......#...#.#...............#..#..................\n                                                  .....#..............................#.............\n                                                  .......#..#..##........#.........#....##.......#..\n                                                  ..#...........#............#.............#........\n                                                  #...................#.##..#....#......#..#........\n                                                  ...............#.......#..#.#........#............\n                                                  ........#..........#........#.#...................\n                                                  ........#.........................................\n                                                  #.....#.......##.............#....................\n                                                  ............#.......#.............#......#........\n                                                  ...........#.......................#.....##.......\n                                                  .#......#.#......#...#..#.#......#.#..........#.#.\n                                                  .#.....#......#.................#.#...............\n                                                  ........#....................##......#......##....\n                                                  #.......#.......................##................\n                                                  ............#.#........#....#.....#.....#.#.#.....\n                                                  .....#..........................................#.\n                                                  ..#..###...........#......#............#..........\n                                                  .......#..............#...#...#...#..............#\n                                                  ...#..............#...............#..#.#..........\n                                                  .........#...........#...#........#..#.#..........\n                                                  .#.....#.....#..............#......#........#..#..\n                                                  ......#.............#........#....#...............\n                                                  .......................#.............#..#..#.....#\n                                                  .....#.....#.........................#....#.....#.\n.##..#........#...................................#.#...................................#...........\n....#...#.................#..#.........#...............#..................#......#...#......#.......\n#..#........#......#..............................#.#..#.......#.........#...................#......\n......#.......#................#..............#.....#........#..#..#........##...........#..........\n....#..#...#..#.#..........#...........#.#..#.........#............##....#..............#...##.#....\n..............#......#..#.........#............#..#......#..................#......................#\n......................#.....#.......#...............................................#.....#...#.#...\n..............#.....#.......#.....................................#.......................#........#\n............#........#....................#....#.##.....#.......#.....#............#..#...#.........\n.....##..#..........#.......................#.#....#...........#..................#.................\n.....................#..#.....#.#....#...#..#........#.##.....#....................#..............##\n.#.............##..........#............#....#.....###............#............#...#.#.......#......\n.###.#..................#.......#....#.....#....#.....#....#.........................#....#.........\n.........#..............................#.......#......#...#.....#..#.......#..............#........\n.......##......#............##.....#................................................#....#.....#....\n..........#.....#................................................#.#..........#...#.#...#...........\n......................................#...#......#.....#.......#.#...#........#..#..................\n.#.....#...#.........#..#.................#.#......#.#.....................................#...#....\n#.#...........#..........................###.......#.........#...#..#.........#..#..#.....#.........\n.#........#...##...............#....##...............##.......#......#..#...#..#.#..................\n#.....##................#..#.#.#.##.........#........#..............#.......................#.......\n...........#.............#.........#..........#..................#..#..........................#....\n............#...........................##...........................#.....#........................\n.#....#..#...##......................................................................#..............\n...##....#...#......#..............#..................#........#...##.........#.....................\n..............#..........#....#.................#..#....##..........#...............................\n................................................#....................#........#.#...................\n....#.................#......#.......#........#...##..........#.................#...........#.......\n.......#....................#.........#........#....#...#...#...#........................#.#........\n.....###..##........................#..............................#............##.......#..........\n...#..#.........................#...#..............#...#.......#..#.#.....#............#........#...\n.....#...........#...#.........#..........#.........#................................#......#......#\n...#..#............................#..........#....###.#...#.......#.#........#...............#.....\n................##.#..#...#.......#.....##.#..#......#...#....#......#....###.#....#................\n..............##.........................#.......#............................#.....#.##..........#.\n...........#..##.............#..#....##............##.....#......#.....................##.....#.....\n.....#.............#..##....................#............#......#............#.......#..##.#........\n..............#...........#...................#.................#....##...........#.................\n..#...................#.......##.....#...#..#........#.#....##.....#.................#.........#.#.#\n......#..................#....................#.......#.#...#........................#.#..........#.\n..##..............#.........#......#......#..........#..#.#.........#..#......#....#....#...........\n............#.......................#...................#.....#...#.................................\n.#....#.............##....##.............#.....#....#.....#..........#.......#...#........#.........\n..#.........#.......#............................#.......#....#.....#..............#.....#..........\n......#........#.#....#...........#.....#...#......#......#...............................#.....##..\n..................#.......##............#.......#......#......#..#.....#.............##......#......\n........#.#..........#........###.#....#....#......#..................#........#..........#.........\n....#........#...................................#.#.....#...##..............#...................#..\n.................................................#.......#.............#.........#.........#........\n............#.......#..................#...#..##............#..#.....#...##.#.#.........#...........\n......................................##......#...\n....#...........#...............................#.\n..#.......#...............#...#.......#.....#...#.\n...................#.....#.#..........#..#........\n..................................................\n..#..#.##.......#......#.....#.#.....#............\n.....#.....#.......#.#................#...........\n...................#......#........##.#..#........\n.....#.........#.........................#........\n.#...#............................#...............\n.....................#..............#..#.........#\n..#...................................#...#.......\n.........#....#.#.......#...#..........#..........\n......#..........#...........#.........#.......#..\n..............#......#............................\n.....#..#...#....#.............#........#..#......\n................#...........................#.#...\n.....#.......##.#.................................\n...........#.....#............#......##.#.........\n..................................................\n.##............................#................#.\n.........#....................#.#......#..........\n...#.......##.#....#..............................\n.....#...........#........##....#...#.#..........#\n#......#..............#..#.....#.......#.......#..\n.................#..#.#....................#....#.\n......#....#.#.##...#............#.#......#...#..#\n..#............##..#.#..............#.#........#..\n.....................#...........#.........#......\n.....##.............#.............................\n...#.....#........#.......#........#..............\n.............#....................................\n...#............#..#..............#..........#....\n.#............#............#..............#..#.#..\n.............#...........#....#.................#.\n....#...........................#.................\n...............#..........................#.....##\n..............#..#......#.#.......#..............#\n.....#..........#.........#............#......##..\n...#...#..............#...........#.#...##.....#.#\n...................#....##.......#.#............#.\n.....#.....#....##......#.............#...........\n............##.......##....#..#..............###..\n..............................#.#....#.........#..\n.......#...............#...#...............#....##\n.......................#...#......................\n..............###..........#............#.....#...\n......#...........#.........#..#..................\n......#..........##........................#..#..#\n....#..............#..............................\n\n26R43R26L32L35R26L50R46L27R37R31R1R32L5R34L2R30L41L47R48L49L5L24L19R49L3L7L34R36R43R28R3R25R20L20R41R46R13L46L17R7R16L14R47L19L29R50R34L22R32R49L21R46R32L10R7L5L47R32L32R46R46L29R6R47L25L36R32L37L37L24R8L44R31L20L24L48L24R32L19L42R43R38L16R20L13R3L30L39L20R8R50L45R44L44L14L5R35R3R5R35L39L41L42R5R6R46L8R4R15L49R5R20R4L25L50R3R23L5R30L27L2L8L2L41R12L34R23L38L19L17R13L42R47L14R33R10R42L2R2R49R47L4R1L38R14L7R3R11R16R34R23R13R33L47L9L20L40R15R2R45L46L3L29R25L13R13R4L48R33R43R50R1R27L13R2L22R2R30L38R44L14R30R19L33L28R21R25R31R22L46L17R28R4L36R24L34R7L29L15L49R35L23R26R23L15L38R19R44L10R18L30L6L14L23L13R45L5L18L23L26L17L22R18L8L31R25L6L22R29L38R3R17R3L5L16L22L45L44L20R36R25L15L19R33R49L12R26L18R32L36L45R20L12L30L45L38R14R9R20R31L28R45L39R39R41R40L30R16L45R11L39R20R33L35L10L33L18L6L19R39R26L11R11L11R10L23R34R40L43L19L14L35R38L29L42L35R9L49R19R2L24R11L47L43L33L28L1R41L26R31R11R35R21L13L46L12R16L3L44R2R32R47R18L9L22L6R4L42R50R27L2L5L24R46L30L36R13R13R13L35L35L47L19L48R1L3R14R43R47L11R1R37L2L34R29R44L34R49L40L45R21L6L13R19L29R1L36R24R37L14R34R17R33L26R2L31R36L1R18L39R50R40L40L1L25R13L18L34L40L26L30R29R47L28L1L27R44L8L30L2R49R13R31R50L8L46L20R3L42L16R9R24R32R6L23R30L31L19L40R27L48L50R46R38L25L31L3L23R27L22R15L32L35R18R18L16L40L43R11R16R45L44L14L37L4L26R13L33R31L16R13R33L10R38R24R4R3R3L19R3L43L10L11R39R50L42R41L33R4R33L20R39R8R18R20R29R36R16L12L4R46L25R10L43L29R34R6L29R11R43L8R14R23R4R1L26R5R39R22R29L36R37L50R46L29R32L22R21L29L2R12L42R5R22L5R23R28R49R45R37L12R36L44R18L42L12R40L8L23L12L20L39R7L26L20L25R40R21R38L23L40L34L7L32R49L3R44L2R40L2R21L33R11R38R29R18L3L48L17L42L44R26R47R5L19R25R40R44L24R3R26R14L30L23R18R46R3R48L18R39R47L39R18L32R31R32R28L44L38R21R46R38L11L38L6L45R3L29L42R34R50R38R29L42L18R38R34R47R9L11R4R42R44R1L16L41R44R33R8R9R20R34L2R20R2R35R37L30R36R35R30R30L7R42L17L23L49L7L8R12L21L15L14R7R12R14R47L12L22L20L47L19R38R50R33L2L33L40R19L27L20L33L40R26R15R27L3L19L28R46L25L17L9L12L15R12L45L34L4L49R47R19R48L45R34L16L28L33R25L27L48L3L20L11R10R45L38R36R12R14R10L35R22L32R36L3L3L26R5L8R29R38L34R5R19L21L2R8L46R43L25L48R16R39R18L22R16R19L13L2L24L12R6R17R30R28L31L26R40L39R24L2R47R30R19L14R21L35R2L26L14L12L47R23R9R12L28R13R21L31L46L20L15L41L3R5L22R1R44L49L12L38L31R33R22L42L1L19R15R49R31L12L30R47R24L46R13R35L27L19L33R21R11L26L27R25L46L1L29R4R45L33L36L12R31R16R22R17L10R16L36L21L15L27R37L22L21R50R37R12L37R17R26R5R22R38L33R18R28L32L11R43R49R50L45L9R6R30L1R50L24L24L22R46R4L35L50L28R12L33L44L1L37L42L28L3L6R18R31L43R48R41R49R37R49R23R20L7L21L37L35R23L8L50L4L3R39R11R1L41R16L50L49R50R24L19R17L35R3R36R38R4R29L50L44R38R5L16L49L4L49L23L30R8L12L12R12R24L21R3R50L47L2R16R27L29L38L2L30R26L13L2R4L1R50L25L27L13L9L49R36R11L48L39R35R24L29R24R46R15L3L6R47L33R1L24R31R43L10L34L35R20R16L15R33R19L38R14R41L45L49L17L31R15R18R20L22R12L22L4L1L47L38R4L21R41R30R18L29R41R6R7L19L17R3L10R23R15R23L38L23R38R46L26R16R50R49R2L28R27L7L27L15R4R40R21L19L28L36R39R46R3L50R50R30L12L15R36R13R30R9L2L6L36R46R39L13L34R2L13L4R31R50L8R17R50L9L35R14R50R41L26R27R22L45R14R43R50R47R32L44R6L5L13R34R14L27L37R44L17L35R18L40L8R31L34L3R2L21L4L26R47R11L29L2L15R18R30L27R46L17L21L33R21R13R15R36L16L23R36R8L36R7L31R32L36L15R17L10L21R24L5L2R45R29L42R25L38R22L27R33R15R47R19L12L29L43L32L13R19L2R29R22R46L31L40L33L27R37R4R11L9R1L38R10L26L35L41R15R13R50R10R39L15R49R1R21R23L22L28R39L1L14L26L24R48R49L40L2R24R2R7L20R25L47R37L46R1L28R38R18R21L13R3L14L2R34R34R27L48L31L28L25L29R45L19R33R41L14L36R20R13R43R35L9R13R3L47L5R49L26L46R24L6R31L4L33R48L27L19L40L39L48L46R44R48R43L50L33L30R39R48L18L48L48R47R38L33L8L16L10L25R47L6L4L41R36R1L21R23R49R2L7R13L50R37R18L46L42L45R5L1R2R39R22L36L43L13R1L20L9L43L6R18R46L31L2L6R35R3L41R35R4R36R4L23R37L50R18R24R16R16R35L2L23L1L3R40L37L41R24L43L38L46R21L35L15R6L48R32L42R33L13L39R38L17L2L34L7L1R31L28R30R14L25R46L42L50L43R36R40L15L40L32R48R34L30R34R46L8R24L2R13L30L27R2R3R25L40R1R4L3R30R44R13R6R22L18R23L40R16L40L31R39R15L14L12R49L38L34L13L26R50L21L4L18R37R38L38R35L9R15L21R14R15R10L38L8R4L47L4R36L25R46R43L9R42R19L36L17L29L21L2R10R29L40R33R37L50L44L9R29R6L6R22L47R14R35R20L28L38L45L26L50L12R23R14L30L45L37R35R14R14R35R19L22L5L3L7L32R41L12R16R33R37R20L18R32R42R34L21L32R38R49R13L37R16R26L47L8L48R50R17L39L9L3L2R48L34R46R17L10R26R44L8R8R50L45L13R9L32R22L23L12R49L37R20L11R9R22L32L49L5L14R34L5R9L43L45L31R17L19R35R8L41R32L11R7L16L9R13L16R18L25R7L21R28R46R43L13R33R29R31R20R42L17L45R41R39L32R40L8L47R7L35L21R46R3R23R45R29L35R37R1L41L50L48L18L4L13L36R1L4L9R28R26L11R34R43L5R5R27L25R15L16R30R14R43R30L24R18L26R18L10L6L40R4L18R28L32L37L15L3R47L29L36R39R49L10L12L34L13L17L12R50L3R35R42R38L26L36L18L9R43L19R21L29R21L5L12L47L32L49L36L37R48R32L18L34R41R13R50L46L23R20L46L3R16R20L47R44L43L47L48L32R29L16L45L15R39R22R33L13R7R9L34R31R48R50R32L25R47L9L6R36L44L35L29L48R28L35R32L2R20L27R5R36R29R32R9L39L4L11L25R36L21R42L33L4R28R32L24R10R21R13L5L16L44L22R30L27L5L1R5R46L27R38R21R36R31L50R9L20R11L24L4L30R16L33L15L27R1R8R25R39L19L28R20L38L28L42L25L22R9R17R48L13L36R10R29R31L8L28L40R21R25L29L7R39R35R16L30L28L23L14R19L31L44R28R8L49R28L44L2L34L36L44L39L46L31L24L49L36L24L42R44R49L22L4L2R17R11L3R25R45R18R38R34L17L16R1L8R48R7L7R25R18L2R1R24R10R48R9L29R18R7R30L14L26L50L31R4L23R7R44L22L50L14R19R37R29R40L4R11L11L18L47R8R39R48R19L14L17L8L7R49R6L26R7L18L18L1L13R15R29L30R36L19R33R41R17R3R19L47R27L29R31R33R36L13R31L2R18R35R21R25R40R43L4L36L38L23R32R39L50R14L40R2L3R1R47L41L36L33R28R44R29R38L18R33R33L42L27R13L37R48L15L25R45R25L22R35L22R50R20L48L24L22R24L45R35L10R19L43R23R40L22L24R26R26L6L10L32L10R44L36R29L24L2L26L25R37R20L32R43L22R44L43R1R18L11R26R38L34L22R49L14R6R39L44L49R8L34L27R13L21R37L41R21R40L20L24R6R50L6R30L33L38L13L33L44L23L50L17L1R1R4L30R4L35R3R13L10R50L27L1R14R2L15L22L33L28R30R7L10L33L11R15R42R6L22R11L38R1L23R19R24R40L43L42R26L31L43R38R32R12L3R37L15L14"
}
