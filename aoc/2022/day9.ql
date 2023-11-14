import lib

module Impl<inStr/0 input> {
  string move(int i) { result = Helpers<input/0>::lines(i) }

  string dir(int i) { result = move(i).charAt(0) }

  int times(int i) { result = move(i).suffix(2).toInt() }

  int stepBefore(int i) {
    i = 0 and result = 0
    or
    result = times(i - 1) + stepBefore(i - 1)
  }

  int stepAtTime(int t) { t in [stepBefore(result) .. stepBefore(result + 1) - 1] }

  string dirAtTime(int t) { result = dir(stepAtTime(t - 1)) }

  predicate headPos(int t, int x, int y) {
    t = 0 and x = 0 and y = 0
    or
    headPos(t - 1, x - 1, y) and dirAtTime(t) = "R"
    or
    headPos(t - 1, x + 1, y) and dirAtTime(t) = "L"
    or
    headPos(t - 1, x, y - 1) and dirAtTime(t) = "U"
    or
    headPos(t - 1, x, y + 1) and dirAtTime(t) = "D"
  }

  predicate tailPos(int t, int x, int y) { knotPos(t, x, y, 1) }

  int numKnots() { result = 10 }

  predicate knotPos(int t, int x, int y, int k) {
    t = 0 and x = 0 and y = 0 and k in [0 .. numKnots() - 1]
    or
    k = 0 and headPos(t, x, y)
    or
    exists(int prevX, int prevY, int headX, int headY |
      knotPos(t - 1, prevX, prevY, k) and knotPos(t, headX, headY, k - 1)
    |
      headX = prevX + [-1, 0, 1] and
      headY = prevY + [-1, 0, 1] and
      x = prevX and
      y = prevY
      or
      headX = prevX and headY = prevY + 2 and x = prevX and y = prevY + 1
      or
      headX = prevX and headY = prevY - 2 and x = prevX and y = prevY - 1
      or
      headX = prevX + 2 and headY = prevY and x = prevX + 1 and y = prevY
      or
      headX = prevX - 2 and headY = prevY and x = prevX - 1 and y = prevY
      or
      headX = prevX + 2 and headY = prevY + [1, 2] and x = prevX + 1 and y = prevY + 1
      or
      headX = prevX + 2 and headY = prevY - [1, 2] and x = prevX + 1 and y = prevY - 1
      or
      headX = prevX - 2 and headY = prevY + [1, 2] and x = prevX - 1 and y = prevY + 1
      or
      headX = prevX - 2 and headY = prevY - [1, 2] and x = prevX - 1 and y = prevY - 1
      or
      headX = prevX + [1, 2] and headY = prevY + 2 and x = prevX + 1 and y = prevY + 1
      or
      headX = prevX - [1, 2] and headY = prevY + 2 and x = prevX - 1 and y = prevY + 1
      or
      headX = prevX + [1, 2] and headY = prevY - 2 and x = prevX + 1 and y = prevY - 1
      or
      headX = prevX - [1, 2] and headY = prevY - 2 and x = prevX - 1 and y = prevY - 1
    )
  }

  predicate tailSaw(int x, int y) { tailPos(_, x, y) }

  predicate longTailSaw(int x, int y) { knotPos(_, x, y, numKnots() - 1) }

  int seenCount() { result = count(int x, int y | tailSaw(x, y)) }

  int longSeenCount() { result = count(int x, int y | longTailSaw(x, y)) }
}

select Impl<testInput/0>::seenCount(), Impl<realInput/0>::seenCount(),
  Impl<testInput/0>::longSeenCount(), Impl<realInput/0>::longSeenCount()

string testInput() { result = "R 4\nU 4\nL 3\nD 1\nR 4\nD 1\nL 5\nR 2" }

string realInput() {
  result =
    "D 2\nR 1\nL 2\nU 1\nR 2\nL 2\nR 2\nL 1\nR 1\nL 1\nR 2\nL 2\nR 1\nD 2\nU 1\nR 1\nL 2\nU 2\nR 2\nU 2\nR 2\nD 1\nL 1\nU 1\nR 2\nL 1\nD 1\nU 1\nL 1\nU 1\nD 2\nU 1\nR 2\nU 1\nL 1\nD 1\nL 1\nU 1\nR 1\nL 1\nU 2\nL 2\nD 2\nL 2\nR 2\nU 1\nR 1\nU 2\nD 2\nR 2\nL 1\nR 1\nD 1\nU 2\nR 1\nL 1\nU 2\nL 2\nU 1\nL 2\nU 1\nR 1\nL 1\nD 2\nU 2\nR 2\nD 1\nR 1\nU 2\nR 2\nL 2\nU 1\nL 1\nD 2\nR 2\nL 1\nR 1\nD 1\nR 1\nL 1\nD 2\nR 1\nU 1\nL 1\nR 1\nL 1\nD 2\nL 1\nU 1\nR 1\nD 1\nR 1\nD 1\nL 2\nU 1\nD 1\nR 2\nD 2\nR 2\nL 2\nU 2\nL 1\nU 1\nL 1\nR 1\nL 1\nU 2\nL 2\nU 2\nL 1\nU 1\nD 1\nU 3\nR 2\nD 2\nR 1\nU 2\nL 2\nD 1\nU 1\nR 2\nU 3\nD 1\nL 3\nU 2\nD 2\nR 1\nD 1\nL 1\nD 2\nL 2\nU 1\nL 2\nR 3\nU 3\nL 1\nU 3\nL 1\nD 1\nU 3\nR 1\nU 3\nD 2\nL 3\nR 3\nL 2\nU 1\nD 1\nU 1\nL 1\nD 1\nR 2\nU 3\nD 3\nL 3\nR 1\nU 3\nD 1\nU 3\nL 1\nD 3\nR 3\nU 2\nD 1\nR 2\nU 1\nR 3\nU 1\nD 1\nU 1\nL 1\nR 3\nU 2\nD 3\nU 2\nR 2\nL 1\nD 3\nR 3\nL 2\nU 1\nL 2\nU 2\nR 3\nU 3\nD 2\nU 2\nD 3\nR 1\nD 1\nR 3\nD 1\nL 3\nR 2\nD 1\nL 1\nD 1\nL 3\nD 1\nL 3\nD 2\nL 2\nD 2\nR 1\nU 2\nD 1\nU 3\nL 3\nD 1\nR 3\nL 2\nD 2\nU 2\nR 1\nU 2\nR 3\nL 1\nR 3\nL 1\nD 1\nU 2\nL 3\nU 3\nR 2\nL 1\nR 2\nU 4\nR 1\nU 2\nL 2\nD 3\nU 1\nL 2\nU 1\nL 2\nD 3\nU 1\nD 3\nU 1\nD 3\nL 2\nR 1\nL 3\nR 2\nU 2\nL 2\nD 3\nL 2\nU 3\nR 4\nL 3\nD 4\nL 3\nU 2\nL 2\nU 4\nR 2\nD 4\nR 1\nD 4\nU 4\nD 3\nR 2\nD 4\nU 1\nD 4\nU 4\nR 2\nD 3\nR 4\nD 2\nL 2\nR 4\nL 1\nD 2\nU 4\nR 4\nU 4\nL 4\nU 2\nD 3\nL 3\nU 3\nR 1\nL 2\nD 2\nL 3\nR 2\nU 3\nD 4\nL 1\nD 4\nU 3\nL 3\nU 4\nD 1\nU 2\nD 4\nL 4\nD 3\nR 3\nU 1\nL 4\nD 2\nR 4\nU 4\nL 4\nU 3\nL 4\nR 3\nD 3\nL 1\nU 2\nR 1\nU 2\nD 3\nU 4\nL 1\nD 2\nU 1\nD 1\nL 1\nD 1\nU 1\nD 3\nL 1\nD 4\nL 2\nR 3\nL 2\nR 4\nL 4\nU 2\nR 3\nL 2\nD 3\nL 2\nU 2\nR 3\nU 1\nD 3\nU 5\nD 4\nU 3\nL 1\nD 4\nU 3\nD 2\nL 1\nR 3\nU 5\nL 5\nR 1\nD 2\nR 2\nD 3\nL 4\nD 4\nU 2\nD 3\nR 5\nD 3\nU 2\nD 4\nL 1\nD 5\nR 2\nD 1\nU 2\nL 1\nR 5\nU 4\nL 5\nD 2\nU 4\nD 5\nU 4\nL 4\nU 3\nD 2\nL 2\nR 2\nD 1\nU 1\nR 5\nL 3\nR 4\nD 5\nR 5\nD 4\nL 1\nR 2\nU 3\nR 5\nD 5\nR 3\nD 1\nR 3\nD 2\nU 4\nD 1\nU 5\nL 1\nU 3\nL 3\nD 1\nR 3\nU 1\nL 3\nR 2\nL 4\nR 4\nU 1\nD 5\nR 2\nL 5\nR 5\nU 3\nD 1\nR 4\nD 5\nL 5\nR 4\nU 5\nR 4\nD 3\nR 4\nD 2\nR 2\nU 1\nD 2\nL 1\nR 1\nL 3\nD 3\nL 5\nD 4\nR 5\nD 2\nL 5\nU 3\nR 3\nL 5\nU 3\nL 5\nR 5\nL 2\nU 4\nD 2\nR 1\nL 5\nR 1\nU 5\nL 2\nR 2\nU 6\nL 6\nU 2\nR 5\nU 3\nR 2\nD 3\nU 3\nD 1\nL 1\nU 2\nR 5\nL 1\nR 5\nD 6\nR 4\nL 4\nU 1\nR 3\nD 5\nU 3\nL 6\nU 1\nD 6\nR 6\nL 4\nR 4\nU 6\nR 6\nU 3\nR 6\nU 2\nR 6\nU 4\nR 2\nL 5\nU 2\nD 6\nL 4\nU 5\nL 4\nR 6\nL 1\nR 3\nL 3\nD 1\nL 5\nD 1\nL 5\nR 2\nD 3\nL 1\nU 6\nR 6\nU 2\nL 3\nR 4\nU 6\nR 3\nL 4\nU 1\nR 1\nD 1\nL 4\nD 6\nU 1\nR 2\nL 6\nU 3\nR 1\nL 1\nD 3\nR 1\nU 4\nD 2\nL 1\nD 3\nR 2\nD 5\nL 3\nR 6\nU 4\nD 4\nL 4\nU 2\nD 2\nL 4\nD 6\nU 5\nD 5\nR 6\nD 1\nL 4\nR 2\nU 3\nD 5\nR 4\nU 6\nR 4\nU 6\nL 7\nU 6\nD 1\nU 2\nD 6\nR 4\nU 7\nD 2\nL 6\nR 2\nU 7\nR 7\nL 1\nU 2\nL 5\nR 4\nL 7\nR 3\nD 5\nU 7\nD 4\nL 6\nU 5\nL 4\nD 2\nU 2\nD 2\nU 5\nR 7\nD 3\nU 3\nD 6\nU 4\nD 2\nR 6\nL 5\nU 3\nR 1\nD 7\nR 7\nU 4\nR 7\nU 2\nR 1\nL 4\nU 6\nL 1\nD 1\nU 3\nR 7\nU 1\nR 3\nL 3\nR 2\nU 6\nL 6\nD 7\nL 7\nR 3\nU 5\nL 5\nD 4\nL 7\nR 5\nU 7\nD 5\nR 2\nU 2\nL 4\nU 4\nD 5\nL 6\nR 3\nD 4\nU 3\nD 6\nL 5\nU 1\nL 4\nR 2\nL 2\nU 7\nR 4\nU 4\nL 4\nD 1\nU 1\nD 3\nU 3\nD 3\nR 6\nL 5\nR 6\nD 1\nU 4\nL 5\nU 2\nD 6\nL 1\nU 5\nD 5\nR 5\nD 1\nL 4\nD 2\nU 1\nR 3\nU 3\nL 3\nD 5\nU 2\nR 4\nU 1\nD 8\nR 2\nU 4\nL 4\nD 8\nR 2\nU 6\nD 4\nR 5\nU 4\nR 2\nL 2\nU 4\nD 8\nR 7\nL 5\nR 5\nU 6\nR 6\nU 7\nD 2\nU 6\nD 1\nR 5\nU 1\nD 6\nR 7\nL 1\nR 1\nD 1\nR 3\nD 8\nR 1\nU 2\nL 4\nR 4\nL 6\nR 2\nU 7\nR 1\nL 3\nD 1\nL 3\nU 7\nR 8\nL 7\nD 1\nR 1\nL 7\nD 7\nU 5\nD 5\nL 1\nU 7\nD 7\nR 5\nD 5\nU 5\nR 6\nL 8\nR 6\nL 1\nR 3\nD 1\nL 2\nU 7\nR 5\nL 4\nU 3\nL 6\nU 6\nR 6\nL 4\nU 6\nR 5\nU 2\nR 7\nU 8\nR 5\nU 2\nR 4\nL 5\nR 1\nD 4\nL 8\nR 3\nL 2\nU 7\nR 4\nL 6\nR 5\nU 2\nL 3\nD 8\nR 8\nD 7\nL 4\nD 4\nR 6\nL 7\nU 8\nL 5\nR 4\nD 4\nR 8\nD 2\nL 7\nD 6\nU 3\nL 4\nR 6\nU 8\nL 2\nR 6\nL 7\nU 4\nL 3\nD 2\nR 8\nU 3\nD 2\nU 5\nR 7\nD 7\nL 6\nU 8\nD 6\nU 5\nD 6\nU 2\nL 7\nR 4\nL 9\nR 2\nU 3\nR 7\nU 6\nL 3\nU 8\nL 9\nU 5\nR 1\nL 5\nD 5\nR 8\nL 3\nU 1\nL 2\nD 5\nU 1\nD 8\nU 5\nD 7\nL 9\nU 6\nD 4\nR 5\nU 3\nL 1\nD 9\nR 4\nD 7\nU 2\nR 2\nD 4\nL 2\nU 9\nR 7\nU 1\nR 2\nD 7\nR 3\nD 6\nL 7\nU 5\nR 9\nU 4\nL 7\nR 5\nU 7\nL 4\nD 4\nR 9\nD 5\nL 5\nD 1\nR 2\nD 6\nL 8\nU 8\nL 6\nD 7\nL 5\nU 2\nL 3\nD 9\nU 8\nD 3\nL 8\nR 2\nD 7\nR 5\nD 3\nU 1\nR 3\nL 9\nU 3\nD 2\nL 4\nD 7\nR 8\nU 7\nD 5\nU 5\nR 7\nL 8\nD 7\nL 7\nD 8\nU 5\nR 9\nU 10\nR 5\nU 6\nR 7\nD 9\nL 2\nR 1\nD 2\nR 9\nL 4\nU 4\nR 5\nD 9\nU 4\nL 7\nD 9\nL 4\nD 4\nL 10\nU 9\nL 8\nR 10\nU 9\nL 10\nU 2\nR 8\nL 2\nD 6\nR 1\nD 1\nL 5\nU 2\nR 9\nU 2\nR 1\nU 1\nL 6\nD 1\nR 2\nD 10\nL 7\nR 2\nU 7\nD 4\nR 9\nL 7\nD 8\nU 5\nR 10\nL 10\nD 2\nU 2\nR 8\nU 9\nD 1\nR 2\nL 10\nU 5\nR 8\nL 7\nD 1\nR 7\nD 3\nU 8\nL 4\nD 3\nU 4\nR 5\nU 9\nR 10\nU 3\nR 10\nL 6\nR 5\nU 8\nD 9\nR 4\nU 9\nL 1\nU 7\nR 4\nU 2\nL 7\nD 9\nU 8\nL 7\nU 8\nL 3\nR 7\nD 7\nL 7\nD 6\nL 2\nD 5\nU 4\nR 8\nL 6\nR 7\nD 4\nU 10\nL 8\nR 10\nD 2\nR 1\nU 7\nL 5\nR 5\nL 10\nD 5\nR 10\nU 7\nL 7\nR 9\nD 2\nL 8\nR 11\nD 4\nR 6\nL 5\nR 8\nU 1\nL 6\nU 3\nL 1\nD 10\nL 9\nD 3\nU 10\nL 9\nU 8\nD 11\nU 11\nL 1\nR 2\nU 1\nL 3\nU 2\nD 1\nU 4\nR 6\nL 6\nR 7\nL 9\nR 8\nL 4\nD 11\nL 4\nU 10\nD 6\nL 10\nU 2\nR 3\nL 10\nD 5\nL 1\nD 2\nR 6\nU 2\nL 2\nU 9\nR 10\nL 4\nD 2\nR 10\nL 5\nU 2\nL 1\nD 6\nL 4\nU 5\nD 8\nU 11\nD 5\nU 10\nL 8\nR 5\nL 6\nR 5\nL 2\nR 7\nD 4\nL 9\nD 2\nR 11\nD 5\nU 6\nD 2\nL 4\nR 9\nL 2\nD 5\nR 2\nD 9\nR 8\nL 3\nU 8\nR 9\nD 8\nR 4\nD 5\nU 7\nD 7\nR 4\nD 10\nL 1\nD 5\nU 11\nL 11\nU 11\nL 10\nU 9\nL 6\nD 4\nR 6\nD 8\nU 6\nD 11\nR 2\nU 9\nL 6\nU 5\nR 10\nD 8\nL 9\nR 8\nD 6\nL 8\nD 12\nU 2\nR 1\nL 1\nU 1\nR 6\nD 3\nU 6\nD 5\nR 9\nL 12\nU 7\nR 6\nL 9\nU 1\nR 12\nD 11\nR 6\nU 11\nD 4\nL 2\nR 12\nU 5\nR 3\nU 11\nD 6\nU 9\nL 10\nU 2\nL 9\nU 9\nR 6\nL 12\nD 2\nU 10\nR 3\nU 12\nL 12\nR 4\nL 11\nD 1\nL 3\nD 11\nU 5\nD 1\nU 12\nL 12\nU 5\nR 8\nL 1\nD 1\nL 3\nU 1\nR 4\nD 4\nL 6\nR 11\nU 11\nD 2\nU 7\nL 3\nD 3\nR 10\nD 1\nU 8\nD 7\nU 6\nL 10\nR 3\nL 6\nD 10\nL 2\nU 6\nD 8\nR 2\nL 5\nU 1\nD 5\nU 10\nD 5\nL 7\nU 3\nR 6\nD 2\nU 5\nD 10\nL 5\nD 2\nR 9\nL 11\nD 3\nL 6\nR 11\nU 10\nL 12\nD 12\nU 8\nD 5\nR 1\nL 6\nD 11\nU 12\nR 11\nD 12\nL 5\nD 7\nR 10\nU 4\nL 1\nR 3\nU 9\nL 13\nU 8\nR 3\nD 4\nR 8\nD 3\nR 8\nD 13\nU 1\nR 12\nU 12\nL 8\nR 5\nD 1\nU 3\nR 9\nD 6\nU 11\nR 3\nD 12\nR 8\nL 6\nD 8\nU 6\nR 13\nL 10\nU 6\nR 5\nL 11\nU 9\nL 12\nR 8\nL 6\nR 3\nD 12\nL 9\nD 3\nU 5\nL 6\nR 7\nL 13\nD 4\nR 7\nU 5\nD 13\nR 4\nU 11\nD 8\nR 5\nD 5\nU 3\nL 6\nU 4\nR 8\nD 8\nU 9\nL 8\nU 2\nR 7\nL 2\nU 1\nD 12\nR 3\nL 2\nR 8\nD 4\nL 7\nR 8\nD 6\nU 10\nR 7\nL 9\nD 5\nR 12\nU 2\nR 10\nU 4\nL 13\nR 9\nL 12\nU 3\nR 10\nU 3\nL 8\nR 12\nU 8\nR 11\nU 5\nL 3\nD 10\nR 8\nD 4\nR 4\nU 9\nL 13\nU 5\nR 11\nL 12\nU 11\nD 9\nL 5\nR 13\nU 2\nL 1\nU 12\nR 13\nL 1\nR 2\nU 6\nR 12\nD 11\nL 8\nU 13\nL 14\nU 13\nL 3\nU 9\nL 10\nR 11\nD 6\nU 8\nD 11\nU 5\nL 11\nU 8\nL 3\nR 2\nD 11\nL 12\nU 14\nR 3\nD 1\nU 14\nR 7\nD 14\nR 4\nD 5\nL 13\nR 2\nL 13\nU 8\nL 7\nD 14\nL 2\nU 13\nD 2\nL 13\nD 13\nU 5\nL 12\nU 3\nL 6\nD 2\nU 3\nL 9\nD 14\nR 3\nL 1\nR 6\nD 3\nU 6\nD 9\nL 5\nD 11\nL 1\nD 11\nL 9\nD 8\nU 13\nD 4\nR 5\nD 14\nL 10\nU 14\nD 14\nR 1\nL 8\nU 5\nD 11\nU 8\nD 14\nL 4\nD 13\nU 13\nR 6\nU 11\nL 9\nU 6\nD 11\nR 11\nU 11\nD 14\nR 6\nL 13\nU 1\nR 11\nL 9\nR 11\nL 4\nR 14\nL 2\nD 14\nR 3\nU 9\nD 6\nU 12\nR 7\nU 9\nL 4\nD 9\nR 11\nL 9\nR 14\nL 12\nU 1\nL 10\nU 7\nR 13\nD 3\nR 8\nL 4\nR 4\nL 3\nU 1\nR 14\nD 4\nR 9\nU 3\nL 12\nU 11\nR 5\nU 4\nL 11\nD 14\nL 12\nR 7\nL 15\nR 14\nD 12\nU 10\nR 11\nD 9\nU 14\nR 5\nD 13\nL 14\nD 9\nU 1\nR 10\nU 15\nR 12\nD 13\nL 9\nR 9\nU 8\nR 2\nU 3\nR 3\nD 8\nU 14\nR 4\nL 7\nU 11\nD 6\nL 14\nD 6\nR 8\nU 8\nR 5\nL 13\nR 9\nD 6\nR 6\nL 9\nU 2\nR 13\nU 4\nD 9\nU 14\nR 15\nD 2\nR 6\nD 7\nL 3\nU 14\nD 5\nU 13\nR 8\nD 15\nU 3\nR 9\nD 10\nR 11\nU 12\nD 8\nR 3\nL 5\nD 15\nL 1\nU 6\nR 15\nD 1\nR 13\nD 1\nU 2\nR 15\nD 3\nL 4\nU 9\nD 1\nL 13\nR 11\nU 15\nR 5\nU 15\nR 13\nL 5\nU 2\nR 5\nD 11\nU 11\nL 12\nD 15\nR 11\nL 7\nD 2\nL 11\nD 2\nL 7\nU 7\nR 5\nD 8\nR 6\nL 10\nU 5\nR 3\nU 7\nR 1\nU 7\nL 5\nU 11\nR 14\nU 9\nD 8\nR 10\nL 9\nR 11\nU 6\nR 14\nU 16\nD 13\nU 16\nL 1\nD 2\nR 13\nD 11\nU 9\nR 4\nL 11\nU 2\nL 7\nR 2\nU 14\nL 11\nR 10\nL 1\nR 15\nU 9\nL 16\nR 11\nD 15\nU 10\nL 7\nR 9\nL 9\nD 16\nU 7\nD 10\nR 11\nL 3\nR 16\nL 6\nR 7\nL 7\nR 13\nL 5\nR 6\nD 15\nR 11\nD 7\nU 5\nD 11\nU 13\nR 13\nU 12\nD 10\nL 11\nD 10\nR 6\nU 10\nD 9\nU 1\nL 13\nU 13\nL 11\nU 15\nL 7\nR 2\nD 2\nU 9\nD 1\nL 15\nU 6\nD 3\nU 7\nD 6\nL 6\nU 14\nL 3\nU 16\nL 8\nD 8\nR 4\nD 1\nU 13\nL 4\nU 1\nR 15\nU 3\nD 6\nL 4\nD 12\nL 16\nD 7\nU 10\nL 3\nR 6\nL 12\nR 9\nD 1\nU 7\nL 14\nD 5\nU 15\nD 14\nL 5\nR 6\nD 4\nU 10\nL 17\nR 9\nD 1\nR 12\nU 17\nR 14\nU 4\nR 14\nU 2\nD 13\nR 6\nL 12\nD 10\nL 9\nD 17\nR 14\nD 12\nL 5\nD 17\nL 8\nU 16\nD 9\nU 7\nL 11\nR 13\nU 2\nD 15\nR 2\nL 5\nU 6\nL 5\nU 15\nD 13\nU 17\nR 17\nL 4\nU 17\nR 1\nD 16\nL 16\nR 7\nU 14\nL 3\nD 12\nL 2\nD 6\nR 10\nU 11\nR 8\nD 8\nU 3\nR 5\nU 12\nD 5\nU 14\nR 13\nU 12\nR 1\nU 4\nD 12\nL 6\nR 8\nD 9\nU 4\nD 16\nL 4\nD 7\nL 2\nU 13\nL 7\nD 16\nU 1\nD 14\nU 14\nL 10\nU 2\nD 11\nL 5\nD 14\nU 14\nL 11\nR 17\nD 3\nR 7\nD 6\nR 17\nD 4\nR 14\nL 7\nU 17\nL 6\nD 7\nL 9\nU 10\nL 4\nD 1\nL 17\nR 4\nD 13\nL 4\nD 9\nU 12\nL 6\nR 18\nL 8\nR 16\nL 14\nD 9\nL 18\nD 2\nU 4\nD 7\nR 8\nD 13\nL 17\nU 3\nD 10\nR 10\nL 13\nD 15\nL 14\nD 11\nR 7\nL 3\nR 17\nU 13\nR 14\nD 5\nL 12\nU 4\nR 17\nD 2\nU 7\nR 9\nU 16\nL 18\nD 13\nR 6\nD 8\nL 18\nD 7\nL 11\nR 9\nU 18\nL 10\nU 11\nD 10\nL 7\nD 9\nR 17\nL 4\nR 2\nU 1\nD 9\nU 16\nD 1\nU 5\nR 9\nU 13\nD 10\nU 10\nL 5\nD 1\nU 11\nL 3\nD 15\nU 2\nR 15\nD 1\nL 15\nR 16\nU 14\nL 9\nD 4\nR 15\nL 9\nU 6\nL 4\nR 13\nU 17\nD 6\nL 14\nD 18\nL 17\nD 2\nL 12\nD 11\nR 14\nU 3\nR 12\nL 9\nR 14\nL 16\nU 14\nL 9\nD 1\nL 7\nD 2\nR 2\nL 18\nD 3\nL 10\nD 15\nL 14\nU 11\nL 11\nD 3\nL 4\nR 14\nD 11\nR 8\nD 8\nL 2\nU 15\nL 15\nD 6\nU 1\nD 19\nU 5\nL 5\nU 17\nD 6\nR 5\nL 10\nR 19\nD 9\nR 12\nL 10\nR 1\nL 17\nU 14\nL 1\nD 1\nU 14\nD 14\nL 8\nD 10\nU 12\nL 18\nU 3\nD 17\nU 4\nL 13\nD 3\nR 16\nU 7\nR 19\nU 14\nD 7\nR 15\nL 19\nR 15\nU 11\nL 9\nU 15\nD 16\nU 3\nL 10\nU 1\nD 4\nU 13\nR 7\nU 15\nD 13\nR 18\nL 4\nU 11\nD 3\nL 14\nR 9\nL 8\nR 8\nU 10\nR 17\nL 16\nU 17\nD 15\nU 8\nD 5\nL 8\nR 9\nD 12\nL 2\nU 19\nL 11\nR 18\nD 14\nR 6\nD 4\nL 3\nD 15\nL 3\nR 1\nU 4\nL 6\nU 14\nL 18\nD 13\nR 12\nU 4\nL 12\nU 15\nL 15\nD 2\nL 13\nR 15\nL 3\nU 13\nR 6\nD 1\nU 12\nD 19\nU 10\nL 13\nD 9\nL 18\nU 3\nD 13\nU 2\nL 10\nD 18\nU 16\nD 9\nU 12"
}
