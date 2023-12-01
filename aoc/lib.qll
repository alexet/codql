signature string inStr();

module Helpers<inStr/0 input> {
  string lines(int i) { result = input().splitAt("\n", i) }

  string groups(int i) { result = input().splitAt("\n\n", i) }

  string groupedLines(int i, int j) { result = groups(i).splitAt("\n", j) }
}

int bitReverseByte(int input) {
  input in [0..255] and
  exists(int b1, int b2 |
    b1 = input.bitAnd(240).bitShiftRight(4).bitOr(input.bitAnd(15).bitShiftLeft(4)) and
    b2 = b1.bitAnd(204).bitShiftRight(2).bitOr(b1.bitAnd(51).bitShiftLeft(2)) and
    result = b2.bitAnd(170).bitShiftRight(1).bitOr(b2.bitAnd(85).bitShiftLeft(1))
  )
}
