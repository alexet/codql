signature string inStr();

module Helpers<inStr/0 input> {
  string lines(int i) { result = input().splitAt("\n", i) }

  string groupedLines(int i, int j) { result = input().splitAt("\n\n", i).splitAt("\n", j) }
}
