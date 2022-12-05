signature string inStr();

module Helpers<inStr/0 input> {
  string lines(int i) { result = input().splitAt("\n", i) }

  string groups(int i) { result = input().splitAt("\n\n", i) }

  string groupedLines(int i, int j) { result = groups(i).splitAt("\n", j) }
}
