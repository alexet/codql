bindingset[input]
string reverse(string input) { result = concat(int i | | input.charAt(i) order by i desc) }

bindingset[input]
string id(string input) { result = input }

import lib

bindingset[input]
signature string moveFunc(string input);

module Impl<inStr/0 input, moveFunc/1 mover> {
  string cratesLines(int i) { result = Helpers<input/0>::groupedLines(0, i) }

  string crate(int line, int column) {
    exists(string lineText | lineText = cratesLines(line) |
      result = lineText.charAt(any(int i | i / 4 = column and i % 4 = 1)) and
      result.regexpMatch("[A-Z]")
    )
  }

  string initialState(int column) { result = strictconcat(int i | | crate(i, column) order by i) }

  string moves(int i) { result = Helpers<input/0>::groupedLines(1, i) }

  int movesSplit(int i, int j) {
    result = moves(i).regexpCapture("move ([0-9]+) from ([0-9]+) to ([0-9]+)", j).toInt()
  }

  predicate move(int i, int amount, int source, int dest) {
    amount = movesSplit(i, 1) and
    source = movesSplit(i, 2) - 1 and
    dest = movesSplit(i, 3) - 1
  }

  string columnStateBefore(int i, int column) {
    i = 0 and result = initialState(column)
    or
    exists(int amount, int source, int dest | move(i - 1, amount, source, dest) |
      column != source and column != dest and result = columnStateBefore(i - 1, column)
      or
      column = dest and
      result =
        mover(columnStateBefore(i - 1, source).prefix(amount)) + columnStateBefore(i - 1, column)
      or
      column = source and
      result = columnStateBefore(i - 1, source).suffix(amount)
    )
  }

  int interactions() { result = count(int i | exists(moves(i))) }

  string finalColumns(int column) { result = columnStateBefore(interactions(), column) }

  string finalReading() {
    result = concat(int column | | finalColumns(column).charAt(0) order by column)
  }
}

select Impl<testInput/0, reverse/1>::finalReading(), Impl<realInput/0, reverse/1>::finalReading(),
  Impl<testInput/0, id/1>::finalReading(), Impl<realInput/0, id/1>::finalReading()

string testInput() {
  result =
    "    [D]    \n[N] [C]    \n[Z] [M] [P]\n 1   2   3 \n\nmove 1 from 2 to 1\nmove 3 from 1 to 3\nmove 2 from 2 to 1\nmove 1 from 1 to 2"
}

string realInput() {
  result =
    "    [S] [C]         [Z]            \n[F] [J] [P]         [T]     [N]    \n[G] [H] [G] [Q]     [G]     [D]    \n[V] [V] [D] [G] [F] [D]     [V]    \n[R] [B] [F] [N] [N] [Q] [L] [S]    \n[J] [M] [M] [P] [H] [V] [B] [B] [D]\n[L] [P] [H] [D] [L] [F] [D] [J] [L]\n[D] [T] [V] [M] [J] [N] [F] [M] [G]\n 1   2   3   4   5   6   7   8   9 \n\nmove 3 from 4 to 6\nmove 1 from 5 to 8\nmove 3 from 7 to 3\nmove 4 from 5 to 7\nmove 1 from 7 to 8\nmove 3 from 9 to 4\nmove 2 from 8 to 2\nmove 4 from 4 to 5\nmove 2 from 5 to 1\nmove 2 from 5 to 6\nmove 7 from 8 to 1\nmove 9 from 3 to 9\nmove 11 from 6 to 5\nmove 2 from 6 to 7\nmove 12 from 1 to 4\nmove 10 from 2 to 9\nmove 2 from 3 to 9\nmove 1 from 7 to 5\nmove 4 from 7 to 6\nmove 2 from 6 to 1\nmove 5 from 1 to 6\nmove 10 from 9 to 1\nmove 9 from 9 to 8\nmove 13 from 4 to 3\nmove 7 from 6 to 2\nmove 2 from 8 to 5\nmove 9 from 3 to 9\nmove 8 from 9 to 8\nmove 4 from 8 to 4\nmove 1 from 7 to 5\nmove 3 from 9 to 1\nmove 7 from 2 to 1\nmove 1 from 3 to 1\nmove 1 from 3 to 6\nmove 1 from 6 to 1\nmove 2 from 3 to 6\nmove 5 from 4 to 1\nmove 1 from 6 to 1\nmove 3 from 8 to 7\nmove 8 from 8 to 4\nmove 3 from 5 to 4\nmove 1 from 6 to 7\nmove 1 from 5 to 8\nmove 4 from 5 to 2\nmove 7 from 5 to 8\nmove 3 from 2 to 7\nmove 7 from 4 to 8\nmove 11 from 8 to 4\nmove 15 from 4 to 1\nmove 25 from 1 to 6\nmove 4 from 8 to 7\nmove 1 from 2 to 4\nmove 11 from 6 to 4\nmove 12 from 6 to 3\nmove 1 from 1 to 9\nmove 1 from 9 to 8\nmove 16 from 1 to 3\nmove 1 from 8 to 7\nmove 12 from 4 to 6\nmove 9 from 6 to 5\nmove 3 from 6 to 5\nmove 6 from 7 to 5\nmove 3 from 3 to 5\nmove 2 from 6 to 3\nmove 11 from 5 to 8\nmove 2 from 8 to 3\nmove 2 from 1 to 4\nmove 7 from 3 to 1\nmove 2 from 4 to 6\nmove 2 from 6 to 2\nmove 5 from 7 to 3\nmove 1 from 1 to 6\nmove 1 from 1 to 8\nmove 2 from 2 to 5\nmove 1 from 7 to 4\nmove 1 from 1 to 2\nmove 10 from 3 to 5\nmove 11 from 3 to 6\nmove 1 from 4 to 9\nmove 1 from 9 to 4\nmove 1 from 4 to 2\nmove 2 from 5 to 9\nmove 2 from 2 to 8\nmove 2 from 1 to 6\nmove 2 from 1 to 2\nmove 2 from 3 to 6\nmove 3 from 8 to 1\nmove 3 from 1 to 4\nmove 7 from 8 to 3\nmove 2 from 9 to 5\nmove 2 from 4 to 9\nmove 7 from 5 to 6\nmove 2 from 8 to 6\nmove 1 from 4 to 8\nmove 2 from 2 to 4\nmove 21 from 6 to 3\nmove 10 from 5 to 7\nmove 7 from 7 to 6\nmove 1 from 9 to 3\nmove 1 from 4 to 9\nmove 1 from 9 to 4\nmove 1 from 8 to 4\nmove 8 from 6 to 4\nmove 1 from 4 to 5\nmove 1 from 5 to 8\nmove 4 from 3 to 6\nmove 1 from 8 to 2\nmove 1 from 4 to 2\nmove 2 from 7 to 3\nmove 2 from 2 to 7\nmove 22 from 3 to 5\nmove 4 from 6 to 2\nmove 2 from 6 to 9\nmove 7 from 3 to 9\nmove 6 from 9 to 1\nmove 18 from 5 to 3\nmove 2 from 5 to 4\nmove 20 from 3 to 5\nmove 3 from 7 to 3\nmove 5 from 1 to 2\nmove 11 from 5 to 7\nmove 1 from 1 to 7\nmove 3 from 9 to 3\nmove 16 from 5 to 8\nmove 7 from 8 to 7\nmove 1 from 9 to 2\nmove 8 from 2 to 3\nmove 2 from 2 to 4\nmove 3 from 3 to 1\nmove 9 from 3 to 8\nmove 1 from 6 to 3\nmove 9 from 7 to 3\nmove 3 from 1 to 8\nmove 1 from 7 to 9\nmove 1 from 9 to 4\nmove 1 from 7 to 5\nmove 10 from 4 to 5\nmove 2 from 4 to 2\nmove 19 from 8 to 5\nmove 1 from 8 to 3\nmove 4 from 3 to 5\nmove 2 from 4 to 8\nmove 4 from 7 to 8\nmove 4 from 3 to 9\nmove 4 from 7 to 6\nmove 2 from 2 to 5\nmove 2 from 3 to 2\nmove 6 from 8 to 7\nmove 1 from 8 to 4\nmove 2 from 6 to 4\nmove 3 from 4 to 8\nmove 3 from 9 to 2\nmove 4 from 7 to 8\nmove 28 from 5 to 8\nmove 16 from 8 to 4\nmove 11 from 8 to 4\nmove 3 from 3 to 4\nmove 7 from 5 to 8\nmove 13 from 8 to 7\nmove 1 from 5 to 6\nmove 1 from 6 to 7\nmove 1 from 9 to 2\nmove 2 from 6 to 2\nmove 12 from 4 to 9\nmove 4 from 4 to 1\nmove 2 from 9 to 8\nmove 4 from 8 to 3\nmove 3 from 4 to 5\nmove 4 from 4 to 1\nmove 4 from 4 to 7\nmove 3 from 7 to 9\nmove 5 from 9 to 7\nmove 7 from 2 to 3\nmove 1 from 5 to 7\nmove 8 from 1 to 5\nmove 1 from 2 to 4\nmove 11 from 3 to 1\nmove 10 from 5 to 3\nmove 3 from 9 to 1\nmove 3 from 9 to 6\nmove 5 from 1 to 6\nmove 7 from 6 to 9\nmove 8 from 9 to 7\nmove 9 from 3 to 4\nmove 1 from 6 to 9\nmove 8 from 7 to 1\nmove 9 from 4 to 2\nmove 2 from 1 to 6\nmove 3 from 2 to 6\nmove 4 from 4 to 6\nmove 2 from 9 to 8\nmove 2 from 1 to 2\nmove 1 from 3 to 8\nmove 2 from 8 to 4\nmove 1 from 6 to 8\nmove 11 from 1 to 6\nmove 1 from 1 to 5\nmove 3 from 2 to 9\nmove 2 from 9 to 3\nmove 1 from 1 to 7\nmove 2 from 4 to 9\nmove 4 from 2 to 9\nmove 2 from 8 to 5\nmove 10 from 6 to 1\nmove 2 from 5 to 6\nmove 5 from 9 to 8\nmove 5 from 8 to 7\nmove 1 from 2 to 1\nmove 7 from 1 to 2\nmove 2 from 9 to 4\nmove 1 from 3 to 5\nmove 15 from 7 to 2\nmove 8 from 6 to 3\nmove 2 from 4 to 3\nmove 2 from 6 to 4\nmove 4 from 7 to 1\nmove 4 from 7 to 5\nmove 1 from 6 to 4\nmove 3 from 1 to 7\nmove 5 from 7 to 6\nmove 4 from 7 to 5\nmove 18 from 2 to 4\nmove 5 from 6 to 4\nmove 4 from 1 to 2\nmove 8 from 3 to 8\nmove 2 from 8 to 4\nmove 2 from 3 to 7\nmove 1 from 5 to 7\nmove 3 from 8 to 4\nmove 2 from 7 to 2\nmove 1 from 3 to 8\nmove 9 from 2 to 6\nmove 2 from 8 to 6\nmove 1 from 7 to 3\nmove 1 from 3 to 5\nmove 3 from 6 to 8\nmove 1 from 8 to 5\nmove 1 from 5 to 9\nmove 1 from 1 to 2\nmove 5 from 4 to 6\nmove 10 from 6 to 2\nmove 5 from 2 to 6\nmove 5 from 6 to 4\nmove 1 from 6 to 3\nmove 6 from 4 to 6\nmove 3 from 2 to 6\nmove 2 from 2 to 3\nmove 11 from 4 to 6\nmove 1 from 9 to 5\nmove 4 from 6 to 7\nmove 1 from 4 to 3\nmove 12 from 4 to 3\nmove 1 from 8 to 6\nmove 9 from 5 to 7\nmove 1 from 5 to 2\nmove 1 from 8 to 5\nmove 1 from 4 to 9\nmove 9 from 7 to 9\nmove 1 from 3 to 4\nmove 2 from 3 to 6\nmove 2 from 5 to 6\nmove 2 from 8 to 5\nmove 11 from 3 to 4\nmove 2 from 3 to 1\nmove 1 from 2 to 3\nmove 1 from 3 to 8\nmove 3 from 7 to 9\nmove 5 from 4 to 2\nmove 2 from 5 to 8\nmove 6 from 4 to 2\nmove 1 from 1 to 3\nmove 12 from 9 to 1\nmove 6 from 1 to 6\nmove 1 from 8 to 4\nmove 1 from 8 to 3\nmove 5 from 2 to 7\nmove 2 from 3 to 9\nmove 5 from 7 to 1\nmove 1 from 7 to 5\nmove 2 from 9 to 1\nmove 14 from 1 to 7\nmove 2 from 4 to 7\nmove 7 from 2 to 4\nmove 1 from 2 to 1\nmove 1 from 1 to 3\nmove 1 from 5 to 4\nmove 1 from 9 to 6\nmove 16 from 6 to 5\nmove 2 from 5 to 4\nmove 12 from 6 to 8\nmove 10 from 4 to 8\nmove 9 from 7 to 3\nmove 4 from 7 to 6\nmove 11 from 5 to 8\nmove 2 from 5 to 2\nmove 14 from 8 to 9\nmove 1 from 5 to 1\nmove 3 from 9 to 4\nmove 2 from 2 to 1\nmove 7 from 8 to 3\nmove 6 from 3 to 5\nmove 8 from 9 to 8\nmove 1 from 6 to 1\nmove 1 from 4 to 2\nmove 4 from 3 to 8\nmove 1 from 7 to 2\nmove 3 from 1 to 5\nmove 2 from 5 to 7\nmove 3 from 9 to 2\nmove 1 from 1 to 8\nmove 5 from 5 to 4\nmove 2 from 7 to 8\nmove 4 from 2 to 5\nmove 1 from 2 to 4\nmove 2 from 7 to 8\nmove 4 from 6 to 2\nmove 6 from 5 to 3\nmove 1 from 6 to 5\nmove 1 from 5 to 3\nmove 1 from 3 to 8\nmove 8 from 8 to 3\nmove 9 from 8 to 5\nmove 9 from 8 to 2\nmove 2 from 8 to 9\nmove 2 from 3 to 8\nmove 5 from 5 to 8\nmove 1 from 3 to 7\nmove 2 from 9 to 5\nmove 7 from 2 to 4\nmove 14 from 4 to 6\nmove 2 from 2 to 7\nmove 1 from 7 to 3\nmove 1 from 7 to 9\nmove 3 from 5 to 2\nmove 1 from 7 to 1\nmove 3 from 2 to 4\nmove 7 from 8 to 2\nmove 3 from 6 to 1\nmove 17 from 3 to 1\nmove 2 from 8 to 3\nmove 6 from 2 to 7\nmove 2 from 7 to 9\nmove 3 from 6 to 8\nmove 2 from 8 to 6\nmove 4 from 2 to 1\nmove 3 from 4 to 7\nmove 1 from 8 to 7\nmove 1 from 8 to 9\nmove 1 from 4 to 2\nmove 3 from 5 to 7\nmove 2 from 3 to 1\nmove 2 from 3 to 5\nmove 5 from 7 to 4\nmove 5 from 7 to 3\nmove 1 from 4 to 8\nmove 3 from 3 to 1\nmove 6 from 1 to 3\nmove 1 from 7 to 5\nmove 2 from 9 to 2\nmove 3 from 5 to 8\nmove 1 from 8 to 1\nmove 8 from 3 to 5\nmove 1 from 4 to 9\nmove 3 from 6 to 5\nmove 3 from 6 to 3\nmove 2 from 3 to 7\nmove 1 from 4 to 7\nmove 3 from 6 to 4\nmove 2 from 7 to 2\nmove 1 from 7 to 8\nmove 2 from 5 to 4\nmove 1 from 6 to 1\nmove 7 from 4 to 7\nmove 7 from 5 to 2\nmove 10 from 2 to 3\nmove 3 from 2 to 6\nmove 3 from 8 to 1\nmove 1 from 8 to 7\nmove 2 from 6 to 3\nmove 1 from 6 to 9\nmove 4 from 7 to 5\nmove 16 from 1 to 5\nmove 1 from 9 to 7\nmove 3 from 7 to 6\nmove 11 from 5 to 6\nmove 2 from 7 to 9\nmove 12 from 6 to 4\nmove 2 from 6 to 9\nmove 6 from 3 to 2\nmove 1 from 5 to 7\nmove 5 from 9 to 5\nmove 1 from 9 to 6\nmove 4 from 3 to 7\nmove 1 from 4 to 2\nmove 7 from 2 to 5\nmove 3 from 5 to 2\nmove 6 from 5 to 6\nmove 3 from 2 to 6\nmove 9 from 6 to 8\nmove 5 from 5 to 9\nmove 5 from 7 to 1\nmove 4 from 1 to 9\nmove 2 from 9 to 4\nmove 1 from 6 to 7\nmove 9 from 4 to 1\nmove 7 from 5 to 9\nmove 18 from 1 to 3\nmove 9 from 9 to 5\nmove 8 from 8 to 2\nmove 1 from 2 to 5\nmove 4 from 2 to 3\nmove 4 from 9 to 6\nmove 1 from 4 to 8\nmove 2 from 5 to 7\nmove 2 from 9 to 2\nmove 10 from 3 to 9\nmove 5 from 5 to 9\nmove 1 from 7 to 2\nmove 2 from 8 to 7\nmove 2 from 3 to 5\nmove 2 from 9 to 1\nmove 2 from 7 to 3\nmove 1 from 2 to 1\nmove 5 from 5 to 8\nmove 1 from 2 to 1\nmove 15 from 3 to 6\nmove 1 from 7 to 6\nmove 10 from 6 to 5\nmove 1 from 7 to 8\nmove 4 from 1 to 6\nmove 1 from 8 to 3\nmove 2 from 1 to 5\nmove 3 from 8 to 1\nmove 1 from 4 to 6\nmove 1 from 4 to 2\nmove 4 from 9 to 7\nmove 6 from 5 to 7\nmove 3 from 1 to 9\nmove 10 from 6 to 8\nmove 2 from 1 to 3\nmove 8 from 7 to 9\nmove 1 from 9 to 6\nmove 2 from 7 to 9\nmove 3 from 3 to 5\nmove 1 from 2 to 6\nmove 2 from 6 to 5\nmove 5 from 9 to 4\nmove 4 from 8 to 2\nmove 1 from 1 to 3\nmove 4 from 5 to 9\nmove 3 from 6 to 1\nmove 2 from 1 to 5\nmove 3 from 5 to 2\nmove 8 from 8 to 3\nmove 11 from 9 to 4\nmove 13 from 4 to 8\nmove 2 from 9 to 2\nmove 2 from 3 to 1\nmove 1 from 4 to 1\nmove 1 from 3 to 8\nmove 2 from 6 to 9\nmove 7 from 8 to 1\nmove 3 from 2 to 5\nmove 7 from 2 to 5\nmove 3 from 4 to 6\nmove 4 from 9 to 2\nmove 2 from 3 to 5\nmove 9 from 5 to 6\nmove 5 from 2 to 7\nmove 2 from 9 to 2\nmove 2 from 9 to 7\nmove 12 from 6 to 8\nmove 5 from 5 to 7\nmove 1 from 9 to 8\nmove 3 from 1 to 6\nmove 5 from 5 to 8\nmove 6 from 1 to 9\nmove 2 from 1 to 5\nmove 1 from 6 to 9\nmove 5 from 9 to 7\nmove 2 from 5 to 8\nmove 11 from 7 to 6\nmove 20 from 8 to 1\nmove 2 from 9 to 8\nmove 4 from 7 to 6\nmove 6 from 8 to 3\nmove 13 from 6 to 9\nmove 4 from 3 to 2\nmove 4 from 6 to 3\nmove 2 from 3 to 6\nmove 5 from 9 to 8\nmove 2 from 7 to 1\nmove 2 from 6 to 9\nmove 6 from 8 to 3\nmove 6 from 3 to 6\nmove 5 from 2 to 9\nmove 22 from 1 to 3\nmove 3 from 2 to 1\nmove 5 from 9 to 3\nmove 1 from 1 to 6\nmove 3 from 6 to 2\nmove 1 from 2 to 4\nmove 33 from 3 to 5\nmove 1 from 8 to 7"
}
