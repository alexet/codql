int resultScore(string lhs, string rhs) {
  lhs = "A" and rhs = "A" and result = 1
  or
  lhs = "A" and rhs = "B" and result = 2
  or
  lhs = "A" and rhs = "C" and result = 0
  or
  lhs = "B" and rhs = "A" and result = 0
  or
  lhs = "B" and rhs = "B" and result = 1
  or
  lhs = "B" and rhs = "C" and result = 2
  or
  lhs = "C" and rhs = "A" and result = 2
  or
  lhs = "C" and rhs = "B" and result = 0
  or
  lhs = "C" and rhs = "C" and result = 1
}

int choiceScore(string rhs) {
  rhs = "A" and result = 1
  or
  rhs = "B" and result = 2
  or
  rhs = "C" and result = 3
}

string oldDecode(string x) {
  x = "X" and result = "A"
  or
  x = "Y" and result = "B"
  or
  x = "Z" and result = "C"
}

int oldScore(string lhs, string rhs) {
  exists(string choice |
    choice = oldDecode(rhs) and
    result = resultScore(lhs, choice) * 3 + choiceScore(choice)
  )
}

int expectedResultScore(string value) {
  value = "X" and result = 0
  or
  value = "Y" and result = 1
  or
  value = "Z" and result = 2
}

int newScore(string lhs, string rhs) {
  exists(string choice |
    resultScore(lhs, choice) = expectedResultScore(rhs) and
    result = resultScore(lhs, choice) * 3 + choiceScore(choice)
  )
}

import lib

signature int scorePred(string lhs, string rhs);

module Impl<inStr/0 input, scorePred/2 score> {
  string turns(int i) { result = Helpers<input/0>::lines(i) }

  string lhs(int i) { result = turns(i).splitAt(" ", 0) }

  string rhs(int i) { result = turns(i).splitAt(" ", 1) }

  int roundScore(int i) { result = score(lhs(i), rhs(i)) }

  int totalScore() { result = strictsum(int round | | roundScore(round)) }
}

module TestImpl1 = Impl<test_input/0, oldScore/2>;

module RealImpl1 = Impl<real_input/0, oldScore/2>;

module TestImpl2 = Impl<test_input/0, newScore/2>;

module RealImpl2 = Impl<real_input/0, newScore/2>;

select TestImpl1::totalScore(), RealImpl1::totalScore(), TestImpl2::totalScore(),
  RealImpl2::totalScore()

string test_input() { result = "A Y\nB X\nC Z" }

string real_input() {
  result =
    "C X\nA Y\nC Z\nB Y\nC Z\nA Z\nB Y\nC Z\nC Z\nB X\nA X\nA Z\nC Z\nC X\nA Z\nA Z\nC Z\nA X\nA Z\nA Z\nA Z\nA Z\nA Z\nC Z\nA Z\nC X\nC Z\nA Z\nA Z\nB Y\nC Z\nB X\nB X\nA Z\nC Z\nA X\nA X\nB Y\nB Z\nB Y\nA Z\nC Z\nC X\nC Z\nC Z\nC Z\nC Z\nA Z\nA Z\nA Y\nA Y\nC Z\nA X\nC Y\nA Z\nB Y\nC Z\nC Z\nB Y\nC Z\nC Z\nC Z\nA Z\nA Z\nB Y\nC Z\nA Z\nC Z\nC Z\nA Z\nB X\nC Z\nA X\nA X\nA Y\nC X\nA Y\nB X\nA Z\nA Z\nC Z\nA Z\nA Y\nC X\nA X\nB Y\nA Z\nA Y\nC Z\nC Y\nA X\nB Z\nB Y\nA Y\nC Z\nC Z\nC Z\nB Y\nA Z\nC Z\nA Y\nC Z\nA X\nC Z\nC Z\nA Z\nA X\nC X\nC X\nA X\nA X\nA Y\nA Z\nC Z\nA X\nA Z\nB Y\nA Y\nA Z\nC Z\nB Y\nA Z\nC Z\nA Z\nA X\nA Z\nB Y\nC Z\nC Z\nC Z\nC X\nA X\nC Z\nA X\nB Y\nC X\nC Z\nB Y\nB Y\nB X\nC Z\nB Y\nC Z\nC Z\nC Z\nA Z\nC Z\nC Z\nB Y\nC Z\nB Z\nC Z\nC Z\nA X\nC Z\nC Z\nA Z\nC Z\nC X\nC Z\nA Z\nA Z\nA X\nB X\nC Y\nA X\nA Y\nC Y\nC Z\nA Z\nA X\nC X\nC Z\nA X\nB Y\nC Z\nA X\nA X\nC Z\nB Y\nC Z\nA Y\nA Z\nB Y\nA Y\nA X\nC X\nA Z\nC Z\nB Y\nC Z\nC Z\nC Z\nC Z\nA Z\nC Y\nC Z\nA Y\nA X\nA Z\nA Z\nA Z\nC Z\nC Z\nA Z\nC Z\nA Z\nC Z\nA Z\nC Z\nA X\nB Y\nC Z\nC Z\nC X\nB X\nA Z\nC Z\nA Y\nC Z\nB Y\nA Z\nC Y\nC Z\nC Y\nC Z\nB Y\nA Y\nA Z\nC Z\nC X\nC Z\nA Z\nA Z\nA Z\nA Z\nA Z\nC Z\nC X\nA X\nC Z\nA X\nA Z\nA Z\nA Z\nA Z\nA Z\nB Y\nC Z\nC Z\nA Z\nC Z\nC Z\nC Z\nA Z\nC Z\nC Z\nB Y\nC Z\nA Z\nA Y\nC Y\nB Y\nA Z\nA X\nA Y\nC X\nB Y\nC Z\nC X\nC Z\nA Z\nB Y\nC Z\nC X\nC Z\nA Y\nB Z\nC Z\nC Z\nC Z\nA X\nB Y\nC Z\nC X\nB Y\nB Y\nC X\nA Z\nB Y\nC Z\nA X\nB Y\nC Z\nC Z\nA Z\nB Y\nB Y\nB Y\nA X\nC Z\nB Y\nB Y\nB Y\nA X\nA Z\nC Z\nC Z\nB Y\nA Z\nB Y\nB X\nA Z\nC X\nA Z\nC Z\nA Z\nC Y\nA X\nB Y\nC Z\nB Y\nC Y\nC X\nA Y\nC Z\nA Y\nC X\nA Z\nA Z\nA Z\nA Z\nC Z\nA Y\nB Y\nC Z\nC Z\nB Y\nC Z\nC Z\nC Z\nC Z\nC Z\nC Z\nA X\nC Z\nC Z\nC Z\nA X\nA Z\nA X\nA Z\nA X\nA X\nC Z\nA Z\nB Y\nC Z\nA Z\nC Y\nA Z\nB Y\nB Y\nC Z\nB Y\nB Y\nA Y\nB Y\nA X\nC Z\nA Y\nC Z\nA Z\nA Z\nA X\nA Z\nA X\nC Z\nB Y\nA Z\nA X\nC Z\nC Z\nC Z\nA Z\nA Z\nC X\nA Z\nA Y\nA X\nC Z\nA Y\nC Z\nB X\nC X\nA X\nA X\nC Z\nA Y\nC X\nA Z\nB X\nA Z\nA Z\nA Z\nA X\nA Y\nA Z\nC Z\nA X\nC Z\nA X\nA Z\nA Z\nB Y\nA Z\nC X\nC X\nC Z\nA Z\nC X\nA Z\nA Y\nC Z\nC Z\nB Y\nC Z\nC Z\nA Z\nA Y\nB X\nC X\nC Z\nA Z\nC Z\nA X\nA Z\nA Z\nB Y\nA Y\nA Z\nA Z\nA Z\nC Y\nB Y\nA Y\nC Z\nC Z\nC X\nB Y\nC Z\nC Z\nA Y\nA X\nC Z\nC Z\nC X\nA Z\nB X\nC Z\nB Y\nA Y\nC Z\nC Z\nB X\nA X\nA X\nC Z\nA X\nA X\nC Z\nA Z\nC Z\nA Z\nA Z\nC Z\nA Y\nC Z\nC Z\nC Z\nA Z\nC Z\nC Z\nA Y\nC Z\nC Z\nC Z\nC Z\nC Z\nA Z\nC Z\nB Y\nA Z\nC Z\nC X\nA X\nC Z\nB Y\nA Z\nA X\nB Y\nC Z\nC Z\nC Z\nA X\nC Z\nA Z\nA Y\nA Y\nA Z\nA Z\nA Y\nB Y\nA Z\nC Z\nB Y\nC Z\nA Z\nC Z\nB Y\nB Z\nA X\nC Z\nA Y\nA Y\nA Z\nA X\nC Z\nC Z\nC Z\nC Z\nC Z\nA Z\nC Z\nA Z\nA Y\nA Z\nC X\nA Z\nC Y\nB Z\nC X\nA Z\nA X\nA X\nB Y\nC X\nC Z\nB Y\nA Z\nC Z\nC Z\nA Z\nC Z\nA Z\nC X\nC Y\nC Z\nA X\nC Y\nC Z\nA Z\nA Z\nC Z\nC Z\nA Y\nC Z\nC Z\nB Z\nC X\nA X\nA Z\nC Z\nA Y\nC Z\nC Z\nA X\nA Z\nA X\nA Y\nA Y\nA Y\nC Z\nB Y\nC Z\nA X\nC Y\nC Z\nB Y\nA X\nC Z\nA Z\nA Z\nB Y\nC Y\nA Y\nC Y\nA Z\nC Z\nA Z\nC Z\nC Z\nA Z\nA Z\nC Z\nA Z\nC Z\nA Y\nC Z\nC X\nC Z\nC Z\nC Z\nC Z\nA X\nB Z\nB X\nB Y\nB Y\nC Z\nA X\nA X\nB Y\nA Z\nA X\nC Z\nA X\nC X\nA Y\nA X\nC Z\nC Z\nC Z\nC Z\nC Z\nA X\nC Z\nB Y\nC X\nA X\nA Z\nA Z\nC Z\nC Z\nA Z\nA Z\nC Z\nA X\nA Z\nB Y\nC X\nA X\nA Y\nA Z\nC Z\nA Z\nA Z\nB Y\nA X\nB Y\nC X\nA Y\nB Y\nA Z\nC Z\nB Y\nA Z\nC Z\nC Z\nA Z\nC Z\nA Z\nC Z\nB Y\nA Z\nA Y\nC Z\nB Y\nA Z\nC Z\nC Z\nA Z\nA X\nA Z\nA Z\nC Y\nA Y\nC Z\nC Y\nC Z\nC Z\nB Y\nC Z\nC Y\nA Z\nC Z\nB Z\nC Y\nB Y\nC Y\nC Z\nA Y\nC Z\nA Z\nC Z\nA Y\nC Z\nC Z\nB Y\nB Y\nA Z\nC Z\nB Z\nC X\nB Y\nB Y\nC X\nB Y\nA X\nA X\nA Y\nA Z\nA X\nA X\nC Z\nC Z\nC Z\nC X\nC Z\nB Y\nB Z\nC Z\nA Z\nA Y\nA X\nB Y\nB X\nA X\nA Z\nC Z\nC Z\nA Z\nC Z\nA X\nB X\nB Z\nC Z\nB Y\nA Z\nA Z\nC X\nA X\nA Y\nC Z\nB Y\nC Z\nA Z\nA Z\nA Y\nC Z\nA Z\nA Z\nA Z\nC Z\nC Z\nC Z\nA X\nA X\nB X\nC Z\nA Y\nA Y\nA Y\nC Z\nA Z\nA X\nC Z\nA Z\nA Z\nA X\nC Z\nC Z\nC X\nA Z\nC Z\nC Z\nC Z\nA Z\nC Z\nA Z\nC X\nA Z\nC Z\nC Z\nA Y\nA Y\nC Z\nC Z\nC X\nA Z\nA Y\nC Z\nB Y\nC Z\nA Z\nC Z\nC X\nA Z\nA X\nB Y\nB Y\nC Z\nA Z\nA Z\nA Z\nB Z\nB Y\nC Z\nA Z\nC Z\nC Z\nA Z\nA Z\nA Z\nA X\nB Y\nC Z\nA X\nA Y\nA Z\nC Z\nA Z\nC Z\nC Z\nC X\nA Y\nC Z\nC Z\nC Z\nC Z\nB Y\nC Z\nC Z\nB Z\nC Z\nA X\nC Z\nC Z\nC Z\nA Z\nC Z\nC X\nA Y\nC Z\nA Z\nA Y\nA X\nB X\nB Y\nA Z\nA Z\nA X\nA Z\nC Z\nA Z\nA Z\nA Z\nA Z\nC Z\nA X\nA Z\nA Z\nA Y\nC Z\nB Y\nA X\nA X\nA X\nB Y\nC Z\nC Z\nC Z\nC Z\nB Y\nA X\nC Z\nB Y\nA Z\nC Z\nA Z\nB X\nB Y\nA X\nC Z\nC Z\nC X\nA Z\nA X\nC Z\nB Z\nA X\nA Z\nC Y\nA X\nC Z\nA X\nC Z\nC Z\nA Y\nA Z\nB Y\nA Z\nC X\nA Y\nC Z\nC Z\nA Y\nA Z\nC Z\nA Y\nA X\nA X\nA Y\nC Z\nC Z\nC Z\nA Z\nA Z\nC X\nA Z\nC Z\nA X\nC Z\nB Y\nC Y\nC Z\nA Z\nC Z\nA Z\nA Z\nC Z\nC Z\nA Z\nC Z\nC X\nA Z\nB Y\nA Y\nC Z\nC Z\nC Z\nC Z\nB Y\nA Z\nA Z\nA Z\nC Z\nA X\nC Z\nA Z\nC Y\nC X\nC Z\nC Z\nC Z\nA X\nB Y\nA X\nC Y\nC Y\nA Z\nA Z\nB Y\nA Y\nA Z\nA X\nC Z\nA Z\nC Z\nC Z\nA Z\nA X\nA Z\nA Z\nA Z\nC Z\nC Z\nA Z\nC Z\nA Z\nB Y\nA Z\nC Z\nA Y\nB Y\nB Y\nC Z\nA X\nA X\nC X\nB X\nB Y\nC Z\nB Y\nC Z\nC Z\nB Y\nC Z\nA Z\nA Y\nC Z\nC Z\nC Z\nB Y\nC Z\nC Y\nC Z\nA Z\nA Z\nB Y\nA X\nA X\nC Z\nB Y\nC X\nC Z\nA Z\nC Z\nC Z\nA X\nA Z\nA X\nC Z\nB Y\nC Z\nC Z\nC Z\nC Z\nA Z\nA Y\nC Z\nC X\nA Y\nA X\nA X\nA X\nC X\nA Z\nB Y\nB X\nC Z\nA Z\nC Z\nC Y\nA Z\nB Y\nA X\nA Z\nA Y\nC Z\nA Z\nA Z\nA X\nC Y\nA Z\nC Z\nA X\nB Y\nC Z\nA Y\nC Z\nC Z\nB Y\nA Y\nC Z\nA X\nA X\nA Y\nC X\nA X\nC X\nC X\nC Z\nA X\nC Z\nC Y\nC Z\nC X\nB Y\nC Z\nC Y\nA X\nC Z\nA X\nB Z\nA Y\nA Z\nC Z\nC Z\nC Z\nC Z\nA X\nC Z\nC Z\nC Z\nA Z\nB Y\nC Z\nC X\nB Y\nA Z\nC Z\nB Z\nC Z\nA Z\nC Z\nA Z\nB Y\nA Z\nC Z\nC Z\nC X\nA X\nA Z\nB Y\nC Z\nA X\nA Z\nA X\nB Y\nC Z\nA X\nC Z\nC Z\nC X\nC Z\nC Z\nC Z\nA X\nC Z\nB Z\nA Z\nB Y\nC Z\nB Z\nC X\nC X\nC Z\nC Z\nC Z\nB X\nC Z\nC Z\nC Z\nA Z\nB X\nA Y\nA Z\nC Z\nA Y\nA Z\nA X\nA Z\nA Y\nA X\nA Z\nA Z\nC Z\nC Z\nC Z\nA Y\nA X\nA Y\nB Y\nC Z\nB Y\nC Z\nC Z\nA X\nC X\nA Z\nC Z\nB Y\nA Z\nC Z\nB X\nA Y\nC Z\nC Z\nA Y\nC Z\nC Z\nA X\nC Y\nC Z\nA Z\nA Z\nA X\nA Y\nA Z\nC Z\nC Z\nA Z\nA X\nC Z\nA Y\nB X\nB X\nA Z\nA Z\nC Z\nA X\nA X\nC Z\nC X\nC Z\nC Z\nC Z\nC Z\nC X\nC X\nC Z\nA Y\nC Z\nC Z\nC Z\nA X\nB Y\nA Z\nC Z\nA Y\nA Y\nA Z\nC Z\nC Z\nA Z\nA Y\nA Z\nC Z\nC Z\nB X\nA X\nC Z\nC Z\nA Z\nC Z\nA Z\nC Z\nA Z\nA X\nA X\nA Z\nA X\nC Z\nC X\nA Z\nC X\nB Y\nA X\nA Z\nA Z\nC Z\nA Y\nA X\nC X\nA Z\nC X\nC Z\nA X\nC Z\nC Z\nB Y\nB Y\nC Z\nC X\nB Y\nA Z\nC Z\nC Z\nC Y\nC Z\nC Y\nC Z\nA X\nA Y\nB X\nC Z\nB Y\nA Y\nA X\nC X\nA Z\nA Y\nC Z\nB Y\nA Y\nC X\nA Z\nA Y\nA X\nC Z\nC Z\nC Z\nC Z\nA X\nA Y\nB Y\nC Z\nC Y\nA X\nA X\nA Z\nA Z\nA Z\nA Z\nA Z\nC Z\nA Z\nC Y\nA Y\nA Y\nB Y\nA Z\nA Z\nA Y\nC Z\nC Z\nA Z\nB Y\nB Y\nC Z\nB Y\nA X\nB Y\nA Y\nB Y\nC X\nB Y\nA X\nB Z\nC Z\nC Z\nC Z\nC Z\nA Y\nC Z\nA Z\nA Y\nB Y\nA X\nC Z\nB X\nC Z\nC Z\nC Z\nA Z\nA Z\nA Z\nA X\nC Y\nA Z\nB Y\nC Z\nC Z\nC Z\nA X\nB Y\nB Z\nC Z\nC Z\nC X\nA Z\nA X\nA X\nC Z\nA Z\nA X\nC Z\nA X\nA Z\nA Y\nC Z\nA Y\nC X\nA Z\nA X\nA Z\nC Z\nB Z\nA Y\nA X\nC X\nC Y\nB Y\nA X\nC Z\nC Z\nC Z\nC X\nC Z\nC X\nC Z\nC Z\nA Z\nA Z\nB Y\nA Y\nC X\nA X\nC Z\nA X\nC Z\nC Z\nB Y\nA Z\nA Y\nB Y\nA X\nC Z\nA Y\nA Z\nC Z\nB Y\nA X\nC Z\nB Y\nC Z\nA Z\nB Y\nC Y\nC X\nB Z\nA Z\nC Z\nA Z\nA Y\nC Z\nA Z\nC Z\nC Z\nC Z\nA Y\nC Z\nC Z\nA Z\nB Z\nC Z\nC Z\nC X\nA Z\nC X\nB X\nC X\nA Y\nC Z\nA Z\nA Y\nC X\nA X\nB Y\nC Y\nA Z\nA Z\nC Y\nC X\nA X\nA Z\nC Z\nA X\nA Z\nC X\nA X\nB X\nC Z\nC Z\nA X\nC X\nA Z\nA Z\nA Y\nC Z\nA X\nB Y\nC Z\nA Z\nC X\nA X\nC Z\nB Y\nA X\nB Y\nA Y\nC Y\nA Y\nC Y\nA X\nA Z\nC Z\nB Y\nC Z\nC Z\nB Y\nA X\nA Y\nB Y\nA X\nB X\nA Z\nC Z\nC X\nA Z\nA X\nC Z\nA Y\nC Z\nA Z\nA Z\nA Z\nA Y\nA Z\nB Y\nC Z\nC X\nC X\nC Z\nA Z\nA Z\nA X\nB Y\nC Z\nA Z\nC X\nB X\nC Z\nC Z\nA Z\nC Z\nC Z\nA Z\nB Y\nA X\nB X\nB Y\nA Z\nA Z\nA Z\nA Z\nA Y\nC Z\nC Z\nC Y\nB Y\nB Y\nB Y\nC Z\nC Z\nA X\nA Y\nC Z\nB Y\nB Z\nA X\nC Y\nC Z\nA X\nC Z\nC X\nA X\nC Z\nC Z\nA Y\nA X\nA Z\nA Z\nA Y\nC Z\nA Z\nC X\nB Z\nC Z\nB Y\nA Y\nC Z\nC Z\nA X\nC Z\nC X\nC X\nA Z\nA Y\nA Y\nB Y\nC X\nC Z\nA Z\nC X\nB Y\nA Z\nC Z\nA Y\nC Z\nA Z\nC Z\nA X\nC X\nA X\nA X\nA Y\nB Y\nC Z\nC Z\nA X\nC Z\nA Y\nA Z\nA Y\nB Y\nC Z\nA Z\nA Z\nA Z\nA Y\nC Y\nB X\nA X\nC Z\nA Y\nC Z\nA Y\nB Z\nA X\nC Z\nA Z\nC Z\nA Z\nA X\nC X\nA X\nA X\nA Z\nA Z\nC X\nB Y\nC Z\nC Y\nA Z\nA Z\nA Z\nA Z\nA Z\nA X\nB Z\nB Y\nA Y\nC Z\nA Z\nB Y\nA Z\nC Y\nA Y\nA X\nC Z\nA Z\nC Z\nC Z\nC Y\nA Z\nC Z\nA X\nA Z\nA Z\nB Y\nC Z\nC Z\nC Z\nC Z\nC Z\nC Z\nC Z\nB Y\nC Z\nC Z\nA Z\nC Z\nB Y\nC X\nC X\nC Z\nC Z\nC Z\nA Z\nB Y\nA X\nC Z\nB Y\nB Y\nC Z\nA X\nC Z\nC X\nC Z\nB Y\nB Y\nC Z\nA Z\nC Z\nC X\nB Y\nC Z\nA Z\nC Z\nC Z\nC Z\nC Z\nA Y\nC Y\nA Y\nC Z\nC Z\nA X\nA Z\nC Y\nC Z\nA X\nB Z\nC X\nC Z\nA Z\nC Z\nC X\nC Z\nC Y\nA X\nA Z\nA Y\nA X\nB X\nA Z\nA Y\nA Z\nB Y\nA Z\nB Y\nB Y\nC Z\nA Z\nC Z\nC Z\nA X\nA X\nC Z\nC Z\nC Z\nC Z\nC X\nA Y\nC Z\nC Z\nA Z\nA Y\nC Z\nA Z\nB Y\nC Z\nC Z\nC Z\nC Z\nA Z\nB Y\nB Z\nB Z\nA Z\nA Y\nA X\nC Z\nB X\nC Z\nB Y\nA X\nC Y\nA Y\nC Z\nC Z\nC X\nC Z\nC X\nC X\nA Z\nA X\nA Z\nC Z\nB X\nA Z\nC Z\nC Z\nA Z\nA Y\nC X\nA X\nC Z\nA X\nA Y\nA X\nA X\nA Z\nA Z\nC Z\nA Z\nA Z\nA Z\nB Y\nA Z\nC Z\nA Y\nC Z\nC Z\nA Z\nA Y\nA Y\nC X\nA X\nB Z\nA Z\nC Z\nA Z\nA Y\nA X\nB Y\nB Y\nA Y\nA Z\nA Z\nB X\nC X\nA Z\nC Z\nC X\nC Z\nC Z\nA X\nC Z\nC Z\nB Y\nA Z\nA Z\nA Y\nA Z\nA Y\nC Z\nC Z\nC Z\nC Z\nB Y\nB Y\nA Z\nC Z\nA Z\nA X\nC Z\nC Z\nA Y\nC Z\nB Y\nA X\nA X\nA Z\nC Z\nC Z\nC Y\nC Z\nA X\nC Z\nA Z\nC Z\nB Y\nA Z\nC Z\nB Y\nB Y\nC Z\nA Y\nC Z\nC Y\nA Z\nA X\nA X\nC Z\nA Y\nC Z\nA Z\nC Z\nA X\nA X\nA Z\nA Z\nC Z\nB Y\nC X\nA Y\nC Z\nC Z\nA X\nC Y\nA Y\nC Z\nC Y\nA Z\nB Z\nC Z\nA Z\nB Y\nB Y\nA Z\nC Z\nA X\nA Z\nC Z\nA Z\nC Z\nC Z\nB Y\nB Y\nA X\nB Y\nA Z\nC Z\nA Z\nA Z\nC Z\nA Y\nC Y\nC Z\nA X\nC Z\nA Z\nC Z\nC Z\nC Y\nC Z\nA Z\nC Z\nC Z\nB Y\nA Z\nC Z\nB X\nB Y\nA Y\nC Z\nA Z\nB Y\nA Z\nC Z\nC X\nC Z\nA Y\nA Y\nA Y\nB Y\nC Z\nA Z\nA Z\nC Z\nA Z\nC X\nA Z\nA Z\nA X\nA Z\nA Y\nC Z\nA Z\nC Z\nA Z\nA X\nC Z\nC X\nC Z\nC Z\nC Z\nC Z\nC Z\nB Y\nC Z\nA Y\nC Z\nB Y\nC X\nC Z\nC Z\nC Z\nB X\nA X\nC Z\nC Z\nC X\nC Z\nA Y\nC Z\nA Z\nA Z\nC Z\nC Z\nC Z\nA Z\nC Z\nA X\nA Z\nC Z\nA Z\nC Z\nA X\nC Z\nC Z\nC X\nA Z\nC Z\nC Z\nC Z\nC Z\nA X\nA Z\nA X\nC Z\nB Y\nC X\nB Y\nA Z\nC Z\nC Z\nA X\nA Z\nA Y\nA X\nA Z\nB Z\nB Y\nC Z\nC Z\nA Y\nC Z\nB Y\nC Z\nB X\nA Z\nC Z\nA Y\nA Z\nA Z\nB Y\nC X\nA Y\nC Z\nC Z\nC Z\nB Z\nB Y\nB X\nA X\nA X\nC Z\nC Z\nC X\nA Y\nC Z\nC Z\nC Y\nC Z\nA Z\nA X\nC Z\nB Y\nC Y\nA Z\nC Z\nA X\nC Z\nC Z\nA X\nA Y\nC Z\nA Y\nC Z\nA X\nC Z\nC Z\nC Z\nC Y\nB Y\nA Z\nC Z\nC X\nB Y\nA Y\nB Y\nC Z\nC Z\nA X\nC Z\nC Y\nA Z\nA X\nA Y\nC Z\nB X\nB Y\nC Z\nA Z\nB Y\nA Y\nC Z\nA X\nB Y\nA X\nC Z\nA Z\nC Z\nB Y\nA Z\nC X\nB Y\nA Y\nA Z\nA Z\nA X\nB Y\nB Y\nC Z\nA X\nC X\nA Z\nB Y\nA X\nB Y\nC Z\nA Z\nA Z\nC Z\nC Z\nA Z\nA X\nC Z\nB Y\nC Z\nC Z\nA Z\nC Z\nA Z\nB Z\nA Z\nC Z\nA Z\nA X\nA X\nA X\nA Y\nC Z\nC Y\nC Z\nC Y\nA X\nA X\nA Y\nC Z\nA Y\nC Z\nC Z\nC X\nB Y\nC Z\nC Z\nC Y\nB Y\nA X\nB X\nA Z\nC Z\nB Y\nA Z\nB Y\nA Y\nA Z\nB Z\nA Y\nA Y\nA X\nA Z\nA Y\nB Y\nC Z\nA X\nC Z\nB Y\nA Z\nC Z\nA Z\nA X\nB Y\nC Z\nA Z\nA Y\nC X\nB Y\nC Z\nC X\nA X\nC Z\nA Y\nC Z\nA X\nB Y\nC Y\nC Z\nA Y\nC Z\nA Z\nA Z\nA Z\nC Z\nC X\nB Y\nB Z\nC Z\nC Z\nC Z\nA Z\nC Z\nC Z\nA Z\nA Z\nB Y\nC Z\nA X\nA Y\nA X\nA Y\nC Z\nC Z\nB Y\nA X\nA Z\nA Z\nA Z\nC Z\nB Z\nC Y\nC Z\nB Y\nC Y\nC Z\nA Z\nC Z\nC X\nA Z\nA Z\nB Y\nA Z\nC Z\nA Y\nA X\nA Z\nA Y\nC Z\nC Z\nB Y\nB Y\nC Z\nC Z\nC Z\nC X\nA Z\nA Z\nC Z\nB Y\nC X\nB X\nC Z\nA Z\nC Y\nC Z\nC Z\nA X\nC Z\nC Z\nC Z\nA Z\nA Y\nC Z\nB Y\nC Z\nA X\nB X\nC X\nC Z\nA Z\nC Z\nA Z\nA Z\nC Z\nA Y\nA Z\nC Z\nA Z\nA Z\nA X\nC X\nC X\nA X\nC Z\nB Y\nB Y\nA Z\nA Z\nA X\nA Y\nB Y\nC Y\nA Z\nA Z\nC Z\nA X\nC Z\nA Y\nB Y\nC X\nA Y\nC Z\nC Z\nC Z\nA Z\nA Z\nC Y\nA X\nA X\nA X\nC X\nC X\nA X\nC Z\nA X\nB Y\nA Z\nA Z\nC Z\nA X\nA X\nA X\nC Z\nC Z\nC Z\nA Z\nC Z\nA Z\nA Z\nA X\nA Y\nA Y\nC Z\nB Y\nA Y\nA Z\nB Y\nB Y\nC Z\nB Y\nA Y\nC X\nA Z\nA Y\nC Z\nC Z\nA X\nA Z\nB Y\nC Z\nA Y\nA Z\nA Z\nA Z\nC Z\nA Z\nB Y\nC Z\nA Z\nA Z\nA Z\nA Y\nA X\nB Y\nA Z\nA Z\nB X\nA Y\nC Z\nC Z\nA Z\nA Z\nB Y\nA Y\nC Z\nA Z\nC Z\nC X\nC Z\nC X\nC Z\nB Y\nA Y\nC Z\nB Y\nA X\nB Y\nB Y\nA Z\nC Z\nA X\nA X\nC Z\nA X\nA Z\nC Z\nC Z\nB Y\nA Z\nC Z\nC Z\nC Z\nC X\nA Z\nA Z\nC Z\nA Z\nC Z\nC Z\nC X\nB Y\nA X\nA Z\nA X\nC Z\nA Y\nC Z\nC Z\nA X\nC Z\nB X\nA Z\nA Z\nC Z\nC Z\nA Y\nA X\nA Z\nA Z\nC Z\nC Z\nC Z\nC Z\nC Z\nB Y\nA Y\nA Z\nC Z\nC Z\nC Z\nC Z\nC Z\nC X\nA Y\nC X\nC Z\nC Z\nA X\nA Z\nA Z\nC Z\nB Z\nA Z\nB Y\nA Z\nC Z\nC Y\nA Z\nC Z\nC Z\nA X\nC Z\nC Z\nB Y\nA Y\nB Y\nC Z\nA Z\nB X\nC Z\nA Y\nB Y\nC Y\nA Z\nA Y"
}
