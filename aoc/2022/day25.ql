select 1

import lib

module TestImpl = Impl<testInput/0>;

module RealImpl = Impl<realInput/0>;

module Impl<inStr/0 input> {
  string lines(int i) { result = Helpers<input/0>::lines(i) }

  int fromSnafuDigit(string s) {
    result = -2 and s = "="
    or
    result = -1 and s = "-"
    or
    result = 0 and s = "0"
    or
    result = 1 and s = "1"
    or
    result = 2 and s = "2"
  }

  string toSnafuDigit(int i) { i = fromSnafuDigit(result) }

  bindingset[s]
  float fromSnafu(string s) {
    result = sum(int i | | fromSnafuDigit(s.charAt(i)) * 5.pow(s.length() - i - 1))
  }

  int snafuDigits(int i, int pos) {
    result = fromSnafuDigit(lines(i).charAt(lines(i).length() - pos - 1))
  }

  predicate add1(int lhs, int rhs, int bqSum, int carryIn, int carryOut) {
    lhs in [-2 .. 2] and
    rhs in [-2 .. 2] and
    carryIn in [-1 .. 1] and
    (
      lhs + rhs + carryIn = -5 and bqSum = 0 and carryOut = -1
      or
      lhs + rhs + carryIn = -4 and bqSum = 1 and carryOut = -1
      or
      lhs + rhs + carryIn = -3 and bqSum = 2 and carryOut = -1
      or
      lhs + rhs + carryIn = -2 and bqSum = -2 and carryOut = 0
      or
      lhs + rhs + carryIn = -1 and bqSum = -1 and carryOut = 0
      or
      lhs + rhs + carryIn = 0 and bqSum = 0 and carryOut = 0
      or
      lhs + rhs + carryIn = 1 and bqSum = 1 and carryOut = 0
      or
      lhs + rhs + carryIn = 2 and bqSum = 2 and carryOut = 0
      or
      lhs + rhs + carryIn = 3 and bqSum = -2 and carryOut = 1
      or
      lhs + rhs + carryIn = 4 and bqSum = -1 and carryOut = 1
      or
      lhs + rhs + carryIn = 5 and bqSum = 0 and carryOut = 1
    )
  }

  int paddedDigits(int n, int i) {
    i < lines(n).length() and result = snafuDigits(n, i)
    or
    i in [lines(n).length() .. padLen()] and result = 0
  }

  signature int bqdigits(int i, int n);

  int padLen() {
    result =
      max(lines(_).length()) + (count(int i | exists(lines(i))).log() / 5.log() + 0.25).floor() + 1
  }

  module SnafuAdd {
    predicate lhs = paddedDigits/2;

    predicate rhs = runningSumDigits/2;

    private predicate doSum(int i, int n, int bqSum, int carryOut) {
      n = 0 and add1(lhs(i, 0), rhs(i, 0), bqSum, 0, carryOut)
      or
      exists(int carryIn |
        doSum(i, n - 1, _, carryIn) and
        add1(lhs(i, n), rhs(i, n), bqSum, carryIn, carryOut)
      )
    }

    int addRes(int i, int n) { doSum(i, n, result, _) }
  }

  int runningSumDigits(int i, int n) {
    i = 0 and n in [0 .. padLen()] and result = 0
    or
    result = SnafuAdd::addRes(i - 1, n)
  }

  int lineCount() { result = count(int i | exists(lines(i))) }

  string finalSum() {
    result =
      concat(int i |
        i in [0 .. padLen()]
      |
        toSnafuDigit(runningSumDigits(lineCount(), i)) order by i desc
      )
  }
}

string testInput() {
  result = "1=-0-2\n12111\n2=0=\n21\n2=01\n111\n20012\n112\n1=-1=\n1-12\n12\n1=\n122"
}

string realInput() {
  result =
    "1=12=1--2220--2=21\n2=20---12\n1=2=-=2-0=0=022\n1212=--0-20=1\n1202-1\n2=2-=1-\n1-22-12-1\n1-1-1120=1=120221\n10-02\n122-12=\n2-2\n20001--=20100\n1-=-00=00=2\n1=--0200=--0=2--1-\n1==--001\n1-10011\n1-1=2-==2=2\n2-=02=02222-=0\n1-121=\n2012=2==\n1--\n1212-2\n1--10-112=\n100--1011-=-12---\n2=\n120\n1=12-1-==0==2-02\n1==10\n12==2201112-1=-\n22201=\n202-022=1111-0\n1-=1-=--2\n111011---\n2-=1122101--1-2-11\n22100\n1=20-112\n21=--1\n1-000--21=110101=\n2-10=02-121=\n112\n121=0-2000=-=01=12=\n11=-121-=-1\n1-20==---=000-\n111221==2-122111\n1=122=22010120121\n2-11=-22=2\n1-\n101=0121121-2122\n1=2221-11-2-=\n212\n11=-==00--\n121-0--1===111\n11\n2==00-21222=-2\n2=-02-=22-2=1\n22==-1222=-1-12--\n1--22\n2110-=2-0-211-12=\n202222-1111\n2-=-=1222221=\n1=-=-==-1=\n1-1-0121\n12-1==0222\n11---100\n1--01020-2\n10=20\n12=1=-002-02-=1222\n1011-0--0121-\n101-2==\n2112021212==212\n1-==1-=110-021-22\n1==20111-2022-0\n1=1=2-=0=\n1-0==11-1--\n1--21-21-0-2-\n11-111=-=10==10-\n12-\n202-10221=\n1-1=-00=0\n2-=11\n200-\n21=1=12022-01-0--=\n1=---0=021-0==\n1-=00-1-0210=2\n1121=1=2=20-\n220100-02111=2211-\n1-0-00-0200-001-\n1002\n12-=0-012-111\n1=-0111-10=0\n21=10-2=1=00-120-\n201=\n21\n2000=0-=\n11==0--212=--12-121\n11-220-0=22-011==\n1-1-0=1-21-101==\n111=\n2--1=2=-\n1==0=0-\n1=021222=0---2-1=\n2-20=210212-0122\n1-2100-021=-2=010-11\n1-=-1-0-1-=-0\n20-122200202-12-0=\n2=-20\n1-1-=-\n11=2=1=1-\n1=11-=-20=20"
}
