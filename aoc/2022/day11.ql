import lib

module Impl<inStr/0 input> {
  string monkey(int monkey, int line) { result = Helpers<input/0>::groupedLines(monkey, line) }

  int monkeyIntialItem(int monkey, int item) {
    result = monkey(monkey, 1).suffix(18).splitAt(",", item).trim().toInt()
  }

  int divisionTest(int monkey) { result = monkey(monkey, 3).suffix(21).trim().toInt() }

  string operation(int monkey) { result = monkey(monkey, 2).charAt(23) }

  predicate isSelf(int monkey) { monkey(monkey, 2).substring(25, 28) = "old" }

  int nonSelfRhs(int monkey) { monkey(monkey, 2).suffix(25).toInt() = result }

  int trueLoc(int monkey) { result = monkey(monkey, 4).suffix(29).trim().toInt() }

  int falseLoc(int monkey) { result = monkey(monkey, 5).suffix(30).trim().toInt() }

  int monkeyCount() { result = count(int i | exists(monkey(i, _))) }

  int worryMod() { result = (sum( | | divisionTest(_).log()).exp() + 0.25).floor() }

  int simpleRounds() { result = 20 }

  int complexRounds() { result = 10000 }

  signature int maxRound();

  bindingset[oldItem]
  signature int afterInspect(int monkey, int oldItem);

  bindingset[oldItem]
  int simpleAfterInspect(int monkey, int oldItem) {
    exists(int new |
      (
        operation(monkey) = "*" and new = oldItem * nonSelfRhs(monkey)
        or
        operation(monkey) = "+" and new = oldItem + nonSelfRhs(monkey)
        or
        isSelf(monkey) and operation(monkey) = "*" and new = oldItem * oldItem
        or
        isSelf(monkey) and operation(monkey) = "+" and new = oldItem + oldItem
      ) and
      result = new/3
    )
  }

  bindingset[oldItem]
  int complexAfterInspect(int monkey, int oldItem) {
    exists(float new |
      (
        operation(monkey) = "*" and new = oldItem.(float) * nonSelfRhs(monkey).(float)
        or
        operation(monkey) = "+" and new = oldItem + nonSelfRhs(monkey)
        or
        isSelf(monkey) and operation(monkey) = "*" and new = oldItem.(float) * oldItem.(float)
        or
        isSelf(monkey) and operation(monkey) = "+" and new = oldItem + oldItem
      ) and
      result = new % worryMod()
    )
  }

  bindingset[oldItem]
  int cachedComplexAfterInspect(int monkey, int oldItem) {
    result = complexAfterInspect(monkey, oldItem)
  }



  module Core<afterInspect/2 valueAfterInspect, maxRound/0 maxRounds> {
    bindingset[input, prevMonkey, newMonkey]
    string getAdded(int newMonkey, int prevMonkey, string input) {
      result =
        concat(int elem, string char, int newVal |
          char = input.splitAt(",", elem) and
          newVal = valueAfterInspect(prevMonkey, char.toInt()) and
          throwDest(prevMonkey, newVal) = newMonkey
        |
          newVal.toString() + "," order by elem
        )
    }

    pragma[assume_small_delta]
    cached
    string valuesBeforeRound(int round, int turn, int monkey) {
      round < maxRounds() and
      (
        round = 0 and
        turn = 0 and
        result = concat(int pos | | monkeyIntialItem(monkey, pos).toString() + "," order by pos) and
        monkey in [0 .. monkeyCount() - 1]
        or
        turn != 0 and
        result =
          valuesBeforeRound(round, turn - 1, monkey) +
            getAdded(monkey, turn - 1, valuesBeforeRound(round, turn - 1, turn - 1)) and
        turn - 1 != monkey
        or
        turn != 0 and
        turn - 1 = monkey and
        result = "" and
        exists(valuesBeforeRound(round, turn - 1, turn - 1))
        or
        turn = 0 and result = valuesBeforeRound(round - 1, monkeyCount(), monkey)
      )
    }

    language[monotonicAggregates]
    int inspectCount(int monkey) {
      result =
        strictsum(int round, string str |
          str = valuesBeforeRound(round, monkey, monkey)
        |
          numValues(str)
        )
    }

    bindingset[s]
    int numValues(string s) {
      s != "" and result = count(int i | exists(s.splitAt(",", i)))
      or
      s = "" and result = 0
    }

    float monkeyBusiness() {
      result =
        sum(int m2 |
          m2 = rank[[1, 2]](int m | | m order by inspectCount(m) desc)
        |
          inspectCount(m2).log()
        ).exp()
    }


    bindingset[value]
    int throwDest(int monkey, int value) {
      value % divisionTest(monkey) = 0 and result = trueLoc(monkey)
      or
      value % divisionTest(monkey) != 0 and result = falseLoc(monkey)
    }
  }

  predicate simpleMonkeyBusiness = Core<simpleAfterInspect/2, simpleRounds/0>::monkeyBusiness/0;

  predicate complexMonkeyBusiness = Core<cachedComplexAfterInspect/2, complexRounds/0>::monkeyBusiness/0;
}

module TestImpl = Impl<testInput/0>;

module RealImpl = Impl<realInput/0>;

select TestImpl::simpleMonkeyBusiness(), RealImpl::simpleMonkeyBusiness(),
  TestImpl::complexMonkeyBusiness(), RealImpl::complexMonkeyBusiness()

string testInput() {
  result =
    "Monkey 0:\n  Starting items: 79, 98\n  Operation: new = old * 19\n  Test: divisible by 23\n    If true: throw to monkey 2\n    If false: throw to monkey 3\n\nMonkey 1:\n  Starting items: 54, 65, 75, 74\n  Operation: new = old + 6\n  Test: divisible by 19\n    If true: throw to monkey 2\n    If false: throw to monkey 0\n\nMonkey 2:\n  Starting items: 79, 60, 97\n  Operation: new = old * old\n  Test: divisible by 13\n    If true: throw to monkey 1\n    If false: throw to monkey 3\n\nMonkey 3:\n  Starting items: 74\n  Operation: new = old + 3\n  Test: divisible by 17\n    If true: throw to monkey 0\n    If false: throw to monkey 1"
}

string realInput() {
  result =
    "Monkey 0:\n  Starting items: 98, 97, 98, 55, 56, 72\n  Operation: new = old * 13\n  Test: divisible by 11\n    If true: throw to monkey 4\n    If false: throw to monkey 7\n\nMonkey 1:\n  Starting items: 73, 99, 55, 54, 88, 50, 55\n  Operation: new = old + 4\n  Test: divisible by 17\n    If true: throw to monkey 2\n    If false: throw to monkey 6\n\nMonkey 2:\n  Starting items: 67, 98\n  Operation: new = old * 11\n  Test: divisible by 5\n    If true: throw to monkey 6\n    If false: throw to monkey 5\n\nMonkey 3:\n  Starting items: 82, 91, 92, 53, 99\n  Operation: new = old + 8\n  Test: divisible by 13\n    If true: throw to monkey 1\n    If false: throw to monkey 2\n\nMonkey 4:\n  Starting items: 52, 62, 94, 96, 52, 87, 53, 60\n  Operation: new = old * old\n  Test: divisible by 19\n    If true: throw to monkey 3\n    If false: throw to monkey 1\n\nMonkey 5:\n  Starting items: 94, 80, 84, 79\n  Operation: new = old + 5\n  Test: divisible by 2\n    If true: throw to monkey 7\n    If false: throw to monkey 0\n\nMonkey 6:\n  Starting items: 89\n  Operation: new = old + 1\n  Test: divisible by 3\n    If true: throw to monkey 0\n    If false: throw to monkey 5\n\nMonkey 7:\n  Starting items: 70, 59, 63\n  Operation: new = old + 3\n  Test: divisible by 7\n    If true: throw to monkey 4\n    If false: throw to monkey 3\n"
}
