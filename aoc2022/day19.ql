import lib

module Impl<inStr/0 input> {
  string blueprint(int n) { result = Helpers<input/0>::lines(n - 1) }

  int oreOreCost(int n) {
    result =
      unique( | | blueprint(n).regexpCapture(".*Each ore robot costs ([0-9]+) ore.*", 1).toInt())
  }

  int clayOreCost(int n) {
    result =
      unique( | | blueprint(n).regexpCapture(".*Each clay robot costs ([0-9]+) ore.*", 1).toInt())
  }

  int obsidianOreCost(int n) {
    result =
      unique( |
        |
        blueprint(n)
              .regexpCapture(".*Each obsidian robot costs ([0-9]+) ore and ([0-9]+) clay.*", 1)
              .toInt()
      )
  }

  int obsidianClayCost(int n) {
    result =
      unique( |
        |
        blueprint(n)
              .regexpCapture(".*Each obsidian robot costs ([0-9]+) ore and ([0-9]+) clay.*", 2)
              .toInt()
      )
  }

  int geodeOreCost(int n) {
    result =
      unique( |
        |
        blueprint(n)
              .regexpCapture(".*Each geode robot costs ([0-9]+) ore and ([0-9]+) obsidian.*", 1)
              .toInt()
      )
  }

  int geodeObsidianCost(int n) {
    result =
      unique( |
        |
        blueprint(n)
              .regexpCapture(".*Each geode robot costs ([0-9]+) ore and ([0-9]+) obsidian.*", 2)
              .toInt()
      )
  }

  bindingset[a, b]
  int cielDiv(int a, int b) { result = (a - 1 + b) / b }

  int oreBotTime(int n, int oreBot, int ore) {
    oreBot in [0 .. maxOre(n)] and
    ore in [0 .. maxOre(n) * maxIterP2()] and
    result = cielDiv(oreOreCost(n) - ore, oreBot).maximum(0) + 1
  }

  int clayBotTime(int n, int oreBot, int ore) {
    oreBot in [0 .. maxOre(n)] and
    ore in [0 .. maxOre(n) * maxIterP2()] and
    result = cielDiv(clayOreCost(n) - ore, oreBot).maximum(0) + 1
  }

  int obsidianBotTime(int n, int oreBot, int ore, int clayBot, int clay) {
    oreBot in [0 .. maxOre(n)] and
    ore in [0 .. maxOre(n) * maxIterP2()] and
    clayBot in [0 .. maxClay(n)] and
    clay in [0 .. maxClay(n) * maxIterP2()] and
    result =
      cielDiv(obsidianOreCost(n) - ore, oreBot)
            .maximum(cielDiv(obsidianClayCost(n) - clay, clayBot))
            .maximum(0) + 1
  }

  int geodeBotTime(int n, int oreBot, int ore, int obsidianBot, int obsidian) {
    oreBot in [0 .. maxOre(n)] and
    ore in [0 .. maxOre(n) * maxIterP2()] and
    obsidianBot in [0 .. maxObsidian(n)] and
    obsidian in [0 .. maxObsidian(n) * maxIterP2()] and
    result =
      cielDiv(geodeOreCost(n) - ore, oreBot)
            .maximum(cielDiv(geodeObsidianCost(n) - obsidian, obsidianBot))
            .maximum(0) + 1
  }

  int maxIterP1() { result = 24 }

  int maxIterP2() { result = 32 }

  int maxNP1() { result = max(int n | exists(blueprint(n))) }

  int maxNP2() { result = 2 }

  module P1Impl = InnerImpl<maxIterP1/0, maxNP1/0>;

  module P2Impl = InnerImpl<maxIterP2/0, maxNP2/0>;

  signature int intPred();

  module InnerImpl<intPred/0 maxIter, intPred/0 maxN> {
    pragma[nomagic]
    predicate reachableState(
      int n, int k, int oreBot, int ore, int clayBot, int clay, int obsidianBot, int obsidian,
      int score
    ) {
      k = 0 and
      exists(blueprint(n)) and
      n <= maxN() and
      oreBot = 1 and
      ore = 0 and
      clayBot = 0 and
      clay = 0 and
      obsidianBot = 0 and
      obsidian = 0 and
      score = 0
      or
      (
        exists(int prevK, int prevOreBot, int prevOre, int prevClay, int prevObsidian |
          reachableState(n, prevK, prevOreBot, prevOre, clayBot, prevClay, obsidianBot,
            prevObsidian, score) and
          exists(int time |
            time = oreBotTime(n, prevOreBot, prevOre) and
            k = prevK + time and
            k <= maxIter() and
            ore = prevOre + prevOreBot * time - oreOreCost(n) and
            clay = prevClay + clayBot * time and
            obsidian = prevObsidian + obsidianBot * time and
            oreBot = prevOreBot + 1
          )
        ) and
        oreBot <= maxOre(n)
        or
        exists(int prevK, int prevClayBot, int prevOre, int prevClay, int prevObsidian |
          reachableState(n, prevK, oreBot, prevOre, prevClayBot, prevClay, obsidianBot,
            prevObsidian, score) and
          exists(int time |
            time = clayBotTime(n, oreBot, prevOre) and
            k = prevK + time and
            k <= maxIter() and
            ore = prevOre + oreBot * time - clayOreCost(n) and
            clay = prevClay + prevClayBot * time and
            obsidian = prevObsidian + obsidianBot * time and
            clayBot = prevClayBot + 1
          )
        ) and
        clayBot <= maxClay(n)
        or
        exists(int prevK, int prevObsidianBot, int prevOre, int prevClay, int prevObsidian |
          reachableState(n, prevK, oreBot, prevOre, clayBot, prevClay, prevObsidianBot,
            prevObsidian, score) and
          exists(int time |
            clayBot > 0 and
            time = obsidianBotTime(n, oreBot, prevOre, clayBot, prevClay) and
            k = prevK + time and
            k <= maxIter() and
            ore = prevOre + oreBot * time - obsidianOreCost(n) and
            clay = prevClay + clayBot * time - obsidianClayCost(n) and
            obsidian = prevObsidian + prevObsidianBot * time and
            obsidianBot = prevObsidianBot + 1
          )
        ) and
        obsidianBot <= maxObsidian(n)
        or
        exists(int prevK, int prevScore, int prevOre, int prevClay, int prevObsidian |
          reachableState(n, prevK, oreBot, prevOre, clayBot, prevClay, obsidianBot, prevObsidian,
            prevScore) and
          exists(int time |
            obsidianBot > 0 and
            time = geodeBotTime(n, oreBot, prevOre, obsidianBot, prevObsidian) and
            k = prevK + time and
            k <= maxIter() and
            ore = prevOre + oreBot * time - geodeOreCost(n) and
            clay = prevClay + clayBot * time and
            obsidian = prevObsidian + obsidianBot * time - geodeObsidianCost(n) and
            score = (prevScore) + (maxIter() - k)
          )
        )
      )
    }

    int maxScore(int n) { result = max(int score | reachableState(n, _, _, _, _, _, _, _, score)) }
  }

  int total() { result = sum(int n | | P1Impl::maxScore(n) * n) }

  int total2() { result = P2Impl::maxScore(1) * P2Impl::maxScore(2) * P2Impl::maxScore(3) }

  int maxOre(int n) {
    result =
      geodeOreCost(n).maximum(obsidianOreCost(n)).maximum(clayOreCost(n)).maximum(oreOreCost(n))
  }

  int maxClay(int n) { result = obsidianClayCost(n).maximum(clayOreCost(n)) }

  int maxObsidian(int n) { result = geodeObsidianCost(n) }
}

select 1

module TestImpl = Impl<testInput/0>;

//module RealImpl = Impl<realInput/0>;
string testInput() {
  result =
    "Blueprint 1: Each ore robot costs 4 ore. Each clay robot costs 2 ore. Each obsidian robot costs 3 ore and 14 clay. Each geode robot costs 2 ore and 7 obsidian.\n Blueprint 2: Each ore robot costs 2 ore. Each clay robot costs 3 ore. Each obsidian robot costs 3 ore and 8 clay. Each geode robot costs 3 ore and 12 obsidian."
}

string realInput() {
  result =
    "Blueprint 1: Each ore robot costs 4 ore. Each clay robot costs 4 ore. Each obsidian robot costs 4 ore and 9 clay. Each geode robot costs 3 ore and 9 obsidian.\n    Blueprint 2: Each ore robot costs 4 ore. Each clay robot costs 3 ore. Each obsidian robot costs 4 ore and 20 clay. Each geode robot costs 4 ore and 8 obsidian.\n    Blueprint 3: Each ore robot costs 2 ore. Each clay robot costs 3 ore. Each obsidian robot costs 2 ore and 16 clay. Each geode robot costs 2 ore and 9 obsidian.\n    Blueprint 4: Each ore robot costs 3 ore. Each clay robot costs 4 ore. Each obsidian robot costs 4 ore and 20 clay. Each geode robot costs 4 ore and 16 obsidian.\n    Blueprint 5: Each ore robot costs 4 ore. Each clay robot costs 4 ore. Each obsidian robot costs 4 ore and 16 clay. Each geode robot costs 2 ore and 15 obsidian.\n    Blueprint 6: Each ore robot costs 2 ore. Each clay robot costs 2 ore. Each obsidian robot costs 2 ore and 20 clay. Each geode robot costs 2 ore and 14 obsidian.\n    Blueprint 7: Each ore robot costs 4 ore. Each clay robot costs 4 ore. Each obsidian robot costs 3 ore and 7 clay. Each geode robot costs 3 ore and 20 obsidian.\n    Blueprint 8: Each ore robot costs 4 ore. Each clay robot costs 4 ore. Each obsidian robot costs 3 ore and 14 clay. Each geode robot costs 4 ore and 15 obsidian.\n    Blueprint 9: Each ore robot costs 4 ore. Each clay robot costs 3 ore. Each obsidian robot costs 3 ore and 7 clay. Each geode robot costs 2 ore and 7 obsidian.\n    Blueprint 10: Each ore robot costs 3 ore. Each clay robot costs 3 ore. Each obsidian robot costs 2 ore and 11 clay. Each geode robot costs 2 ore and 19 obsidian.\n    Blueprint 11: Each ore robot costs 3 ore. Each clay robot costs 3 ore. Each obsidian robot costs 3 ore and 20 clay. Each geode robot costs 2 ore and 12 obsidian.\n    Blueprint 12: Each ore robot costs 4 ore. Each clay robot costs 4 ore. Each obsidian robot costs 4 ore and 20 clay. Each geode robot costs 2 ore and 8 obsidian.\n    Blueprint 13: Each ore robot costs 2 ore. Each clay robot costs 4 ore. Each obsidian robot costs 3 ore and 14 clay. Each geode robot costs 4 ore and 9 obsidian.\n    Blueprint 14: Each ore robot costs 3 ore. Each clay robot costs 4 ore. Each obsidian robot costs 4 ore and 18 clay. Each geode robot costs 3 ore and 8 obsidian.\n    Blueprint 15: Each ore robot costs 4 ore. Each clay robot costs 4 ore. Each obsidian robot costs 2 ore and 9 clay. Each geode robot costs 3 ore and 15 obsidian.\n    Blueprint 16: Each ore robot costs 2 ore. Each clay robot costs 3 ore. Each obsidian robot costs 3 ore and 11 clay. Each geode robot costs 2 ore and 16 obsidian.\n    Blueprint 17: Each ore robot costs 2 ore. Each clay robot costs 3 ore. Each obsidian robot costs 3 ore and 13 clay. Each geode robot costs 3 ore and 15 obsidian.\n    Blueprint 18: Each ore robot costs 3 ore. Each clay robot costs 3 ore. Each obsidian robot costs 3 ore and 16 clay. Each geode robot costs 3 ore and 20 obsidian.\n    Blueprint 19: Each ore robot costs 2 ore. Each clay robot costs 4 ore. Each obsidian robot costs 3 ore and 19 clay. Each geode robot costs 4 ore and 8 obsidian.\n    Blueprint 20: Each ore robot costs 4 ore. Each clay robot costs 3 ore. Each obsidian robot costs 4 ore and 16 clay. Each geode robot costs 2 ore and 15 obsidian.\n    Blueprint 21: Each ore robot costs 4 ore. Each clay robot costs 4 ore. Each obsidian robot costs 4 ore and 7 clay. Each geode robot costs 2 ore and 19 obsidian.\n    Blueprint 22: Each ore robot costs 4 ore. Each clay robot costs 4 ore. Each obsidian robot costs 2 ore and 14 clay. Each geode robot costs 3 ore and 17 obsidian.\n    Blueprint 23: Each ore robot costs 4 ore. Each clay robot costs 3 ore. Each obsidian robot costs 4 ore and 8 clay. Each geode robot costs 2 ore and 8 obsidian.\n    Blueprint 24: Each ore robot costs 4 ore. Each clay robot costs 4 ore. Each obsidian robot costs 4 ore and 7 clay. Each geode robot costs 4 ore and 17 obsidian.\n    Blueprint 25: Each ore robot costs 3 ore. Each clay robot costs 3 ore. Each obsidian robot costs 3 ore and 16 clay. Each geode robot costs 3 ore and 9 obsidian.\n    Blueprint 26: Each ore robot costs 4 ore. Each clay robot costs 3 ore. Each obsidian robot costs 4 ore and 15 clay. Each geode robot costs 4 ore and 9 obsidian.\n    Blueprint 27: Each ore robot costs 3 ore. Each clay robot costs 4 ore. Each obsidian robot costs 2 ore and 20 clay. Each geode robot costs 4 ore and 7 obsidian.\n    Blueprint 28: Each ore robot costs 3 ore. Each clay robot costs 3 ore. Each obsidian robot costs 3 ore and 17 clay. Each geode robot costs 4 ore and 8 obsidian.\n    Blueprint 29: Each ore robot costs 3 ore. Each clay robot costs 4 ore. Each obsidian robot costs 3 ore and 12 clay. Each geode robot costs 3 ore and 17 obsidian.\n    Blueprint 30: Each ore robot costs 4 ore. Each clay robot costs 4 ore. Each obsidian robot costs 4 ore and 5 clay. Each geode robot costs 2 ore and 10 obsidian."
}
