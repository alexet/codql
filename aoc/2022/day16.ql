import lib

module Impl<inStr/0 input> {
  string parts(int i, int k) {
    result =
      Helpers<input/0>::lines(i)
          .regexpCapture("Valve ([A-Z][A-Z]) has flow rate=([0-9]+); tunnels? leads? to valves? (.*)",
            k)
  }

  string valveName(int i) { result = parts(i, 1) }

  int flowRate(int i) { result = parts(i, 2).toInt() }

  string tunnelNames(int i) { result = parts(i, 3).splitAt(", ") }

  int tunnelLink(int i) { valveName(result) = tunnelNames(i) }

  predicate flowTunnel(int i) { flowRate(i) > 0 }

  int flowRank(int i) { i = rank[result + 1](int t | flowTunnel(t)) }

  int flowRankInv(int i) { i = flowRank(result) }

  bindingset[prev, valve]
  int setValve(int prev, int valve) { result = prev.bitOr(1.bitShiftLeft(valve)) }

  int maxValveIndex() { result = max(int i | i = flowRank(_)) }

  int allValves() { result = 1.bitShiftLeft(count(int i | i = flowRank(_))) - 1 }

  int maxValve() { result = max(int i | exists(valveName(i))) }

  int startValve() { valveName(result) = "AA" }

  class Valve instanceof int {
    string name;

    Valve() { name = valveName(this) }

    string toString() { result = name }

    Valve neighbours() { result = tunnelLink(this) }

    int flowRate() { result = flowRate(this) }
  }

  class InterestingValve extends Valve {
    InterestingValve() { this.flowRate() > 0 or this = startValve() }

    int distanceTo(InterestingValve other) { result = travelTime(this, other) }
  }

  class ValveSet instanceof int {
    ValveSet() { this in [0 .. allValves()] }

    ValveSet setValve(Valve v) { result = setValve(this, flowRank(v)) }

    ValveSet setValveStrict(Valve v) { result = this.setValve(v) and result != this }

    ValveSet larger1Step() {
      result = this.setValveStrict(any(InterestingValve a)) and
      result != this
    }

    ValveSet larger() { result = this.larger1Step+() }

    string toString() { result = print(this) }
  }

  predicate interestingValve(InterestingValve a) { any() }

  int travelTime(InterestingValve a, InterestingValve b) =
    shortestDistances(interestingValve/1, tunnelLink/1)(a, b, result)

  signature int startPoint(ValveSet initValves, Valve initPos, int round);

  pragma[nomagic]
  int move(ValveSet prevValves, Valve prevPos, ValveSet nextValves, Valve nextPos, int score) {
    (
      nextValves = prevValves.setValveStrict(prevPos) and
      score = prevPos.flowRate() and
      nextPos.(InterestingValve) = prevPos and
      result = 1
      or
      result = 1 and
      nextPos = prevPos.neighbours() and
      nextValves.(ValveSet) = prevValves and
      score = 0
    )
  }

  module DoIter<startPoint/3 actualStart> {
    predicate reachable(int round, ValveSet valves, Valve pos) {
      exists(actualStart(valves, pos, round))
      or
      round in [1 .. 30] and
      exists(int prevValves, int prevPos, int time |
        time = move(prevValves, prevPos, valves, pos, _) and
        reachable(round - time, prevValves, prevPos)
      )
    }

    pragma[nomagic]
    predicate step(
      int round, ValveSet valves, Valve pos, int nextValves, int nextPos, int time, int score
    ) {
      time = move(valves, pos, nextValves, nextPos, score) and
      reachable(round - time, valves, pos)
    }

    language[monotonicAggregates]
    pragma[nomagic]
    int bestScore(int round, ValveSet valves, Valve pos) {
      result = actualStart(valves, pos, round)
      or
      round in [1 .. 30] and
      result =
        max(ValveSet prevValves, Valve prevPos, int score, int time |
          step(round, prevValves, prevPos, valves, pos, time, score)
        |
          bestScore(round - time, prevValves, prevPos) + (score) * (30 - round)
        )
    }

    int bestScoreR(ValveSet valves, Valve pos) {
      result = bestScore(30, valves, pos) and
      not exists(ValveSet smaller |
        valves = smaller.larger() and bestScore(30, smaller, pos) > result
      )
    }
  }

  int p1Start(ValveSet initValves, Valve initPos, int round) {
    initValves = 0 and initPos = startValve() and round = 0 and result = 0
  }

  int bestScoreP1() { result = max(DoIter<p1Start/3>::bestScoreR(_, _)) }

  int p2StartPerson(ValveSet initValves, Valve initPos, int round) {
    initValves = 0 and initPos = startValve() and round = 4 and result = 0
  }

  int p2StartElephant(ValveSet initValves, Valve initPos, int round) {
    result = DoIter<p2StartPerson/3>::bestScoreR(initValves, _) and
    round = 4 and
    initPos = startValve()
  }

  int bestScoreP2() { result = max(DoIter<p2StartElephant/3>::bestScore(30, _, _)) }

  string print(int valveSet) {
    valveSet in [0 .. allValves()] and
    result =
      "{" +
        concat(int i |
          i in [0 .. maxValveIndex()] and valveSet.bitAnd(1.bitShiftLeft(i)) != 0
        |
          valveName(flowRankInv(i)), ", "
        ) + "}"
  }
}

module TestImpl = Impl<testInput/0>;

module RealImpl = Impl<realInput/0>;

select 1

string testInput() {
  result =
    "Valve AA has flow rate=0; tunnels lead to valves DD, II, BB\nValve BB has flow rate=13; tunnels lead to valves CC, AA\nValve CC has flow rate=2; tunnels lead to valves DD, BB\nValve DD has flow rate=20; tunnels lead to valves CC, AA, EE\nValve EE has flow rate=3; tunnels lead to valves FF, DD\nValve FF has flow rate=0; tunnels lead to valves EE, GG\nValve GG has flow rate=0; tunnels lead to valves FF, HH\nValve HH has flow rate=22; tunnel leads to valve GG\nValve II has flow rate=0; tunnels lead to valves AA, JJ\nValve JJ has flow rate=21; tunnel leads to valve II"
}

string realInput() {
  result =
    "Valve IK has flow rate=6; tunnels lead to valves EU, XY, AD, SC, CH\nValve YW has flow rate=11; tunnels lead to valves HD, MW, ID, JD, BJ\nValve HD has flow rate=0; tunnels lead to valves YW, AA\nValve LZ has flow rate=0; tunnels lead to valves CR, IT\nValve LO has flow rate=0; tunnels lead to valves CH, YB\nValve PM has flow rate=0; tunnels lead to valves EN, YB\nValve ME has flow rate=0; tunnels lead to valves VP, TX\nValve CK has flow rate=0; tunnels lead to valves MD, LL\nValve RM has flow rate=0; tunnels lead to valves TX, AA\nValve MU has flow rate=0; tunnels lead to valves MD, BX\nValve WK has flow rate=0; tunnels lead to valves HG, IP\nValve MT has flow rate=0; tunnels lead to valves ZZ, CR\nValve EN has flow rate=0; tunnels lead to valves JE, PM\nValve AD has flow rate=0; tunnels lead to valves JE, IK\nValve IT has flow rate=8; tunnels lead to valves RY, LZ, KC\nValve JD has flow rate=0; tunnels lead to valves MD, YW\nValve RY has flow rate=0; tunnels lead to valves IT, YB\nValve FS has flow rate=10; tunnels lead to valves QQ, IP, VG, VP, LL\nValve VT has flow rate=0; tunnels lead to valves TX, MW\nValve WF has flow rate=0; tunnels lead to valves JE, HJ\nValve CH has flow rate=0; tunnels lead to valves LO, IK\nValve PZ has flow rate=17; tunnels lead to valves NZ, HJ\nValve SS has flow rate=18; tunnel leads to valve BJ\nValve MW has flow rate=0; tunnels lead to valves YW, VT\nValve JE has flow rate=16; tunnels lead to valves AD, JG, EN, ZZ, WF\nValve AA has flow rate=0; tunnels lead to valves LQ, NG, RM, CA, HD\nValve DS has flow rate=21; tunnel leads to valve PB\nValve QQ has flow rate=0; tunnels lead to valves FS, ID\nValve HG has flow rate=20; tunnels lead to valves QF, WK\nValve ID has flow rate=0; tunnels lead to valves QQ, YW\nValve WL has flow rate=0; tunnels lead to valves KI, EU\nValve OT has flow rate=0; tunnels lead to valves CR, KI\nValve KI has flow rate=14; tunnels lead to valves OT, UN, WL, XU, KC\nValve ZZ has flow rate=0; tunnels lead to valves MT, JE\nValve VD has flow rate=0; tunnels lead to valves CR, RI\nValve PB has flow rate=0; tunnels lead to valves DS, MD\nValve XU has flow rate=0; tunnels lead to valves KI, SQ\nValve CR has flow rate=7; tunnels lead to valves OT, MT, XY, VD, LZ\nValve QF has flow rate=0; tunnels lead to valves HG, NZ\nValve JG has flow rate=0; tunnels lead to valves JE, QL\nValve VP has flow rate=0; tunnels lead to valves FS, ME\nValve HJ has flow rate=0; tunnels lead to valves WF, PZ\nValve MD has flow rate=12; tunnels lead to valves CK, MU, CA, JD, PB\nValve SQ has flow rate=22; tunnel leads to valve XU\nValve XY has flow rate=0; tunnels lead to valves CR, IK\nValve VG has flow rate=0; tunnels lead to valves LQ, FS\nValve YB has flow rate=13; tunnels lead to valves RI, RY, LO, UN, PM\nValve LQ has flow rate=0; tunnels lead to valves AA, VG\nValve BX has flow rate=0; tunnels lead to valves MU, TX\nValve KC has flow rate=0; tunnels lead to valves IT, KI\nValve IP has flow rate=0; tunnels lead to valves FS, WK\nValve SC has flow rate=0; tunnels lead to valves NG, IK\nValve BJ has flow rate=0; tunnels lead to valves SS, YW\nValve NZ has flow rate=0; tunnels lead to valves QF, PZ\nValve TX has flow rate=3; tunnels lead to valves RM, QL, BX, ME, VT\nValve EU has flow rate=0; tunnels lead to valves WL, IK\nValve QL has flow rate=0; tunnels lead to valves TX, JG\nValve CA has flow rate=0; tunnels lead to valves MD, AA\nValve LL has flow rate=0; tunnels lead to valves FS, CK\nValve UN has flow rate=0; tunnels lead to valves KI, YB\nValve RI has flow rate=0; tunnels lead to valves YB, VD\nValve NG has flow rate=0; tunnels lead to valves SC, AA"
}
