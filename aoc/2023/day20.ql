import lib

module Impl<inStr/0 input> {
  import Helpers<input/0>

  string rawTarget(int n, int k) { result = lines(n).splitAt("->", 1).splitAt(",", k).trim() }

  string target(string s, int k) { result = rawTarget(any(int n | ruleName(n) = s), k) }

  string ruleName(int n) {
    lines(n).splitAt("->", 0).trim().regexpCapture("(%|&)?([a-z]+)", 2) = result
  }

  predicate isFlipFlop(string m) { lines(any(int n | ruleName(n) = m)).charAt(0) = "%" }

  predicate isConjunction(string m) { lines(any(int n | ruleName(n) = m)).charAt(0) = "&" }

  string conjuctionInput(string n) {
    target(result, _) = n and
    isConjunction(n)
  }

  boolean flipFlopState(int outerPress, int iter, string rule) {
    outerPress = 0 and iter = 0 and isFlipFlop(rule) and result = false
    or
    iter = 0 and
    result = flipFlopState(outerPress - 1, doneIter(outerPress - 1), rule)
    or
    exists(string target, boolean isHigh | isActivation(outerPress, iter, _, target, isHigh) |
      target != rule and result = flipFlopState(outerPress, iter - 1, rule)
      or
      target = rule and isHigh = true and result = flipFlopState(outerPress, iter - 1, rule)
      or
      target = rule and
      isHigh = false and
      result = flipFlopState(outerPress, iter - 1, rule).booleanNot()
    )
  }

  string flipFlopState(int outerPress) {
    outerPress = outerPresses() and
    result = concat(string rule |

      | rule + "=" + flipFlopState(outerPress, doneIter(outerPress), rule).toString()
    ,"," order by rule)

  }

  string conjunctionState(int outerPress) {
    outerPress = outerPresses() and
    result = concat(string source, string conj |
      | source + "->" + conj + "=" + lastConjout(outerPress, doneIter(outerPress), source, conj).toString()
    ,"," order by conj, source)
  }

  string fullState(int outerPress) {
    outerPress = outerPresses() and
    result = flipFlopState(outerPress) + "," + conjunctionState(outerPress)
  }

  predicate stateState(int i, int j) {
    fullState(i) = fullState(j) and i < j
  }

  int jump() {
    result = min(int i | 
      exists(int j | stateState(j, j + i)))
  }

  boolean conjunctionState(int outerPress, int iter, string rule) {
    exists(string input |
      input = conjuctionInput(rule) and
      lastConjout(outerPress, iter, input, rule) = false
    ) and
    result = true
    or
    exists(lastConjout(outerPress, iter, _, _)) and
    isConjunction(rule) and
    forall(string input | input = conjuctionInput(rule) |
    trueConjout(outerPress, iter, input, rule)
    ) and
    result = false
  }

  pragma[noinline]
  predicate trueConjout(int outerPress, int iter, string source, string conj) {
    lastConjout(outerPress, iter, source, conj) = true
  }

  boolean lastConjout(int outerPress, int iter, string source, string conj) {
    outerPress = 0 and iter = -1 and result = false and source = conjuctionInput(conj)
    or
    iter = -1 and
    result = lastConjout(outerPress - 1, doneIter(outerPress - 1), source, conj)
    or
    exists(string s, string target, boolean isHigh |
      isActivation(outerPress, iter, s, target, isHigh) and source = conjuctionInput(conj)
    |
      if target = conj and source = s
      then result = isHigh
      else result = lastConjout(outerPress, iter - 1, source, conj)
    )
  }

  int targetCount(string rule) {
    rule = ruleName(_) and
    result = count(int k | exists(target(rule, k)))
  }

  int outerPresses() { result in [0 .. 999] }

  int insertPoint(int outerPress, int iter) {
    result = 1 and iter = 0 and outerPress = outerPresses()
    or
    exists(string prev, boolean prevHigh | isActivation(outerPress, iter - 1, _, prev, prevHigh) |
      prev = "broadcaster" and result = insertPoint(outerPress, iter - 1) + targetCount(prev)
      or
      isFlipFlop(prev) and prevHigh = true and result = insertPoint(outerPress, iter - 1)
      or
      isFlipFlop(prev) and
      prevHigh = false and
      result = insertPoint(outerPress, iter - 1) + targetCount(prev)
      or
      isConjunction(prev) and result = insertPoint(outerPress, iter - 1) + targetCount(prev)
      or
      not prev = ruleName(_) and result = insertPoint(outerPress, iter - 1)
    )
  }

  int doneIter(int outerPress) { result + 1 = insertPoint(outerPress, result + 1) }

  predicate isActivation(int outerPress, int iter, string source, string target, boolean isHigh) {
    outerPress = outerPresses() and
    source = "button" and
    iter = 0 and
    target = "broadcaster" and
    isHigh = false
    or
    exists(int prev, boolean prevHigh |
      exists(int k |
        isActivation(outerPress, prev, _, source, prevHigh) and
        source = "broadcaster" and
        isHigh = prevHigh and
        target = target(source, k) and
        iter = insertPoint(outerPress, prev) + k
      )
      or
      exists( int k|
        isActivation(outerPress, prev, _, source, prevHigh) and
        isFlipFlop(source) and
        prevHigh = false and
        isHigh = flipFlopState(outerPress, iter - 1, source) and
        target = target(source, k) and
        iter = insertPoint(outerPress, prev) + k
      )
      or
      exists(int k |
        isActivation(outerPress, prev, _, source, prevHigh) and
        isConjunction(source) and
        isHigh = conjunctionState(outerPress, iter - 1, source) and
        target = target(source, k) and
        iter = insertPoint(outerPress, prev) + k
      )
    )
  }

  int totalLow() {
    result = count(int outerPress, int iter | isActivation(outerPress, iter, _, _, false))
  }

  int totalHigh() {
    result = count(int outerPress, int iter | isActivation(outerPress, iter, _, _, true))
  }

  int lowInIter(int outerPress) {
    result = strictcount(int iter | isActivation(outerPress, iter, _, _, false))
  }

  int highInIter(int outerPress) {
    result = strictcount(int iter | isActivation(outerPress, iter, _, _, true))
  }

  int p1Results() {
    result = totalLow() * totalHigh()
  }
}
string testInput() { result = "broadcaster -> a, b, c\n%a -> b\n%b -> c\n%c -> inv\n&inv -> a" }

string testInput2() {
  result = "broadcaster -> a\n%a -> inv, con\n&inv -> b\n%b -> con\n&con -> output"
}

module TestImpl = Impl<testInput/0>;

module TestImpl2 = Impl<testInput2/0>;

string realInput() {
  result ="&kl -> ll\n%vd -> ff, mb\n%dx -> hb, fx\n%jj -> xt, th\n%ld -> fq, ff\n%bn -> ff, lg\n%mv -> hb, mx\n%mx -> xp\n%qm -> gz, tj\n%zd -> zp\n%tq -> mf\n&vm -> ll\n%qr -> jj\n%bv -> th, lr\n%rf -> lq, tj\nbroadcaster -> lp, fn, tp, zz\n%rk -> rc, th\n&tj -> xh, gv, gz, bt, ct, vb, lp\n%dg -> rf, tj\n%xt -> rk, th\n%fq -> ff\n%gz -> dg\n%rl -> hb\n%rc -> st, th\n%km -> fz, hb\n%gv -> ct\n%lr -> tq\n%lg -> vd\n%jh -> th\n%rs -> sq, ff\n%bt -> kc\n%mf -> th, qr\n%xf -> km\n%tp -> hb, sv\n%ch -> hb, mv\n%xp -> hb, xf\n%xh -> js\n%fz -> hb, dx\n%zp -> bn\n&kv -> ll\n&ll -> rx\n%zz -> fj, ff\n%lp -> gv, tj\n&vb -> ll\n&th -> tq, lr, vm, fn, qr\n%sq -> zd, ff\n%st -> th, jh\n%fx -> rl, hb\n%fj -> rs\n%lq -> tj\n%fn -> th, bv\n%ct -> xh\n&ff -> kl, zd, lg, zz, fj, zp\n%js -> tj, bt\n%mb -> ld, ff\n&hb -> sv, xf, kv, tp, mx\n%kc -> qm, tj\n%sv -> ch\n"
}

module RealImpl = Impl<realInput/0>;

select 1
