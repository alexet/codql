import lib

module Impl<inStr/0 input> {
  int time(int race) {
    result = Helpers<input/0>::lines(0).splitAt(":").regexpFind("[0-9]+", race, _).toInt()
  }

  int distance(int race) {
    result = Helpers<input/0>::lines(1).splitAt(":").regexpFind("[0-9]+", race, _).toInt()
  }

  int boatDistance(int race, int holdTime) {
    holdTime in [0 .. time(race)] and
    result = (time(race) - holdTime) * holdTime
  }

  predicate wins(int race, int holdTime) { boatDistance(race, holdTime) > distance(race) }

  int winCount(int race) {
    exists(time(race)) and
    result = count(int holdTime | wins(race, holdTime))
  }

  int winProduct() { result = (sum(int race | | winCount(race).log()).exp() + 0.5).floor() }

  float fullTime() {
    result =
      concat(int pos, string char |
        char = Helpers<input/0>::lines(0).charAt(pos) and char.regexpMatch("[0-9]")
      |
        char order by pos
      ).toFloat()
  }

  float fullDistance() {
    result =
      concat(int pos, string char |
        char = Helpers<input/0>::lines(1).charAt(pos) and char.regexpMatch("[0-9]")
      |
        char order by pos
      ).toFloat()
  }

  // We want min/max x st (time - x) * x > distance
  // i.e solve and round up/down
  // Solving x^2 - time*x + distance=0
  float solutions() {
    exists(float b, float c |
      b = -fullTime() and
      c = fullDistance()
    |
      result = ((-b) + ([-1.0, 1.0]) * (b * b - 4 * c).sqrt()) / (2)
    )
  }

  int rangeStart() { result = min(solutions()).ceil() }

  int rangeEnd() { result = max(solutions()).floor() }

  int winRange() { result = rangeEnd() - rangeStart() + 1 }
}

string testInput() { result = "Time:      7  15   30\nDistance:  9  40  200" }

string realInput() {
  result = "Time:        42     68     69     85\nDistance:   284   1005   1122   1341"
}

module TestImpl = Impl<testInput/0>;

module RealImpl = Impl<realInput/0>;

select RealImpl::winProduct(), RealImpl::winRange()
