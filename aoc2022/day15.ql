import lib

signature int inInt();

int ten() { result = 10 }

int twenty() { result = 20 }

module Impl<inStr/0 input, inInt/0 importantRow, inInt/0 maxCoord> {
  int sensorParts(int n, int k) {
    Helpers<input/0>::lines(n)
        .trim()
        .regexpCapture("Sensor at x=(-?[0-9]+), y=(-?[0-9]+): closest beacon is at x=(-?[0-9]+), y=(-?[0-9]+)",
          k)
        .toInt() = result
  }

  predicate sensor(int x, int y, int beaconX, int beaconY) {
    exists(int n |
      sensorParts(n, 1) = x and
      sensorParts(n, 2) = y and
      sensorParts(n, 3) = beaconX and
      sensorParts(n, 4) = beaconY
    )
  }

  int sensorDist(int x, int y) {
    exists(int beaconX, int beaconY |
      sensor(x, y, beaconX, beaconY) and
      result = (beaconX - x).abs() + (beaconY - y).abs()
    )
  }

  predicate coveredRange(int y, int rangeStart, int rangeEnd) {
    y in [0 .. maxCoord()] and
    exists(int sensorRow, int sensorColumn, int sensorYDist, int maxDist |
      sensorYDist = maxDist - (sensorRow - y).abs() and
      sensorDist(sensorColumn, sensorRow) = maxDist and
      sensorYDist >= 0 and
      rangeStart = sensorColumn - sensorYDist and
      rangeEnd = sensorColumn + sensorYDist
    )
  }

  int positionIndex(int row, int x) {
    x = rank[result](int y | coveredRange(row, y, _) or coveredRange(row, _, y))
  }

  int rangeStartCount(int row, int index) {
    exists(int x |
      index = positionIndex(row, x) and result = count(int y | coveredRange(row, x, y))
    )
  }

  int rangeEndCount(int row, int index) {
    exists(int y |
      index = positionIndex(row, y) and result = count(int x | coveredRange(row, x, y))
    )
  }

  int rangeDepthAfter(int row, int index) {
    index = 0 and result = 0 and row in [0 .. maxCoord()]
    or
    result =
      rangeDepthAfter(row, index - 1) + rangeStartCount(row, index) - rangeEndCount(row, index)
  }

  predicate mergedRange(int row, int rangeStart, int rangeEnd) {
    exists(int startIndex, int endIndex |
      rangeDepthAfter(row, startIndex - 1) = 0 and
      endIndex = min(int i | i > startIndex and rangeDepthAfter(row, i) = 0) and
      startIndex = positionIndex(row, rangeStart) and
      endIndex = positionIndex(row, rangeEnd)
    )
  }

  predicate trimmedMergedRange(int row, int rangeStart, int rangeEnd) {
    exists(int origStart, int origEnd |
      mergedRange(row, origStart, origEnd) and
      rangeStart = origStart.maximum(0) and
      rangeEnd = origEnd.minimum(maxCoord()) and
      rangeStart < rangeEnd
    )
  }

  int totalMergedSize(int row) {
    result = strictsum(int x, int y | trimmedMergedRange(row, x, y) | y - x + 1)
  }

  int keyRow() { result = min(int row | | row order by totalMergedSize(row)) }

  int xCoord() {
    trimmedMergedRange(keyRow(), _, result - 1) and
    trimmedMergedRange(keyRow(), result + 1, _) and
    not trimmedMergedRange(keyRow(), result, result)
  }

  float freq() { result = xCoord().(float) * 4000000.0 + keyRow() }

  int totalRangeSize() {
    result = sum(int x, int y | mergedRange(importantRow(), x, y) | y - x + 1)
  }

  int beaconInRow() { sensor(_, _, result, importantRow()) }

  int coveredCount() { result = totalRangeSize() - count(beaconInRow()) }
}

int twoMillion() { result = 2000000 }

int fourMillion() { result = 4000000 }

module TestImpl = Impl<testInput/0, ten/0, twenty/0>;

module RealImpl = Impl<realInput/0, twoMillion/0, fourMillion/0>;

select 1

string testInput() {
  result =
    "Sensor at x=2, y=18: closest beacon is at x=-2, y=15\nSensor at x=9, y=16: closest beacon is at x=10, y=16\nSensor at x=13, y=2: closest beacon is at x=15, y=3\nSensor at x=12, y=14: closest beacon is at x=10, y=16\nSensor at x=10, y=20: closest beacon is at x=10, y=16\nSensor at x=14, y=17: closest beacon is at x=10, y=16\nSensor at x=8, y=7: closest beacon is at x=2, y=10\nSensor at x=2, y=0: closest beacon is at x=2, y=10\nSensor at x=0, y=11: closest beacon is at x=2, y=10\nSensor at x=20, y=14: closest beacon is at x=25, y=17\nSensor at x=17, y=20: closest beacon is at x=21, y=22\nSensor at x=16, y=7: closest beacon is at x=15, y=3\nSensor at x=14, y=3: closest beacon is at x=15, y=3\nSensor at x=20, y=1: closest beacon is at x=15, y=3"
}

string realInput() {
  result =
    "Sensor at x=3088287, y=2966967: closest beacon is at x=3340990, y=2451747\n  Sensor at x=289570, y=339999: closest beacon is at x=20077, y=1235084\n  Sensor at x=1940197, y=3386754: closest beacon is at x=2010485, y=3291030\n  Sensor at x=1979355, y=2150711: closest beacon is at x=1690952, y=2000000\n  Sensor at x=2859415, y=1555438: closest beacon is at x=3340990, y=2451747\n  Sensor at x=1015582, y=2054755: closest beacon is at x=1690952, y=2000000\n  Sensor at x=1794782, y=3963737: closest beacon is at x=2183727, y=4148084\n  Sensor at x=2357608, y=2559811: closest beacon is at x=2010485, y=3291030\n  Sensor at x=2936, y=1218210: closest beacon is at x=20077, y=1235084\n  Sensor at x=2404143, y=3161036: closest beacon is at x=2010485, y=3291030\n  Sensor at x=12522, y=1706324: closest beacon is at x=20077, y=1235084\n  Sensor at x=1989162, y=3317864: closest beacon is at x=2010485, y=3291030\n  Sensor at x=167388, y=3570975: closest beacon is at x=-1018858, y=4296788\n  Sensor at x=1586527, y=2233885: closest beacon is at x=1690952, y=2000000\n  Sensor at x=746571, y=1442967: closest beacon is at x=20077, y=1235084\n  Sensor at x=3969726, y=3857699: closest beacon is at x=3207147, y=4217920\n  Sensor at x=1403393, y=2413121: closest beacon is at x=1690952, y=2000000\n  Sensor at x=2343717, y=3649198: closest beacon is at x=2183727, y=4148084\n  Sensor at x=1473424, y=688269: closest beacon is at x=2053598, y=-169389\n  Sensor at x=2669347, y=190833: closest beacon is at x=2053598, y=-169389\n  Sensor at x=2973167, y=3783783: closest beacon is at x=3207147, y=4217920\n  Sensor at x=2011835, y=3314181: closest beacon is at x=2010485, y=3291030\n  Sensor at x=1602224, y=2989728: closest beacon is at x=2010485, y=3291030\n  Sensor at x=3928889, y=1064434: closest beacon is at x=3340990, y=2451747\n  Sensor at x=2018358, y=3301778: closest beacon is at x=2010485, y=3291030\n  Sensor at x=1811905, y=2084187: closest beacon is at x=1690952, y=2000000\n  Sensor at x=1767697, y=1873118: closest beacon is at x=1690952, y=2000000\n  Sensor at x=260786, y=1154525: closest beacon is at x=20077, y=1235084"
}
