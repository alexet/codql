bindingset[r1Start, r1End, r2Start, r2End]
predicate intersectRange(
  int r1Start, int r1End, int r2Start, int r2End, int resultStart, int resultEnd
) {
  resultStart = r1Start.maximum(r2Start) and
  resultEnd = r1End.minimum(r2End) and
  resultStart < resultEnd
}

bindingset[r1Start, r1End, off]
predicate offSetRange(int r1Start, int r1End, int off, int resultStart, int resultEnd) {
  resultStart = r1Start + off and
  resultEnd = r1End + off
}

bindingset[start, end, value]
predicate rangeContains(int start, int end, int value) { value >= start and value < end }

signature module IndexedRangeList {
  bindingset[this]
  class Key;

  bindingset[this]
  class Value;

  predicate isRange(Key k, int start, int end, Value value);
}

module IntersectRangeList<IndexedRangeList Input> {
  private import Input

  private predicate rankedRanges(Key k, int index, int start, int end, Value value) {
    start = rank[index](int oStart | isRange(k, oStart, _, _)) and
    isRange(k, start, end, value)
  }

  private int maxIndex(Key k) { result = max(int index | rankedRanges(k, index, _, _, _)) }

  bindingset[start, end]
  predicate intersection(Key k, int start, int end, int rStart, int rEnd, Value value) {
    exists(int mappingStart, int mappingEnd |
      rankedRanges(k, _, mappingStart, mappingEnd, value) and
      intersectRange(mappingStart, mappingEnd, start, end, rStart, rEnd)
    )
  }

  bindingset[start, end]
  predicate notIntersection(Key k, int start, int end, int rStart, int rEnd) {
    exists(int mappingStart |
      rankedRanges(k, 1, mappingStart, _, _) and
      start < mappingStart and
      rStart = start and
      rEnd = end.minimum(mappingStart)
    )
    or
    exists(int mappingEnd |
      rankedRanges(k, maxIndex(k), _, mappingEnd, _) and
      end > mappingEnd and
      rStart = start.minimum(mappingEnd) and
      rEnd = end
    )
    or
    exists(int index, int prevEnd, int nextStart |
      rankedRanges(k, index, _, prevEnd, _) and
      rankedRanges(k, index + 1, nextStart, _, _) and
      intersectRange(prevEnd, nextStart, start, end, rStart, rEnd)
    )
  }
}
