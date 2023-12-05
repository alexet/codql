bindingset[r1Start, r1End, r2Start, r2End]
predicate intersectRange(
  float r1Start, float r1End, float r2Start, float r2End, float resultStart, float resultEnd
) {
  resultStart = r1Start.maximum(r2Start) and
  resultEnd = r1End.minimum(r2End) and
  resultStart < resultEnd
}

bindingset[r1Start, r1End, off]
predicate offSetRange(float r1Start, float r1End, float off, float resultStart, float resultEnd) {
  resultStart = r1Start + off and
  resultEnd = r1End + off
}

bindingset[start, end, value]
predicate rangeContains(float start, float end, float value) { value >= start and value < end }

signature module IndexedRangeList {
  bindingset[this]
  class Key;

  bindingset[this]
  class Value;

  predicate isRange(Key k, float start, float end, Value value);
}

module IntersectRangeList<IndexedRangeList Input> {
  private import Input

  private predicate rankedRanges(Key k, float index, float start, float end, Value value) {
    start = rank[index](float oStart | isRange(k, oStart, _, _)) and
    isRange(k, start, end, value)
  }

  private float maxIndex(Key k) { result = max(float index | rankedRanges(k, index, _, _, _)) }

  bindingset[start, end]
  predicate intersection(Key k, float start, float end, float rStart, float rEnd, Value value) {
    exists(float mappingStart, float mappingEnd |
      rankedRanges(k, _, mappingStart, mappingEnd, value) and
      intersectRange(mappingStart, mappingEnd, start, end, rStart, rEnd)
    )
  }

  bindingset[start, end]
  predicate notIntersection(Key k, float start, float end, float rStart, float rEnd) {
    exists(float mappingStart |
      rankedRanges(k, 1, mappingStart, _, _) and
      start < mappingStart and
      rStart = start and
      rEnd = end.minimum(mappingStart)
    )
    or
    exists(float mappingEnd |
      rankedRanges(k, maxIndex(k), _, mappingEnd, _) and
      end > mappingEnd and
      rStart = start.minimum(mappingEnd) and
      rEnd = end
    )
    or
    exists(float index, float prevEnd, float nextStart |
      rankedRanges(k, index, _, prevEnd, _) and
      rankedRanges(k, index + 1, nextStart, _, _) and
      intersectRange(prevEnd, nextStart, start, end, rStart, rEnd)
    )
  }
}
