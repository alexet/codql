import lib

module Impl<inStr/0 input> {
    string instr(int i) {
        result = Helpers<input/0>::lines(i).prefix(4)
    }

    int arg(int i) {
        result = Helpers<input/0>::lines(i).suffix(5).toInt()
    }
    int timeTaken(string arg) {
        arg = "noop" and result = 1 or
        arg = "addx" and result = 2
    }

    int valueAt(int pc, int cycle) {
        pc = 0 and cycle = 0 and result = 1 or
        exists(int prevCycle, int prevPC, string instrCode |
            pc = prevPC + 1 and
            cycle = prevCycle + timeTaken(instrCode) and
            instrCode = instr(pc - 1) and
            (
                instrCode = "addx" and result = valueAt(prevPC, prevCycle) + arg(pc - 1) or
                instrCode = "noop" and result = valueAt(prevPC, prevCycle)
            )
        )
    }
    int fullValueAt(int cycle) {
        cycle in [0.. any(int i | exists(valueAt(_, i)))] and
        (
            result = valueAt(_, cycle) or
            not exists(valueAt(_, cycle)) and
            result = fullValueAt(cycle- 1)

        )
    }

    bindingset[cycle]
    predicate isInteresting(int cycle) {
        cycle % 40 = 20
    }

    int signalStrength(int cycle) {
        // Note that until this point we have been using 0 based cycles
        result = fullValueAt(cycle-1) * cycle
    }

    int interestingSignalStrength(int cycle) {
        isInteresting(cycle) and
        result = signalStrength(cycle)
    }

    int interestingSum() {
        result = sum(int i | | interestingSignalStrength(i))
    }

    string visible(int cycle) {
        exists(int crtPos, int value | crtPos = cycle % 40 and value = fullValueAt(cycle) |
            value = crtPos + [-1,0,1] and result = "#" or
            not(value = crtPos + [-1,0,1]) and result = "."
        )

    }

    int maxCycle() {
        result = max(int i | exists(fullValueAt(i)))
    }

    string text() {
        result = strictconcat(int row | row in [0..maxCycle() / 40] | strictconcat(int column | column in [0..39] | visible(row * 40 + column) order by column) , "\n" order by row )
    }
}

module TestImpl = Impl<testInput/0>;
module SmallTestImpl = Impl<smallInput/0>;
module RealImpl = Impl<realInput/0>;


select TestImpl::interestingSum(), RealImpl::interestingSum(), TestImpl::text(), RealImpl::text()

string testInput() {
    result = "addx 15\naddx -11\naddx 6\naddx -3\naddx 5\naddx -1\naddx -8\naddx 13\naddx 4\nnoop\naddx -1\naddx 5\naddx -1\naddx 5\naddx -1\naddx 5\naddx -1\naddx 5\naddx -1\naddx -35\naddx 1\naddx 24\naddx -19\naddx 1\naddx 16\naddx -11\nnoop\nnoop\naddx 21\naddx -15\nnoop\nnoop\naddx -3\naddx 9\naddx 1\naddx -3\naddx 8\naddx 1\naddx 5\nnoop\nnoop\nnoop\nnoop\nnoop\naddx -36\nnoop\naddx 1\naddx 7\nnoop\nnoop\nnoop\naddx 2\naddx 6\nnoop\nnoop\nnoop\nnoop\nnoop\naddx 1\nnoop\nnoop\naddx 7\naddx 1\nnoop\naddx -13\naddx 13\naddx 7\nnoop\naddx 1\naddx -33\nnoop\nnoop\nnoop\naddx 2\nnoop\nnoop\nnoop\naddx 8\nnoop\naddx -1\naddx 2\naddx 1\nnoop\naddx 17\naddx -9\naddx 1\naddx 1\naddx -3\naddx 11\nnoop\nnoop\naddx 1\nnoop\naddx 1\nnoop\nnoop\naddx -13\naddx -19\naddx 1\naddx 3\naddx 26\naddx -30\naddx 12\naddx -1\naddx 3\naddx 1\nnoop\nnoop\nnoop\naddx -9\naddx 18\naddx 1\naddx 2\nnoop\nnoop\naddx 9\nnoop\nnoop\nnoop\naddx -1\naddx 2\naddx -37\naddx 1\naddx 3\nnoop\naddx 15\naddx -21\naddx 22\naddx -6\naddx 1\nnoop\naddx 2\naddx 1\nnoop\naddx -10\nnoop\nnoop\naddx 20\naddx 1\naddx 2\naddx 2\naddx -6\naddx -11\nnoop\nnoop\nnoop"
}

string smallInput() {
    result = "noop\naddx 3\naddx -5"
}

string realInput() {
    result = "noop\nnoop\nnoop\naddx 3\naddx 20\nnoop\naddx -12\nnoop\naddx 4\nnoop\nnoop\nnoop\naddx 1\naddx 2\naddx 5\naddx 16\naddx -14\naddx -25\naddx 30\naddx 1\nnoop\naddx 5\nnoop\naddx -38\nnoop\nnoop\nnoop\naddx 3\naddx 2\nnoop\nnoop\nnoop\naddx 5\naddx 5\naddx 2\naddx 13\naddx 6\naddx -16\naddx 2\naddx 5\naddx -15\naddx 16\naddx 7\nnoop\naddx -2\naddx 2\naddx 5\naddx -39\naddx 4\naddx -2\naddx 2\naddx 7\nnoop\naddx -2\naddx 17\naddx -10\nnoop\nnoop\naddx 5\naddx -1\naddx 6\nnoop\naddx -2\naddx 5\naddx -8\naddx 12\naddx 3\naddx -2\naddx -19\naddx -16\naddx 2\naddx 5\nnoop\naddx 25\naddx 7\naddx -29\naddx 3\naddx 4\naddx -4\naddx 9\nnoop\naddx 2\naddx -20\naddx 23\naddx 1\nnoop\naddx 5\naddx -10\naddx 14\naddx 2\naddx -1\naddx -38\nnoop\naddx 20\naddx -15\nnoop\naddx 7\nnoop\naddx 26\naddx -25\naddx 2\naddx 7\nnoop\nnoop\naddx 2\naddx -5\naddx 6\naddx 5\naddx 2\naddx 8\naddx -3\nnoop\naddx 3\naddx -2\naddx -38\naddx 13\naddx -6\nnoop\naddx 1\naddx 5\nnoop\nnoop\nnoop\nnoop\naddx 2\nnoop\nnoop\naddx 7\naddx 3\naddx -2\naddx 2\naddx 5\naddx 2\nnoop\naddx 1\naddx 5\nnoop\nnoop\nnoop\nnoop\nnoop\nnoop"
}