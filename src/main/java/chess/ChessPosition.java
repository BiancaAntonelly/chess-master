package chess;

import boardgame.Position;

public class ChessPosition {

    //@ public invariant row >= 1 && row <= 8;
    //@ public invariant col >= 'a' && col <= 'h';

    //@ spec_public
    private final int row;

    //@ spec_public
    private final char col;

    /*@ public normal_behavior
      @   requires col >= 'a' && col <= 'h';
      @   requires row >= 1 && row <= 8;
      @   ensures this.row == row;
      @   ensures this.col == col;
      @ also public exceptional_behavior
      @   requires col < 'a' || col > 'h' || row < 1 || row > 8;
      @   signals_only ChessException;
      @   signals (ChessException e) true;
      @*/
    public ChessPosition(int row, char col) {
        if (col < 'a'|| col > 'h' || row < 1 || row > 8) {
            throw new ChessException("Posição inválida");
        }
        this.row = row;
        this.col = col;
    }

    /*@ public normal_behavior
      @   ensures \result == row;
      @   ensures \result >= 1 && \result <= 8;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ int getRow() {
        return row;
    }

    /*@ public normal_behavior
      @   ensures \result == col;
      @   ensures \result >= 'a' && \result <= 'h';
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ char getCol() {
        return col;
    }

    /*@ public normal_behavior
      @   ensures \result != null;
      @*/
    protected /*@ non_null @*/ Position toPosition() {
        return new Position(8 - row, col - 'a');
    }

    /*@ public normal_behavior
      @   requires pos != null;
      @   requires pos.getRow() >= 0 && pos.getRow() < 8;
      @   requires pos.getCol() >= 0 && pos.getCol() < 8;
      @   ensures \result != null;
      @*/
    protected static /*@ non_null @*/ ChessPosition fromPosition(/*@ non_null @*/ Position pos) {
        if (pos == null) {
            throw new IllegalArgumentException("Position cannot be null");
        }
        int rowCalc = 8 - pos.getRow();
        int colCalcInt = 'a' + pos.getCol();
        char colCalc = (char) colCalcInt;
        return new ChessPosition(rowCalc, colCalc);
    }

    /*@ public normal_behavior
      @   ensures \result != null;
      @   ensures \result.length() > 0;
      @   assignable \nothing;
      @*/
    public /*@ pure non_null @*/ String getString() {
        return row + ", " + col;
    }

    /*@ also public normal_behavior
      @   assignable \everything;
      @*/
    @Override
    public String toString() {
        return "" + col + row;
    }

    /*@ also public normal_behavior
      @   assignable \nothing;
      @*/
    @Override
    public /*@ pure @*/ boolean equals(/*@ nullable @*/ Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null || getClass() != obj.getClass()) {
            return false;
        }
        ChessPosition that = (ChessPosition) obj;
        return row == that.row && col == that.col;
    }

    /*@ also public normal_behavior
      @   assignable \everything;
      @*/
    @Override
    public int hashCode() {
        return 31 * row + col;
    }
}
