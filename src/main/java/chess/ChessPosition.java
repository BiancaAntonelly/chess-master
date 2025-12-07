package chess;

import boardgame.Position;

public class ChessPosition {

    //@ public invariant 1 <= row && row <= 8;
    //@ public invariant 'a' <= col && col <= 'h';

    //@ spec_public
    private final int row;

    //@ spec_public
    private final char col;

    /*@ normal_behavior
      @   requires col >= 'a' && col <= 'h';
      @   requires row >= 1 && row <= 8;
      @   ensures this.row == row;
      @   ensures this.col == col;
      @*/
    public ChessPosition(int row, char col) {
        if (col < 'a'|| col > 'h' || row < 1 || row > 8) {
            throw new ChessException("Posição inválida");
        }
        this.row = row;
        this.col = col;
    }

    /*@ normal_behavior
      @ ensures \result == row;
      @ pure
      @*/
    public int getRow() { return row; }

    /*@ normal_behavior
      @ ensures \result == col;
      @ pure
      @*/
    public char getCol() { return col; }

    /*@ normal_behavior
      @   ensures \result != null;
      @   ensures \result.getRow() == 8 - row;
      @   ensures \result.getCol() == col - 'a';
      @   assignable \nothing;
      @*/
    protected Position toPosition() {
        return new Position(8 - row, col - 'a');
    }

    /*@ normal_behavior
      @   requires pos != null;
      @   requires pos.getRow() >= 0 && pos.getRow() <= 7;
      @   requires pos.getCol() >= 0 && pos.getCol() <= 7;
      @   ensures \result != null;
      @   ensures \result.getRow() == 8 - pos.getRow();
      @   ensures \result.getCol() == (char)('a' + pos.getCol());
      @   assignable \nothing;
      @ also
      @ normal_behavior
      @   requires pos == null || pos.getRow() < 0 || pos.getRow() > 7 || pos.getCol() < 0 || pos.getCol() > 7;
      @   ensures \result == null;
      @   assignable \nothing;
      @*/
    protected static /*@ nullable */ ChessPosition fromPosition(/*@ nullable */ Position pos) {

        if (pos == null) {
            return null;
        }

        if (pos.getRow() < 0 || pos.getRow() > 7 ||
                pos.getCol() < 0 || pos.getCol() > 7) {
            return null;
        }

        int rowCalc = 8 - pos.getRow();
        int colCalc = 'a' + pos.getCol();

        /*@ assert 1 <= rowCalc && rowCalc <= 8; */
        /*@ assert 0 <= pos.getCol() && pos.getCol() <= 7; */
        /*@ assert 'a' <= colCalc && colCalc <= 'h'; */

        /*@ assert rowCalc == 8 - pos.getRow(); */
        /*@ assert colCalc == 'a' + pos.getCol(); */

        return new ChessPosition(rowCalc, (char) colCalc);
    }

    /*@ normal_behavior
      @ ensures \result != null;
      @ pure
      @*/
    public String getString() {
        return row + ", " + col;
    }
}
