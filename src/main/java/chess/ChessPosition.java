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
      @   ensures \result == row;
      @   pure
      @*/
    public int getRow() { return row; }

    /*@ normal_behavior
      @   ensures \result == col;
      @   pure
      @*/
    public char getCol() { return col; }

    /*@ normal_behavior
      @   ensures \result != null;
      @   ensures \result.getRow() == 8 - row;
      @   ensures \result.getCol() == col - 'a';
      @   assignable \nothing;
      @   pure
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
      @   pure
      @*/
    protected static ChessPosition fromPosition(Position pos) {
        int rowCalc = 8 - pos.getRow();
        int colCalc = 'a' + pos.getCol();
        return new ChessPosition(rowCalc, (char) colCalc);
    }

    /*@ normal_behavior
      @   ensures \result != null;
      @   pure
      @*/
    public String getString() {
        return row + ", " + col;
    }
}
