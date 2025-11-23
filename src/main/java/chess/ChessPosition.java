package chess;

import boardgame.Position;

public class ChessPosition {

    //@ public invariant 1 <= row && row <= 8;
    //@ public invariant 'a' <= col && col <= 'h';

    //@ spec_public
    private final int row;

    //@ spec_public
    private final char col;

    /*@ public normal_behavior
      @   requires col >= 'a' && col <= 'h';
      @   requires row >= 1 && row <= 8;
      @   ensures this.row == row;
      @   ensures this.col == col;
      @*/
    public ChessPosition(int row, char col) {
        if (col < 'a'|| col > 'h' || row < 1 || row > 8) {
            throw new ChessException("Posição no tabuleiro inválida. Posições válidas: de a1 até h8");
        }

        this.row = row;
        this.col = col;
    }

    /*@ public normal_behavior
      @   ensures \result == row;
      @   pure
      @*/
    public int getRow() {
        return row;
    }

    /*@ public normal_behavior
      @   ensures \result == col;
      @   pure
      @*/
    public char getCol() {
        return col;
    }

    /*@ public normal_behavior
      @   ensures \result.getRow() == 8 - row;
      @   ensures \result.getCol() == col - 'a';
      @   pure
      @*/
    protected Position toPosition() {
        int newRow = 8 - row;
        int newCol = col - 'a';
        return new Position(newRow, newCol);
    }

    /*@
      @ public normal_behavior
      @     requires pos != null;
      @     requires pos.getRow() >= 0 && pos.getRow() <= 7;
      @     requires pos.getCol() >= 0 && pos.getCol() <= 7;
      @     ensures \result != null;
      @     ensures \result.getRow() == 8 - pos.getRow();
      @     ensures \result.getCol() == (char) ('a' + pos.getCol());
      @     assignable \nothing;
      @ also
      @ public normal_behavior
      @     requires pos == null || pos.getRow() < 0 || pos.getRow() > 7
      @           || pos.getCol() < 0 || pos.getCol() > 7;
      @     ensures \result == null;
      @     assignable \nothing;
      @*/
    protected static /*@ nullable */ ChessPosition fromPosition(/*@ nullable */ Position pos) {
        if (pos == null) {
            return null;
        }
        if (pos.getRow() < 0 || pos.getRow() > 7 || pos.getCol() < 0 || pos.getCol() > 7) {
            return null;
        }

        int toRow = 8 - pos.getRow();
        char toCol = (char) ('a' + pos.getCol());
        return new ChessPosition(toRow, toCol);
    }

    @Override
    public String toString() {
        return String.format("%c%d", col, row);
    }
}
