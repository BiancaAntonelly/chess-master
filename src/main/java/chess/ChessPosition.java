package chess;

import boardgame.Position;

/**
 * Representa uma posição no tabuleiro de xadrez usando notação algébrica.
 * Coluna: 'a' até 'h' (da esquerda para direita)
 * Linha: 1 até 8 (de baixo para cima)
 */
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
      @   assignable this.row, this.col;
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
      @   ensures \result.getRow() == 8 - row;
      @   ensures \result.getCol() == col - 'a';
      @   ensures \result.getRow() >= 0 && \result.getRow() < 8;
      @   ensures \result.getCol() >= 0 && \result.getCol() < 8;
      @   assignable \nothing;
      @*/
    protected /*@ pure non_null @*/ Position toPosition() {
        return new Position(8 - row, col - 'a');
    }

    /*@ public normal_behavior
      @   requires pos != null;
      @   requires pos.getRow() >= 0 && pos.getRow() < 8;
      @   requires pos.getCol() >= 0 && pos.getCol() < 8;
      @   ensures \result != null;
      @   ensures \result.getRow() == 8 - pos.getRow();
      @   ensures \result.getCol() == (char)('a' + pos.getCol());
      @   assignable \nothing;
      @*/
    protected static /*@ pure non_null @*/ ChessPosition fromPosition(/*@ non_null @*/ Position pos) {
        int rowCalc = 8 - pos.getRow();
        int colCalc = 'a' + pos.getCol();
        return new ChessPosition(rowCalc, (char) colCalc);
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
      @   ensures \result != null;
      @   ensures \result.length() == 2;
      @   assignable \nothing;
      @*/
    @Override
    public /*@ pure non_null @*/ String toString() {
        return "" + col + row;
    }

    /*@ also
      @ public normal_behavior
      @   requires obj != null;
      @   ensures \result <==> (obj instanceof ChessPosition &&
      @           ((ChessPosition)obj).row == this.row &&
      @           ((ChessPosition)obj).col == this.col);
      @ also public normal_behavior
      @   requires obj == null;
      @   ensures \result == false;
      @   assignable \nothing;
      @*/
    @Override
    public /*@ pure @*/ boolean equals(/*@ nullable @*/ Object obj) {
        if (this == obj) return true;
        if (obj == null || getClass() != obj.getClass()) return false;
        ChessPosition that = (ChessPosition) obj;
        return row == that.row && col == that.col;
    }

    /*@ also
      @ public normal_behavior
      @   ensures \result == 31 * row + col;
      @   assignable \nothing;
      @*/
    @Override
    public /*@ pure @*/ int hashCode() {
        return 31 * row + col;
    }
}
