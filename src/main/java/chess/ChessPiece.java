package chess;

import boardgame.Board;
import boardgame.Piece;
import boardgame.Position;

/**
 * Classe abstrata que representa uma peça de xadrez.
 * Estende Piece e adiciona funcionalidades específicas do xadrez
 * como cor da peça e contagem de movimentos.
 */
public abstract class ChessPiece extends Piece {

    //@ public invariant color != null;
    //@ public invariant moveCount >= 0;
    //@ public invariant moveCount <= Integer.MAX_VALUE;

    //@ spec_public
    private final /*@ non_null @*/ Color color;

    //@ spec_public
    private int moveCount;

    /*@ public normal_behavior
      @   requires board != null;
      @   requires color != null;
      @   ensures this.color == color;
      @   ensures this.moveCount == 0;
      @   ensures getBoard() == board;
      @   assignable this.color, this.moveCount;
      @*/
    public ChessPiece(/*@ non_null @*/ Board board, /*@ non_null @*/ Color color) {
        super(board);
        this.color = color;
        this.moveCount = 0;
    }

    /*@ public normal_behavior
      @   ensures \result == color;
      @   ensures \result != null;
      @   ensures \result == Color.WHITE || \result == Color.BLACK;
      @   assignable \nothing;
      @   pure
      @*/
    public /*@ pure non_null @*/ Color getColor() {
        return color;
    }

    /*@ public normal_behavior
      @   ensures \result == moveCount;
      @   ensures \result >= 0;
      @   assignable \nothing;
      @   pure
      @*/
    public /*@ pure @*/ int getMoveCount() {
        return moveCount;
    }

    /*@ public normal_behavior
      @   requires moveCount < Integer.MAX_VALUE;
      @   ensures moveCount == \old(moveCount) + 1;
      @   ensures moveCount > 0;
      @   assignable moveCount;
      @*/
    public void increaseMoveCount() {
        moveCount++;
    }

    /*@ public normal_behavior
      @   requires moveCount > 0;
      @   ensures moveCount == \old(moveCount) - 1;
      @   ensures moveCount >= 0;
      @   assignable moveCount;
      @*/
    public void decreaseMoveCount() {
        moveCount--;
    }

    /*@ public normal_behavior
      @   requires position != null;
      @   requires position.getRow() >= 0 && position.getRow() < 8;
      @   requires position.getCol() >= 0 && position.getCol() < 8;
      @   ensures \result != null;
      @   ensures \result.getRow() == 8 - position.getRow();
      @   ensures \result.getCol() == (char)('a' + position.getCol());
      @   ensures \result.getRow() >= 1 && \result.getRow() <= 8;
      @   ensures \result.getCol() >= 'a' && \result.getCol() <= 'h';
      @   assignable \nothing;
      @   pure
      @*/
    public /*@ pure non_null @*/ ChessPosition getChessPosition() {
        return ChessPosition.fromPosition(position);
    }

    /*@ public normal_behavior
      @   requires pos != null;
      @   requires pos.getRow() >= 0 && pos.getRow() < 8;
      @   requires pos.getCol() >= 0 && pos.getCol() < 8;
      @   requires getBoard().positionExists(pos);
      @   ensures \result == true ==> getBoard().piece(pos) != null;
      @   ensures \result == true ==> ((ChessPiece)getBoard().piece(pos)).getColor() != this.color;
      @   ensures \result == false ==> (getBoard().piece(pos) == null ||
      @           ((ChessPiece)getBoard().piece(pos)).getColor() == this.color);
      @   assignable \nothing;
      @   pure
      @*/
    public /*@ pure @*/ boolean isThereOpponentPiece(/*@ non_null @*/ Position pos) {
        ChessPiece p = (ChessPiece) getBoard().piece(pos);
        return p != null && p.getColor() != color;
    }

    /*@ public normal_behavior
      @   requires pos != null;
      @   requires pos.getRow() >= 0 && pos.getRow() < 8;
      @   requires pos.getCol() >= 0 && pos.getCol() < 8;
      @   requires getBoard().positionExists(pos);
      @   ensures \result == true ==> (getBoard().piece(pos) == null ||
      @           ((ChessPiece)getBoard().piece(pos)).getColor() != this.color);
      @   ensures \result == false ==> (getBoard().piece(pos) != null &&
      @           ((ChessPiece)getBoard().piece(pos)).getColor() == this.color);
      @   assignable \nothing;
      @   pure
      @*/
    protected /*@ pure @*/ boolean canMoveTo(/*@ non_null @*/ Position pos) {
        ChessPiece p = (ChessPiece) getBoard().piece(pos);
        return p == null || p.getColor() != color;
    }

    /*@ also
      @ public normal_behavior
      @   ensures \result != null;
      @   ensures \result.length() >= 1;
      @   assignable \nothing;
      @   pure
      @*/
    @Override
    public abstract /*@ pure non_null @*/ String toString();
}
