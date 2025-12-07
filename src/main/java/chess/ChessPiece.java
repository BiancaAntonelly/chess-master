package chess;

import boardgame.Board;
import boardgame.Piece;
import boardgame.Position;

/**
 * Classe abstrata que representa uma peça de xadrez genérica.
 * Estende a classe Piece do pacote boardgame e adiciona funcionalidades específicas de xadrez.
 */
public abstract class ChessPiece extends Piece {

    //@ public invariant color != null;
    //@ public invariant moveCount >= 0;

    //@ spec_public
    private final Color color;

    //@ spec_public
    private int moveCount;

    /*@ public normal_behavior
      @   requires board != null;
      @   requires color != null;
      @   ensures getColor() == color;
      @   ensures getMoveCount() == 0;
      @*/
    public ChessPiece(Board board, Color color) {
        super(board);
        this.color = color;
    }

    /*@ public normal_behavior
      @   ensures \result == color;
      @   ensures \result != null;
      @   assignable \nothing;
      @ pure
      @*/
    public Color getColor() {
        return color;
    }

    /*@ public normal_behavior
      @   ensures \result == moveCount;
      @   ensures \result >= 0;
      @   assignable \nothing;
      @ pure
      @*/
    public int getMoveCount() {
        return moveCount;
    }

    /*@ public normal_behavior
      @   requires moveCount < Integer.MAX_VALUE;
      @   ensures moveCount == \old(moveCount) + 1;
      @   assignable moveCount;
      @*/
    public void increaseMoveCount() {
        moveCount++;
    }

    /*@ public normal_behavior
      @   requires moveCount > 0;
      @   ensures moveCount == \old(moveCount) - 1;
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
      @   assignable \nothing;
      @*/
    public ChessPosition getChessPosition() {
        return ChessPosition.fromPosition(position);
    }

    /*@ public normal_behavior
      @   requires pos != null;
      @   assignable \nothing;
      @*/
    public boolean isThereOpponentPiece(Position pos) {
        ChessPiece p = (ChessPiece) getBoard().piece(pos);
        return p != null && p.getColor() != color;
    }

}
