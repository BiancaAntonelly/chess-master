package chess;

import boardgame.Board;
import boardgame.Piece;
import boardgame.Position;

public abstract class ChessPiece extends Piece {

    //@ public invariant color != null;
    //@ public invariant moveCount >= 0;
    //@ public invariant getBoard() != null;

    //@ spec_public
    private final Color color;

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
    public ChessPiece(Board board, Color color) {
        super(board);
        this.color = color;
    }

    /*@ public normal_behavior
      @ ensures \result == color;
      @ pure
      @*/
    public Color getColor() {
        return color;
    }

    /*@ public normal_behavior
      @ ensures \result == moveCount;
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
      @ requires moveCount > 0;
      @ ensures moveCount == \old(moveCount) - 1;
      @ assignable moveCount;
      @*/
    public void decreaseMoveCount() {
        moveCount--;
    }

    /*@ public normal_behavior
      @   requires getPosition() != null;
      @   requires getPosition().getRow() >= 0 && getPosition().getRow() < 8;
      @   requires getPosition().getCol() >= 0 && getPosition().getCol() < 8;
      @   ensures \result != null;
      @   ensures \result.getRow() == 8 - getPosition().getRow();
      @   ensures \result.getCol() == (char)('a' + getPosition().getCol());
      @   pure
      @*/
    public ChessPosition getChessPosition() {
        return ChessPosition.fromPosition(position);
    }

    /*@ public normal_behavior
      @   requires pos != null;
      @   requires getBoard() != null;
      @   requires getBoard().positionExists(pos);
      @   ensures \result == (getBoard().piece(pos) != null &&
      @                       ((ChessPiece)getBoard().piece(pos)).getColor() != this.color);
      @   pure
      @*/
    public boolean isThereOpponentPiece(Position pos) {
        ChessPiece p = (ChessPiece) getBoard().piece(pos);
        return p != null && p.getColor() != color;
    }

}
